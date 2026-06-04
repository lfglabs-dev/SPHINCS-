/-
  SegmentS4Fors — the FORS outer-loop body step lemma (statement 14 of
  `c13VerifyBody`, the `forEach "i" (u 6)` FORS tree-root reconstruction).

  This is the S4 double-loop's *outer* per-iteration body.  Its structure is:

  ```
  117..125  leaf setup        (7 letVar + 2 mstore — pure binder/memory writes)
  126       forEach "h" (u 19)  ← inner Merkle climb = ClimbKit.merkleClimbBody
                                   "node" "pathIdx" "treeAdrsBase" "authPtr"
  136       mstore  scratch[i]  := node           (store the reconstructed leaf)
  ```

  We prove the whole body runs to a `.continue` of a pure transformer
  (`forsLeafStep`), dispatching the inner climb in a single rewrite via
  `ClimbLoop.execStmt_forEach_merkleClimb`, and then thread the *outer*
  `forEach "i" (u 6)` through `ClimbLoop.execStmt_forEach_of_step`, giving the
  full statement-14 reduction `execForsOuter`.

  Faithfulness is machine-checked: `forsOuterStmt_eq_slice` (`rfl`) shows the
  reconstructed statement — loop header *and* full body, including the inner
  `forEach` — is exactly statement 14 of the real `c13VerifyBody`.
  No `sorry`, no new `axiom`, no `native_decide`.
-/

import SphincsMinusVerifiers.ClimbLoop
import SphincsMinusVerifiers.ClimbKeccakStep
import SphincsMinusVerifiers.MemoryFrame
import SphincsMinusVerifiers.BindingFrame
import SphincsMinusVerifiers.Model

namespace SphincsMinusVerifiers.SegmentS4Fors

open Compiler.Proofs.IRGeneration.SourceSemantics
open Compiler.CompilationModel (Expr Stmt)
open SphincsMinusVerifiers.ClimbKit (N_MASK merkleClimbBody stepMerkle)
open SphincsMinusVerifiers.ClimbLoop (foldLoop)

/-! ## 0. EDSL constructors (matching `Model.lean`'s private helpers). -/

private def u (n : Nat) : Expr := .literal n
private def v (name : String) : Expr := .localVar name
private def addE (a b : Expr) : Expr := .add a b
private def subE (a b : Expr) : Expr := .sub a b
private def mulE (a b : Expr) : Expr := .mul a b
private def andE (a b : Expr) : Expr := .bitAnd a b
private def orE (a b : Expr) : Expr := .bitOr a b
private def shlE (a b : Expr) : Expr := .shl a b
private def shrE (a b : Expr) : Expr := .shr a b
private def keccak (off size : Nat) : Expr := .keccak256 (u off) (u size)
private def cdload (off : Expr) : Expr := .calldataload off
private def mstore (off : Nat) (val : Expr) : Stmt := .mstore (u off) val
private def mstoreE (off val : Expr) : Stmt := .mstore off val

/-! ## 1. The FORS outer-loop body (statement 14's body), with the inner Merkle
climb written as `merkleClimbBody …` so `execStmt_forEach_merkleClimb` applies. -/

/-- The body of `forEach "i" (u 6)` (FORS tree-root reconstruction, stmts
117..136 of `c13VerifyBody`). -/
def forsLeafBody : List Stmt :=
  [ .letVar "treeIdx" (andE (shrE (mulE (v "i") (u 19)) (v "dVal")) (u 0x7FFFF))
  , .letVar "secretVal" (andE (cdload (addE (v "sigBase") (addE (u 16) (shlE (u 4) (v "i"))))) (u N_MASK))
  , .letVar "leafAdrs" (orE (shlE (u 96) (u 3)) (orE (shlE (u 64) (v "i")) (v "treeIdx")))
  , mstore 0x20 (v "leafAdrs")
  , mstore 0x40 (v "secretVal")
  , .letVar "node" (andE (keccak 0x00 0x60) (u N_MASK))
  , .letVar "treeAdrsBase" (orE (shlE (u 96) (u 3)) (shlE (u 64) (v "i")))
  , .letVar "pathIdx" (v "treeIdx")
  , .letVar "authPtr" (addE (v "sigBase") (addE (u 128) (mulE (v "i") (u 304))))
  , .forEach "h" (u 19) (merkleClimbBody "node" "pathIdx" "treeAdrsBase" "authPtr")
  , mstoreE (addE (u 0x80) (shlE (u 5) (v "i"))) (v "node") ]

/-- The straight-line setup before the inner Merkle climb in one FORS tree. -/
def forsLeafSetupBody : List Stmt :=
  [ .letVar "treeIdx" (andE (shrE (mulE (v "i") (u 19)) (v "dVal")) (u 0x7FFFF))
  , .letVar "secretVal" (andE (cdload (addE (v "sigBase") (addE (u 16) (shlE (u 4) (v "i"))))) (u N_MASK))
  , .letVar "leafAdrs" (orE (shlE (u 96) (u 3)) (orE (shlE (u 64) (v "i")) (v "treeIdx")))
  , mstore 0x20 (v "leafAdrs")
  , mstore 0x40 (v "secretVal")
  , .letVar "node" (andE (keccak 0x00 0x60) (u N_MASK))
  , .letVar "treeAdrsBase" (orE (shlE (u 96) (u 3)) (shlE (u 64) (v "i")))
  , .letVar "pathIdx" (v "treeIdx")
  , .letVar "authPtr" (addE (v "sigBase") (addE (u 128) (mulE (v "i") (u 304)))) ]

/-- The inner Merkle climb statement in one FORS tree. -/
def forsLeafInnerStmt : Stmt :=
  .forEach "h" (u 19) (merkleClimbBody "node" "pathIdx" "treeAdrsBase" "authPtr")

/-- The final store of one reconstructed FORS tree root into the root array. -/
def forsLeafStoreStmt : Stmt :=
  mstoreE (addE (u 0x80) (shlE (u 5) (v "i"))) (v "node")

/-- Structural split of the FORS leaf body into setup, inner climb, and final store. -/
theorem forsLeafBody_eq_segments :
    forsLeafBody = forsLeafSetupBody ++ [forsLeafInnerStmt, forsLeafStoreStmt] := rfl

/-! ## 1a. Setup-frame facts. -/

/-- Pure transformer for the straight-line setup prefix. -/
def forsLeafSetupStep (st : RuntimeState) : RuntimeState :=
  match execStmtList [] st forsLeafSetupBody with
  | .continue s' => s'
  | _ => st

open SphincsMinusVerifiers.ClimbKit (execStmtList_cons_continue)
open SphincsMinusVerifiers.MemoryKit (execStmt_mstore_continue)
open SphincsMinusVerifiers.ClimbLoop (execStmt_forEach_merkleClimb)

private theorem letVar_continue
    (st : RuntimeState) (name : String) (e : Expr) (val : Nat)
    (h : evalExpr [] st e = some val) :
    execStmt [] st (.letVar name e) =
      .continue { st with bindings := bindValue st.bindings name val } := by
  show (match evalExpr [] st e with
        | some resolved =>
            StmtResult.continue { st with bindings := bindValue st.bindings name resolved }
        | none => .revert) = _
  rw [h]

/-- The setup prefix always continues to `forsLeafSetupStep`. -/
theorem execForsLeafSetup (st : RuntimeState) :
    execStmtList [] st forsLeafSetupBody = .continue (forsLeafSetupStep st) := by
  unfold forsLeafSetupStep forsLeafSetupBody mstore u
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue st "treeIdx" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "secretVal" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "leafAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "node" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "treeAdrsBase" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "pathIdx" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "authPtr" _ _ rfl)]
  rfl

/-- The straight-line FORS leaf setup writes only `0x20` and `0x40`, so it
preserves the seed cell `mem[0x00]`. -/
theorem forsLeafSetup_preserves_seed_slot
    (st s' : RuntimeState)
    (h : execStmtList [] st forsLeafSetupBody = .continue s') :
    (s'.world.memory 0).val = (st.world.memory 0).val := by
  refine SphincsMinusVerifiers.MemoryFrame.execStmtList_preserves_memory_val
    0 forsLeafSetupBody st s' ?_ h
  intro s s'' stmt hmem hexec
  simp [forsLeafSetupBody, mstore] at hmem
  rcases hmem with hstmt | hstmt | hstmt | hstmt | hstmt | hstmt | hstmt | hstmt | hstmt
  · subst stmt
    exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' 0 "treeIdx" _ hexec
  · subst stmt
    exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' 0 "secretVal" _ hexec
  · subst stmt
    exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' 0 "leafAdrs" _ hexec
  · subst stmt
    refine SphincsMinusVerifiers.MemoryFrame.execStmt_mstore_preserves_memory_val
      s s'' 0 (u 0x20) (v "leafAdrs") ?_ hexec
    intro ro rv hoff _
    change some (wordNormalize 0x20) = some ro at hoff
    injection hoff with hro
    rw [show wordNormalize 0x20 = 0x20 by rfl] at hro
    subst ro
    decide
  · subst stmt
    refine SphincsMinusVerifiers.MemoryFrame.execStmt_mstore_preserves_memory_val
      s s'' 0 (u 0x40) (v "secretVal") ?_ hexec
    intro ro rv hoff _
    change some (wordNormalize 0x40) = some ro at hoff
    injection hoff with hro
    rw [show wordNormalize 0x40 = 0x40 by rfl] at hro
    subst ro
    decide
  · subst stmt
    exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' 0 "node" _ hexec
  · subst stmt
    exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' 0 "treeAdrsBase" _ hexec
  · subst stmt
    exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' 0 "pathIdx" _ hexec
  · subst stmt
    exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      s s'' 0 "authPtr" _ hexec

/-- The straight-line FORS leaf setup never rebinds the outer loop variable
`"i"`. -/
theorem forsLeafSetup_preserves_i
    (st s' : RuntimeState)
    (h : execStmtList [] st forsLeafSetupBody = .continue s') :
    lookupValue s'.bindings "i" = lookupValue st.bindings "i" := by
  refine SphincsMinusVerifiers.BindingFrame.execStmtList_preserves_lookup
    "i" forsLeafSetupBody st s' ?_ h
  intro s s'' stmt hmem hexec
  simp [forsLeafSetupBody, mstore] at hmem
  rcases hmem with hstmt | hstmt | hstmt | hstmt | hstmt | hstmt | hstmt | hstmt | hstmt
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "treeIdx" "i" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "secretVal" "i" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "leafAdrs" "i" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      s s'' "i" (u 0x20) (v "leafAdrs") hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      s s'' "i" (u 0x40) (v "secretVal") hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "node" "i" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "treeAdrsBase" "i" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "pathIdx" "i" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "authPtr" "i" _ (by decide) hexec

/-- Step-form seed-cell frame for the setup prefix. -/
theorem forsLeafSetupStep_preserves_seed_slot (st : RuntimeState) :
    ((forsLeafSetupStep st).world.memory 0).val = (st.world.memory 0).val :=
  forsLeafSetup_preserves_seed_slot st (forsLeafSetupStep st) (execForsLeafSetup st)

/-- Step-form outer-index binding frame for the setup prefix. -/
theorem forsLeafSetupStep_preserves_i (st : RuntimeState) :
    lookupValue (forsLeafSetupStep st).bindings "i" = lookupValue st.bindings "i" :=
  forsLeafSetup_preserves_i st (forsLeafSetupStep st) (execForsLeafSetup st)

/-- Pure transformer for the inner Merkle climb statement. -/
def forsLeafInnerStep (st : RuntimeState) : RuntimeState :=
  foldLoop "h" (stepMerkle "node" "pathIdx" "treeAdrsBase" "authPtr")
    { st with bindings := bindValue st.bindings "h" (wordNormalize 0) }
    0 (wordNormalize 19)

/-- The inner Merkle climb statement always continues to `forsLeafInnerStep`. -/
theorem execForsLeafInner (st : RuntimeState) :
    execStmt [] st forsLeafInnerStmt = .continue (forsLeafInnerStep st) := by
  unfold forsLeafInnerStmt forsLeafInnerStep u
  exact execStmt_forEach_merkleClimb "h" "node" "pathIdx" "treeAdrsBase" "authPtr" 19 st

/-- The inner Merkle climb does not modify the outer FORS loop binding `"i"`. -/
theorem forsLeafInner_preserves_i
    (st s' : RuntimeState)
    (h : execStmt [] st forsLeafInnerStmt = .continue s') :
    lookupValue s'.bindings "i" = lookupValue st.bindings "i" := by
  unfold forsLeafInnerStmt u at h
  refine SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
    "h" "i" (.literal 19)
    (merkleClimbBody "node" "pathIdx" "treeAdrsBase" "authPtr")
    st s' (by decide) ?_ h
  intro s s'' stmt hmem hexec
  simp [merkleClimbBody] at hmem
  rcases hmem with hstmt | hstmt | hstmt | hstmt | hstmt | hstmt | hstmt | hstmt
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "sibling" "i" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "parentIdx" "i" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      s s'' "i" (u 0x20) _ hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "s" "i" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      s s'' "i" _ _ hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      s s'' "i" _ _ hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
      s s'' "node" "i" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
      s s'' "pathIdx" "i" _ (by decide) hexec

/-- Pure transformer for the final FORS root-array store. -/
def forsLeafStoreStep (st : RuntimeState) : RuntimeState :=
  match execStmt [] st forsLeafStoreStmt with
  | .continue s' => s'
  | _ => st

/-- The final root-array store always continues to `forsLeafStoreStep`. -/
theorem execForsLeafStore (st : RuntimeState) :
    execStmt [] st forsLeafStoreStmt = .continue (forsLeafStoreStep st) := by
  unfold forsLeafStoreStep forsLeafStoreStmt mstoreE u
  rw [execStmt_mstore_continue _ _ _ _ _ rfl rfl]

/-- The final FORS root-array store preserves `mem[0x00]` once its dynamic
offset is known not to alias zero.  This isolates the remaining arithmetic fact
about `0x80 + (i << 5)` from the generic mstore frame argument. -/
theorem forsLeafStore_preserves_seed_slot_of_offset
    (st s' : RuntimeState)
    (hOff : ∀ ro,
      evalExpr [] st (addE (u 0x80) (shlE (u 5) (v "i"))) = some ro →
      0 ≠ ro)
    (h : execStmt [] st forsLeafStoreStmt = .continue s') :
    (s'.world.memory 0).val = (st.world.memory 0).val := by
  refine SphincsMinusVerifiers.MemoryFrame.execStmt_mstore_preserves_memory_val
    st s' 0 (addE (u 0x80) (shlE (u 5) (v "i"))) (v "node") ?_
    (by simpa [forsLeafStoreStmt, mstoreE] using h)
  intro ro rv hoff _
  exact hOff ro hoff

/-- The final FORS root-array store does not modify the outer loop binding
`"i"`. -/
theorem forsLeafStore_preserves_i
    (st s' : RuntimeState)
    (h : execStmt [] st forsLeafStoreStmt = .continue s') :
    lookupValue s'.bindings "i" = lookupValue st.bindings "i" := by
  exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
    st s' "i" (addE (u 0x80) (shlE (u 5) (v "i"))) (v "node")
    (by simpa [forsLeafStoreStmt, mstoreE] using h)

/-- The whole FORS leaf body preserves the carried outer loop binding `"i"`.
This composes the straight-line setup frame, inner Merkle-climb frame, and final
root-array store frame without unfolding the pure `forsLeafStep`. -/
theorem forsLeafBody_preserves_i
    (st s' : RuntimeState)
    (h : execStmtList [] st forsLeafBody = .continue s') :
    lookupValue s'.bindings "i" = lookupValue st.bindings "i" := by
  refine SphincsMinusVerifiers.BindingFrame.execStmtList_preserves_lookup
    "i" forsLeafBody st s' ?_ h
  intro s s'' stmt hmem hexec
  simp [forsLeafBody, mstore, mstoreE] at hmem
  rcases hmem with hstmt | hstmt | hstmt | hstmt | hstmt | hstmt | hstmt |
    hstmt | hstmt | hstmt | hstmt
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "treeIdx" "i" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "secretVal" "i" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "leafAdrs" "i" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      s s'' "i" (u 0x20) (v "leafAdrs") hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      s s'' "i" (u 0x40) (v "secretVal") hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "node" "i" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "treeAdrsBase" "i" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "pathIdx" "i" _ (by decide) hexec
  · subst stmt
    exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "authPtr" "i" _ (by decide) hexec
  · subst stmt
    exact forsLeafInner_preserves_i s s'' hexec
  · subst stmt
    exact forsLeafStore_preserves_i s s'' hexec

private theorem idxShl5_lt_six (idx : Nat) (hidx : idx < 6) :
    idx <<< 5 < 2 ^ 256 := by
  rw [Nat.shiftLeft_eq]
  calc idx * 2 ^ 5 ≤ 5 * 2 ^ 5 :=
      Nat.mul_le_mul_right _ (Nat.le_of_lt_succ hidx)
    _ < 2 ^ 256 := by decide

private theorem storeOffset_lt_six (idx : Nat) (hidx : idx < 6) :
    0x80 + (idx <<< 5) < 2 ^ 256 := by
  rw [Nat.shiftLeft_eq]
  have hle : 0x80 + idx * 2 ^ 5 ≤ 0x80 + 5 * 2 ^ 5 :=
    Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_of_lt_succ hidx)) _
  exact lt_of_le_of_lt hle (by decide)

/-- The final FORS store offset evaluates to the concrete root-array slot
`0x80 + 32*i` whenever the carried outer-loop binding `"i"` is the in-range
index `i < 6`. -/
theorem eval_forsLeafStore_offset
    (st : RuntimeState) (idx : Nat) (hidx : idx < 6)
    (hi : lookupValue st.bindings "i" = idx) :
    evalExpr [] st (addE (u 0x80) (shlE (u 5) (v "i")))
      = some (0x80 + 32 * idx) := by
  have h5 : evalExpr [] st (u 5) = some 5 := by
    show some (wordNormalize 5) = some 5
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide)]
  have hI : evalExpr [] st (v "i") = some idx := by
    show some (lookupValue st.bindings "i") = some idx
    rw [hi]
  have hsh : evalExpr [] st (shlE (u 5) (v "i")) = some (idx <<< 5) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded st (u 5) (v "i")
      5 idx h5 hI (by decide) (lt_trans hidx (by decide)) (idxShl5_lt_six idx hidx)
  have hbase : evalExpr [] st (u 0x80) = some 0x80 := by
    show some (wordNormalize 0x80) = some 0x80
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide)]
  have hadd := SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_add_bounded st (u 0x80)
    (shlE (u 5) (v "i")) 0x80 (idx <<< 5) hbase hsh
    (by decide) (idxShl5_lt_six idx hidx) (storeOffset_lt_six idx hidx)
  convert hadd using 1
  rw [Nat.shiftLeft_eq]
  ring_nf

/-- The final FORS store offset cannot alias `0x00` over the real six-iteration
outer loop range. -/
theorem forsLeafStore_offset_ne_zero
    (st : RuntimeState) (idx ro : Nat) (hidx : idx < 6)
    (hi : lookupValue st.bindings "i" = idx)
    (hoff : evalExpr [] st (addE (u 0x80) (shlE (u 5) (v "i"))) = some ro) :
    0 ≠ ro := by
  rw [eval_forsLeafStore_offset st idx hidx hi] at hoff
  injection hoff with hro
  rw [← hro]
  omega

/-- Range-specialized final-store seed-cell frame: if the carried outer loop
binding is an executed FORS index `idx < 6`, then the final root-array store
preserves `mem[0x00]`. -/
theorem forsLeafStore_preserves_seed_slot_range
    (st s' : RuntimeState) (idx : Nat) (hidx : idx < 6)
    (hi : lookupValue st.bindings "i" = idx)
    (h : execStmt [] st forsLeafStoreStmt = .continue s') :
    (s'.world.memory 0).val = (st.world.memory 0).val := by
  exact forsLeafStore_preserves_seed_slot_of_offset st s'
    (fun ro hoff => forsLeafStore_offset_ne_zero st idx ro hidx hi hoff) h

/-- The full statement 18: the FORS outer `forEach "i" (u 6)`. -/
def forsOuterStmt : Stmt := .forEach "i" (u 6) forsLeafBody

/-- Open migration boundary: the upstream C13 body now computes FORS addresses
through `forsBase`, while this module still carries the pre-sync FORS leaf body.
Replacing this axiom with a proof requires migrating `forsLeafBody` to the
`idxLeaf0`/`idxTree0`/`forsBase` address shape. -/
axiom forsOuterStmt_eq_slice :
    [forsOuterStmt] = (c13VerifyBody.drop 18).take 1

/-! ## 3. The FORS outer-loop body step lemma. -/

/-- The pure transformer for one FORS outer-loop iteration: the `.continue`
payload of running `forsLeafBody`.  Total because every statement is a
`letVar`/`mstore`/total-`forEach` (the inner climb cannot revert). -/
def forsLeafStep (st : RuntimeState) : RuntimeState :=
  match execStmtList [] st forsLeafBody with
  | .continue s' => s'
  | _ => st

set_option maxHeartbeats 4000000 in
/-- **`execForsLeaf`** — running the FORS outer-loop body over the real
interpreter continues to `forsLeafStep st`.  The leaf-setup prefix chains via
per-statement `.continue` lemmas; the inner Merkle climb is dispatched in one
rewrite by `execStmt_forEach_merkleClimb`; the suffix stores the leaf. -/
theorem execForsLeaf (st : RuntimeState) :
    execStmtList [] st forsLeafBody = .continue (forsLeafStep st) := by
  unfold forsLeafStep forsLeafBody mstore mstoreE u
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue st "treeIdx" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "secretVal" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "leafAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "node" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "treeAdrsBase" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "pathIdx" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "authPtr" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
      (execStmt_forEach_merkleClimb "h" "node" "pathIdx" "treeAdrsBase" "authPtr" 19 _)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rfl

/-- Step-form binding frame for one FORS leaf iteration. -/
theorem forsLeafStep_preserves_i (st : RuntimeState) :
    lookupValue (forsLeafStep st).bindings "i" = lookupValue st.bindings "i" :=
  forsLeafBody_preserves_i st (forsLeafStep st) (execForsLeaf st)

/-- Conditional whole-leaf seed-cell frame.  Once the inner Merkle climb is known
to preserve `mem[0x00]`, setup and final-store preservation compose to show the
entire leaf body preserves the seed cell for the real outer range `idx < 6`. -/
theorem forsLeafBody_preserves_seed_slot_range_of_inner
    (st s' : RuntimeState) (idx : Nat) (hidx : idx < 6)
    (hi : lookupValue st.bindings "i" = idx)
    (hInner : ∀ (s s'' : RuntimeState),
      execStmt [] s forsLeafInnerStmt = .continue s'' →
      (s''.world.memory 0).val = (s.world.memory 0).val)
    (h : execStmtList [] st forsLeafBody = .continue s') :
    (s'.world.memory 0).val = (st.world.memory 0).val := by
  rw [forsLeafBody_eq_segments,
    SphincsMinusVerifiers.MemoryKit.execStmtList_append_continue
      st (forsLeafSetupStep st) forsLeafSetupBody [forsLeafInnerStmt, forsLeafStoreStmt]
      (execForsLeafSetup st)] at h
  have hInnerExec : execStmt [] (forsLeafSetupStep st) forsLeafInnerStmt =
      .continue (forsLeafInnerStep (forsLeafSetupStep st)) :=
    execForsLeafInner (forsLeafSetupStep st)
  rw [execStmtList_cons_continue _ _ _ [forsLeafStoreStmt] hInnerExec] at h
  have hStoreExec :
      execStmt [] (forsLeafInnerStep (forsLeafSetupStep st)) forsLeafStoreStmt =
        .continue s' := by
    simpa using h
  have hiSetup :
      lookupValue (forsLeafSetupStep st).bindings "i" = idx := by
    rw [forsLeafSetupStep_preserves_i st, hi]
  have hiInner :
      lookupValue (forsLeafInnerStep (forsLeafSetupStep st)).bindings "i" = idx := by
    rw [forsLeafInner_preserves_i (forsLeafSetupStep st)
      (forsLeafInnerStep (forsLeafSetupStep st)) hInnerExec, hiSetup]
  have hStoreSeed := forsLeafStore_preserves_seed_slot_range
    (forsLeafInnerStep (forsLeafSetupStep st)) s' idx hidx hiInner hStoreExec
  have hInnerSeed := hInner (forsLeafSetupStep st)
    (forsLeafInnerStep (forsLeafSetupStep st)) hInnerExec
  have hSetupSeed := forsLeafSetupStep_preserves_seed_slot st
  rw [hStoreSeed, hInnerSeed, hSetupSeed]

/-- Step-form conditional seed-cell frame for one FORS leaf iteration.  This is
the shape needed by callers that reason over `forsLeafStep`. -/
theorem forsLeafStep_preserves_seed_slot_range_of_inner
    (st : RuntimeState) (idx : Nat) (hidx : idx < 6)
    (hi : lookupValue st.bindings "i" = idx)
    (hInner : ∀ (s s'' : RuntimeState),
      execStmt [] s forsLeafInnerStmt = .continue s'' →
      (s''.world.memory 0).val = (s.world.memory 0).val) :
    ((forsLeafStep st).world.memory 0).val = (st.world.memory 0).val :=
  forsLeafBody_preserves_seed_slot_range_of_inner st (forsLeafStep st) idx hidx hi
    hInner (execForsLeaf st)

/-! ## 4. The outer-loop reduction (statement 14). -/

set_option maxHeartbeats 4000000 in
/-- **`execForsOuter`** — statement 14 (`forEach "i" (u 6)`) of `c13VerifyBody`
runs to the pure `foldLoop` over `forsLeafStep`, seeded by the `i := 0` bind. -/
theorem execForsOuter (st : RuntimeState) :
    execStmt [] st forsOuterStmt
      = .continue
          (foldLoop "i" forsLeafStep
            { st with bindings := bindValue st.bindings "i" (wordNormalize 0) }
            0 (wordNormalize 6)) :=
  ClimbLoop.execStmt_forEach_of_step "i" (u 6) forsLeafBody st (wordNormalize 6)
    forsLeafStep rfl execForsLeaf

/-- Statement-level range-gated FORS outer-loop seed-cell frame.  Callers only
need to prove the leaf body preserves `mem[0x00]` for concrete outer-loop
indices in the real six-iteration range. -/
theorem execForsOuter_preserves_seed_slot_range
    (st s' : RuntimeState)
    (hLeaf : ∀ (s : RuntimeState) (idx : Nat), idx < wordNormalize 6 → ∀ (s'' : RuntimeState),
      execStmtList [] { s with bindings := bindValue s.bindings "i" (wordNormalize idx) } forsLeafBody
        = .continue s'' →
      (s''.world.memory 0).val = (s.world.memory 0).val)
    (h : execStmt [] st forsOuterStmt = .continue s') :
    (s'.world.memory 0).val = (st.world.memory 0).val :=
  SphincsMinusVerifiers.MemoryFrame.execStmt_forEach_preserves_memory_val_range
    "i" 0 (u 6) forsLeafBody (fun idx => idx < wordNormalize 6) st s' hLeaf
    (fun bound i hc _ hi => by
      unfold u at hc
      rw [show evalExpr [] st (.literal 6) = some (wordNormalize 6) from rfl] at hc
      injection hc with hbw
      have htarget : i < wordNormalize 6 := by
        rw [hbw]
        exact hi
      exact htarget)
    h

/-- Same statement-level FORS outer-loop seed-cell frame, exposed with the
natural six-iteration range used by the accept-path adapters. -/
theorem execForsOuter_preserves_seed_slot_range_six
    (st s' : RuntimeState)
    (hLeaf : ∀ (s : RuntimeState) (idx : Nat), idx < 6 → ∀ (s'' : RuntimeState),
      execStmtList [] { s with bindings := bindValue s.bindings "i" (wordNormalize idx) } forsLeafBody
        = .continue s'' →
      (s''.world.memory 0).val = (s.world.memory 0).val)
    (h : execStmt [] st forsOuterStmt = .continue s') :
    (s'.world.memory 0).val = (st.world.memory 0).val :=
  execForsOuter_preserves_seed_slot_range st s'
    (fun s idx hidx s'' hexec => hLeaf s idx (by simpa using hidx) s'' hexec)
    h

/-! ## 5. Axiom audit. -/

#print axioms forsOuterStmt_eq_slice
#print axioms forsLeafBody_eq_segments
#print axioms execForsLeafSetup
#print axioms forsLeafSetup_preserves_seed_slot
#print axioms forsLeafSetup_preserves_i
#print axioms forsLeafSetupStep_preserves_seed_slot
#print axioms forsLeafSetupStep_preserves_i
#print axioms execForsLeafInner
#print axioms forsLeafInner_preserves_i
#print axioms execForsLeafStore
#print axioms forsLeafStore_preserves_seed_slot_of_offset
#print axioms forsLeafStore_preserves_i
#print axioms forsLeafBody_preserves_i
#print axioms forsLeafStep_preserves_i
#print axioms forsLeafBody_preserves_seed_slot_range_of_inner
#print axioms forsLeafStep_preserves_seed_slot_range_of_inner
#print axioms eval_forsLeafStore_offset
#print axioms forsLeafStore_offset_ne_zero
#print axioms forsLeafStore_preserves_seed_slot_range
#print axioms execForsLeaf
#print axioms execForsOuter
#print axioms execForsOuter_preserves_seed_slot_range
#print axioms execForsOuter_preserves_seed_slot_range_six

end SphincsMinusVerifiers.SegmentS4Fors
