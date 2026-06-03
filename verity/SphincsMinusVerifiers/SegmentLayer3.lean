/-
  SegmentLayer3 — the Layer-3 hypertree-climb loop body (statement 25 of
  `c13VerifyBody`, the `forEach "layer" (u 2)` outer climb).

  The layer body is *guarded*: after accumulating the WOTS checksum `digitSum`
  it reverts unless `digitSum = 208` (Model.lean:167).  So unlike the totally
  continuing FORS/Merkle loops, this body has the shape

  ```
  execStmtList [] ls layerBody = if layerGuard ls then .continue (stepLayer ls) else .revert
  ```

  proved here as `execLayerBody`.  This is exactly the `hstep` hypothesis of the
  guarded loop-threading engine `ClimbLoopGuarded.execForEachLoop_of_guarded_step`,
  so once the per-iteration guards are discharged the whole `forEach "layer"`
  folds to a pure `foldLoop` over `stepLayer` (`execLayerLoop`).

  Faithfulness is machine-checked: `layerStmt_eq_slice` (`rfl`) shows the
  reconstructed statement — loop header and full body, every inner `forEach` and
  the checksum-guard `ite` included — is exactly statement 25 of `c13VerifyBody`.
  No `sorry`, no new `axiom`, no `native_decide`.
-/

import SphincsMinusVerifiers.ClimbLoop
import SphincsMinusVerifiers.ClimbLoopGuarded
import SphincsMinusVerifiers.ClimbKeccakStep
import SphincsMinusVerifiers.BindingFrame
import SphincsMinusVerifiers.MemoryFrame
import SphincsMinusVerifiers.Model
import SphincsMinusVerifierSpec.C13Concrete

namespace SphincsMinusVerifiers.SegmentLayer3

open Compiler.Proofs.IRGeneration.SourceSemantics
open Compiler.CompilationModel
open Compiler.CompilationModel (Expr Stmt)
open SphincsMinusVerifiers.ClimbKit (N_MASK merkleClimbBody wotsChainBody stepMerkle stepWots
  wotsChainStep execStmtList_cons_continue)
open SphincsMinusVerifiers.MemoryKit (execStmt_mstore_continue execStmt_letVar_continue)
open SphincsMinusVerifiers.ClimbLoop (foldLoop execStmt_forEach_of_step execStmt_forEach_merkleClimb)

/-! ## 0. EDSL constructors (matching `Model.lean`'s private helpers). -/

private def u (n : Nat) : Expr := .literal n
private def v (name : String) : Expr := .localVar name
private def notE (x : Expr) : Expr := .logicalNot x
private def eqE (a b : Expr) : Expr := .eq a b
private def addE (a b : Expr) : Expr := .add a b
private def subE (a b : Expr) : Expr := .sub a b
private def mulE (a b : Expr) : Expr := .mul a b
private def andE (a b : Expr) : Expr := .bitAnd a b
private def orE (a b : Expr) : Expr := .bitOr a b
private def xorE (a b : Expr) : Expr := .bitXor a b
private def shlE (a b : Expr) : Expr := .shl a b
private def shrE (a b : Expr) : Expr := .shr a b
private def keccak (off size : Nat) : Expr := .keccak256 (u off) (u size)
private def cdload (off : Expr) : Expr := .calldataload off
private def mloadE (off : Expr) : Expr := .mload off
private def mstore (off : Nat) (val : Expr) : Stmt := .mstore (u off) val
private def mstoreE (off val : Expr) : Stmt := .mstore off val

private def revert0 : List Stmt :=
  [ .unsafeYul <|
      UnsafeYulFragment.rawRevert (.lit 0) (.lit 0)
        { name := "raw_yul_revert_0_0_refines_solidity_assembly"
          obligation := "The handwritten Yul revert(0, 0) must match the Solidity assembly observable revert behavior."
          proofStatus := .assumed }
        "raw_yul_revert_0_0" ]

/-- The checksum-guard condition: `digitSum ≠ 208`. -/
private def condE : Expr := notE (eqE (v "digitSum") (u 208))

/-! ## 1. Per-statement `.continue` combinator for `assignVar`. -/

/-- `assignVar` shares the interpreter's `letVar` step semantics. -/
private theorem assignVar_continue
    (st : RuntimeState) (name : String) (e : Expr) (val : Nat)
    (h : evalExpr [] st e = some val) :
    execStmt [] st (.assignVar name e) =
      .continue { st with bindings := bindValue st.bindings name val } := by
  show (match evalExpr [] st e with
        | some resolved =>
            StmtResult.continue { st with bindings := bindValue st.bindings name resolved }
        | none => .revert) = _
  rw [h]

/-! ## 2. Inner-loop body step lemmas. -/

/-- The digit-sum accumulation loop body (`forEach "ii" (u 43)`). -/
def digitSumBody : List Stmt :=
  [ .assignVar "digitSum" (addE (v "digitSum") (andE (shrE (mulE (v "ii") (u 3)) (v "d")) (u 0x7))) ]

def digitSumStep (st : RuntimeState) : RuntimeState :=
  match execStmtList [] st digitSumBody with | .continue s' => s' | _ => st

def digitAt (d i : Nat) : Nat :=
  (d >>> (3 * i)) % 8

def digitSumFold (d acc index : Nat) : Nat → Nat
  | 0 => acc
  | remaining + 1 => digitSumFold d (acc + digitAt d index) (index + 1) remaining

theorem digitSumStepLemma (st : RuntimeState) :
    execStmtList [] st digitSumBody = .continue (digitSumStep st) := by
  unfold digitSumStep digitSumBody
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue st "digitSum" _ _ rfl)]
  rfl

/-- Low-three-bit mask in the numeric form used by the concrete WOTS digit sum. -/
theorem nat_land_low3 (x : Nat) : Nat.land x 0x7 = x % 2 ^ 3 := by
  change (x &&& (2 ^ 3 - 1)) = x % 2 ^ 3
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_land]
  by_cases hi : i < 3
  · have hmask : (2 ^ 3 - 1).testBit i = true := by
      rw [Nat.testBit_two_pow_sub_one]
      exact decide_eq_true hi
    rw [hmask, Bool.and_true]
    rw [Nat.testBit_mod_two_pow]
    simp [hi]
  · have hmask : (2 ^ 3 - 1).testBit i = false := by
      rw [Nat.testBit_two_pow_sub_one]
      exact decide_eq_false hi
    rw [hmask, Bool.and_false]
    rw [Nat.testBit_mod_two_pow]
    simp [hi]

/-- One executable digit-sum loop iteration adds the next three-bit WOTS digit.
This is the local arithmetic brick for the eventual 43-iteration digit-cell
correspondence; it does not unfold the enclosing layer prefix. -/
theorem digitSumStep_digitSum_eq
    (st : RuntimeState) (ii d acc : Nat)
    (hii : lookupValue st.bindings "ii" = ii)
    (hd : lookupValue st.bindings "d" = d)
    (hacc : lookupValue st.bindings "digitSum" = acc)
    (hiiLt : ii < 43)
    (hdLt : d < 2 ^ 256)
    (haddLt : acc + (d >>> (3 * ii)) % 8 < 2 ^ 256) :
    lookupValue (digitSumStep st).bindings "digitSum"
      = acc + (d >>> (3 * ii)) % 8 := by
  have hiiEval : evalExpr [] st (v "ii") = some ii := by
    exact congrArg some hii
  have hdEval : evalExpr [] st (v "d") = some d := by
    exact congrArg some hd
  have haccEval : evalExpr [] st (v "digitSum") = some acc := by
    exact congrArg some hacc
  have hmul :
      evalExpr [] st (mulE (v "ii") (u 3)) = some (3 * ii) := by
    show (do
      let lhs : Verity.Core.Uint256 := ← evalExpr [] st (v "ii")
      let rhs : Verity.Core.Uint256 := ← evalExpr [] st (u 3)
      pure (lhs * rhs).val) = some (3 * ii)
    rw [hiiEval]
    show some ((Verity.Core.Uint256.ofNat ii * Verity.Core.Uint256.ofNat 3).val)
      = some (3 * ii)
    show some (((Verity.Core.Uint256.ofNat ii).val * (Verity.Core.Uint256.ofNat 3).val)
          % Verity.Core.Uint256.modulus) = some (3 * ii)
    have hiiv : (Verity.Core.Uint256.ofNat ii).val = ii :=
      Nat.mod_eq_of_lt (lt_trans hiiLt (by decide : 43 < 2 ^ 256))
    have h3v : (Verity.Core.Uint256.ofNat 3).val = 3 :=
      Nat.mod_eq_of_lt (by decide : 3 < 2 ^ 256)
    have hmod : Verity.Core.Uint256.modulus = 2 ^ 256 := rfl
    rw [hiiv, h3v, hmod, Nat.mul_comm,
      Nat.mod_eq_of_lt (by
        calc
          3 * ii ≤ 3 * 42 := Nat.mul_le_mul_left 3 (Nat.le_of_lt_succ hiiLt)
          _ < 2 ^ 256 := by decide)]
  have hshiftLt : 3 * ii < 2 ^ 256 := by
    calc
      3 * ii ≤ 3 * 42 := Nat.mul_le_mul_left 3 (Nat.le_of_lt_succ hiiLt)
      _ < 2 ^ 256 := by decide
  have hshr :
      evalExpr [] st (shrE (mulE (v "ii") (u 3)) (v "d"))
        = some (d >>> (3 * ii)) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shr_bounded
      st (mulE (v "ii") (u 3)) (v "d") (3 * ii) d
      hmul hdEval hshiftLt hdLt
  have hshrLt : d >>> (3 * ii) < 2 ^ 256 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.lt_of_le_of_lt (Nat.div_le_self d (2 ^ (3 * ii))) hdLt
  have hdigit :
      evalExpr [] st (andE (shrE (mulE (v "ii") (u 3)) (v "d")) (u 0x7))
        = some ((d >>> (3 * ii)) % 8) := by
    have hshrLit :
        evalExpr [] st (shrE (mulE (v "ii") (Expr.literal 3)) (v "d"))
          = some (d >>> (3 * ii)) := by
      simpa [u] using hshr
    unfold andE u
    rw [SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_bitAnd_literal
      st (shrE (mulE (v "ii") (Expr.literal 3)) (v "d")) (d >>> (3 * ii)) 0x7
      hshrLit hshrLt (by decide : 0x7 < 2 ^ 256)]
    rw [nat_land_low3]
    norm_num
  have hdigitLt : (d >>> (3 * ii)) % 8 < 2 ^ 256 :=
    lt_trans (Nat.mod_lt _ (by decide : 0 < 8)) (by decide : 8 < 2 ^ 256)
  have haccLt : acc < 2 ^ 256 :=
    lt_of_le_of_lt (Nat.le_add_right acc ((d >>> (3 * ii)) % 8)) haddLt
  have hsum :
      evalExpr [] st
        (addE (v "digitSum") (andE (shrE (mulE (v "ii") (u 3)) (v "d")) (u 0x7)))
        = some (acc + (d >>> (3 * ii)) % 8) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_add_bounded
      st (v "digitSum") (andE (shrE (mulE (v "ii") (u 3)) (v "d")) (u 0x7))
      acc ((d >>> (3 * ii)) % 8) haccEval hdigit haccLt hdigitLt haddLt
  unfold digitSumStep digitSumBody
  rw [execStmtList_cons_continue _ _ _ _
    (assignVar_continue st "digitSum" _ _ hsum)]
  simp only [execStmtList, MemoryKit.lookupValue_bindValue_self]

theorem digitSumStep_preserves_d (st : RuntimeState) :
    lookupValue (digitSumStep st).bindings "d" = lookupValue st.bindings "d" := by
  unfold digitSumStep digitSumBody
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue st "digitSum" _ _ rfl)]
  simp only [execStmtList, MemoryKit.lookupValue_bindValue_ne, ne_eq, String.reduceEq,
    not_false_eq_true]

/-- The pure digit-sum loop fold accumulates exactly the recursive digit fold.
This is the 43-iteration lift of `digitSumStep_digitSum_eq`; it reasons over
`foldLoop` directly and does not unfold the enclosing layer prefix. -/
theorem foldLoop_digitSum_eq
    (st : RuntimeState) (d acc index remaining : Nat)
    (hd : lookupValue st.bindings "d" = d)
    (hacc : lookupValue st.bindings "digitSum" = acc)
    (hRange : index + remaining ≤ 43)
    (hdLt : d < 2 ^ 256)
    (haccLt : acc + 7 * remaining < 2 ^ 256) :
    lookupValue
        (foldLoop "ii" digitSumStep st index remaining).bindings
        "digitSum"
      = digitSumFold d acc index remaining := by
  induction remaining generalizing st acc index with
  | zero =>
      simp [ClimbLoop.foldLoop_zero, digitSumFold, hacc]
  | succ remaining ih =>
      rw [ClimbLoop.foldLoop_succ]
      let s1 : RuntimeState :=
        { st with bindings := bindValue st.bindings "ii" (wordNormalize index) }
      have hidxLt : index < 43 := by omega
      have hidxNorm : wordNormalize index = index := by
        rw [wordNormalize_eq_mod]
        exact Nat.mod_eq_of_lt (lt_trans hidxLt (by decide : 43 < 2 ^ 256))
      have hii : lookupValue s1.bindings "ii" = index := by
        simp only [s1, hidxNorm, MemoryKit.lookupValue_bindValue_self]
      have hd1 : lookupValue s1.bindings "d" = d := by
        rw [MemoryKit.lookupValue_bindValue_ne _ "ii" "d" _ (by decide), hd]
      have hacc1 : lookupValue s1.bindings "digitSum" = acc := by
        rw [MemoryKit.lookupValue_bindValue_ne _ "ii" "digitSum" _ (by decide), hacc]
      have hdigitLe : digitAt d index ≤ 7 := by
        unfold digitAt
        exact Nat.le_pred_of_lt (Nat.mod_lt _ (by decide : 0 < 8))
      have haddLt : acc + digitAt d index < 2 ^ 256 := by
        omega
      have hstep :
          lookupValue (digitSumStep s1).bindings "digitSum"
            = acc + digitAt d index := by
        unfold digitAt
        exact digitSumStep_digitSum_eq s1 index d acc
          hii hd1 hacc1 hidxLt hdLt haddLt
      have hdStep : lookupValue (digitSumStep s1).bindings "d" = d := by
        rw [digitSumStep_preserves_d, hd1]
      have hRangeTail : index + 1 + remaining ≤ 43 := by omega
      have haccLtTail : (acc + digitAt d index) + 7 * remaining < 2 ^ 256 := by
        omega
      have htail :=
        ih (digitSumStep s1) (acc + digitAt d index) (index + 1)
          hdStep hstep hRangeTail haccLtTail
      simpa [s1, digitSumFold] using htail

/-- The 43-step executable checksum fold targets exactly the concrete C13 WOTS
digit-sum function.  This connects the local loop arithmetic to the spec-side
grinding predicate without unfolding the layer prefix or WOTS-chain loops. -/
theorem digitSumFold_zero_eq_wotsDigitSum (d : Nat) :
    digitSumFold d 0 0 43 = SphincsMinusVerifierSpec.C13Concrete.wotsDigitSum d := by
  unfold SphincsMinusVerifierSpec.C13Concrete.wotsDigitSum digitSumFold digitAt
  rfl

/-- The WOTS-chain outer-loop body (`forEach "i" (u 43)`), with its inner
variable-bound chain `forEach "step" (v "steps")` written as `wotsChainBody`. -/
def wotsOuterBody : List Stmt :=
  [ .letVar "digit" (andE (shrE (mulE (v "i") (u 3)) (v "d")) (u 0x7))
  , .letVar "steps" (subE (u 7) (v "digit"))
  , .letVar "val" (andE (cdload (addE (v "wotsPtr") (shlE (u 4) (v "i")))) (u N_MASK))
  , .letVar "chainBase" (orE (v "wotsAdrs") (shlE (u 32) (v "i")))
  , .forEach "step" (v "steps") wotsChainBody
  , mstoreE (addE (u 0x80) (shlE (u 5) (v "i"))) (v "val") ]

def wotsOuterStep (st : RuntimeState) : RuntimeState :=
  match execStmtList [] st wotsOuterBody with | .continue s' => s' | _ => st

theorem wotsOuterStepLemma (st : RuntimeState) :
    execStmtList [] st wotsOuterBody = .continue (wotsOuterStep st) := by
  unfold wotsOuterStep wotsOuterBody mstoreE
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue st "digit" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "steps" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "val" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "chainBase" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
      (execStmt_forEach_of_step "step" (v "steps") wotsChainBody _ _ stepWots rfl wotsChainStep)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rfl

/-- The WOTS-pk copy loop body (`forEach "i" (u 43)`). -/
def copyBody : List Stmt :=
  [ mstoreE (addE (u 0x40) (shlE (u 5) (v "i"))) (mloadE (addE (u 0x80) (shlE (u 5) (v "i")))) ]

def copyStep (st : RuntimeState) : RuntimeState :=
  match execStmtList [] st copyBody with | .continue s' => s' | _ => st

theorem copyStepLemma (st : RuntimeState) :
    execStmtList [] st copyBody = .continue (copyStep st) := by
  unfold copyStep copyBody mstoreE
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rfl

/-! ## 3. The Layer-3 body reconstruction (Model.lean:154-203), split around the
checksum-guard `ite` as `prefix11 ++ (ite :: suffix14)`. -/

/-- Statements 154-161, stopping just before the WOTS digest keccak binding. -/
def prefixBeforeWotsDigest : List Stmt :=
  [ .letVar "idxLeaf" (andE (v "idxTree") (u 0x7FF))
  , .assignVar "idxTree" (shrE (u 11) (v "idxTree"))
  , .letVar "wotsAdrs" (orE (shlE (u 224) (v "layer")) (orE (shlE (u 128) (v "idxTree")) (shlE (u 64) (v "idxLeaf"))))
  , .letVar "countOff" (addE (v "sigOff") (u 688))
  , .letVar "count" (shrE (u 224) (cdload (addE (v "sigBase") (v "countOff"))))
  , mstore 0x20 (v "wotsAdrs")
  , mstore 0x40 (v "currentNode")
  , mstore 0x60 (v "count")
  ]

/-- Prefix up to and including the WOTS ADRS store, just before the
`currentNode` store. -/
def prefixBeforeWotsDigestCurrentNodeSlot : List Stmt :=
  [ .letVar "idxLeaf" (andE (v "idxTree") (u 0x7FF))
  , .assignVar "idxTree" (shrE (u 11) (v "idxTree"))
  , .letVar "wotsAdrs" (orE (shlE (u 224) (v "layer")) (orE (shlE (u 128) (v "idxTree")) (shlE (u 64) (v "idxLeaf"))))
  , .letVar "countOff" (addE (v "sigOff") (u 688))
  , .letVar "count" (shrE (u 224) (cdload (addE (v "sigBase") (v "countOff"))))
  , mstore 0x20 (v "wotsAdrs")
  ]

/-- Prefix just before the WOTS ADRS store at `0x20`. -/
def prefixBeforeWotsDigestAdrsSlot : List Stmt :=
  [ .letVar "idxLeaf" (andE (v "idxTree") (u 0x7FF))
  , .assignVar "idxTree" (shrE (u 11) (v "idxTree"))
  , .letVar "wotsAdrs" (orE (shlE (u 224) (v "layer")) (orE (shlE (u 128) (v "idxTree")) (shlE (u 64) (v "idxLeaf"))))
  , .letVar "countOff" (addE (v "sigOff") (u 688))
  , .letVar "count" (shrE (u 224) (cdload (addE (v "sigBase") (v "countOff"))))
  ]

theorem prefixBeforeWotsDigestCurrentNodeSlot_eq_adrsSlot_append :
    prefixBeforeWotsDigestCurrentNodeSlot =
      prefixBeforeWotsDigestAdrsSlot ++ [mstore 0x20 (v "wotsAdrs")] := rfl

theorem prefixBeforeWotsDigest_eq_currentNodeSlot_append :
    prefixBeforeWotsDigest =
      prefixBeforeWotsDigestCurrentNodeSlot ++
        [ mstore 0x40 (v "currentNode"), mstore 0x60 (v "count") ] := rfl

/-- Statements 154-163, stopping just before the digit-sum loop. -/
def prefixBeforeDigitSum : List Stmt :=
  [ .letVar "idxLeaf" (andE (v "idxTree") (u 0x7FF))
  , .assignVar "idxTree" (shrE (u 11) (v "idxTree"))
  , .letVar "wotsAdrs" (orE (shlE (u 224) (v "layer")) (orE (shlE (u 128) (v "idxTree")) (shlE (u 64) (v "idxLeaf"))))
  , .letVar "countOff" (addE (v "sigOff") (u 688))
  , .letVar "count" (shrE (u 224) (cdload (addE (v "sigBase") (v "countOff"))))
  , mstore 0x20 (v "wotsAdrs")
  , mstore 0x40 (v "currentNode")
  , mstore 0x60 (v "count")
  , .letVar "d" (keccak 0x00 0x80)
  , .letVar "digitSum" (u 0)
  ]

theorem prefixBeforeDigitSum_eq_prefixBeforeWotsDigest_append :
    prefixBeforeDigitSum =
      prefixBeforeWotsDigest ++ [ .letVar "d" (keccak 0x00 0x80), .letVar "digitSum" (u 0) ] :=
  rfl

/-- Statements 154-163 + the digit-sum loop (everything before the guard). -/
def prefix11 : List Stmt :=
  [ .letVar "idxLeaf" (andE (v "idxTree") (u 0x7FF))
  , .assignVar "idxTree" (shrE (u 11) (v "idxTree"))
  , .letVar "wotsAdrs" (orE (shlE (u 224) (v "layer")) (orE (shlE (u 128) (v "idxTree")) (shlE (u 64) (v "idxLeaf"))))
  , .letVar "countOff" (addE (v "sigOff") (u 688))
  , .letVar "count" (shrE (u 224) (cdload (addE (v "sigBase") (v "countOff"))))
  , mstore 0x20 (v "wotsAdrs")
  , mstore 0x40 (v "currentNode")
  , mstore 0x60 (v "count")
  , .letVar "d" (keccak 0x00 0x80)
  , .letVar "digitSum" (u 0)
  , .forEach "ii" (u 43) digitSumBody ]

theorem prefix11_eq_prefixBeforeDigitSum_append :
    prefix11 = prefixBeforeDigitSum ++ [ .forEach "ii" (u 43) digitSumBody ] := rfl

/-- Statements 168-203 (everything after the guard). -/
def suffix14 : List Stmt :=
  [ .letVar "wotsPtr" (addE (v "sigBase") (v "sigOff"))
  , .forEach "i" (u 43) wotsOuterBody
  , .letVar "pkAdrs" (orE (shlE (u 224) (v "layer")) (orE (shlE (u 128) (v "idxTree")) (orE (shlE (u 96) (u 1)) (shlE (u 64) (v "idxLeaf")))))
  , mstore 0x20 (v "pkAdrs")
  , .forEach "i" (u 43) copyBody
  , .letVar "wotsPk" (andE (keccak 0x00 0x5A0) (u N_MASK))
  , .letVar "authOff" (addE (v "countOff") (u 4))
  , .letVar "treeAdrs" (orE (shlE (u 224) (v "layer")) (orE (shlE (u 128) (v "idxTree")) (shlE (u 96) (u 2))))
  , .letVar "merkleNode" (v "wotsPk")
  , .letVar "mIdx" (v "idxLeaf")
  , .letVar "merklePtr" (addE (v "sigBase") (v "authOff"))
  , .forEach "h" (u 11) (merkleClimbBody "merkleNode" "mIdx" "treeAdrs" "merklePtr")
  , .assignVar "currentNode" (v "merkleNode")
  , .assignVar "sigOff" (addE (v "authOff") (u 176)) ]

/-- The straight-line part of `suffix14` before the XMSS Merkle-climb loop.
This state carries the concrete WOTS public-key word and the initialized
`merkleNode`/`mIdx`/`treeAdrs`/`merklePtr` cells consumed by the generic
Merkle-climb frame lemmas. -/
def suffixBeforeMerkle : List Stmt :=
  [ .letVar "wotsPtr" (addE (v "sigBase") (v "sigOff"))
  , .forEach "i" (u 43) wotsOuterBody
  , .letVar "pkAdrs" (orE (shlE (u 224) (v "layer")) (orE (shlE (u 128) (v "idxTree")) (orE (shlE (u 96) (u 1)) (shlE (u 64) (v "idxLeaf")))))
  , mstore 0x20 (v "pkAdrs")
  , .forEach "i" (u 43) copyBody
  , .letVar "wotsPk" (andE (keccak 0x00 0x5A0) (u N_MASK))
  , .letVar "authOff" (addE (v "countOff") (u 4))
  , .letVar "treeAdrs" (orE (shlE (u 224) (v "layer")) (orE (shlE (u 128) (v "idxTree")) (shlE (u 96) (u 2))))
  , .letVar "merkleNode" (v "wotsPk")
  , .letVar "mIdx" (v "idxLeaf")
  , .letVar "merklePtr" (addE (v "sigBase") (v "authOff")) ]

def layerBody : List Stmt := prefix11 ++ (.ite condE revert0 [] :: suffix14)

def layerStmt : Stmt := .forEach "layer" (u 2) layerBody

set_option maxHeartbeats 8000000 in
/-- Faithfulness: `layerStmt` is *exactly* statement 25 of `c13VerifyBody`
(loop header, full body, every inner `forEach` and the checksum-guard `ite`). -/
theorem layerStmt_eq_slice :
    [layerStmt] = (c13VerifyBody.drop 25).take 1 := rfl

/-- One-step unfold of `execStmtList` on a cons, kept generic so the head
`execStmt` stays symbolic (no reduction of concrete loop-states). -/
private theorem execStmtList_cons_eq (st : RuntimeState) (s : Stmt) (rest : List Stmt) :
    execStmtList [] st (s :: rest) =
      (match execStmt [] st s with
        | .continue n => execStmtList [] n rest
        | .stop n => .stop n
        | .return rv rs => .return rv rs
        | .revert => .revert) := by
  show (match execStmt [] st s with
        | .continue n => execStmtList [] n rest
        | .stop n => .stop n
        | .return rv rs => .return rv rs
        | .revert => .revert) = _
  rfl

/-! ## 4. Threading the guard-free prefix and suffix. -/

/-- The state after the straight-line setup has populated the WOTS-digest
scratch frame, just before binding `"d"` from `keccak256(0x00, 0x80)`. -/
def beforeWotsDigest (ls : RuntimeState) : RuntimeState :=
  match execStmtList [] ls prefixBeforeWotsDigest with | .continue s' => s' | _ => ls

theorem beforeWotsDigest_eq (ls : RuntimeState) :
    execStmtList [] ls prefixBeforeWotsDigest = .continue (beforeWotsDigest ls) := by
  unfold beforeWotsDigest prefixBeforeWotsDigest mstore u
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "idxLeaf" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "idxTree" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "countOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "count" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rfl

/-- The WOTS-digest setup does not touch the seed scratch slot at `0x00`. -/
theorem beforeWotsDigest_seed_slot_eq (ls : RuntimeState) :
    ((beforeWotsDigest ls).world.memory 0x00).val = (ls.world.memory 0x00).val := by
  exact SphincsMinusVerifiers.MemoryFrame.execStmtList_preserves_memory_val
    0x00 prefixBeforeWotsDigest ls (beforeWotsDigest ls)
    (by
      intro s s'' stmt hmem hexec
      unfold prefixBeforeWotsDigest mstore u at hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
          s s'' 0x00 "idxLeaf" _ hexec
      · exact SphincsMinusVerifiers.MemoryFrame.execStmt_assignVar_preserves_memory_val
          s s'' 0x00 "idxTree" _ hexec
      · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
          s s'' 0x00 "wotsAdrs" _ hexec
      · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
          s s'' 0x00 "countOff" _ hexec
      · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
          s s'' 0x00 "count" _ hexec
      · exact SphincsMinusVerifiers.MemoryFrame.execStmt_mstore_preserves_memory_val
          s s'' 0x00 (u 0x20) (v "wotsAdrs")
          (by
            intro ro rv hoff hval
            have hro : ro = 0x20 := by
              change some (wordNormalize 0x20) = some ro at hoff
              injection hoff with h
              rw [← h]
              rfl
            rw [hro]
            decide) hexec
      · exact SphincsMinusVerifiers.MemoryFrame.execStmt_mstore_preserves_memory_val
          s s'' 0x00 (u 0x40) (v "currentNode")
          (by
            intro ro rv hoff hval
            have hro : ro = 0x40 := by
              change some (wordNormalize 0x40) = some ro at hoff
              injection hoff with h
              rw [← h]
              rfl
            rw [hro]
            decide) hexec
      · exact SphincsMinusVerifiers.MemoryFrame.execStmt_mstore_preserves_memory_val
          s s'' 0x00 (u 0x60) (v "count")
          (by
            intro ro rv hoff hval
            have hro : ro = 0x60 := by
              change some (wordNormalize 0x60) = some ro at hoff
              injection hoff with h
              rw [← h]
              rfl
            rw [hro]
            decide) hexec)
    (beforeWotsDigest_eq ls)

/-- State just before the WOTS-digest setup stores `"currentNode"` at `0x40`. -/
def beforeWotsDigestCurrentNodeSlot (ls : RuntimeState) : RuntimeState :=
  match execStmtList [] ls prefixBeforeWotsDigestCurrentNodeSlot with
  | .continue s' => s'
  | _ => ls

theorem beforeWotsDigestCurrentNodeSlot_eq (ls : RuntimeState) :
    execStmtList [] ls prefixBeforeWotsDigestCurrentNodeSlot =
      .continue (beforeWotsDigestCurrentNodeSlot ls) := by
  unfold beforeWotsDigestCurrentNodeSlot prefixBeforeWotsDigestCurrentNodeSlot mstore u
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "idxLeaf" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "idxTree" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "countOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "count" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rfl

/-- State just before the WOTS-digest setup stores `"wotsAdrs"` at `0x20`. -/
def beforeWotsDigestAdrsSlot (ls : RuntimeState) : RuntimeState :=
  match execStmtList [] ls prefixBeforeWotsDigestAdrsSlot with
  | .continue s' => s'
  | _ => ls

theorem beforeWotsDigestAdrsSlot_eq (ls : RuntimeState) :
    execStmtList [] ls prefixBeforeWotsDigestAdrsSlot =
      .continue (beforeWotsDigestAdrsSlot ls) := by
  unfold beforeWotsDigestAdrsSlot prefixBeforeWotsDigestAdrsSlot u
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "idxLeaf" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "idxTree" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "countOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "count" _ _ rfl)]
  rfl

/-- The WOTS-digest setup writes the computed `"wotsAdrs"` binding to the
`0x20` scratch slot. -/
theorem beforeWotsDigest_wotsAdrs_slot_eq (ls : RuntimeState) :
    ((beforeWotsDigest ls).world.memory 0x20).val =
      wordNormalize (lookupValue (beforeWotsDigestAdrsSlot ls).bindings "wotsAdrs") := by
  unfold beforeWotsDigest
  rw [prefixBeforeWotsDigest_eq_currentNodeSlot_append]
  rw [MemoryKit.execStmtList_append_continue _ _ _ _ (beforeWotsDigestCurrentNodeSlot_eq ls)]
  unfold beforeWotsDigestCurrentNodeSlot
  rw [prefixBeforeWotsDigestCurrentNodeSlot_eq_adrsSlot_append]
  rw [MemoryKit.execStmtList_append_continue _ _ _ _ (beforeWotsDigestAdrsSlot_eq ls)]
  unfold mstore u
  let adr := beforeWotsDigestAdrsSlot ls
  let st20 : RuntimeState :=
    { adr with world := { adr.world with
        memory := SphincsMinusVerifiers.MemoryKit.memUpdate adr.world.memory 0x20
          (lookupValue adr.bindings "wotsAdrs") } }
  have h20 :
      execStmtList [] adr [Stmt.mstore (Expr.literal 0x20) (v "wotsAdrs")] =
        .continue st20 := by
    rw [execStmtList_cons_continue _ _ _ _
      (execStmt_mstore_continue adr (Expr.literal 0x20) (v "wotsAdrs") 0x20
        (lookupValue adr.bindings "wotsAdrs") rfl rfl)]
    rfl
  rw [h20]
  let mid := st20
  let st40 : RuntimeState :=
    { mid with world := { mid.world with
        memory := SphincsMinusVerifiers.MemoryKit.memUpdate mid.world.memory 0x40
          (lookupValue mid.bindings "currentNode") } }
  let st60 : RuntimeState :=
    { st40 with world := { st40.world with
        memory := SphincsMinusVerifiers.MemoryKit.memUpdate st40.world.memory 0x60
          (lookupValue mid.bindings "count") } }
  have htail :
      execStmtList [] mid
        [ Stmt.mstore (Expr.literal 0x40) (v "currentNode"),
          Stmt.mstore (Expr.literal 0x60) (v "count") ] = .continue st60 := by
    rw [execStmtList_cons_continue _ _ _ _
      (execStmt_mstore_continue mid (Expr.literal 0x40) (v "currentNode") 0x40
        (lookupValue mid.bindings "currentNode") rfl rfl)]
    rw [execStmtList_cons_continue _ _ _ _
      (execStmt_mstore_continue st40 (Expr.literal 0x60) (v "count") 0x60
        (lookupValue mid.bindings "count") rfl rfl)]
    rfl
  rw [htail]
  show (SphincsMinusVerifiers.MemoryKit.memUpdate
      (SphincsMinusVerifiers.MemoryKit.memUpdate
        (SphincsMinusVerifiers.MemoryKit.memUpdate adr.world.memory 0x20
          (lookupValue adr.bindings "wotsAdrs"))
        0x40 (lookupValue adr.bindings "currentNode"))
      0x60 (lookupValue adr.bindings "count") 0x20).val =
        wordNormalize (lookupValue adr.bindings "wotsAdrs")
  rw [SphincsMinusVerifiers.MemoryKit.memUpdate_diff _ _ _ _ (by decide)]
  rw [SphincsMinusVerifiers.MemoryKit.memUpdate_diff _ _ _ _ (by decide)]
  rw [SphincsMinusVerifiers.MemoryKit.memUpdate_val_same]

/-- Spec-facing WOTS ADRS scratch fact: once the computed `"wotsAdrs"` binding is
identified with a bounded word, the `0x20` scratch slot contains that exact word. -/
theorem beforeWotsDigest_wotsAdrs_slot_eq_of_lookup
    (ls : RuntimeState) (wotsAdrs : Nat)
    (hadr : lookupValue (beforeWotsDigestAdrsSlot ls).bindings "wotsAdrs" = wotsAdrs)
    (hadrLt : wotsAdrs < 2 ^ 256) :
    ((beforeWotsDigest ls).world.memory 0x20).val = wotsAdrs := by
  rw [beforeWotsDigest_wotsAdrs_slot_eq, hadr, wordNormalize_eq_mod]
  exact Nat.mod_eq_of_lt hadrLt

theorem beforeWotsDigestCurrentNodeSlot_currentNode_lookup_eq (ls : RuntimeState) :
    lookupValue (beforeWotsDigestCurrentNodeSlot ls).bindings "currentNode" =
      lookupValue ls.bindings "currentNode" := by
  refine SphincsMinusVerifiers.BindingFrame.execStmtList_preserves_lookup
    "currentNode" prefixBeforeWotsDigestCurrentNodeSlot ls
    (beforeWotsDigestCurrentNodeSlot ls) ?_ (beforeWotsDigestCurrentNodeSlot_eq ls)
  intro s s'' stmt hmem hexec
  unfold prefixBeforeWotsDigestCurrentNodeSlot mstore u at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "idxLeaf" "currentNode" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
      s s'' "idxTree" "currentNode" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "wotsAdrs" "currentNode" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "countOff" "currentNode" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      s s'' "count" "currentNode" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      s s'' "currentNode" _ _ hexec

/-- The WOTS-digest setup writes the incoming `"currentNode"` binding to the
`0x40` scratch slot. -/
theorem beforeWotsDigest_currentNode_slot_eq (ls : RuntimeState) :
    ((beforeWotsDigest ls).world.memory 0x40).val =
      wordNormalize (lookupValue ls.bindings "currentNode") := by
  unfold beforeWotsDigest
  rw [prefixBeforeWotsDigest_eq_currentNodeSlot_append]
  rw [MemoryKit.execStmtList_append_continue _ _ _ _ (beforeWotsDigestCurrentNodeSlot_eq ls)]
  unfold mstore u
  let mid := beforeWotsDigestCurrentNodeSlot ls
  let st40 : RuntimeState :=
    { mid with world := { mid.world with
        memory := SphincsMinusVerifiers.MemoryKit.memUpdate mid.world.memory 0x40
          (lookupValue mid.bindings "currentNode") } }
  let st60 : RuntimeState :=
    { st40 with world := { st40.world with
        memory := SphincsMinusVerifiers.MemoryKit.memUpdate st40.world.memory 0x60
          (lookupValue mid.bindings "count") } }
  have htail :
      execStmtList [] mid
        [ Stmt.mstore (Expr.literal 0x40) (v "currentNode"),
          Stmt.mstore (Expr.literal 0x60) (v "count") ] = .continue st60 := by
    rw [execStmtList_cons_continue _ _ _ _
      (execStmt_mstore_continue mid (Expr.literal 0x40) (v "currentNode") 0x40
        (lookupValue mid.bindings "currentNode") rfl rfl)]
    rw [execStmtList_cons_continue _ _ _ _
      (execStmt_mstore_continue st40 (Expr.literal 0x60) (v "count") 0x60
        (lookupValue mid.bindings "count") rfl rfl)]
    rfl
  rw [htail]
  show (SphincsMinusVerifiers.MemoryKit.memUpdate
      (SphincsMinusVerifiers.MemoryKit.memUpdate mid.world.memory 0x40
        (lookupValue mid.bindings "currentNode"))
      0x60 (lookupValue mid.bindings "count") 0x40).val =
        wordNormalize (lookupValue ls.bindings "currentNode")
  rw [SphincsMinusVerifiers.MemoryKit.memUpdate_diff _ _ _ _ (by decide)]
  rw [SphincsMinusVerifiers.MemoryKit.memUpdate_val_same]
  rw [beforeWotsDigestCurrentNodeSlot_currentNode_lookup_eq ls]

/-- Spec-facing current-node scratch fact: if the incoming binding is a bounded
word, the `0x40` scratch slot contains that exact word. -/
theorem beforeWotsDigest_currentNode_slot_eq_of_lookup
    (ls : RuntimeState) (currentNode : Nat)
    (hcur : lookupValue ls.bindings "currentNode" = currentNode)
    (hcurLt : currentNode < 2 ^ 256) :
    ((beforeWotsDigest ls).world.memory 0x40).val = currentNode := by
  rw [beforeWotsDigest_currentNode_slot_eq, hcur, wordNormalize_eq_mod]
  exact Nat.mod_eq_of_lt hcurLt

/-- The state after the straight-line prefix that sets up `"d"` and initializes
`"digitSum"`, just before the 43-step checksum loop. -/
def beforeDigitSum (ls : RuntimeState) : RuntimeState :=
  match execStmtList [] ls prefixBeforeDigitSum with | .continue s' => s' | _ => ls

theorem beforeDigitSum_eq (ls : RuntimeState) :
    execStmtList [] ls prefixBeforeDigitSum = .continue (beforeDigitSum ls) := by
  unfold beforeDigitSum prefixBeforeDigitSum mstore u
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "idxLeaf" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "idxTree" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "countOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "count" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "d" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "digitSum" _ _ rfl)]
  rfl

theorem beforeDigitSum_digitSum_eq_zero (ls : RuntimeState) :
    lookupValue (beforeDigitSum ls).bindings "digitSum" = 0 := by
  unfold beforeDigitSum prefixBeforeDigitSum mstore u
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "idxLeaf" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "idxTree" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "countOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "count" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "d" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "digitSum" _ _ rfl)]
  have h0 : wordNormalize 0 = 0 := by
    rw [wordNormalize_eq_mod]
    exact Nat.zero_mod _
  simp only [execStmtList, h0, MemoryKit.lookupValue_bindValue_self]

/-- If the WOTS-digest scratch frame contains the four expected words, then the
straight-line prefix binds `"d"` to the corresponding concrete keccak word.
This is the hash half of the remaining `"d" = wotsDigest ...` correspondence;
the caller still identifies the scratch words with `seed`, `WOTS_HASH` ADRS,
`currentNode`, and the parsed WOTS count. -/
theorem beforeDigitSum_d_eq_keccakWords_of_beforeWotsDigest_memory
    (ls : RuntimeState) (seed wotsAdrs currentNode count : Nat)
    (h0 : ((beforeWotsDigest ls).world.memory 0x00).val = seed)
    (h1 : ((beforeWotsDigest ls).world.memory 0x20).val = wotsAdrs)
    (h2 : ((beforeWotsDigest ls).world.memory 0x40).val = currentNode)
    (h3 : ((beforeWotsDigest ls).world.memory 0x60).val = count) :
    lookupValue (beforeDigitSum ls).bindings "d"
      = SphincsMinusVerifierSpec.C13Concrete.keccakWords
          [seed, wotsAdrs, currentNode, count] := by
  unfold beforeDigitSum
  rw [prefixBeforeDigitSum_eq_prefixBeforeWotsDigest_append]
  rw [MemoryKit.execStmtList_append_continue _ _ _ _ (beforeWotsDigest_eq ls)]
  have hkeccak :
      evalExpr [] (beforeWotsDigest ls) (keccak 0x00 0x80)
        = some (SphincsMinusVerifierSpec.C13Concrete.keccakWords
          [seed, wotsAdrs, currentNode, count]) := by
    unfold keccak u
    apply SphincsMinusVerifiers.KeccakBridge.evalExpr_keccak256_eq_keccakWords
    · rfl
    · rfl
    · intro i hi
      have hi4 : i < 4 := by simpa using hi
      match i with
      | 0 => simpa using h0
      | 1 => simpa using h1
      | 2 => simpa using h2
      | 3 => simpa using h3
      | j + 4 =>
          omega
  let dval := SphincsMinusVerifierSpec.C13Concrete.keccakWords
    [seed, wotsAdrs, currentNode, count]
  let stD : RuntimeState :=
    { beforeWotsDigest ls with
      bindings := bindValue (beforeWotsDigest ls).bindings "d" dval }
  let stSum : RuntimeState :=
    { stD with bindings := bindValue stD.bindings "digitSum" (wordNormalize 0) }
  have htail :
      execStmtList [] (beforeWotsDigest ls)
          [ .letVar "d" (keccak 0x00 0x80), .letVar "digitSum" (u 0) ]
        = .continue stSum := by
    rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "d" _ _ hkeccak)]
    rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "digitSum" _ _ rfl)]
    rfl
  rw [htail]
  simp only [stSum, stD, dval, MemoryKit.lookupValue_bindValue_ne, ne_eq, String.reduceEq,
    not_false_eq_true, MemoryKit.lookupValue_bindValue_self]

/-- Spec-shaped version of
`beforeDigitSum_d_eq_keccakWords_of_beforeWotsDigest_memory`: once the WOTS
scratch ADRS word is identified as `adrsWotsHashBase`, the executable `"d"`
cell is exactly the concrete C13 `wotsDigest`. -/
theorem beforeDigitSum_d_eq_wotsDigest_of_beforeWotsDigest_memory
    (ls : RuntimeState) (seed layer idxTree idxLeaf count currentNode : Nat)
    (h0 : ((beforeWotsDigest ls).world.memory 0x00).val = seed)
    (h1 :
      ((beforeWotsDigest ls).world.memory 0x20).val
        = SphincsMinusVerifierSpec.C13Concrete.adrsWotsHashBase layer idxTree idxLeaf)
    (h2 : ((beforeWotsDigest ls).world.memory 0x40).val = currentNode)
    (h3 : ((beforeWotsDigest ls).world.memory 0x60).val = count) :
    lookupValue (beforeDigitSum ls).bindings "d"
      =
    SphincsMinusVerifierSpec.C13Concrete.wotsDigest
      seed layer idxTree idxLeaf count currentNode := by
  simpa [SphincsMinusVerifierSpec.C13Concrete.wotsDigest] using
    beforeDigitSum_d_eq_keccakWords_of_beforeWotsDigest_memory
      ls seed (SphincsMinusVerifierSpec.C13Concrete.adrsWotsHashBase layer idxTree idxLeaf)
      currentNode count h0 h1 h2 h3

/-- The state after running `prefix11` (always continues). -/
def afterDigit (ls : RuntimeState) : RuntimeState :=
  match execStmtList [] ls prefix11 with | .continue s' => s' | _ => ls

theorem afterDigit_eq (ls : RuntimeState) :
    execStmtList [] ls prefix11 = .continue (afterDigit ls) := by
  unfold afterDigit
  rw [prefix11_eq_prefixBeforeDigitSum_append]
  rw [MemoryKit.execStmtList_append_continue _ _ _ _ (beforeDigitSum_eq ls)]
  have hloop :
      execStmtList [] (beforeDigitSum ls) [ .forEach "ii" (u 43) digitSumBody ]
        =
      .continue
        (foldLoop "ii" digitSumStep
          { beforeDigitSum ls with
            bindings := bindValue (beforeDigitSum ls).bindings "ii" (wordNormalize 0) }
          0 (wordNormalize 43)) := by
    unfold u
    rw [execStmtList_cons_continue _ _ _ _
      (execStmt_forEach_of_step "ii" (.literal 43) digitSumBody _ _ digitSumStep rfl digitSumStepLemma)]
    rfl
  rw [hloop]

/-- `afterDigit` is the setup prefix followed by the pure 43-step digit fold.
This exposes the loop entry state without re-elaborating the loop body. -/
theorem afterDigit_eq_foldLoop_digitSum (ls : RuntimeState) :
    afterDigit ls =
      foldLoop "ii" digitSumStep
        { beforeDigitSum ls with
          bindings := bindValue (beforeDigitSum ls).bindings "ii" (wordNormalize 0) }
        0 (wordNormalize 43) := by
  unfold afterDigit
  rw [prefix11_eq_prefixBeforeDigitSum_append]
  rw [MemoryKit.execStmtList_append_continue _ _ _ _ (beforeDigitSum_eq ls)]
  have hloop :
      execStmtList [] (beforeDigitSum ls) [ .forEach "ii" (u 43) digitSumBody ]
        =
      .continue
        (foldLoop "ii" digitSumStep
          { beforeDigitSum ls with
            bindings := bindValue (beforeDigitSum ls).bindings "ii" (wordNormalize 0) }
          0 (wordNormalize 43)) := by
    unfold u
    rw [execStmtList_cons_continue _ _ _ _
      (execStmt_forEach_of_step "ii" (.literal 43) digitSumBody _ _ digitSumStep rfl digitSumStepLemma)]
    rfl
  rw [hloop]

/-- Once the straight-line setup has bound `"d"` to a concrete 256-bit word, the
post-prefix executable checksum cell is exactly the concrete C13 WOTS digit sum.
The remaining open prefix obligation is therefore just identifying that `"d"`
cell with `wotsDigest ...`. -/
theorem afterDigit_digitSum_eq_wotsDigitSum_of_beforeDigitSum_d
    (ls : RuntimeState) (d : Nat)
    (hd : lookupValue (beforeDigitSum ls).bindings "d" = d)
    (hdLt : d < 2 ^ 256) :
    lookupValue (afterDigit ls).bindings "digitSum"
      = SphincsMinusVerifierSpec.C13Concrete.wotsDigitSum d := by
  let loopStart : RuntimeState :=
    { beforeDigitSum ls with
      bindings := bindValue (beforeDigitSum ls).bindings "ii" (wordNormalize 0) }
  have h43 : wordNormalize 43 = 43 := by
    rw [wordNormalize_eq_mod]
    exact Nat.mod_eq_of_lt (by decide : 43 < 2 ^ 256)
  have hdStart : lookupValue loopStart.bindings "d" = d := by
    rw [MemoryKit.lookupValue_bindValue_ne _ "ii" "d" _ (by decide), hd]
  have haccStart : lookupValue loopStart.bindings "digitSum" = 0 := by
    rw [MemoryKit.lookupValue_bindValue_ne _ "ii" "digitSum" _ (by decide),
      beforeDigitSum_digitSum_eq_zero]
  rw [afterDigit_eq_foldLoop_digitSum, h43]
  have hfold :=
    foldLoop_digitSum_eq loopStart d 0 0 43 hdStart haccStart
      (by norm_num) hdLt (by decide : 0 + 7 * 43 < 2 ^ 256)
  rw [hfold]
  exact digitSumFold_zero_eq_wotsDigitSum d

/-- Combined WOTS digit-cell bridge from the WOTS-digest scratch frame: the
post-prefix executable `"digitSum"` cell is the concrete digit sum of the
concrete WOTS digest.  The remaining outer obligation is to prove that the
straight-line stores indeed populate this scratch frame from the parsed C13
layer inputs. -/
theorem afterDigit_digitSum_eq_wotsDigitSum_wotsDigest_of_beforeWotsDigest_memory
    (ls : RuntimeState) (seed layer idxTree idxLeaf count currentNode : Nat)
    (h0 : ((beforeWotsDigest ls).world.memory 0x00).val = seed)
    (h1 :
      ((beforeWotsDigest ls).world.memory 0x20).val
        = SphincsMinusVerifierSpec.C13Concrete.adrsWotsHashBase layer idxTree idxLeaf)
    (h2 : ((beforeWotsDigest ls).world.memory 0x40).val = currentNode)
    (h3 : ((beforeWotsDigest ls).world.memory 0x60).val = count) :
    lookupValue (afterDigit ls).bindings "digitSum"
      =
    SphincsMinusVerifierSpec.C13Concrete.wotsDigitSum
      (SphincsMinusVerifierSpec.C13Concrete.wotsDigest
        seed layer idxTree idxLeaf count currentNode) := by
  have hd :
      lookupValue (beforeDigitSum ls).bindings "d"
        =
      SphincsMinusVerifierSpec.C13Concrete.wotsDigest
        seed layer idxTree idxLeaf count currentNode :=
    beforeDigitSum_d_eq_wotsDigest_of_beforeWotsDigest_memory
      ls seed layer idxTree idxLeaf count currentNode h0 h1 h2 h3
  have hdLt :
      SphincsMinusVerifierSpec.C13Concrete.wotsDigest
        seed layer idxTree idxLeaf count currentNode < 2 ^ 256 := by
    simpa [SphincsMinusVerifierSpec.C13Concrete.wotsDigest,
      Compiler.Constants.evmModulus] using
      SphincsMinusVerifiers.KeccakBridge.keccakWords_lt
        [seed, SphincsMinusVerifierSpec.C13Concrete.adrsWotsHashBase layer idxTree idxLeaf,
          currentNode, count]
  exact afterDigit_digitSum_eq_wotsDigitSum_of_beforeDigitSum_d
    ls
    (SphincsMinusVerifierSpec.C13Concrete.wotsDigest
      seed layer idxTree idxLeaf count currentNode)
    hd hdLt

/-- The pure transformer for one accepting layer iteration: the `.continue`
payload of `suffix14` run from `afterDigit ls`. -/
def stepLayer (ls : RuntimeState) : RuntimeState :=
  match execStmtList [] (afterDigit ls) suffix14 with | .continue s' => s' | _ => afterDigit ls

/-- The state immediately before the XMSS Merkle-climb loop inside one accepting
layer iteration. -/
def beforeMerkle (ls : RuntimeState) : RuntimeState :=
  match execStmtList [] (afterDigit ls) suffixBeforeMerkle with
  | .continue s' => s'
  | _ => afterDigit ls

theorem beforeMerkle_eq (ls : RuntimeState) :
    execStmtList [] (afterDigit ls) suffixBeforeMerkle = .continue (beforeMerkle ls) := by
  unfold beforeMerkle suffixBeforeMerkle mstore u
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsPtr" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
      (execStmt_forEach_of_step "i" (.literal 43) wotsOuterBody _ _ wotsOuterStep rfl wotsOuterStepLemma)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "pkAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _
      (execStmt_forEach_of_step "i" (.literal 43) copyBody _ _ copyStep rfl copyStepLemma)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsPk" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "authOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "treeAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "merkleNode" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "mIdx" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "merklePtr" _ _ rfl)]
  rfl

/-- The exact folded XMSS Merkle-climb state inside one accepting layer iteration. -/
def afterMerkle (ls : RuntimeState) : RuntimeState :=
  foldLoop "h" (stepMerkle "merkleNode" "mIdx" "treeAdrs" "merklePtr")
    { beforeMerkle ls with
      bindings := bindValue (beforeMerkle ls).bindings "h" (wordNormalize 0) }
    0 (wordNormalize 11)

set_option maxHeartbeats 4000000 in
theorem suffix14_continues (ls : RuntimeState) :
    execStmtList [] (afterDigit ls) suffix14 = .continue (stepLayer ls) := by
  unfold stepLayer suffix14 mstore u
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsPtr" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
      (execStmt_forEach_of_step "i" (.literal 43) wotsOuterBody _ _ wotsOuterStep rfl wotsOuterStepLemma)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "pkAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _
      (execStmt_forEach_of_step "i" (.literal 43) copyBody _ _ copyStep rfl copyStepLemma)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsPk" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "authOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "treeAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "merkleNode" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "mIdx" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "merklePtr" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
      (execStmt_forEach_merkleClimb "h" "merkleNode" "mIdx" "treeAdrs" "merklePtr" 11 _)]
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "currentNode" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "sigOff" _ _ rfl)]
  rfl

/-- The final two layer assignments do not rebind `"merkleNode"`.  This is the
cheap tail brick used by structural layer-suffix proofs without replaying the
whole WOTS/XMSS prefix. -/
theorem finalLayerTail_preserves_merkleNode (st : RuntimeState) :
    lookupValue
        (match execStmtList [] st
            [ .assignVar "currentNode" (v "merkleNode")
            , .assignVar "sigOff" (addE (v "authOff") (u 176)) ] with
          | .continue s' => s'
          | _ => st).bindings
        "merkleNode"
      = lookupValue st.bindings "merkleNode" := by
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "currentNode" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "sigOff" _ _ rfl)]
  simp only [execStmtList, MemoryKit.lookupValue_bindValue_ne,
    ne_eq, String.reduceEq, not_false_eq_true]

set_option maxHeartbeats 4000000 in
/-- **`stepLayer_currentNode_eq_merkleNode`** — structural identification of the
*left* operand of the final `currentNode == root` compare.  The last two statements
of `suffix14` are `currentNode := merkleNode; sigOff := …`; neither reassigns
`merkleNode`, so in the post-iteration state the `"currentNode"` binding equals the
`"merkleNode"` binding — the output of the Merkle-climb `forEach "h"` loop.  This
pins the compare's left operand to the climb result *structurally*, without
evaluating any keccak (the climbed value is carried as an opaque bound term, peeled
by key only).  It is the first Phase-3b sub-brick on the open (left-operand) half:
the remaining obligation is to identify that climbed `merkleNode` value with the
abstract spec's `foldHypertree`/`xmssRootFromSig` root — the genuine keccak data
correspondence. -/
theorem stepLayer_currentNode_eq_merkleNode (ls : RuntimeState) :
    lookupValue (stepLayer ls).bindings "currentNode"
      = lookupValue (stepLayer ls).bindings "merkleNode" := by
  unfold stepLayer suffix14 mstore u
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsPtr" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
      (execStmt_forEach_of_step "i" (.literal 43) wotsOuterBody _ _ wotsOuterStep rfl wotsOuterStepLemma)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "pkAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _
      (execStmt_forEach_of_step "i" (.literal 43) copyBody _ _ copyStep rfl copyStepLemma)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "wotsPk" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "authOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "treeAdrs" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "merkleNode" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "mIdx" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "merklePtr" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
      (execStmt_forEach_merkleClimb "h" "merkleNode" "mIdx" "treeAdrs" "merklePtr" 11 _)]
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "currentNode" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "sigOff" _ _ rfl)]
  simp only [execStmtList, MemoryKit.lookupValue_bindValue_ne, MemoryKit.lookupValue_bindValue_self,
    ne_eq, String.reduceEq, not_false_eq_true]

/-! ## 5. The guarded layer-body step lemma. -/

/-- The per-iteration guard: the checksum condition resolves to `0`
(`digitSum = 208`), i.e. the layer body does *not* revert. -/
def layerGuard (ls : RuntimeState) : Bool :=
  evalExpr [] (afterDigit ls) condE == some 0

/-- If the guard-free prefix's accumulated checksum binding is the C13 target
`208`, the executable layer guard passes.  This is a small public bridge from the
data-cell fact callers naturally prove (`"digitSum"` after `prefix11`) to the
guard predicate consumed by the guarded loop engine. -/
theorem layerGuard_of_afterDigit_digitSum_eq
    (ls : RuntimeState)
    (hDigit : lookupValue (afterDigit ls).bindings "digitSum" = 208) :
    layerGuard ls = true := by
  have hEq :
      evalExpr [] (afterDigit ls) (eqE (v "digitSum") (u 208)) = some 1 := by
    unfold eqE v u
    show (do
      let lhs ← some (lookupValue (afterDigit ls).bindings "digitSum")
      let rhs ← some (wordNormalize 208)
      pure (boolWord (decide (lhs = rhs)))) = some 1
    rw [hDigit]
    rfl
  have hCond : evalExpr [] (afterDigit ls) condE = some 0 := by
    unfold condE notE
    show (do
      let value ← evalExpr [] (afterDigit ls) (eqE (v "digitSum") (u 208))
      pure (boolWord (decide (value = 0)))) = some 0
    rw [hEq]
    rfl
  unfold layerGuard
  rw [hCond]
  rfl

/-- The checksum-guard `ite` (then = `revert0`, else = `[]`): continues with the
same state when its condition resolves to `0`, reverts otherwise. -/
private theorem ite_revert0_branch (st : RuntimeState) (cond : Expr) :
    execStmt [] st (.ite cond revert0 []) =
      match evalExpr [] st cond with
      | some r => if r != 0 then .revert else .continue st
      | none => .revert := by
  show (match evalExpr [] st cond with
        | some resolved =>
            if resolved != 0 then execStmtList [] st revert0 else execStmtList [] st []
        | none => .revert) = _
  cases evalExpr [] st cond with
  | none => rfl
  | some r => cases hr : r != 0 <;> simp only [hr, Bool.false_eq_true, if_true, if_false] <;> rfl

/-- **`execLayerBody`** — the guarded layer body: continues to `stepLayer ls`
when the checksum guard passes, reverts otherwise.  This is the `hstep`
hypothesis consumed by `ClimbLoopGuarded.execForEachLoop_of_guarded_step`. -/
theorem execLayerBody (ls : RuntimeState) :
    execStmtList [] ls layerBody
      = if layerGuard ls then .continue (stepLayer ls) else .revert := by
  unfold layerBody
  rw [MemoryKit.execStmtList_append_continue _ _ _ _ (afterDigit_eq ls)]
  rw [execStmtList_cons_eq, ite_revert0_branch]
  unfold layerGuard
  cases hc : evalExpr [] (afterDigit ls) condE with
  | none => rfl
  | some r =>
      by_cases hr : r = 0
      · subst hr
        simp only [bne_self_eq_false, beq_self_eq_true, reduceIte]
        exact suffix14_continues ls
      · have hb : (r != 0) = true := by simp [hr]
        have hb2 : (some r == some (0 : Nat)) = false := by simp [hr]
        simp only [hb, hb2]; rfl

/-! ## 6. The full guarded layer-loop fold. -/

/-- **`execLayerLoop`** — given that every threaded layer iteration's checksum
guard passes (`allGuardsPass`), the whole `forEach "layer" (u 2)` statement folds
to the pure `foldLoop` over `stepLayer`, exactly as the unguarded engine. -/
theorem execLayerLoop (state : RuntimeState)
    (hguards : ClimbLoopGuarded.allGuardsPass "layer" stepLayer layerGuard
        { state with bindings := bindValue state.bindings "layer" (wordNormalize 0) } 0 (wordNormalize 2)) :
    execStmt [] state layerStmt
      = .continue
          (foldLoop "layer" stepLayer
            { state with bindings := bindValue state.bindings "layer" (wordNormalize 0) }
            0 (wordNormalize 2)) :=
  ClimbLoopGuarded.execStmt_forEach_of_guarded_step "layer" (u 2) layerBody state (wordNormalize 2)
    stepLayer layerGuard rfl execLayerBody hguards

/-! ## 7. Axiom audit. -/

#print axioms layerStmt_eq_slice
#print axioms nat_land_low3
#print axioms digitSumStep_digitSum_eq
#print axioms digitSumStep_preserves_d
#print axioms foldLoop_digitSum_eq
#print axioms digitSumFold_zero_eq_wotsDigitSum
#print axioms beforeWotsDigest_eq
#print axioms beforeWotsDigest_seed_slot_eq
#print axioms beforeWotsDigest_wotsAdrs_slot_eq
#print axioms beforeWotsDigest_wotsAdrs_slot_eq_of_lookup
#print axioms beforeWotsDigest_currentNode_slot_eq
#print axioms beforeWotsDigest_currentNode_slot_eq_of_lookup
#print axioms beforeDigitSum_eq
#print axioms beforeDigitSum_digitSum_eq_zero
#print axioms beforeDigitSum_d_eq_keccakWords_of_beforeWotsDigest_memory
#print axioms beforeDigitSum_d_eq_wotsDigest_of_beforeWotsDigest_memory
#print axioms afterDigit_digitSum_eq_wotsDigitSum_wotsDigest_of_beforeWotsDigest_memory
#print axioms afterDigit_eq_foldLoop_digitSum
#print axioms afterDigit_digitSum_eq_wotsDigitSum_of_beforeDigitSum_d
#print axioms layerGuard_of_afterDigit_digitSum_eq
#print axioms beforeMerkle_eq
#print axioms finalLayerTail_preserves_merkleNode
#print axioms execLayerBody
#print axioms execLayerLoop
#print axioms stepLayer_currentNode_eq_merkleNode

end SphincsMinusVerifiers.SegmentLayer3
