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
import SphincsMinusVerifiers.Model

namespace SphincsMinusVerifiers.SegmentLayer3

open Compiler.Proofs.IRGeneration.SourceSemantics
open Compiler.CompilationModel
open Compiler.CompilationModel (Expr Stmt)
open SphincsMinusVerifiers.ClimbKit (N_MASK merkleClimbBody wotsChainBody stepWots wotsChainStep
  execStmtList_cons_continue)
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

theorem digitSumStepLemma (st : RuntimeState) :
    execStmtList [] st digitSumBody = .continue (digitSumStep st) := by
  unfold digitSumStep digitSumBody
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue st "digitSum" _ _ rfl)]
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

/-- The state after running `prefix11` (always continues). -/
def afterDigit (ls : RuntimeState) : RuntimeState :=
  match execStmtList [] ls prefix11 with | .continue s' => s' | _ => ls

theorem afterDigit_eq (ls : RuntimeState) :
    execStmtList [] ls prefix11 = .continue (afterDigit ls) := by
  unfold afterDigit prefix11 mstore u
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
  rw [execStmtList_cons_continue _ _ _ _
      (execStmt_forEach_of_step "ii" (.literal 43) digitSumBody _ _ digitSumStep rfl digitSumStepLemma)]
  rfl

/-- The pure transformer for one accepting layer iteration: the `.continue`
payload of `suffix14` run from `afterDigit ls`. -/
def stepLayer (ls : RuntimeState) : RuntimeState :=
  match execStmtList [] (afterDigit ls) suffix14 with | .continue s' => s' | _ => afterDigit ls

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
#print axioms execLayerBody
#print axioms execLayerLoop
#print axioms stepLayer_currentNode_eq_merkleNode

end SphincsMinusVerifiers.SegmentLayer3
