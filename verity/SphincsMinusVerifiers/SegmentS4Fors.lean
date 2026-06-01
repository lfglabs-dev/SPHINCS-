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

/-- The full statement 14: the FORS outer `forEach "i" (u 6)`. -/
def forsOuterStmt : Stmt := .forEach "i" (u 6) forsLeafBody

/-- Faithfulness: `forsOuterStmt` is *exactly* statement 14 of `c13VerifyBody`
(loop header and full body, inner `forEach` included). -/
theorem forsOuterStmt_eq_slice :
    [forsOuterStmt] = (c13VerifyBody.drop 14).take 1 := rfl

/-! ## 2. Local per-statement `.continue` combinators. -/

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

/-! ## 3. The FORS outer-loop body step lemma. -/

/-- The pure transformer for one FORS outer-loop iteration: the `.continue`
payload of running `forsLeafBody`.  Total because every statement is a
`letVar`/`mstore`/total-`forEach` (the inner climb cannot revert). -/
def forsLeafStep (st : RuntimeState) : RuntimeState :=
  match execStmtList [] st forsLeafBody with
  | .continue s' => s'
  | _ => st

open SphincsMinusVerifiers.ClimbKit (execStmtList_cons_continue)
open SphincsMinusVerifiers.MemoryKit (execStmt_mstore_continue)
open SphincsMinusVerifiers.ClimbLoop (execStmt_forEach_merkleClimb)

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

/-! ## 5. Axiom audit. -/

#print axioms forsOuterStmt_eq_slice
#print axioms execForsLeaf
#print axioms execForsOuter

end SphincsMinusVerifiers.SegmentS4Fors
