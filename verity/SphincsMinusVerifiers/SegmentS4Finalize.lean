/-
  SegmentS4Finalize — the FORS finalize block (statements 15..21 of
  `c13VerifyBody`), run after the FORS outer loop (`SegmentS4Fors.execForsOuter`)
  and before the climb seed (`SegmentSeed.execSegmentSeed`).

  Per `INTERFACE_CONTRACT.md` (the S4b/S4c rows), these seven statements are:

  ```
  15  letVar "lastSecret"  := and (cdload (sigBase + 16 + (4<<6))) N_MASK
  16  mstore 0x20          := (96<<3) | (64<<6)        -- FORS_TREE adrs, 7th leaf
  17  mstore 0x40          := lastSecret
  18  mstore 0x140         := and (keccak 0x00 0x60) N_MASK   -- forced-zero leaf
  19  mstore 0x20          := 96<<4                     -- FORS_ROOTS adrs
  20  forEach "i" (u 7)    [ mstore (0x40 + 32*i) := mload (0x80 + 32*i) ]
  21  letVar "forsPk"      := and (keccak 0x00 0x120) N_MASK  -- 7-root compress
  ```

  Statement 20 is the root-compression copy loop; it threads through
  `ClimbLoop.execStmt_forEach_of_step` exactly as the FORS / hypertree climbs do,
  with a one-statement `mstore` body (`forsCopyBody`).  Everything else is a
  `letVar` / `mstore` that continues unconditionally, so the whole block reduces
  to a single pure transformer `forsFinalizeStep`.

  Faithfulness is machine-checked: `forsFinalizeBody_eq_slice` (`rfl`) shows the
  reconstructed seven statements are exactly statements 15..21 of the real
  `c13VerifyBody`.  No `sorry`, no new `axiom`, no `native_decide`.
-/

import SphincsMinusVerifiers.ClimbLoop
import SphincsMinusVerifiers.Model

namespace SphincsMinusVerifiers.SegmentS4Finalize

open Compiler.Proofs.IRGeneration.SourceSemantics
open Compiler.CompilationModel (Expr Stmt)
open SphincsMinusVerifiers.ClimbKit (N_MASK)
open SphincsMinusVerifiers.ClimbLoop (foldLoop)

/-! ## 0. EDSL constructors (matching `Model.lean`'s private helpers). -/

private def u (n : Nat) : Expr := .literal n
private def v (name : String) : Expr := .localVar name
private def addE (a b : Expr) : Expr := .add a b
private def andE (a b : Expr) : Expr := .bitAnd a b
private def orE (a b : Expr) : Expr := .bitOr a b
private def shlE (a b : Expr) : Expr := .shl a b
private def keccak (off size : Nat) : Expr := .keccak256 (u off) (u size)
private def cdload (off : Expr) : Expr := .calldataload off
private def mloadE (off : Expr) : Expr := .mload off
private def mstore (off : Nat) (val : Expr) : Stmt := .mstore (u off) val
private def mstoreE (off val : Expr) : Stmt := .mstore off val

/-! ## 1. The root-compression copy loop body (statement 20's body). -/

/-- The body of `forEach "i" (u 7)`: copy FORS root slot `0x80 + 32*i` into the
compression slot `0x40 + 32*i`.  A single total `mstore`. -/
def forsCopyBody : List Stmt :=
  [ mstoreE (addE (u 0x40) (shlE (u 5) (v "i"))) (mloadE (addE (u 0x80) (shlE (u 5) (v "i")))) ]

/-- The pure transformer for one copy-loop iteration. -/
def forsCopyStep (st : RuntimeState) : RuntimeState :=
  match execStmtList [] st forsCopyBody with
  | .continue s' => s'
  | _ => st

open SphincsMinusVerifiers.ClimbKit (execStmtList_cons_continue)
open SphincsMinusVerifiers.MemoryKit (execStmt_mstore_continue execStmt_letVar_continue)

/-- Running the copy-loop body continues to `forsCopyStep st` (the single
`mstore` reads a memory cell and writes another — both total). -/
theorem execForsCopy (st : RuntimeState) :
    execStmtList [] st forsCopyBody = .continue (forsCopyStep st) := by
  unfold forsCopyStep forsCopyBody mstoreE
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rfl

/-! ## 2. The full FORS finalize block (statements 15..21). -/

/-- Statements 15..21 of `c13VerifyBody`: the forced-zero 7th FORS leaf, the
root-compression copy loop, and the `forsPk` compression keccak. -/
def forsFinalizeBody : List Stmt :=
  [ .letVar "lastSecret" (andE (cdload (addE (v "sigBase") (addE (u 16) (shlE (u 4) (u 6))))) (u N_MASK))
  , mstore 0x20 (orE (shlE (u 96) (u 3)) (shlE (u 64) (u 6)))
  , mstore 0x40 (v "lastSecret")
  , mstore 0x140 (andE (keccak 0x00 0x60) (u N_MASK))
  , mstore 0x20 (shlE (u 96) (u 4))
  , .forEach "i" (u 7) forsCopyBody
  , .letVar "forsPk" (andE (keccak 0x00 0x120) (u N_MASK)) ]

/-- Faithfulness: `forsFinalizeBody` is *exactly* statements 15..21 of
`c13VerifyBody` (the FORS finalize block, copy loop included). -/
theorem forsFinalizeBody_eq_slice :
    forsFinalizeBody = (c13VerifyBody.drop 15).take 7 := rfl

/-! ## 4. The finalize-block step lemma. -/

/-- The pure transformer for the FORS finalize block: the `.continue` payload of
running `forsFinalizeBody`.  Total because every statement is a
`letVar`/`mstore`/total-`forEach` (the copy loop cannot revert). -/
def forsFinalizeStep (st : RuntimeState) : RuntimeState :=
  match execStmtList [] st forsFinalizeBody with
  | .continue s' => s'
  | _ => st

open SphincsMinusVerifiers.ClimbLoop (execStmt_forEach_of_step)

set_option maxHeartbeats 4000000 in
/-- **`execForsFinalize`** — running the FORS finalize block over the real
interpreter continues to `forsFinalizeStep st`.  The leaf-hash setup chains via
per-statement `.continue` lemmas; the copy loop is dispatched by
`execStmt_forEach_of_step` over `execForsCopy`; the `forsPk` keccak finishes. -/
theorem execForsFinalize (st : RuntimeState) :
    execStmtList [] st forsFinalizeBody = .continue (forsFinalizeStep st) := by
  unfold forsFinalizeStep forsFinalizeBody mstore u
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue st "lastSecret" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _
      (execStmt_forEach_of_step "i" (.literal 7) forsCopyBody _ (wordNormalize 7)
        forsCopyStep rfl execForsCopy)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_letVar_continue _ "forsPk" _ _ rfl)]
  rfl

/-! ## 5. Axiom audit. -/

#print axioms forsFinalizeBody_eq_slice
#print axioms execForsCopy
#print axioms execForsFinalize

end SphincsMinusVerifiers.SegmentS4Finalize
