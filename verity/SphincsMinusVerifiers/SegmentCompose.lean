/-
  SegmentCompose — the full-body control-flow composition of the C13 accept path.

  Each Phase-2 segment lemma threads one slice of `c13VerifyBody` through the real
  interpreter to a symbolic step transformer:

  * `SegmentS2.execS2`            stmts 1..9   → `.continue (s2Step ·)`
  * `SegmentS3.execSegmentS3`     stmts 10..13 → guarded `.continue (stepS3 ·)`
  * `SegmentS4Fors.execForsOuter` stmt  14     → `.continue (foldLoop "i" forsLeafStep ·)`
  * `SegmentS4Finalize.execForsFinalize` stmts 15..21 → `.continue (forsFinalizeStep ·)`
  * `SegmentSeed.execSegmentSeed` stmts 22..24 → `.continue (stepSeed ·)`
  * `SegmentLayer3.execLayerLoop` stmt  25     → guarded `.continue (foldLoop "layer" stepLayer ·)`

  This file composes them — under the length guard and the two body guards (the
  FORS forced-zero guard and the WOTS-checksum climb guards) — into a single
  equality reducing the whole `c13VerifyBody` run to the 3-statement return tail
  (`drop 26`) over one named composite state `afterLayer`.  The reshape of the
  body into the named segments is machine-checked by `rfl` (`body_reshape`).

  This is the **control-flow** backbone of the Phase-3 bridge: it touches neither
  `execC13` nor the `c13_refines_byte_spec` axiom.  The residual gap before the
  axiom can flip is the data correspondence (each step's keccak values vs. the
  abstract spec functions).  No `sorry`, no new `axiom`, no `native_decide`.
-/

import SphincsMinusVerifiers.SegmentS2
import SphincsMinusVerifiers.SegmentS3
import SphincsMinusVerifiers.SegmentS4Fors
import SphincsMinusVerifiers.SegmentS4Finalize
import SphincsMinusVerifiers.SegmentSeed
import SphincsMinusVerifiers.SegmentLayer3

namespace SphincsMinusVerifiers.SegmentCompose

open Compiler.Proofs.IRGeneration.SourceSemantics
open Compiler.CompilationModel (Expr Stmt)
open SphincsMinusVerifiers

/-! ## 1. The composite accept-path states. -/

def afterS2 (st : RuntimeState) : RuntimeState := SegmentS2.s2Step st

def afterS3 (st : RuntimeState) : RuntimeState := SegmentS3.stepS3 (afterS2 st)

def afterFors (st : RuntimeState) : RuntimeState :=
  ClimbLoop.foldLoop "i" SegmentS4Fors.forsLeafStep
    { (afterS3 st) with bindings := bindValue (afterS3 st).bindings "i" (wordNormalize 0) }
    0 (wordNormalize 6)

def afterFinalize (st : RuntimeState) : RuntimeState :=
  SegmentS4Finalize.forsFinalizeStep (afterFors st)

def afterSeed (st : RuntimeState) : RuntimeState := SegmentSeed.stepSeed (afterFinalize st)

def afterLayer (st : RuntimeState) : RuntimeState :=
  ClimbLoop.foldLoop "layer" SegmentLayer3.stepLayer
    { (afterSeed st) with bindings := bindValue (afterSeed st).bindings "layer" (wordNormalize 0) }
    0 (wordNormalize 2)

/-! ## 2. Faithful reshape of the body into named segments (machine-checked). -/

set_option maxHeartbeats 4000000 in
theorem body_reshape :
    c13VerifyBody.tail =
      SegmentS2.s2Body ++ (SegmentS3.segmentS3 ++ ([SegmentS4Fors.forsOuterStmt] ++
        (SegmentS4Finalize.forsFinalizeBody ++ (SegmentSeed.segmentSeed ++
          ([SegmentLayer3.layerStmt] ++ c13VerifyBody.drop 26))))) := rfl

/-! ## 3. Singleton-statement continue helper. -/

private theorem execSingleton_continue (st st' : RuntimeState) (s : Stmt)
    (h : execStmt [] st s = .continue st') :
    execStmtList [] st [s] = .continue st' := by
  rw [execStmtList_cons_continue st st' s [] h]; rfl

/-! ## 4. The headline composition. -/

/-- **`execC13Body_thread`** — under the length guard, the FORS forced-zero guard,
and the WOTS-checksum climb guards, the entire compiled `c13VerifyBody` run reduces
through every straight-line block and loop to the 3-statement return tail over the
composite accept state `afterLayer st`.  Pure control-flow composition of the
Phase-2 segment lemmas; no bridge axiom, no `execC13`. -/
theorem execC13Body_thread
    (st : RuntimeState)
    (hlen : lookupValue st.bindings "sig_length" = wordNormalize 3688)
    (hg3 : SegmentS3.s3Guard (afterS2 st) = 0)
    (hgL : ClimbLoopGuarded.allGuardsPass "layer" SegmentLayer3.stepLayer SegmentLayer3.layerGuard
        { (afterSeed st) with bindings := bindValue (afterSeed st).bindings "layer" (wordNormalize 0) }
        0 (wordNormalize 2)) :
    execStmtList [] st c13VerifyBody
      = execStmtList [] (afterLayer st) (c13VerifyBody.drop 26) := by
  rw [c13VerifyBody_passes_length_guard st hlen, body_reshape]
  -- S2 (stmts 1..9).  The type ascription folds `s2Step st` into `afterS2 st`
  -- (definitional), so every later rewrite stays in named-composite form.
  have hS2 : execStmtList [] st SegmentS2.s2Body = .continue (afterS2 st) :=
    SegmentS2.execS2 st
  rw [MemoryKit.execStmtList_append_continue _ _ _ _ hS2]
  -- S3 (stmts 10..13), forced-zero guard passes
  have hS3 : execStmtList [] (afterS2 st) SegmentS3.segmentS3
      = .continue (afterS3 st) := by
    rw [SegmentS3.execSegmentS3, if_pos hg3]; rfl
  rw [MemoryKit.execStmtList_append_continue _ _ _ _ hS3]
  -- FORS outer loop (stmt 14)
  have hFors : execStmtList [] (afterS3 st) [SegmentS4Fors.forsOuterStmt]
      = .continue (afterFors st) :=
    execSingleton_continue _ _ _ (SegmentS4Fors.execForsOuter (afterS3 st))
  rw [MemoryKit.execStmtList_append_continue _ _ _ _ hFors]
  -- FORS finalize (stmts 15..21)
  have hFin : execStmtList [] (afterFors st) SegmentS4Finalize.forsFinalizeBody
      = .continue (afterFinalize st) :=
    SegmentS4Finalize.execForsFinalize (afterFors st)
  rw [MemoryKit.execStmtList_append_continue _ _ _ _ hFin]
  -- Seed (stmts 22..24)
  have hSeed : execStmtList [] (afterFinalize st) SegmentSeed.segmentSeed
      = .continue (afterSeed st) :=
    SegmentSeed.execSegmentSeed (afterFinalize st)
  rw [MemoryKit.execStmtList_append_continue _ _ _ _ hSeed]
  -- Layer-3 climb (stmt 25), checksum guards pass
  have hLayer : execStmtList [] (afterSeed st) [SegmentLayer3.layerStmt]
      = .continue (afterLayer st) :=
    execSingleton_continue _ _ _ (SegmentLayer3.execLayerLoop (afterSeed st) hgL)
  rw [MemoryKit.execStmtList_append_continue _ _ _ _ hLayer]

/-! ## 5. Threading the 3-statement return tail to a concrete boolean. -/

/-- The EVM boolean word the body returns: the final `currentNode == root` test,
evaluated over the composite accept state `afterLayer st`. -/
def acceptWord (st : RuntimeState) : Nat :=
  boolWord (decide (lookupValue (afterLayer st).bindings "currentNode"
                    = lookupValue (afterLayer st).bindings "root"))

private theorem drop26_eq :
    c13VerifyBody.drop 26 =
      [ (.letVar "valid" (.eq (.localVar "currentNode") (.localVar "root")) : Stmt),
        .mstore (.literal 0) (.localVar "valid"),
        .return (.mload (.literal 0)) ] := rfl

/-- One-step reduction of the trailing `.return` statement: when its expression
resolves, the whole singleton list returns that value (state existentially
quantified — the returned boolean is all the bridge needs). -/
private theorem execStmtList_return_singleton
    (st : RuntimeState) (e : Expr) (val : Nat)
    (h : evalExpr [] st e = some val) :
    ∃ fs, execStmtList [] st [(.return e : Stmt)] = .return val fs := by
  refine ⟨{ st with world := { st.world with
      memory := fun o => if o = 0 then val else st.world.memory o } }, ?_⟩
  show (match (match evalExpr [] st e with
              | some resolved =>
                  StmtResult.return resolved
                    { st with world := { st.world with
                        memory := fun o => if o = 0 then resolved else st.world.memory o } }
              | none => .revert) with
        | .continue n => execStmtList [] n []
        | .stop n => .stop n
        | .return value next => .return value next
        | .revert => .revert) = _
  rw [h]

/-- **`execC13Body_returns`** — the *entire* `c13VerifyBody` run, under the same
three guards, reduces to a single `.return` whose value is the EVM boolean word of
the final `currentNode == root` comparison.  This closes the **control-flow** side
end-to-end (body ⟶ returned boolean); the only remaining obligation is the data
correspondence (`acceptWord st` matching `ByteLevel.verifyBytes`'s accept
decision).  Touches neither `execC13` nor the bridge axiom. -/
theorem execC13Body_returns
    (st : RuntimeState)
    (hlen : lookupValue st.bindings "sig_length" = wordNormalize 3688)
    (hg3 : SegmentS3.s3Guard (afterS2 st) = 0)
    (hgL : ClimbLoopGuarded.allGuardsPass "layer" SegmentLayer3.stepLayer SegmentLayer3.layerGuard
        { (afterSeed st) with bindings := bindValue (afterSeed st).bindings "layer" (wordNormalize 0) }
        0 (wordNormalize 2)) :
    ∃ finalState,
      execStmtList [] st c13VerifyBody
        = .return (wordNormalize (acceptWord st)) finalState := by
  rw [execC13Body_thread st hlen hg3 hgL, drop26_eq]
  -- stmt 26: letVar "valid" (currentNode == root)
  have hletVal : evalExpr [] (afterLayer st)
      (.eq (.localVar "currentNode") (.localVar "root")) = some (acceptWord st) := rfl
  have hlet := MemoryKit.execStmt_letVar_continue (afterLayer st) "valid"
      (.eq (.localVar "currentNode") (.localVar "root")) (acceptWord st) hletVal
  rw [execStmtList_cons_continue _ _ _ _ hlet]
  -- stmt 27: mstore 0x00 (v "valid")
  set s1 := { (afterLayer st) with
      bindings := bindValue (afterLayer st).bindings "valid" (acceptWord st) } with hs1
  have hval : evalExpr [] s1 (.localVar "valid") = some (acceptWord st) := by
    show some (lookupValue s1.bindings "valid") = some (acceptWord st)
    rw [hs1, MemoryKit.lookupValue_bindValue_self]
  have hmstore := MemoryKit.execStmt_mstore_continue s1 (.literal 0) (.localVar "valid")
      (wordNormalize 0) (acceptWord st) rfl hval
  rw [execStmtList_cons_continue _ _ _ _ hmstore]
  -- stmt 28: return (mload 0x00) — reads back the just-stored boolean
  have hmload : evalExpr []
      { s1 with world := { s1.world with
          memory := MemoryKit.memUpdate s1.world.memory (wordNormalize 0) (acceptWord st) } }
      (.mload (.literal 0)) = some (wordNormalize (acceptWord st)) := by
    rw [MemoryKit.evalExpr_mload_eq _ (.literal 0) (wordNormalize 0) rfl]
    show some (MemoryKit.memUpdate s1.world.memory (wordNormalize 0) (acceptWord st)
                (wordNormalize 0)).val = _
    rw [MemoryKit.mstore_then_mload_same]
  exact execStmtList_return_singleton _ (.mload (.literal 0)) _ hmload

/-! ## 6. Axiom audit. -/

#print axioms body_reshape
#print axioms execC13Body_thread
#print axioms execC13Body_returns

end SphincsMinusVerifiers.SegmentCompose
