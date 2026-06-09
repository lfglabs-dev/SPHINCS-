import SphincsMinusVerifiers.C12SegmentWotsSetup
import SphincsMinusVerifiers.ProofCore
import SphincsMinusVerifiers.SegmentAcceptSpec

namespace SphincsMinusVerifiers.C12SegmentFinal

open Compiler.CompilationModel (Stmt Expr)
open Compiler.Proofs.IRGeneration.SourceSemantics
open SphincsMinusVerifierSpec
open SphincsMinusVerifierSpec.C13Concrete (hash16OfWord wordOfHash16)
open SphincsMinusVerifiers.MemoryKit (execStmtList_append_continue execStmt_mstore_continue)

private def u (n : Nat) : Expr := .literal n
private def v (name : String) : Expr := .localVar name
private def eqE (a b : Expr) : Expr := .eq a b
private def mloadE (off : Expr) : Expr := .mload off
private def mstore (off : Nat) (val : Expr) : Stmt := .mstore (u off) val

/-- The executable final C12 comparison after the five-layer hypertree loop. -/
def c12FinalResult (st : RuntimeState) : Option Bool :=
  some (decide (lookupValue st.bindings "currentNode" = lookupValue st.bindings "root"))

def c12FinalSegment : List Stmt := [
  .letVar "valid" (eqE (v "currentNode") (v "root")),
  mstore 0x00 (v "valid"),
  .return (mloadE (u 0x00))
]

theorem c12FinalSegment_eq_after_layer_loop :
    c12FinalSegment = C12SegmentWotsSetup.c12AfterLayerLoop := rfl

def c12FinalBool (st : RuntimeState) : Bool :=
  decide (lookupValue st.bindings "currentNode" = lookupValue st.bindings "root")

def c12FinalWord (st : RuntimeState) : Nat :=
  boolWord (c12FinalBool st)

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

theorem execC12FinalSegment
    (st : RuntimeState) :
    ∃ finalState,
      execStmtList [] st c12FinalSegment =
        .return (wordNormalize (c12FinalWord st)) finalState := by
  unfold c12FinalSegment mstore mloadE eqE v u
  have hletVal : evalExpr [] st
      (.eq (.localVar "currentNode") (.localVar "root")) =
        some (c12FinalWord st) := rfl
  have hlet := MemoryKit.execStmt_letVar_continue st "valid"
      (.eq (.localVar "currentNode") (.localVar "root")) (c12FinalWord st) hletVal
  rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ _ hlet]
  set s1 := { st with bindings := bindValue st.bindings "valid" (c12FinalWord st) } with hs1
  have hval : evalExpr [] s1 (.localVar "valid") = some (c12FinalWord st) := by
    show some (lookupValue s1.bindings "valid") = some (c12FinalWord st)
    rw [hs1, MemoryKit.lookupValue_bindValue_self]
  have hmstore := execStmt_mstore_continue s1 (.literal 0) (.localVar "valid")
      (wordNormalize 0) (c12FinalWord st) rfl hval
  rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ _ hmstore]
  have hmload : evalExpr []
      { s1 with world := { s1.world with
          memory := MemoryKit.memUpdate s1.world.memory (wordNormalize 0) (c12FinalWord st) } }
      (.mload (.literal 0)) = some (wordNormalize (c12FinalWord st)) := by
    rw [MemoryKit.evalExpr_mload_eq _ (.literal 0) (wordNormalize 0) rfl]
    show some (MemoryKit.memUpdate s1.world.memory (wordNormalize 0) (c12FinalWord st)
                (wordNormalize 0)).val = _
    rw [MemoryKit.mstore_then_mload_same]
  exact execStmtList_return_singleton _ (.mload (.literal 0)) _ hmload

theorem c12AfterLayerLoop_observed_eq_final_result
    (st : RuntimeState) :
    observeStmtResultBool
        (execStmtList [] st C12SegmentWotsSetup.c12AfterLayerLoop)
      =
    c12FinalResult st := by
  rw [← c12FinalSegment_eq_after_layer_loop]
  obtain ⟨finalState, hExec⟩ := execC12FinalSegment st
  rw [hExec]
  unfold c12FinalResult c12FinalWord c12FinalBool
  rw [SphincsMinusVerifiers.observeStmtResultBool_return_boolWord]

/-- Final C12 comparison reduced to named model/spec facts.

The remaining semantic work is no longer the whole final-result equality: callers
only need to identify the model's final `currentNode` and `root` words, prove the
parsed verifier reached `.ok specRoot`, and relate the word comparison to the
byte-level root predicate. -/
theorem c12FinalResult_eq_verifyParsed_of_root_bindings
    (st : RuntimeState)
    (pkSeed pkRoot message : ByteArray) (sigParsed : Signature)
    (specRoot : ByteArray)
    (hSpec :
      verifyParsed C12Concrete.c12PrimitivesConcrete c12
        { pkSeed := pkSeed, pkRoot := pkRoot } message sigParsed =
          some (rootMatchesPk c12 specRoot pkRoot))
    (hCurrent :
      lookupValue st.bindings "currentNode" = wordOfHash16 specRoot)
    (hRoot :
      lookupValue st.bindings "root" = wordOfHash16 pkRoot)
    (hWordCmp :
      decide (wordOfHash16 specRoot = wordOfHash16 pkRoot) =
        rootMatchesPk c12 specRoot pkRoot) :
    c12FinalResult st =
      verifyParsed C12Concrete.c12PrimitivesConcrete c12
        { pkSeed := pkSeed, pkRoot := pkRoot } message sigParsed := by
  unfold c12FinalResult
  rw [hCurrent, hRoot, hWordCmp, hSpec]

/-- C12 final comparison bridge: the model's word equality agrees with the
byte-spec root comparison once the produced spec root is canonical as a
16-byte `wordOfHash16` rendering.  The public-key root side is projected by
`rootMatchesPk` for `c12`, so it needs no caller roundtrip premise. -/
theorem wordCmp_of_wordOfHash16_rootMatchesPk_c12
    (specRoot pkRoot : ByteArray)
    (hSpec : hash16OfWord (wordOfHash16 specRoot) = specRoot) :
    decide (wordOfHash16 specRoot = wordOfHash16 pkRoot)
      = rootMatchesPk c12 specRoot pkRoot := by
  rw [← SegmentAcceptSpec.wordOfHash16_lowBytesProjection16 pkRoot]
  unfold rootMatchesPk comparePkRootBytes
  simp [c12]
  exact SegmentAcceptSpec.wordCmp_of_wordOfHash16_roundtrip
    specRoot (lowBytesProjection 16 pkRoot) hSpec
    (SegmentAcceptSpec.hash16OfWord_wordOfHash16_of_size
      (lowBytesProjection 16 pkRoot) (by
        simp [lowBytesProjection, bytesOfNatBE, ByteArray.size]))

#print axioms execC12FinalSegment
#print axioms c12AfterLayerLoop_observed_eq_final_result
#print axioms c12FinalResult_eq_verifyParsed_of_root_bindings
#print axioms wordCmp_of_wordOfHash16_rootMatchesPk_c12

end SphincsMinusVerifiers.C12SegmentFinal
