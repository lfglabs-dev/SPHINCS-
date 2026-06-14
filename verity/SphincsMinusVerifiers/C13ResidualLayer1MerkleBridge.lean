import SphincsMinusVerifiers.C13ResidualLayer1StateFacts

namespace SphincsMinusVerifiers

open SphincsMinusVerifierSpec
open Compiler.Proofs.IRGeneration.SourceSemantics
open SphincsMinusVerifiers.MkC13State

theorem c13Residual_beforeMerkle_merkleNode_eq_wotsPk (ls : RuntimeState) :
    lookupValue (SegmentLayer3.beforeMerkle ls).bindings "merkleNode" =
      lookupValue (SegmentLayer3.beforeMerkle ls).bindings "wotsPk" := by
  unfold SegmentLayer3.beforeMerkle
  rw [show SegmentLayer3.suffixBeforeMerkle =
      SegmentLayer3.suffixBeforeMIdx ++
        [ .letVar "mIdx" (.localVar "idxLeaf")
        , .letVar "merklePtr" (.add
            (.localVar "sigBase") (.localVar "authOff")) ] by rfl]
  rw [MemoryKit.execStmtList_append_continue _ _ _ _ (SegmentLayer3.beforeMIdx_eq ls)]
  rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "mIdx" _ _ rfl)]
  rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "merklePtr" _ _ rfl)]
  simp only [Compiler.Proofs.IRGeneration.SourceSemantics.execStmtList]
  rw [MemoryKit.lookupValue_bindValue_ne _ "merklePtr" "merkleNode" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "mIdx" "merkleNode" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "merklePtr" "wotsPk" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "mIdx" "wotsPk" _ (by decide)]
  unfold SegmentLayer3.beforeMIdx SegmentLayer3.suffixBeforeMIdx
  rw [MemoryKit.execStmtList_append_continue _ _ _ _ (SegmentLayer3.beforeAuthOff_eq ls)]
  rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "authOff" _ _ rfl)]
  rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "treeAdrs" _ _ rfl)]
  rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "merkleNode" _ _ rfl)]
  simp only [Compiler.Proofs.IRGeneration.SourceSemantics.execStmtList]
  rw [MemoryKit.lookupValue_bindValue_self]
  rw [MemoryKit.lookupValue_bindValue_ne _ "merkleNode" "wotsPk" _ (by decide)]

theorem c13Residual_beforeMerkle_wotsPk_eq_beforeAuthOff_wotsPk (ls : RuntimeState) :
    lookupValue (SegmentLayer3.beforeMerkle ls).bindings "wotsPk" =
      lookupValue (SegmentLayer3.beforeAuthOff ls).bindings "wotsPk" := by
  unfold SegmentLayer3.beforeMerkle
  rw [show SegmentLayer3.suffixBeforeMerkle =
        SegmentLayer3.suffixBeforeAuthOff ++
          SegmentLayer3.suffixBeforeMerkle.drop SegmentLayer3.suffixBeforeAuthOff.length by rfl]
  rw [MemoryKit.execStmtList_append_continue _ _ _ _ (SegmentLayer3.beforeAuthOff_eq ls)]
  simp only [SegmentLayer3.suffixBeforeAuthOff, SegmentLayer3.suffixBeforeMerkle,
    List.length_cons, List.length_nil, List.drop]
  rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "authOff" _ _ rfl)]
  rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "treeAdrs" _ _ rfl)]
  rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "merkleNode" _ _ rfl)]
  rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "mIdx" _ _ rfl)]
  rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "merklePtr" _ _ rfl)]
  simp only [Compiler.Proofs.IRGeneration.SourceSemantics.execStmtList]
  rw [MemoryKit.lookupValue_bindValue_ne _ "merklePtr" "wotsPk" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "mIdx" "wotsPk" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "merkleNode" "wotsPk" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "treeAdrs" "wotsPk" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "authOff" "wotsPk" _ (by decide)]

def C13ResidualXmssAuthCdAt
    (pkSeed pkRoot message sig : Bytes) (merklePtr : Nat) : Nat → Nat :=
  fun j =>
    Compiler.Proofs.YulGeneration.calldataloadWord 0
      (headWords pkSeed pkRoot message sig.size ++ bytesToWords sig)
      (merklePtr + 16 * j)

end SphincsMinusVerifiers
