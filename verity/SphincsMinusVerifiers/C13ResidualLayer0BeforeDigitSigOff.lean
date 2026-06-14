import SphincsMinusVerifiers.SegmentLayer3

namespace SphincsMinusVerifiers

open Compiler.Proofs.IRGeneration.SourceSemantics

theorem c13_beforeDigitLoop_preserves_sigOff (ls : RuntimeState) :
    lookupValue (SegmentLayer3.beforeDigitLoop ls).bindings "sigOff" =
      lookupValue ls.bindings "sigOff" := by
  refine BindingFrame.execStmtList_preserves_lookup "sigOff"
    SegmentLayer3.prefixBeforeDigitLoop
    ls (SegmentLayer3.beforeDigitLoop ls) ?_ (SegmentLayer3.beforeDigitLoop_eq ls)
  intro s s'' stmt hmem hexec
  simp [SegmentLayer3.prefixBeforeDigitLoop] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact BindingFrame.execStmt_letVar_preserves_lookup _ _ "idxLeaf" "sigOff" _ (by decide) hexec
  · exact BindingFrame.execStmt_assignVar_preserves_lookup _ _ "idxTree" "sigOff" _ (by decide) hexec
  · exact BindingFrame.execStmt_letVar_preserves_lookup _ _ "wotsAdrs" "sigOff" _ (by decide) hexec
  · exact BindingFrame.execStmt_letVar_preserves_lookup _ _ "countOff" "sigOff" _ (by decide) hexec
  · exact BindingFrame.execStmt_letVar_preserves_lookup _ _ "count" "sigOff" _ (by decide) hexec
  · exact BindingFrame.execStmt_mstore_preserves_lookup _ _ "sigOff" _ _ hexec
  · exact BindingFrame.execStmt_mstore_preserves_lookup _ _ "sigOff" _ _ hexec
  · exact BindingFrame.execStmt_mstore_preserves_lookup _ _ "sigOff" _ _ hexec
  · exact BindingFrame.execStmt_letVar_preserves_lookup _ _ "d" "sigOff" _ (by decide) hexec
  · exact BindingFrame.execStmt_letVar_preserves_lookup _ _ "digitSum" "sigOff" _ (by decide) hexec

end SphincsMinusVerifiers
