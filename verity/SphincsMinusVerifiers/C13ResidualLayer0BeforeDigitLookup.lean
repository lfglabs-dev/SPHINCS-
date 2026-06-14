import SphincsMinusVerifiers.SegmentLayer3

namespace SphincsMinusVerifiers

open Compiler.Proofs.IRGeneration.SourceSemantics

theorem c13_beforeDigitLoop_lookup_eq_beforeDigest_of_ne
    (ls : RuntimeState) (key : String)
    (hneD : "d" ≠ key) (hneSum : "digitSum" ≠ key) :
    lookupValue (SegmentLayer3.beforeDigitLoop ls).bindings key =
      lookupValue (SegmentLayer3.beforeDigest ls).bindings key := by
  have h : execStmtList [] ls
      (SegmentLayer3.prefixBeforeDigest ++
        [ Compiler.CompilationModel.Stmt.letVar "d"
            (.keccak256 (.literal 0x00) (.literal 0x80))
        , Compiler.CompilationModel.Stmt.letVar "digitSum" (.literal 0) ]) =
      .continue (SegmentLayer3.beforeDigitLoop ls) :=
    SegmentLayer3.beforeDigitLoop_eq ls
  rw [MemoryKit.execStmtList_append_continue _ _ _ _
    (SegmentLayer3.beforeDigest_eq ls)] at h
  rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "d" _ _ rfl)] at h
  rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "digitSum" _ _ rfl)] at h
  have hnil : ∀ (s : RuntimeState), execStmtList [] s [] = StmtResult.continue s :=
    fun _ => rfl
  rw [hnil] at h
  have he := StmtResult.continue.inj h
  rw [← he]
  rw [MemoryKit.lookupValue_bindValue_ne _ "digitSum" key _ hneSum]
  rw [MemoryKit.lookupValue_bindValue_ne _ "d" key _ hneD]

end SphincsMinusVerifiers
