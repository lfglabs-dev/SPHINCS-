import SphincsMinusVerifiers.Proofs

namespace SphincsMinusVerifiers

open SphincsMinusVerifierSpec
open Compiler.Proofs.IRGeneration.SourceSemantics
open SphincsMinusVerifiers.MkC13State
open SphincsMinusVerifiers.SegmentCompose

theorem c13_light_world (ls : RuntimeState) :
    (c13BeforeWotsPkLightState ls).world = (SegmentLayer3.afterDigit ls).world := rfl

theorem c13_light_bindings (ls : RuntimeState) :
    (c13BeforeWotsPkLightState ls).bindings =
      bindValue
        (bindValue (SegmentLayer3.afterDigit ls).bindings "wotsPtr"
          ((evalExpr [] (SegmentLayer3.afterDigit ls)
            (.add (.localVar "sigBase") (.localVar "sigOff"))).getD 0))
        "i" (wordNormalize 0) := rfl

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

set_option maxHeartbeats 2000000 in
theorem c13_layer0_light_seed0 (pkSeed pkRoot message sig : Bytes) :
    ((c13BeforeWotsPkLightState
        (c13FirstLayerGuardState pkSeed pkRoot message sig)).world.memory 0x00).val =
      C13Concrete.wordOfHash16 pkSeed := by
  rw [c13_light_world]
  rw [SegmentLayer3.afterDigit_preserves_memory_zero]
  exact c13FirstLayerGuardState_seed_slot pkSeed pkRoot message sig

set_option maxHeartbeats 2000000 in
theorem c13_layer0_light_d0 (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk : Bytes) (lsig : XmssLayerSig)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      sigParsed.fors = some forsPk)
    (hLayer0 : sigParsed.layers[0]? = some lsig) :
    lookupValue
        (c13BeforeWotsPkLightState
          (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings "d" =
      C13Concrete.wotsDigest (C13Concrete.wordOfHash16 pkSeed)
        0
        ((C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048)
        ((C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex % 2048)
        lsig.wots.count (C13Concrete.wordOfHash16 forsPk) := by
  rw [c13_light_bindings]
  rw [MemoryKit.lookupValue_bindValue_ne _ "i" "d" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "wotsPtr" "d" _ (by decide)]
  rw [SegmentLayer3.afterDigit_preserves_lookup_of_ne
    (c13FirstLayerGuardState pkSeed pkRoot message sig) "d"
    (by decide) (by decide)]
  exact SegmentLayer3.beforeDigitLoop_d_eq_wotsDigest_of_scratch
    (c13FirstLayerGuardState pkSeed pkRoot message sig)
    (C13Concrete.wordOfHash16 pkSeed) 0
    ((C13Concrete.c13PrimitivesConcrete.hMsg c13
      { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048)
    ((C13Concrete.c13PrimitivesConcrete.hMsg c13
      { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex % 2048)
    lsig.wots.count
    (C13Concrete.wordOfHash16 forsPk)
    (c13FirstLayerBeforeDigest_seed_slot pkSeed pkRoot message sig)
    (c13FirstLayerBeforeDigest_wotsAdrs_slot_hyperIndex
      pkSeed pkRoot message sig sigParsed hParse)
    (c13FirstLayerBeforeDigest_currentNode_slot
      pkSeed pkRoot message sig forsPk
      (c13AfterFinalize_forsPk_of_parse_fors
        pkSeed pkRoot message sig sigParsed forsPk hParse hFors))
    (c13FirstLayerBeforeDigest_count_slot_hyperIndex
      pkSeed pkRoot message sig sigParsed lsig hParse hLayer0)

set_option maxHeartbeats 2000000 in
theorem c13_layer0_light_adrs0 (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed) :
    lookupValue
        (c13BeforeWotsPkLightState
          (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings "wotsAdrs" =
      C13Concrete.adrsWotsHashBase 0
        ((C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048)
        ((C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex % 2048) := by
  rw [c13_light_bindings]
  rw [MemoryKit.lookupValue_bindValue_ne _ "i" "wotsAdrs" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "wotsPtr" "wotsAdrs" _ (by decide)]
  rw [SegmentLayer3.afterDigit_preserves_lookup_of_ne
    (c13FirstLayerGuardState pkSeed pkRoot message sig) "wotsAdrs"
    (by decide) (by decide)]
  rw [c13_beforeDigitLoop_lookup_eq_beforeDigest_of_ne
    (c13FirstLayerGuardState pkSeed pkRoot message sig) "wotsAdrs"
    (by decide) (by decide)]
  exact c13FirstLayerBeforeDigest_wotsAdrs_hyperIndex
    pkSeed pkRoot message sig sigParsed hParse

set_option maxHeartbeats 2000000 in
theorem c13_layer0_light_wptr0 (pkSeed pkRoot message sig : Bytes) :
    lookupValue
        (c13BeforeWotsPkLightState
          (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings "wotsPtr" =
      sigDataOffset + 1952 := by
  rw [c13_light_bindings]
  rw [MemoryKit.lookupValue_bindValue_ne _ "i" "wotsPtr" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_self]
  have hSigBase : evalExpr []
      (SegmentLayer3.afterDigit
        (c13FirstLayerGuardState pkSeed pkRoot message sig))
      (.localVar "sigBase") = some sigDataOffset := by
    show some (lookupValue
      (SegmentLayer3.afterDigit
        (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
      "sigBase") = _
    rw [SegmentLayer3.afterDigit_preserves_lookup_of_ne
      (c13FirstLayerGuardState pkSeed pkRoot message sig) "sigBase"
      (by decide) (by decide)]
    rw [SegmentLayer3.beforeDigitLoop_preserves_sigBase]
    rw [c13FirstLayerGuardState_sigBase]
  have hSigOff : evalExpr []
      (SegmentLayer3.afterDigit
        (c13FirstLayerGuardState pkSeed pkRoot message sig))
      (.localVar "sigOff") = some 1952 := by
    show some (lookupValue
      (SegmentLayer3.afterDigit
        (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
      "sigOff") = _
    rw [SegmentLayer3.afterDigit_preserves_lookup_of_ne
      (c13FirstLayerGuardState pkSeed pkRoot message sig) "sigOff"
      (by decide) (by decide)]
    rw [c13_beforeDigitLoop_preserves_sigOff]
    rw [c13FirstLayerGuardState_sigOff]
    rw [SegmentS2.wordNormalize_of_lt (by decide : 1952 < 2 ^ 256)]
  rw [SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_add_bounded
    _ _ _ _ _ hSigBase hSigOff
    (by decide) (by decide) (by decide)]
  rfl

set_option maxHeartbeats 2000000 in
theorem c13_layer0_light_cd0 (pkSeed pkRoot message sig : Bytes) :
    (c13BeforeWotsPkLightState
        (c13FirstLayerGuardState pkSeed pkRoot message sig)).world.calldata =
      headWords pkSeed pkRoot message sig.size ++ bytesToWords sig := by
  rw [c13_light_world]
  rw [(SegmentLayer3.afterDigit_preserves_selector_calldata
    (c13FirstLayerGuardState pkSeed pkRoot message sig)).2]
  exact c13FirstLayerGuardState_calldata pkSeed pkRoot message sig

end SphincsMinusVerifiers
