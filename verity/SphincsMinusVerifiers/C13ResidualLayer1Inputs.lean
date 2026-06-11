import SphincsMinusVerifiers.C13ResidualLayer0Inputs

namespace SphincsMinusVerifiers

open SphincsMinusVerifierSpec
open Compiler.Proofs.IRGeneration.SourceSemantics
open SphincsMinusVerifiers.MkC13State
open SphincsMinusVerifiers.SegmentCompose

set_option maxHeartbeats 2000000 in
theorem c13_layer1_light_seed1 (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed) :
    ((c13BeforeWotsPkLightState
        (c13SecondLayerGuardState pkSeed pkRoot message sig)).world.memory 0x00).val =
      C13Concrete.wordOfHash16 pkSeed := by
  rw [c13_light_world]
  rw [SegmentLayer3.afterDigit_preserves_memory_zero]
  unfold c13SecondLayerGuardState
  rw [ClimbLoopGuarded.loopState_preserves_memory_val]
  exact c13FirstStepLayer_seed_slot_of_memory_zero pkSeed pkRoot message sig
    (by
      simpa [c13FirstLayerGuardState_eq_c13LayerLoopState0] using
        c13FirstLayerStep_preserves_memory_zero_of_parse
          pkSeed pkRoot message sig sigParsed hParse)

set_option maxHeartbeats 2000000 in
theorem c13_layer1_current0Root (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hZero : forcedZeroOk c13
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      sigParsed.fors = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      forsPk sigParsed.layers = .ok specRoot)
    (d : C13Concrete.FoldHypertreeC13OkTwoLayerData
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      forsPk sigParsed.layers specRoot) :
    lookupValue (c13SecondLayerGuardState pkSeed pkRoot message sig).bindings
        "currentNode" = C13Concrete.wordOfHash16 d.root0 := by
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  have hWotsPk0 :
      C13FoldOkAfterMerkleRawXmssClimbInitialWotsPkDataLayer0
        pkSeed pkRoot message sig sigParsed forsPk specRoot :=
    c13_ok_afterMerkle_initial_wotsPk_residual_layer0
      pkSeed pkRoot message sig sigParsed forsPk specRoot hParse hZero hFors hFold
  have hInit0 :
      C13FoldOkAfterMerkleNormalizedXmssClimbInitialFrameDataLayer0
        pkSeed pkRoot message sig sigParsed forsPk specRoot :=
    c13FoldOkAfterMerkleNormalizedXmssClimbInitialFrameDataLayer0_of_wotsPk
      pkSeed pkRoot message sig sigParsed forsPk specRoot hParse hWotsPk0
  have hRawInit0 :
      C13FoldOkAfterMerkleRawXmssClimbInitialFrameDataLayer0
        pkSeed pkRoot message sig sigParsed forsPk specRoot :=
    c13FoldOkAfterMerkleRawXmssClimbInitialFrameDataLayer0_of_wotsPk
      pkSeed pkRoot message sig sigParsed forsPk specRoot hParse hWotsPk0
  have hD0 :
      ∀ i, i < 11 →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
          d.lsig0.authPath
          (c13XmssAuthCdAt pkSeed pkRoot message sig
            (sigDataOffset + (1952 + 868 * 0 + 692))) i := by
    simpa [pk, c13XmssAuthCdAt] using
      SphincsMinusVerifiers.ClimbMemFrameMerkle.xmss_climb_data_range
        pkSeed pkRoot message sig c13 sigParsed d.lsig0 0
        (sigDataOffset + (1952 + 868 * 0 + 692))
        hParse (by decide : 0 < 2) d.hLayer0 rfl
  have hTreeLt0 :
      C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048) < 2 ^ 256 :=
    c13_adrsXmssTree_lt_of_bounds 0 (digest.hyperIndex / 2048)
      (by decide : 0 < 2 ^ 32)
      (lt_of_le_of_lt (Nat.div_le_self _ _)
        (C13Concrete.hMsgC13_hyperIndex_lt pk sigParsed.R message))
  have hMIdxNorm0 :
      wordNormalize (digest.hyperIndex % 2048) = digest.hyperIndex % 2048 :=
    wordNormalize_mod_2048 digest.hyperIndex
  have hAfterRaw :
      lookupValue
          (SegmentLayer3.afterMerkle
            (CurrentNodeFrame.c13LayerLoopState0
              (mkC13State pkSeed pkRoot message sig))).bindings
          "merkleNode"
        =
          C13Concrete.xmssClimb (C13Concrete.wordOfHash16 pkSeed)
            (C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048))
            11 0 (digest.hyperIndex % 2048)
            (C13Concrete.wordOfHash16 d.wotsPk0) d.lsig0.authPath := by
    simpa [pk, digest] using
      c13AfterMerkleRawXmssClimb_of_layer_site_bounded
        pkSeed pkRoot message sig
        (C13Concrete.wordOfHash16 pkSeed)
        (C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048))
        0 d.lsig0.authPath
        (by decide : 0 < 2) hTreeLt0
        (CurrentNodeFrame.c13LayerLoopState0
          (mkC13State pkSeed pkRoot message sig))
        (digest.hyperIndex % 2048)
        (C13Concrete.wordOfHash16 d.wotsPk0)
        hD0
        (by simpa [pk, digest] using hInit0 d)
        (by simpa [pk, digest] using hRawInit0 d)
        hMIdxNorm0
  have hRawStep :
      lookupValue
          (SegmentLayer3.stepLayer
            (CurrentNodeFrame.c13LayerLoopState0
              (mkC13State pkSeed pkRoot message sig))).bindings
          "merkleNode"
        =
          C13Concrete.xmssClimb (C13Concrete.wordOfHash16 pkSeed)
            (C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048))
            11 0 (digest.hyperIndex % 2048)
            (C13Concrete.wordOfHash16 d.wotsPk0) d.lsig0.authPath :=
    c13_stepLayer_merkleNode_eq_xmssClimb_of_afterMerkle
      (CurrentNodeFrame.c13LayerLoopState0
        (mkC13State pkSeed pkRoot message sig))
      _ _ _ _ _ hAfterRaw
  have hMerkle0Root :
      lookupValue
          (SegmentLayer3.stepLayer
            (CurrentNodeFrame.c13LayerLoopState0
              (mkC13State pkSeed pkRoot message sig))).bindings
          "merkleNode"
        = C13Concrete.wordOfHash16 d.root0 :=
    SegmentAcceptSpec.stepLayer_merkleNode_eq_wordOfHash16_root_of_xmssClimb_wots_success
      pk (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
      forsPk d.wotsPk0 d.root0 d.lsig0.wots d.lsig0.authPath
      (CurrentNodeFrame.c13LayerLoopState0
        (mkC13State pkSeed pkRoot message sig))
      (by
        simpa [pk, digest, C13Concrete.c13PrimitivesConcrete,
          C13Concrete.wotsPkFromSigC13AtLayer_zero] using d.hWots0)
      (by
        simpa [pk, digest, C13Concrete.c13PrimitivesConcrete,
          C13Concrete.xmssRootFromSigC13AtLayer_zero] using d.hXmss0)
      (by simpa [pk, digest] using hRawStep)
  unfold c13SecondLayerGuardState ClimbLoopGuarded.loopState
  rw [MemoryKit.lookupValue_bindValue_ne _ "layer" "currentNode" _ (by decide)]
  rw [SegmentLayer3.stepLayer_currentNode_eq_merkleNode]
  simpa [pk, digest] using hMerkle0Root

set_option maxHeartbeats 2000000 in
theorem c13_layer1_light_d1 (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (root0 : Bytes) (lsig : XmssLayerSig)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hLayer1 : sigParsed.layers[1]? = some lsig)
    (hStepSeed :
      ((SegmentLayer3.stepLayer
        (c13FirstLayerGuardState pkSeed pkRoot message sig)).world.memory 0x00).val =
        C13Concrete.wordOfHash16 pkSeed)
    (hCurrent :
      lookupValue (c13SecondLayerGuardState pkSeed pkRoot message sig).bindings
        "currentNode" = C13Concrete.wordOfHash16 root0) :
    lookupValue
        (c13BeforeWotsPkLightState
          (c13SecondLayerGuardState pkSeed pkRoot message sig)).bindings "d" =
      C13Concrete.wotsDigest (C13Concrete.wordOfHash16 pkSeed)
        1
        (((C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048) / 2048)
        (((C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048) % 2048)
        lsig.wots.count (C13Concrete.wordOfHash16 root0) := by
  rw [c13_light_bindings]
  rw [MemoryKit.lookupValue_bindValue_ne _ "i" "d" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "wotsPtr" "d" _ (by decide)]
  rw [SegmentLayer3.afterDigit_preserves_lookup_of_ne
    (c13SecondLayerGuardState pkSeed pkRoot message sig) "d"
    (by decide) (by decide)]
  exact SegmentLayer3.beforeDigitLoop_d_eq_wotsDigest_of_scratch
    (c13SecondLayerGuardState pkSeed pkRoot message sig)
    (C13Concrete.wordOfHash16 pkSeed) 1
    (((C13Concrete.c13PrimitivesConcrete.hMsg c13
      { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048) / 2048)
    (((C13Concrete.c13PrimitivesConcrete.hMsg c13
      { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048) % 2048)
    lsig.wots.count
    (C13Concrete.wordOfHash16 root0)
    (c13SecondLayerBeforeDigest_seed_slot_of_first_step_seed_slot
      pkSeed pkRoot message sig hStepSeed)
    (c13SecondLayerBeforeDigest_wotsAdrs_slot_hyperIndex
      pkSeed pkRoot message sig sigParsed hParse)
    (c13SecondLayerBeforeDigest_currentNode_slot
      pkSeed pkRoot message sig root0 hCurrent)
    (c13SecondLayerBeforeDigest_count_slot_hyperIndex
      pkSeed pkRoot message sig sigParsed lsig hParse hLayer1)

set_option maxHeartbeats 2000000 in
theorem c13_layer1_light_adrs1 (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed) :
    lookupValue
        (c13BeforeWotsPkLightState
          (c13SecondLayerGuardState pkSeed pkRoot message sig)).bindings "wotsAdrs" =
      C13Concrete.adrsWotsHashBase 1
        (((C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048) / 2048)
        (((C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048) % 2048) := by
  rw [c13_light_bindings]
  rw [MemoryKit.lookupValue_bindValue_ne _ "i" "wotsAdrs" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "wotsPtr" "wotsAdrs" _ (by decide)]
  rw [SegmentLayer3.afterDigit_preserves_lookup_of_ne
    (c13SecondLayerGuardState pkSeed pkRoot message sig) "wotsAdrs"
    (by decide) (by decide)]
  rw [c13_beforeDigitLoop_lookup_eq_beforeDigest_of_ne
    (c13SecondLayerGuardState pkSeed pkRoot message sig) "wotsAdrs"
    (by decide) (by decide)]
  exact c13SecondLayerBeforeDigest_wotsAdrs_hyperIndex
    pkSeed pkRoot message sig sigParsed hParse

set_option maxHeartbeats 2000000 in
theorem c13_layer1_light_wptr1 (pkSeed pkRoot message sig : Bytes) :
    lookupValue
        (c13BeforeWotsPkLightState
          (c13SecondLayerGuardState pkSeed pkRoot message sig)).bindings "wotsPtr" =
      sigDataOffset + (1952 + 868) := by
  rw [c13_light_bindings]
  rw [MemoryKit.lookupValue_bindValue_ne _ "i" "wotsPtr" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_self]
  have hSigBase : evalExpr []
      (SegmentLayer3.afterDigit
        (c13SecondLayerGuardState pkSeed pkRoot message sig))
      (.localVar "sigBase") = some sigDataOffset := by
    show some (lookupValue
      (SegmentLayer3.afterDigit
        (c13SecondLayerGuardState pkSeed pkRoot message sig)).bindings
      "sigBase") = _
    rw [SegmentLayer3.afterDigit_preserves_lookup_of_ne
      (c13SecondLayerGuardState pkSeed pkRoot message sig) "sigBase"
      (by decide) (by decide)]
    rw [SegmentLayer3.beforeDigitLoop_preserves_sigBase]
    rw [c13SecondLayerGuardState_sigBase]
  have hSigOff : evalExpr []
      (SegmentLayer3.afterDigit
        (c13SecondLayerGuardState pkSeed pkRoot message sig))
      (.localVar "sigOff") = some 2820 := by
    show some (lookupValue
      (SegmentLayer3.afterDigit
        (c13SecondLayerGuardState pkSeed pkRoot message sig)).bindings
      "sigOff") = _
    rw [SegmentLayer3.afterDigit_preserves_lookup_of_ne
      (c13SecondLayerGuardState pkSeed pkRoot message sig) "sigOff"
      (by decide) (by decide)]
    rw [c13_beforeDigitLoop_preserves_sigOff]
    rw [c13SecondLayerGuardState_sigOff]
  rw [SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_add_bounded
    _ _ _ _ _ hSigBase hSigOff
    (by decide) (by decide) (by decide)]
  rfl

set_option maxHeartbeats 2000000 in
theorem c13_layer1_light_cd1 (pkSeed pkRoot message sig : Bytes) :
    (c13BeforeWotsPkLightState
        (c13SecondLayerGuardState pkSeed pkRoot message sig)).world.calldata =
      headWords pkSeed pkRoot message sig.size ++ bytesToWords sig := by
  rw [c13_light_world]
  rw [(SegmentLayer3.afterDigit_preserves_selector_calldata
    (c13SecondLayerGuardState pkSeed pkRoot message sig)).2]
  exact c13SecondLayerGuardState_calldata pkSeed pkRoot message sig

end SphincsMinusVerifiers
