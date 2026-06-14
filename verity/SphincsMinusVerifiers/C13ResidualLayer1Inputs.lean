import SphincsMinusVerifiers.C13ResidualLayer1Facts
import SphincsMinusVerifiers.C13ResidualLayer0Inputs
import SphincsMinusVerifiers.C13ResidualLayer1StepSeedFrame

namespace SphincsMinusVerifiers

open SphincsMinusVerifierSpec
open Compiler.Proofs.IRGeneration.SourceSemantics
open SphincsMinusVerifiers.MkC13State
open SphincsMinusVerifiers.SegmentCompose

axiom c13ResidualFirstLayerStep_seed_slot_of_parse
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed) :
    ((SegmentLayer3.stepLayer
      (c13ResidualFirstLayerGuardState pkSeed pkRoot message sig)).world.memory 0x00).val =
      C13Concrete.wordOfHash16 pkSeed

set_option maxHeartbeats 2000000 in
theorem c13_layer1_light_seed1 (pkSeed pkRoot message sig : Bytes)
    (hStepSeed :
      ((SegmentLayer3.stepLayer
        (c13ResidualFirstLayerGuardState pkSeed pkRoot message sig)).world.memory 0x00).val =
        C13Concrete.wordOfHash16 pkSeed) :
    ((c13BeforeWotsPkLightState
        (c13ResidualSecondLayerGuardState pkSeed pkRoot message sig)).world.memory 0x00).val =
      C13Concrete.wordOfHash16 pkSeed := by
  unfold c13BeforeWotsPkLightState
  unfold SegmentLayer3AddressCells.beforeWotsPkWotsPtrFrom
  rw [SegmentLayer3.afterDigit_preserves_memory_zero]
  unfold c13ResidualSecondLayerGuardState
  rw [ClimbLoopGuarded.loopState_preserves_memory_val]
  exact hStepSeed

axiom c13Residual_layer1_current0Root (pkSeed pkRoot message sig : Bytes)
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
    lookupValue (c13ResidualSecondLayerGuardState pkSeed pkRoot message sig).bindings
        "currentNode" = C13Concrete.wordOfHash16 d.root0

set_option maxHeartbeats 2000000 in
theorem c13_layer1_light_d1 (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (root0 : Bytes) (lsig : XmssLayerSig)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hLayer1 : sigParsed.layers[1]? = some lsig)
    (hStepSeed :
      ((SegmentLayer3.stepLayer
        (c13ResidualFirstLayerGuardState pkSeed pkRoot message sig)).world.memory 0x00).val =
        C13Concrete.wordOfHash16 pkSeed)
    (hCurrent :
      lookupValue (c13ResidualSecondLayerGuardState pkSeed pkRoot message sig).bindings
        "currentNode" = C13Concrete.wordOfHash16 root0) :
    lookupValue
        (c13BeforeWotsPkLightState
          (c13ResidualSecondLayerGuardState pkSeed pkRoot message sig)).bindings "d" =
      C13Concrete.wotsDigest (C13Concrete.wordOfHash16 pkSeed)
        1
        (((C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048) / 2048)
        (((C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048) % 2048)
        lsig.wots.count (C13Concrete.wordOfHash16 root0) := by
  unfold c13BeforeWotsPkLightState
  unfold SegmentLayer3AddressCells.beforeWotsPkWotsPtrFrom
  rw [MemoryKit.lookupValue_bindValue_ne _ "i" "d" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "wotsPtr" "d" _ (by decide)]
  rw [SegmentLayer3.afterDigit_preserves_lookup_of_ne
    (c13ResidualSecondLayerGuardState pkSeed pkRoot message sig) "d"
    (by decide) (by decide)]
  exact SegmentLayer3.beforeDigitLoop_d_eq_wotsDigest_of_scratch
    (c13ResidualSecondLayerGuardState pkSeed pkRoot message sig)
    (C13Concrete.wordOfHash16 pkSeed) 1
    (((C13Concrete.c13PrimitivesConcrete.hMsg c13
      { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048) / 2048)
    (((C13Concrete.c13PrimitivesConcrete.hMsg c13
      { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048) % 2048)
    lsig.wots.count
    (C13Concrete.wordOfHash16 root0)
    (c13ResidualSecondLayerBeforeDigest_seed_slot_of_first_step_seed_slot
      pkSeed pkRoot message sig hStepSeed)
    (c13ResidualSecondLayerBeforeDigest_wotsAdrs_slot_hyperIndex
      pkSeed pkRoot message sig sigParsed hParse)
    (c13ResidualSecondLayerBeforeDigest_currentNode_slot
      pkSeed pkRoot message sig root0 hCurrent)
    (c13ResidualSecondLayerBeforeDigest_count_slot_hyperIndex
      pkSeed pkRoot message sig sigParsed lsig hParse hLayer1)

set_option maxHeartbeats 2000000 in
theorem c13_layer1_light_adrs1 (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed) :
    lookupValue
        (c13BeforeWotsPkLightState
          (c13ResidualSecondLayerGuardState pkSeed pkRoot message sig)).bindings "wotsAdrs" =
      C13Concrete.adrsWotsHashBase 1
        (((C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048) / 2048)
        (((C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048) % 2048) := by
  unfold c13BeforeWotsPkLightState
  unfold SegmentLayer3AddressCells.beforeWotsPkWotsPtrFrom
  rw [MemoryKit.lookupValue_bindValue_ne _ "i" "wotsAdrs" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "wotsPtr" "wotsAdrs" _ (by decide)]
  rw [SegmentLayer3.afterDigit_preserves_lookup_of_ne
    (c13ResidualSecondLayerGuardState pkSeed pkRoot message sig) "wotsAdrs"
    (by decide) (by decide)]
  rw [c13_beforeDigitLoop_lookup_eq_beforeDigest_of_ne
    (c13ResidualSecondLayerGuardState pkSeed pkRoot message sig) "wotsAdrs"
    (by decide) (by decide)]
  exact c13ResidualSecondLayerBeforeDigest_wotsAdrs_hyperIndex
    pkSeed pkRoot message sig sigParsed hParse

set_option maxHeartbeats 2000000 in
theorem c13_layer1_light_wptr1 (pkSeed pkRoot message sig : Bytes) :
    lookupValue
        (c13BeforeWotsPkLightState
          (c13ResidualSecondLayerGuardState pkSeed pkRoot message sig)).bindings "wotsPtr" =
      sigDataOffset + (1952 + 868) := by
  unfold c13BeforeWotsPkLightState
  unfold SegmentLayer3AddressCells.beforeWotsPkWotsPtrFrom
  rw [MemoryKit.lookupValue_bindValue_ne _ "i" "wotsPtr" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_self]
  have hSigBase : evalExpr []
      (SegmentLayer3.afterDigit
        (c13ResidualSecondLayerGuardState pkSeed pkRoot message sig))
      (.localVar "sigBase") = some sigDataOffset := by
    show some (lookupValue
      (SegmentLayer3.afterDigit
        (c13ResidualSecondLayerGuardState pkSeed pkRoot message sig)).bindings
      "sigBase") = _
    rw [SegmentLayer3.afterDigit_preserves_lookup_of_ne
      (c13ResidualSecondLayerGuardState pkSeed pkRoot message sig) "sigBase"
      (by decide) (by decide)]
    rw [SegmentLayer3.beforeDigitLoop_preserves_sigBase]
    rw [c13ResidualSecondLayerGuardState_sigBase]
  have hSigOff : evalExpr []
      (SegmentLayer3.afterDigit
        (c13ResidualSecondLayerGuardState pkSeed pkRoot message sig))
      (.localVar "sigOff") = some 2820 := by
    show some (lookupValue
      (SegmentLayer3.afterDigit
        (c13ResidualSecondLayerGuardState pkSeed pkRoot message sig)).bindings
      "sigOff") = _
    rw [SegmentLayer3.afterDigit_preserves_lookup_of_ne
      (c13ResidualSecondLayerGuardState pkSeed pkRoot message sig) "sigOff"
      (by decide) (by decide)]
    rw [c13_beforeDigitLoop_preserves_sigOff]
    rw [c13ResidualSecondLayerGuardState_sigOff]
  rw [SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_add_bounded
    _ _ _ _ _ hSigBase hSigOff
    (by decide) (by decide) (by decide)]
  rfl

set_option maxHeartbeats 2000000 in
theorem c13_layer1_light_cd1 (pkSeed pkRoot message sig : Bytes) :
    (c13BeforeWotsPkLightState
        (c13ResidualSecondLayerGuardState pkSeed pkRoot message sig)).world.calldata =
      headWords pkSeed pkRoot message sig.size ++ bytesToWords sig := by
  unfold c13BeforeWotsPkLightState
  unfold SegmentLayer3AddressCells.beforeWotsPkWotsPtrFrom
  rw [(SegmentLayer3.afterDigit_preserves_selector_calldata
    (c13ResidualSecondLayerGuardState pkSeed pkRoot message sig)).2]
  exact c13ResidualSecondLayerGuardState_calldata pkSeed pkRoot message sig

end SphincsMinusVerifiers
