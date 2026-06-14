import SphincsMinusVerifiers.C13ResidualLayer1StateBase

namespace SphincsMinusVerifiers

open SphincsMinusVerifierSpec
open Compiler.Proofs.IRGeneration.SourceSemantics
open SphincsMinusVerifiers.MkC13State

theorem c13ResidualSecondLayerGuardState_sigBase
    (pkSeed pkRoot message sig : Bytes) :
    lookupValue (c13ResidualSecondLayerGuardState pkSeed pkRoot message sig).bindings
        "sigBase" = sigDataOffset := by
  unfold c13ResidualSecondLayerGuardState ClimbLoopGuarded.loopState
  rw [MemoryKit.lookupValue_bindValue_ne _ "layer" "sigBase" _ (by decide)]
  rw [SegmentLayer3.stepLayer_sigBase_eq]
  exact c13ResidualLayer0GuardState_sigBase pkSeed pkRoot message sig

theorem c13ResidualSecondLayerGuardState_sigOff
    (pkSeed pkRoot message sig : Bytes) :
    lookupValue (c13ResidualSecondLayerGuardState pkSeed pkRoot message sig).bindings
        "sigOff" = 2820 := by
  unfold c13ResidualSecondLayerGuardState ClimbLoopGuarded.loopState
  rw [MemoryKit.lookupValue_bindValue_ne _ "layer" "sigOff" _ (by decide)]
  have hSigOffRaw :
      lookupValue (c13ResidualFirstLayerGuardState pkSeed pkRoot message sig).bindings
          "sigOff" = 1952 := by
    rw [c13ResidualLayer0GuardState_sigOff]
    exact SegmentS2.wordNormalize_of_lt (by decide : 1952 < 2 ^ 256)
  exact SegmentLayer3.stepLayer_sigOff_eq_of_sigOff
    (c13ResidualFirstLayerGuardState pkSeed pkRoot message sig)
    1952 hSigOffRaw
    (by decide : 1952 < 2 ^ 256)
    (by decide : 1952 + 688 < 2 ^ 256)
    (by decide : 1952 + 692 < 2 ^ 256)
    (by decide : 1952 + 868 < 2 ^ 256)

theorem c13ResidualSecondLayerGuardState_layer
    (pkSeed pkRoot message sig : Bytes) :
    lookupValue (c13ResidualSecondLayerGuardState pkSeed pkRoot message sig).bindings
        "layer" = 1 := by
  unfold c13ResidualSecondLayerGuardState ClimbLoopGuarded.loopState
  rw [MemoryKit.lookupValue_bindValue_self]
  exact SegmentS2.wordNormalize_of_lt (by decide : 1 < 2 ^ 256)

theorem c13ResidualSecondLayerGuardState_selector
    (pkSeed pkRoot message sig : Bytes) :
    (c13ResidualSecondLayerGuardState pkSeed pkRoot message sig).selector = 0 := by
  unfold c13ResidualSecondLayerGuardState ClimbLoopGuarded.loopState
  have hFrame :=
    SegmentLayer3.stepLayer_preserves_selector_calldata
      (c13ResidualFirstLayerGuardState pkSeed pkRoot message sig)
  rw [hFrame.1]
  exact c13ResidualLayer0GuardState_selector pkSeed pkRoot message sig

theorem c13ResidualSecondLayerGuardState_calldata
    (pkSeed pkRoot message sig : Bytes) :
    (c13ResidualSecondLayerGuardState pkSeed pkRoot message sig).world.calldata =
      headWords pkSeed pkRoot message sig.size ++ bytesToWords sig := by
  unfold c13ResidualSecondLayerGuardState ClimbLoopGuarded.loopState
  have hFrame :=
    SegmentLayer3.stepLayer_preserves_selector_calldata
      (c13ResidualFirstLayerGuardState pkSeed pkRoot message sig)
  rw [hFrame.2]
  exact c13ResidualLayer0GuardState_calldata pkSeed pkRoot message sig

theorem c13ResidualSecondLayerGuardState_idxTree_hyperIndex
    (pkSeed pkRoot message sig : Bytes) {sigParsed : Signature}
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed) :
    let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
    let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
    lookupValue (c13ResidualSecondLayerGuardState pkSeed pkRoot message sig).bindings
        "idxTree" = digest.hyperIndex / 2048 := by
  intro pk digest
  unfold c13ResidualSecondLayerGuardState ClimbLoopGuarded.loopState
  rw [MemoryKit.lookupValue_bindValue_ne _ "layer" "idxTree" _ (by decide)]
  exact SegmentLayer3.stepLayer_idxTree_eq_of_idxTree
    (c13ResidualFirstLayerGuardState pkSeed pkRoot message sig)
    digest.hyperIndex
    (c13ResidualLayer0GuardState_idxTree_hyperIndex
      pkSeed pkRoot message sig hParse)
    (lt_trans
      (C13Concrete.hMsgC13_hyperIndex_lt pk sigParsed.R message)
      (by decide : 2 ^ 22 < 2 ^ 256))

end SphincsMinusVerifiers
