import SphincsMinusVerifiers.C13ResidualLayer1ScalarFacts
import SphincsMinusVerifiers.SegmentLayer3MerkleFrame

namespace SphincsMinusVerifiers

open SphincsMinusVerifierSpec
open Compiler.Proofs.IRGeneration.SourceSemantics
open SphincsMinusVerifiers.MkC13State

theorem c13ResidualFirstLayerBeforeMerkle_mIdx_hyperIndex
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed) :
    let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
    let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
    lookupValue
        (SegmentLayer3.beforeMerkle
          (c13ResidualFirstLayerGuardState pkSeed pkRoot message sig)).bindings
        "mIdx" = digest.hyperIndex % 2048 := by
  intro pk digest
  exact SegmentLayer3.beforeMerkle_mIdx_eq_of_idxTree
    (c13ResidualFirstLayerGuardState pkSeed pkRoot message sig)
    digest.hyperIndex
    (c13ResidualLayer0GuardState_idxTree_hyperIndex
      pkSeed pkRoot message sig hParse)
    (lt_trans
      (C13Concrete.hMsgC13_hyperIndex_lt pk sigParsed.R message)
      (by decide : 2 ^ 22 < 2 ^ 256))

theorem c13ResidualFirstLayerBeforeMerkle_layerFrozenSite
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed) :
    SegmentLayer3MerkleFrame.LayerFrozenSite 0 pkSeed pkRoot message sig
      (SegmentLayer3.beforeMerkle
        (c13ResidualFirstLayerGuardState pkSeed pkRoot message sig)) := by
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  let treeAdrs : Nat := C13Concrete.adrsXmssTree 0 (digest.hyperIndex / 2048)
  refine ⟨treeAdrs, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact
      (SegmentLayer3.beforeMerkle_preserves_selector_calldata
        (c13ResidualFirstLayerGuardState pkSeed pkRoot message sig)).1.trans
        (c13ResidualLayer0GuardState_selector pkSeed pkRoot message sig)
  · exact
      (SegmentLayer3.beforeMerkle_preserves_selector_calldata
        (c13ResidualFirstLayerGuardState pkSeed pkRoot message sig)).2.trans
        (c13ResidualLayer0GuardState_calldata pkSeed pkRoot message sig)
  · have hSigOffRaw :
        lookupValue (c13ResidualFirstLayerGuardState pkSeed pkRoot message sig).bindings
            "sigOff" = 1952 := by
      rw [c13ResidualLayer0GuardState_sigOff]
      exact SegmentS2.wordNormalize_of_lt (by decide : 1952 < 2 ^ 256)
    have hPtr :=
      SegmentLayer3.beforeMerkle_merklePtr_eq_of_sigBase_sigOff
        (c13ResidualFirstLayerGuardState pkSeed pkRoot message sig)
        sigDataOffset 1952
        (c13ResidualLayer0GuardState_sigBase pkSeed pkRoot message sig)
        hSigOffRaw
        (by decide : sigDataOffset < 2 ^ 256)
        (by decide : 1952 < 2 ^ 256)
        (by decide : 1952 + 688 < 2 ^ 256)
        (by decide : 1952 + 692 < 2 ^ 256)
        (by decide : sigDataOffset + (1952 + 692) < 2 ^ 256)
    simpa using hPtr
  · dsimp [treeAdrs]
    exact SegmentLayer3.beforeMerkle_treeAdrs_eq_of_layer_idxTree
      (c13ResidualFirstLayerGuardState pkSeed pkRoot message sig)
      0 digest.hyperIndex
      (c13ResidualLayer0GuardState_layer pkSeed pkRoot message sig)
      (c13ResidualLayer0GuardState_idxTree_hyperIndex
        pkSeed pkRoot message sig hParse)
      (by decide : 0 < 2 ^ 32)
      (C13Concrete.hMsgC13_hyperIndex_lt pk sigParsed.R message)
  · dsimp [treeAdrs]
    exact c13Residual_adrsXmssTree_lt_of_bounds 0 (digest.hyperIndex / 2048)
      (by decide : 0 < 2 ^ 32)
      (lt_of_le_of_lt (Nat.div_le_self _ _)
        (C13Concrete.hMsgC13_hyperIndex_lt pk sigParsed.R message))
  · rw [c13ResidualFirstLayerBeforeMerkle_mIdx_hyperIndex
      pkSeed pkRoot message sig sigParsed hParse]
    exact lt_trans (Nat.mod_lt _ (by decide : 0 < 2048))
      (by decide : 2048 < 2 ^ 256)

end SphincsMinusVerifiers
