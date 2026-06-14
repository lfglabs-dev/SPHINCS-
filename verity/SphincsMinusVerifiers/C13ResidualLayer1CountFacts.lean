import SphincsMinusVerifiers.C13ResidualLayer1StateFacts

namespace SphincsMinusVerifiers

open SphincsMinusVerifierSpec
open Compiler.Proofs.IRGeneration.SourceSemantics
open SphincsMinusVerifiers.MkC13State

theorem c13ResidualSecondLayerBeforeDigest_count_hyperIndex
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature)
    (lsig : XmssLayerSig)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hLayer1 : sigParsed.layers[1]? = some lsig) :
    lookupValue
        (SegmentLayer3.beforeDigest
          (c13ResidualSecondLayerGuardState pkSeed pkRoot message sig)).bindings
        "count" = lsig.wots.count := by
  have hRaw :=
    SegmentLayer3.beforeDigest_count_eq_of_sigBase_sigOff_calldata
      (c13ResidualSecondLayerGuardState pkSeed pkRoot message sig)
      sigDataOffset 2820
      (headWords pkSeed pkRoot message sig.size ++ bytesToWords sig)
      (c13ResidualSecondLayerGuardState_sigBase pkSeed pkRoot message sig)
      (c13ResidualSecondLayerGuardState_sigOff pkSeed pkRoot message sig)
      (c13ResidualSecondLayerGuardState_selector pkSeed pkRoot message sig)
      (c13ResidualSecondLayerGuardState_calldata pkSeed pkRoot message sig)
      (by decide : sigDataOffset < 2 ^ 256)
      (by decide : 2820 < 2 ^ 256)
      (by decide : 2820 + 688 < 2 ^ 256)
      (by decide :
        sigDataOffset + (2820 + 688) < 2 ^ 256)
  rw [SphincsMinusVerifiers.SiblingCalldata.shr224_calldata_eq_readBE4
      pkSeed pkRoot message sig (2820 + 688)] at hRaw
  have hCountSpec :=
    C13Concrete.parseSignatureC13_layer_wots_count
      hParse (by decide : 1 < 2) hLayer1
  rw [hCountSpec]
  rw [show 1952 + 868 * 1 + 688 = 2820 + 688 by decide]
  rw [← SphincsMinusVerifiers.SiblingCalldata.readBE4_eq_fold sig (2820 + 688)]
  exact hRaw

theorem c13ResidualSecondLayer_wotsCount_norm
    (sig : Bytes) (sigParsed : Signature) (lsig : XmssLayerSig)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hLayer1 : sigParsed.layers[1]? = some lsig) :
    wordNormalize lsig.wots.count = lsig.wots.count := by
  have hCountSpec :=
    C13Concrete.parseSignatureC13_layer_wots_count
      hParse (by decide : 1 < 2) hLayer1
  rw [hCountSpec]
  rw [show 1952 + 868 * 1 + 688 = 3508 by decide]
  rw [← SphincsMinusVerifiers.SiblingCalldata.readBE4_eq_fold sig 3508]
  exact SegmentS2.wordNormalize_of_lt
    (lt_trans
      (SphincsMinusVerifiers.SiblingCalldata.readBE_lt sig 3508 4)
      (by decide : 256 ^ 4 < 2 ^ 256))

theorem c13ResidualSecondLayerBeforeDigest_count_slot_hyperIndex
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature)
    (lsig : XmssLayerSig)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hLayer1 : sigParsed.layers[1]? = some lsig) :
    ((SegmentLayer3.beforeDigest
        (c13ResidualSecondLayerGuardState pkSeed pkRoot message sig)).world.memory 0x60).val =
      lsig.wots.count := by
  rw [SegmentLayer3.beforeDigest_memory_0x60_eq_of_count
    (c13ResidualSecondLayerGuardState pkSeed pkRoot message sig) lsig.wots.count
    (c13ResidualSecondLayerBeforeDigest_count_hyperIndex
      pkSeed pkRoot message sig sigParsed lsig hParse hLayer1)]
  exact c13ResidualSecondLayer_wotsCount_norm sig sigParsed lsig hParse hLayer1

end SphincsMinusVerifiers
