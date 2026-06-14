import SphincsMinusVerifiers.C13ResidualLayer0Facts

namespace SphincsMinusVerifiers

open SphincsMinusVerifierSpec
open Compiler.Proofs.IRGeneration.SourceSemantics

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
          (c13ResidualLayer0GuardState pkSeed pkRoot message sig)).bindings "d" =
      C13Concrete.wotsDigest (C13Concrete.wordOfHash16 pkSeed)
        0
        ((C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048)
        ((C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex % 2048)
        lsig.wots.count (C13Concrete.wordOfHash16 forsPk) := by
  unfold c13BeforeWotsPkLightState
  unfold SegmentLayer3AddressCells.beforeWotsPkWotsPtrFrom
  rw [MemoryKit.lookupValue_bindValue_ne _ "i" "d" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "wotsPtr" "d" _ (by decide)]
  rw [SegmentLayer3.afterDigit_preserves_lookup_of_ne
    (c13ResidualLayer0GuardState pkSeed pkRoot message sig) "d"
    (by decide) (by decide)]
  exact SegmentLayer3.beforeDigitLoop_d_eq_wotsDigest_of_scratch
    (c13ResidualLayer0GuardState pkSeed pkRoot message sig)
    (C13Concrete.wordOfHash16 pkSeed) 0
    ((C13Concrete.c13PrimitivesConcrete.hMsg c13
      { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048)
    ((C13Concrete.c13PrimitivesConcrete.hMsg c13
      { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex % 2048)
    lsig.wots.count
    (C13Concrete.wordOfHash16 forsPk)
    (c13ResidualLayer0BeforeDigest_seed_slot pkSeed pkRoot message sig)
    (c13ResidualLayer0BeforeDigest_wotsAdrs_slot_hyperIndex
      pkSeed pkRoot message sig sigParsed hParse)
    (c13ResidualLayer0BeforeDigest_currentNode_slot
      pkSeed pkRoot message sig forsPk
      (c13Residual_afterFinalize_forsPk_of_parse_fors
        pkSeed pkRoot message sig sigParsed forsPk hParse hFors))
    (c13ResidualLayer0BeforeDigest_count_slot_hyperIndex
      pkSeed pkRoot message sig sigParsed lsig hParse hLayer0)

end SphincsMinusVerifiers
