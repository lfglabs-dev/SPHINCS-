import SphincsMinusVerifiers.C13ResidualLayer0Facts
import SphincsMinusVerifiers.C13ResidualLayer0BeforeDigitLookup

namespace SphincsMinusVerifiers

open SphincsMinusVerifierSpec
open Compiler.Proofs.IRGeneration.SourceSemantics

set_option maxHeartbeats 2000000 in
theorem c13_layer0_light_adrs0 (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed) :
    lookupValue
        (c13BeforeWotsPkLightState
          (c13ResidualLayer0GuardState pkSeed pkRoot message sig)).bindings "wotsAdrs" =
      C13Concrete.adrsWotsHashBase 0
        ((C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048)
        ((C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex % 2048) := by
  unfold c13BeforeWotsPkLightState
  unfold SegmentLayer3AddressCells.beforeWotsPkWotsPtrFrom
  rw [MemoryKit.lookupValue_bindValue_ne _ "i" "wotsAdrs" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "wotsPtr" "wotsAdrs" _ (by decide)]
  rw [SegmentLayer3.afterDigit_preserves_lookup_of_ne
    (c13ResidualLayer0GuardState pkSeed pkRoot message sig) "wotsAdrs"
    (by decide) (by decide)]
  rw [c13_beforeDigitLoop_lookup_eq_beforeDigest_of_ne
    (c13ResidualLayer0GuardState pkSeed pkRoot message sig) "wotsAdrs"
    (by decide) (by decide)]
  exact c13ResidualLayer0BeforeDigest_wotsAdrs_hyperIndex
    pkSeed pkRoot message sig sigParsed hParse

end SphincsMinusVerifiers
