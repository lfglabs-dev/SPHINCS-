import SphincsMinusVerifiers.C13ResidualLayer0Facts

namespace SphincsMinusVerifiers

open SphincsMinusVerifierSpec
open Compiler.Proofs.IRGeneration.SourceSemantics

set_option maxHeartbeats 2000000 in
theorem c13_layer0_light_seed0 (pkSeed pkRoot message sig : Bytes) :
    ((c13BeforeWotsPkLightState
        (c13ResidualLayer0GuardState pkSeed pkRoot message sig)).world.memory 0x00).val =
  C13Concrete.wordOfHash16 pkSeed := by
  unfold c13BeforeWotsPkLightState
  unfold SegmentLayer3AddressCells.beforeWotsPkWotsPtrFrom
  rw [SegmentLayer3.afterDigit_preserves_memory_zero]
  exact c13ResidualLayer0GuardState_seed_slot pkSeed pkRoot message sig

end SphincsMinusVerifiers
