import SphincsMinusVerifiers.C13ResidualLayer1StateBase

namespace SphincsMinusVerifiers

open SphincsMinusVerifierSpec

theorem c13ResidualSecondLayerBeforeDigest_seed_slot_of_first_step_seed_slot
    (pkSeed pkRoot message sig : Bytes)
    (hStepSeed :
      ((SegmentLayer3.stepLayer
        (c13ResidualFirstLayerGuardState pkSeed pkRoot message sig)).world.memory 0x00).val =
        C13Concrete.wordOfHash16 pkSeed) :
    ((SegmentLayer3.beforeDigest
        (c13ResidualSecondLayerGuardState pkSeed pkRoot message sig)).world.memory 0x00).val =
      C13Concrete.wordOfHash16 pkSeed := by
  rw [SegmentLayer3.beforeDigest_preserves_memory_zero]
  unfold c13ResidualSecondLayerGuardState
  rw [ClimbLoopGuarded.loopState_preserves_memory_val]
  exact hStepSeed

end SphincsMinusVerifiers
