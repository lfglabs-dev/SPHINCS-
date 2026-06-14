import SphincsMinusVerifiers.C13ResidualLayer0Facts

namespace SphincsMinusVerifiers

open SphincsMinusVerifierSpec
open Compiler.Proofs.IRGeneration.SourceSemantics
open SphincsMinusVerifiers.MkC13State

set_option maxHeartbeats 2000000 in
theorem c13_layer0_light_cd0 (pkSeed pkRoot message sig : Bytes) :
    (c13BeforeWotsPkLightState
        (c13ResidualLayer0GuardState pkSeed pkRoot message sig)).world.calldata =
      headWords pkSeed pkRoot message sig.size ++ bytesToWords sig := by
  unfold c13BeforeWotsPkLightState
  unfold SegmentLayer3AddressCells.beforeWotsPkWotsPtrFrom
  rw [(SegmentLayer3.afterDigit_preserves_selector_calldata
    (c13ResidualLayer0GuardState pkSeed pkRoot message sig)).2]
  exact c13ResidualLayer0GuardState_calldata pkSeed pkRoot message sig

end SphincsMinusVerifiers
