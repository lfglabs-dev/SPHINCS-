import SphincsMinusVerifiers.C13ResidualLayer0Facts
import SphincsMinusVerifiers.C13ResidualLayer0BeforeDigitSigOff

namespace SphincsMinusVerifiers

open SphincsMinusVerifierSpec
open Compiler.Proofs.IRGeneration.SourceSemantics
open SphincsMinusVerifiers.MkC13State

set_option maxHeartbeats 2000000 in
theorem c13_layer0_light_wptr0 (pkSeed pkRoot message sig : Bytes) :
    lookupValue
        (c13BeforeWotsPkLightState
          (c13ResidualLayer0GuardState pkSeed pkRoot message sig)).bindings "wotsPtr" =
      sigDataOffset + 1952 := by
  unfold c13BeforeWotsPkLightState
  unfold SegmentLayer3AddressCells.beforeWotsPkWotsPtrFrom
  rw [MemoryKit.lookupValue_bindValue_ne _ "i" "wotsPtr" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_self]
  have hSigBase : evalExpr []
      (SegmentLayer3.afterDigit
        (c13ResidualLayer0GuardState pkSeed pkRoot message sig))
      (.localVar "sigBase") = some sigDataOffset := by
    show some (lookupValue
      (SegmentLayer3.afterDigit
        (c13ResidualLayer0GuardState pkSeed pkRoot message sig)).bindings
      "sigBase") = _
    rw [SegmentLayer3.afterDigit_preserves_lookup_of_ne
      (c13ResidualLayer0GuardState pkSeed pkRoot message sig) "sigBase"
      (by decide) (by decide)]
    rw [SegmentLayer3.beforeDigitLoop_preserves_sigBase]
    rw [c13ResidualLayer0GuardState_sigBase]
  have hSigOff : evalExpr []
      (SegmentLayer3.afterDigit
        (c13ResidualLayer0GuardState pkSeed pkRoot message sig))
      (.localVar "sigOff") = some 1952 := by
    show some (lookupValue
      (SegmentLayer3.afterDigit
        (c13ResidualLayer0GuardState pkSeed pkRoot message sig)).bindings
      "sigOff") = _
    rw [SegmentLayer3.afterDigit_preserves_lookup_of_ne
      (c13ResidualLayer0GuardState pkSeed pkRoot message sig) "sigOff"
      (by decide) (by decide)]
    rw [c13_beforeDigitLoop_preserves_sigOff]
    rw [c13ResidualLayer0GuardState_sigOff]
    rw [SegmentS2.wordNormalize_of_lt (by decide : 1952 < 2 ^ 256)]
  rw [SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_add_bounded
    _ _ _ _ _ hSigBase hSigOff
    (by decide) (by decide) (by decide)]
  rfl

end SphincsMinusVerifiers
