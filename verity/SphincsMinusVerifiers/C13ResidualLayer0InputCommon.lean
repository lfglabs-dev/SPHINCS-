import SphincsMinusVerifiers.C13ResidualInterface

namespace SphincsMinusVerifiers

open Compiler.Proofs.IRGeneration.SourceSemantics

theorem c13_light_world (ls : RuntimeState) :
    (c13BeforeWotsPkLightState ls).world = (SegmentLayer3.afterDigit ls).world := rfl

theorem c13_light_bindings (ls : RuntimeState) :
    (c13BeforeWotsPkLightState ls).bindings =
      bindValue
        (bindValue (SegmentLayer3.afterDigit ls).bindings "wotsPtr"
          ((evalExpr [] (SegmentLayer3.afterDigit ls)
            (.add (.localVar "sigBase") (.localVar "sigOff"))).getD 0))
        "i" (wordNormalize 0) := rfl

end SphincsMinusVerifiers
