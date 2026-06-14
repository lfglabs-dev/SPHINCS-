import SphincsMinusVerifiers.SegmentLayer3
import SphincsMinusVerifiers.SegmentLayer3AddressCells

namespace SphincsMinusVerifiers

open Compiler.Proofs.IRGeneration.SourceSemantics

/-- Lightweight C13 WOTS-outer entry state used by the residual assembly
bridges.  It is the post-digit state with only the WOTS pointer and loop index
bindings installed, before running the WOTS-outer fold. -/
def c13BeforeWotsPkLightState (ls : RuntimeState) : RuntimeState :=
  { SegmentLayer3AddressCells.beforeWotsPkWotsPtrFrom
      (SegmentLayer3.afterDigit ls) with
    bindings :=
      bindValue
        (SegmentLayer3AddressCells.beforeWotsPkWotsPtrFrom
          (SegmentLayer3.afterDigit ls)).bindings
        "i" (wordNormalize 0) }

end SphincsMinusVerifiers
