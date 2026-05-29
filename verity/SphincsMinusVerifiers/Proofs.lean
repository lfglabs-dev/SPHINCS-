/-
  Refinement hooks from the Verity models to the abstract SPHINCS- verifier
  specifications.

  The theorem statements are intentionally shaped for future Verity/ECM proofs:
  each modeled Solidity verifier exposes an observable `exec...` relation where
  `none` means revert and `some b` means normal boolean return.  The final proof
  obligation is exactly `ImplementsVerifier`.
-/

import SphincsMinusVerifierSpec.Spec
import SphincsMinusVerifiers.Model

namespace SphincsMinusVerifiers

open SphincsMinusVerifierSpec

/--
Concrete primitive semantics for the C13 Keccak/SPHINCS- variant.

This remains opaque until the executable Verity semantics and byte-level hash
models are connected, but it is intentionally fixed per verifier.  A single
compiled contract cannot implement `verifySpec` for every possible
`Primitives` package.
-/
axiom c13Primitives : Primitives

/-- Concrete primitive semantics for the C12 Keccak/SPHINCS- variant. -/
axiom c12Primitives : Primitives

/-- Concrete primitive semantics for the SHA2 SLH-DSA verifier variant. -/
axiom slhDsaSha2_128_24_Primitives : Primitives

/-- Placeholder observable semantics for the compiled C13 Verity model.
Future work should instantiate this with Verity's executable semantics for
`c13Model` after the line-by-line model is complete and compiled. -/
opaque execC13 :
  PublicKey → Bytes → Bytes → Option Bool

/-- Placeholder observable semantics for the compiled C12 Verity model. -/
opaque execC12 :
  PublicKey → Bytes → Bytes → Option Bool

/-- Placeholder observable semantics for the compiled SHA2 SLH-DSA model. -/
opaque execSlhDsaSha2_128_24 :
  PublicKey → Bytes → Bytes → Option Bool

theorem c13_refines_spec
    : ImplementsVerifier c13Primitives c13 execC13 := by
  sorry

theorem c12_refines_spec
    : ImplementsVerifier c12Primitives c12 execC12 := by
  sorry

theorem slhDsaSha2_128_24_refines_spec
    : ImplementsVerifier slhDsaSha2_128_24_Primitives slhDsaSha2_128_24 execSlhDsaSha2_128_24 := by
  sorry

/--
Compilation-model presence checks.  These are small regression anchors: if the
models are renamed or removed, the refinement file stops compiling before any
semantic proof attempt starts.
-/
example : c13Model.name = "SphincsC13Asm_VerityModel" := rfl
example : c12Model.name = "SPHINCs_C12Asm_VerityModel" := rfl
example : slhDsaSha2_128_24_Model.name = "SLH_DSA_SHA2_128_24_VerityModel" := rfl

end SphincsMinusVerifiers
