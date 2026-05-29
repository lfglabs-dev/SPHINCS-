/-
  Refinement hooks from the Verity models to the SPHINCS- verifier specs.

  Theorem statements target the byte-level contract spec first. Each modeled
  Solidity verifier exposes an observable `exec...` relation where `none` means
  revert and `some b` means normal boolean return. The byte-level spec handles
  public-key bytes and signature-byte parsing, then delegates to the parsed
  algorithmic verifier in `verifyParsed`.
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
  Bytes → Bytes → Bytes → Bytes → Option Bool

/-- Placeholder observable semantics for the compiled C12 Verity model. -/
opaque execC12 :
  Bytes → Bytes → Bytes → Bytes → Option Bool

/-- Placeholder observable semantics for the compiled SHA2 SLH-DSA model. -/
opaque execSlhDsaSha2_128_24 :
  Bytes → Bytes → Bytes → Bytes → Option Bool

theorem c13_refines_byte_spec
    : SphincsMinusVerifierSpec.ByteLevel.ImplementsByteVerifier c13Primitives c13 execC13 := by
  sorry

theorem c12_refines_byte_spec
    : SphincsMinusVerifierSpec.ByteLevel.ImplementsByteVerifier c12Primitives c12 execC12 := by
  sorry

theorem slhDsaSha2_128_24_refines_byte_spec
    : SphincsMinusVerifierSpec.ByteLevel.ImplementsByteVerifier
        slhDsaSha2_128_24_Primitives slhDsaSha2_128_24 execSlhDsaSha2_128_24 := by
  sorry

theorem c13_refines_spec
    : ∀ pkSeed pkRoot message sig,
        execC13 pkSeed pkRoot message sig =
          verifySpec c13Primitives c13
            { pkSeed := pkSeed, pkRoot := pkRoot } message sig := by
  intro pkSeed pkRoot message sig
  rw [c13_refines_byte_spec]
  exact SphincsMinusVerifierSpec.ByteLevel.verifyBytes_eq_verifySpec
    c13Primitives c13 pkSeed pkRoot message sig

theorem c12_refines_spec
    : ∀ pkSeed pkRoot message sig,
        execC12 pkSeed pkRoot message sig =
          verifySpec c12Primitives c12
            { pkSeed := pkSeed, pkRoot := pkRoot } message sig := by
  intro pkSeed pkRoot message sig
  rw [c12_refines_byte_spec]
  exact SphincsMinusVerifierSpec.ByteLevel.verifyBytes_eq_verifySpec
    c12Primitives c12 pkSeed pkRoot message sig

theorem slhDsaSha2_128_24_refines_spec
    : ∀ pkSeed pkRoot message sig,
        execSlhDsaSha2_128_24 pkSeed pkRoot message sig =
          verifySpec slhDsaSha2_128_24_Primitives slhDsaSha2_128_24
            { pkSeed := pkSeed, pkRoot := pkRoot } message sig := by
  intro pkSeed pkRoot message sig
  rw [slhDsaSha2_128_24_refines_byte_spec]
  exact SphincsMinusVerifierSpec.ByteLevel.verifyBytes_eq_verifySpec
    slhDsaSha2_128_24_Primitives slhDsaSha2_128_24 pkSeed pkRoot message sig

/--
Compilation-model presence checks.  These are small regression anchors: if the
models are renamed or removed, the refinement file stops compiling before any
semantic proof attempt starts.
-/
example : c13Model.name = "SphincsC13Asm_VerityModel" := rfl
example : c12Model.name = "SPHINCs_C12Asm_VerityModel" := rfl
example : slhDsaSha2_128_24_Model.name = "SLH_DSA_SHA2_128_24_VerityModel" := rfl

end SphincsMinusVerifiers
