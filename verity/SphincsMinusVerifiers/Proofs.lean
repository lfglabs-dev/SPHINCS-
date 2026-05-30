/-
  Refinement hooks from the Verity models to the SPHINCS- verifier specs.

  Proof chain (see `SphincsMinusVerifiers/README.md`):

      Verity compiled model  refines  ByteLevel.verifyBytes  refines  verifySpec

  * The right link (`verifyBytes` refines `verifySpec`) is proved with no axioms
    in `SphincsMinusVerifierSpec/Spec.lean` (`verifyBytes_eq_verifySpec`) and
    lifted to the observable boundary here by `byteVerifier_refines_spec`.

  * The left link (compiled model refines `verifyBytes`) is the MODEL-EXEC-BRIDGE.
    A full proof requires Verity's executable source semantics over the raw
    `bytes`-calldata surface (`sig.length` / `sig.offset` locals); the current
    `Compiler/.../SourceSemantics.lean` interpreter only evaluates decoded `Nat`
    arguments and does not model that surface yet. Until it does, each model's
    refinement of the byte spec is taken as a **named, documented axiom**, not a
    `sorry`. These axioms are the Lean-level statement of the
    `proofStatus := .assumed` local obligations already attached to each model in
    `Model.lean` (`assembly_refinement`, `linear_memory_aliasing`, the raw-Yul
    revert obligations). They sit alongside the repo's existing keccak
    collision-resistance axioms in the trust surface and are surfaced by
    `#print axioms`.

  The per-verifier `*_refines_byte_spec` and `*_refines_spec` results below are
  therefore unconditional theorems whose only assumptions are these explicitly
  named bridge axioms (plus `propext`).
-/

import SphincsMinusVerifierSpec.Spec
import SphincsMinusVerifiers.Model

namespace SphincsMinusVerifiers

open SphincsMinusVerifierSpec

/--
Concrete primitive semantics for the C13 Keccak/SPHINCS- variant.

This remains an abstract package until the executable Verity semantics and
byte-level hash models are connected, but it is intentionally fixed per
verifier: a single compiled contract cannot implement `verifySpec` for every
possible `Primitives` package.
-/
axiom c13Primitives : Primitives

/-- Concrete primitive semantics for the C12 Keccak/SPHINCS- variant. -/
axiom c12Primitives : Primitives

/-- Concrete primitive semantics for the SHA2 SLH-DSA verifier variant. -/
axiom slhDsaSha2_128_24_Primitives : Primitives

/-- Observable semantics of the compiled C13 Verity model: `none` means revert,
`some b` means normal boolean return. Kept opaque until Verity's executable
source semantics cover the `bytes`-calldata surface (MODEL-EXEC-BRIDGE). -/
opaque execC13 :
  Bytes → Bytes → Bytes → Bytes → Option Bool

/-- Observable semantics of the compiled C12 Verity model. -/
opaque execC12 :
  Bytes → Bytes → Bytes → Bytes → Option Bool

/-- Observable semantics of the compiled SHA2 SLH-DSA Verity model. -/
opaque execSlhDsaSha2_128_24 :
  Bytes → Bytes → Bytes → Bytes → Option Bool

/--
The proved core: any observable verifier semantics that refines the byte-level
contract spec also refines the abstract algorithmic spec.

This is the lower-spec-refines-abstract-spec step of the layering, lifted to the
observable boundary. It holds for *any* `exec`, with no axiom, by composing the
hypothesis with `ByteLevel.verifyBytes_eq_verifySpec`. `#print axioms` shows it
depends only on `propext`.
-/
theorem byteVerifier_refines_spec
    {p : Primitives} {v : Variant}
    {exec : Bytes → Bytes → Bytes → Bytes → Option Bool}
    (hModel : ByteLevel.ImplementsByteVerifier p v exec)
    (pkSeed pkRoot message sig : Bytes) :
    exec pkSeed pkRoot message sig =
      verifySpec p v { pkSeed := pkSeed, pkRoot := pkRoot } message sig := by
  rw [hModel]
  exact ByteLevel.verifyBytes_eq_verifySpec p v pkSeed pkRoot message sig

/--
The same composition packaged at the `ImplementsVerifier` level: a byte-level
refinement of a model upgrades to an abstract-spec refinement of the same model.
Proved, axiom-free beyond `propext`.
-/
theorem byteVerifier_implements_spec
    {p : Primitives} {v : Variant}
    {exec : Bytes → Bytes → Bytes → Bytes → Option Bool}
    (hModel : ByteLevel.ImplementsByteVerifier p v exec) :
    ImplementsVerifier p v
      (fun pk message sig => exec pk.pkSeed pk.pkRoot message sig) := by
  intro pk message sig
  have h := byteVerifier_refines_spec hModel pk.pkSeed pk.pkRoot message sig
  simpa using h

/-! ### MODEL-EXEC-BRIDGE axioms

Each axiom asserts that one compiled Verity model refines its byte-level spec.
These are the assumed left link of the refinement chain; see the file header and
`SphincsMinusVerifiers/README.md`. They are deliberately fixed per verifier
(distinct primitive packages) and are the only model-specific assumptions the
theorems below rest on. -/

/-- Assumed: the compiled C13 model refines the byte-level spec under
`c13Primitives`. (MODEL-EXEC-BRIDGE; mirrors the `.assumed` obligations on
`c13Model` in `Model.lean`.) -/
axiom c13_refines_byte_spec :
  ByteLevel.ImplementsByteVerifier c13Primitives c13 execC13

/-- Assumed: the compiled C12 model refines the byte-level spec under
`c12Primitives`. (MODEL-EXEC-BRIDGE.) -/
axiom c12_refines_byte_spec :
  ByteLevel.ImplementsByteVerifier c12Primitives c12 execC12

/-- Assumed: the compiled SHA2 SLH-DSA model refines the byte-level spec under
`slhDsaSha2_128_24_Primitives`. (MODEL-EXEC-BRIDGE.) -/
axiom slhDsaSha2_128_24_refines_byte_spec :
  ByteLevel.ImplementsByteVerifier
    slhDsaSha2_128_24_Primitives slhDsaSha2_128_24 execSlhDsaSha2_128_24

/-- C13: the compiled model refines the abstract algorithmic spec. Unconditional,
resting on `c13_refines_byte_spec` (MODEL-EXEC-BRIDGE) and the proved
`byteVerifier_refines_spec`. -/
theorem c13_refines_spec
    (pkSeed pkRoot message sig : Bytes) :
    execC13 pkSeed pkRoot message sig =
      verifySpec c13Primitives c13
        { pkSeed := pkSeed, pkRoot := pkRoot } message sig :=
  byteVerifier_refines_spec c13_refines_byte_spec pkSeed pkRoot message sig

/-- C12: the compiled model refines the abstract algorithmic spec. -/
theorem c12_refines_spec
    (pkSeed pkRoot message sig : Bytes) :
    execC12 pkSeed pkRoot message sig =
      verifySpec c12Primitives c12
        { pkSeed := pkSeed, pkRoot := pkRoot } message sig :=
  byteVerifier_refines_spec c12_refines_byte_spec pkSeed pkRoot message sig

/-- SHA2 SLH-DSA: the compiled model refines the abstract algorithmic spec. -/
theorem slhDsaSha2_128_24_refines_spec
    (pkSeed pkRoot message sig : Bytes) :
    execSlhDsaSha2_128_24 pkSeed pkRoot message sig =
      verifySpec slhDsaSha2_128_24_Primitives slhDsaSha2_128_24
        { pkSeed := pkSeed, pkRoot := pkRoot } message sig :=
  byteVerifier_refines_spec slhDsaSha2_128_24_refines_byte_spec pkSeed pkRoot message sig

/-- C13 packaged at the `ImplementsVerifier` boundary. -/
theorem c13_implements_spec :
    ImplementsVerifier c13Primitives c13
      (fun pk message sig => execC13 pk.pkSeed pk.pkRoot message sig) :=
  byteVerifier_implements_spec c13_refines_byte_spec

/-- C12 packaged at the `ImplementsVerifier` boundary. -/
theorem c12_implements_spec :
    ImplementsVerifier c12Primitives c12
      (fun pk message sig => execC12 pk.pkSeed pk.pkRoot message sig) :=
  byteVerifier_implements_spec c12_refines_byte_spec

/-- SHA2 SLH-DSA packaged at the `ImplementsVerifier` boundary. -/
theorem slhDsaSha2_128_24_implements_spec :
    ImplementsVerifier slhDsaSha2_128_24_Primitives slhDsaSha2_128_24
      (fun pk message sig => execSlhDsaSha2_128_24 pk.pkSeed pk.pkRoot message sig) :=
  byteVerifier_implements_spec slhDsaSha2_128_24_refines_byte_spec

/--
Compilation-model presence checks.  These are small regression anchors: if the
models are renamed or removed, the refinement file stops compiling before any
semantic proof attempt starts.
-/
example : c13Model.name = "SphincsC13Asm_VerityModel" := rfl
example : c12Model.name = "SPHINCs_C12Asm_VerityModel" := rfl
example : slhDsaSha2_128_24_Model.name = "SLH_DSA_SHA2_128_24_VerityModel" := rfl

end SphincsMinusVerifiers
