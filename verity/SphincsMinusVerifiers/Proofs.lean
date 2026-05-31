/-
  Refinement hooks from the Verity models to the SPHINCS- verifier specs.

  Proof chain (see `SphincsMinusVerifiers/README.md`):

      Verity compiled model  refines  ByteLevel.verifyBytes  refines  verifySpec

  * The right link (`verifyBytes` refines `verifySpec`) is proved with no axioms
    in `SphincsMinusVerifierSpec/Spec.lean` (`verifyBytes_eq_verifySpec`) and
    lifted to the observable boundary here by `byteVerifier_refines_spec`.

  * The left link (compiled model refines `verifyBytes`) is the MODEL-EXEC-BRIDGE.
    Verity's executable source semantics (`Compiler/.../SourceSemantics.lean`)
    *does* model the raw `bytes`-calldata surface: `evalExpr` handles
    `.calldataload` / `.calldatasize` / `.param` / `.localVar`, and `execStmt` /
    `execStmtList` run statements over a `RuntimeState`. As of the keccak
    source-semantics work, the interpreter now also models the native `keccak256`
    opcode: `evalExpr` on `.keccak256 off size` returns the *computed* 32-byte
    digest of the word-aligned memory slice (`keccakMemorySlice`, backed by the
    in-tree pure `KeccakEngine`), no longer `none`. So the keccak-family bodies
    (C13, C12) no longer revert at their first hash; their accept subdomain is
    now *reachable* through the real interpreter, and the residual gap there is
    proof size — the line-by-line equivalence of the full hypertree climb against
    `ByteLevel.verifyBytes` — not a framework limitation. The SHA-256 precompile
    (`staticcall` to `0x02`) remains unmodeled (`evalExpr_staticcall = none`): a
    faithful model is blocked by the word-keyed `RuntimeState` memory vs. the
    SLH-DSA body's overlapping sub-word `mstore`s (the `linear_memory_aliasing`
    obligation), so the SHA-2 body still reverts at its first precompile call and
    that accept subdomain stays out of reach pending a byte-addressed memory
    model. Until the full per-body accept equivalence is proved, each model's
    refinement of the byte spec is taken as a **named, documented axiom**, not a
    `sorry`. These axioms are the Lean-level statement of the
    `proofStatus := .assumed` local obligations already attached to each model in
    `Model.lean` (`assembly_refinement`, `linear_memory_aliasing`, the raw-Yul
    revert obligations). They sit alongside the repo's existing keccak
    collision-resistance axioms in the trust surface and are surfaced by
    `#print axioms`. Two unconditional slices of this bridge are already
    discharged (no bridge axiom): the malformed-length subdomain — see the
    `*_interp_agrees_verifyBytes_bad_length` theorems below, which run the real
    interpreter on the real body and prove two-sided agreement with the byte spec
    — and the length-guard pass-through on the good-length subdomain (the first
    accept-path step) — see `*VerifyBody_passes_length_guard` in `Model.lean`,
    which proves the real interpreter falls through the guard to the body when
    `sig_length` matches.

  The per-verifier `*_refines_byte_spec` and `*_refines_spec` results below are
  therefore unconditional theorems whose only assumptions are these explicitly
  named bridge axioms (plus `propext`).

  ## Scope: implementation-correctness, NOT unforgeability

  These proofs establish *implementation correctness*: each compiled verifier
  faithfully runs the SPHINCS- verification *algorithm* and reaches the algorithm's
  verdict (accept / reject / revert), down to the byte-level parsing and the
  +C grinding checks (`verifyParsed_accepts_sound` exhibits the reconstructed
  witness on the accept side).

  They do **not** prove anything about the cryptographic *security* of SPHINCS-.
  Nothing here shows the scheme is EUF-CMA secure, that signatures are
  unforgeable, or that the hash families are collision-resistant; those are
  cryptographic assumptions, not theorems of this development. The `Primitives`
  package is taken abstractly (hashing/parsing supplied as opaque operations), so
  a verifier that "accepts" here means exactly "the on-chain code accepts under the
  modeled algorithm", which is the correct conditional statement: *if* SPHINCS- is
  secure as a scheme, *then* this contract enforces it faithfully. Unforgeability
  is out of scope by design.
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

/-! ### Bytes-level bad-length agreement (sound slice of MODEL-EXEC-BRIDGE)

These theorems connect the *real* interpreter run of each compiled `*VerifyBody`
to the byte-level spec `ByteLevel.verifyBytes` on the malformed-length subdomain,
introducing **no axiom**. They strengthen the interpreter-side revert lemmas in
`Model.lean` (which quantify over an abstract `RuntimeState`) into a two-sided
agreement at the `Bytes` boundary: for a state whose ABI-decoded `sig_length`
local equals the calldata signature length, a wrong length makes the compiled
body `revert` (`execStmtList ... = .revert`) *and* makes `verifyBytes` return
`none`. This is a genuine, machine-checked fragment of the `*_refines_byte_spec`
bridge equality, *proved* over a concrete `RuntimeState` rather than assumed; the
accept-path equality remains the carried bridge axiom. The hypotheses are stated
on `wordNormalize sig.size` (the 256-bit word the EVM length prefix decodes to);
for any realistic `sig.size < 2^256` this is exactly `sig.size ≠ <expected>`. -/

open Compiler.Proofs.IRGeneration.SourceSemantics in
/-- A concrete `RuntimeState` whose ABI-decoded `sig_length` local is the calldata
signature length. `world`/`selector` are immaterial to the length guard. -/
def badLenState (sigSize : Nat) : RuntimeState :=
  { world := Verity.defaultState
  , bindings := [("sig_length", wordNormalize sigSize)] }

open Compiler.Proofs.IRGeneration.SourceSemantics in
@[simp] theorem badLenState_sig_length (sigSize : Nat) :
    lookupValue (badLenState sigSize).bindings "sig_length" = wordNormalize sigSize := rfl

open Compiler.Proofs.IRGeneration.SourceSemantics in
/-- C13: the real compiled body run and the byte spec agree (both reject by
`revert`/`none`) on every wrong-length input. Proved, no bridge axiom. -/
theorem c13_interp_agrees_verifyBytes_bad_length
    (pkSeed pkRoot message sig : Bytes)
    (hne : wordNormalize sig.size ≠ wordNormalize 3688) :
    execStmtList [] (badLenState sig.size) c13VerifyBody = .revert
      ∧ ByteLevel.verifyBytes c13Primitives c13 pkSeed pkRoot message sig = none := by
  refine ⟨?_, ?_⟩
  · apply c13VerifyBody_reverts_on_bad_length
    rw [badLenState_sig_length]; exact hne
  · apply ByteLevel.verifyBytes_bad_length
    intro h
    exact hne (congrArg wordNormalize h)

open Compiler.Proofs.IRGeneration.SourceSemantics in
/-- C12: the real compiled body run and the byte spec agree on every wrong-length
input. Proved, no bridge axiom. -/
theorem c12_interp_agrees_verifyBytes_bad_length
    (pkSeed pkRoot message sig : Bytes)
    (hne : wordNormalize sig.size ≠ wordNormalize 6512) :
    execStmtList [] (badLenState sig.size) c12VerifyBody = .revert
      ∧ ByteLevel.verifyBytes c12Primitives c12 pkSeed pkRoot message sig = none := by
  refine ⟨?_, ?_⟩
  · apply c12VerifyBody_reverts_on_bad_length
    rw [badLenState_sig_length]; exact hne
  · apply ByteLevel.verifyBytes_bad_length
    intro h
    exact hne (congrArg wordNormalize h)

open Compiler.Proofs.IRGeneration.SourceSemantics in
/-- SHA-2 SLH-DSA: the real compiled body run and the byte spec agree on every
wrong-length input. Proved, no bridge axiom. -/
theorem slhDsaSha2_128_24_interp_agrees_verifyBytes_bad_length
    (pkSeed pkRoot message sig : Bytes)
    (hne : wordNormalize sig.size ≠ wordNormalize 3856) :
    execStmtList [] (badLenState sig.size) slhDsaSha2VerifyBody = .revert
      ∧ ByteLevel.verifyBytes slhDsaSha2_128_24_Primitives slhDsaSha2_128_24
          pkSeed pkRoot message sig = none := by
  refine ⟨?_, ?_⟩
  · apply slhDsaSha2VerifyBody_reverts_on_bad_length
    rw [badLenState_sig_length]; exact hne
  · apply ByteLevel.verifyBytes_bad_length
    intro h
    exact hne (congrArg wordNormalize h)

/-! ### Surfaced accept-direction soundness

`verifyBytes_accepts_sound` (proved axiom-free beyond `propext` in `Spec.lean`)
lifted across each MODEL-EXEC-BRIDGE axiom to the observable `exec*` boundary: an
accepting compiled run exhibits a canonical public key, a parsed signature, and a
hypertree climb terminating in a root that matches `pkRoot`. -/

/-- Generic lifter: any observable verifier refining its byte spec inherits the
byte-level accept-direction soundness. -/
theorem exec_accepts_sound
    {p : Primitives} {v : Variant}
    {exec : Bytes → Bytes → Bytes → Bytes → Option Bool}
    (hModel : ByteLevel.ImplementsByteVerifier p v exec)
    (pkSeed pkRoot message sig : Bytes)
    (hAcc : exec pkSeed pkRoot message sig = some true) :
    ∃ pk parsedSig forsPk root,
      ByteLevel.parsePublicKey v pkSeed pkRoot = some pk ∧
      p.parseSignature v sig = some parsedSig ∧
      signatureShapeOk v parsedSig = true ∧
      forcedZeroOk v (p.hMsg v pk parsedSig.R message) = true ∧
      p.forsPkFromSig v pk (p.hMsg v pk parsedSig.R message) parsedSig.fors = some forsPk ∧
      foldHypertree p v pk (p.hMsg v pk parsedSig.R message) forsPk parsedSig.layers = .ok root ∧
      (root == pk.pkRoot) = true := by
  have hBytes : ByteLevel.verifyBytes p v pkSeed pkRoot message sig = some true := by
    rw [← hModel]; exact hAcc
  exact ByteLevel.verifyBytes_accepts_sound p v pkSeed pkRoot message sig hBytes

/-- C13: accepting compiled run ⇒ well-formed reconstructed witness. -/
theorem execC13_accepts_sound
    (pkSeed pkRoot message sig : Bytes)
    (hAcc : execC13 pkSeed pkRoot message sig = some true) :
    ∃ pk parsedSig forsPk root,
      ByteLevel.parsePublicKey c13 pkSeed pkRoot = some pk ∧
      c13Primitives.parseSignature c13 sig = some parsedSig ∧
      signatureShapeOk c13 parsedSig = true ∧
      forcedZeroOk c13 (c13Primitives.hMsg c13 pk parsedSig.R message) = true ∧
      c13Primitives.forsPkFromSig c13 pk (c13Primitives.hMsg c13 pk parsedSig.R message) parsedSig.fors = some forsPk ∧
      foldHypertree c13Primitives c13 pk (c13Primitives.hMsg c13 pk parsedSig.R message) forsPk parsedSig.layers = .ok root ∧
      (root == pk.pkRoot) = true :=
  exec_accepts_sound c13_refines_byte_spec pkSeed pkRoot message sig hAcc

/-- C12: accepting compiled run ⇒ well-formed reconstructed witness. -/
theorem execC12_accepts_sound
    (pkSeed pkRoot message sig : Bytes)
    (hAcc : execC12 pkSeed pkRoot message sig = some true) :
    ∃ pk parsedSig forsPk root,
      ByteLevel.parsePublicKey c12 pkSeed pkRoot = some pk ∧
      c12Primitives.parseSignature c12 sig = some parsedSig ∧
      signatureShapeOk c12 parsedSig = true ∧
      forcedZeroOk c12 (c12Primitives.hMsg c12 pk parsedSig.R message) = true ∧
      c12Primitives.forsPkFromSig c12 pk (c12Primitives.hMsg c12 pk parsedSig.R message) parsedSig.fors = some forsPk ∧
      foldHypertree c12Primitives c12 pk (c12Primitives.hMsg c12 pk parsedSig.R message) forsPk parsedSig.layers = .ok root ∧
      (root == pk.pkRoot) = true :=
  exec_accepts_sound c12_refines_byte_spec pkSeed pkRoot message sig hAcc

/-- SHA2 SLH-DSA: accepting compiled run ⇒ well-formed reconstructed witness. -/
theorem execSlhDsaSha2_128_24_accepts_sound
    (pkSeed pkRoot message sig : Bytes)
    (hAcc : execSlhDsaSha2_128_24 pkSeed pkRoot message sig = some true) :
    ∃ pk parsedSig forsPk root,
      ByteLevel.parsePublicKey slhDsaSha2_128_24 pkSeed pkRoot = some pk ∧
      slhDsaSha2_128_24_Primitives.parseSignature slhDsaSha2_128_24 sig = some parsedSig ∧
      signatureShapeOk slhDsaSha2_128_24 parsedSig = true ∧
      forcedZeroOk slhDsaSha2_128_24 (slhDsaSha2_128_24_Primitives.hMsg slhDsaSha2_128_24 pk parsedSig.R message) = true ∧
      slhDsaSha2_128_24_Primitives.forsPkFromSig slhDsaSha2_128_24 pk (slhDsaSha2_128_24_Primitives.hMsg slhDsaSha2_128_24 pk parsedSig.R message) parsedSig.fors = some forsPk ∧
      foldHypertree slhDsaSha2_128_24_Primitives slhDsaSha2_128_24 pk (slhDsaSha2_128_24_Primitives.hMsg slhDsaSha2_128_24 pk parsedSig.R message) forsPk parsedSig.layers = .ok root ∧
      (root == pk.pkRoot) = true :=
  exec_accepts_sound slhDsaSha2_128_24_refines_byte_spec pkSeed pkRoot message sig hAcc

/--
Compilation-model presence checks.  These are small regression anchors: if the
models are renamed or removed, the refinement file stops compiling before any
semantic proof attempt starts.
-/
example : c13Model.name = "SphincsC13Asm_VerityModel" := rfl
example : c12Model.name = "SPHINCs_C12Asm_VerityModel" := rfl
example : slhDsaSha2_128_24_Model.name = "SLH_DSA_SHA2_128_24_VerityModel" := rfl

end SphincsMinusVerifiers
