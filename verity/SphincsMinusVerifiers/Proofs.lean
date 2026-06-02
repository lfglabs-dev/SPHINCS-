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

import SphincsMinusVerifiers.ProofCore
import SphincsMinusVerifiers.C13BridgePrep
import SphincsMinusVerifiers.KeccakBridge

namespace SphincsMinusVerifiers

open SphincsMinusVerifierSpec
open Compiler.Proofs.IRGeneration.SourceSemantics
open SphincsMinusVerifiers.MkC13State
open SphincsMinusVerifiers.SegmentCompose

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

/-- Assumed: the exported opaque C13 runner `execC13` refines the byte-level
spec under `c13Primitives`.  The concrete bridge work below targets
`execC13Concrete` and must be completed before this exported runner is exposed
definitionally. -/
axiom c13_refines_byte_spec :
  ByteLevel.ImplementsByteVerifier c13Primitives c13 execC13

/-- Assumed: the concrete C12 source-semantics runner `execC12` refines the
byte-level spec under `c12Primitives`. -/
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

/-- C13: the internal concrete observable runner and byte spec agree on every malformed
signature length. This is the same bad-length bridge as
`c13_interp_agrees_verifyBytes_bad_length`, lifted all the way to `execC13Concrete`
over the frozen byte-facing entry state. -/
theorem execC13Concrete_agrees_verifyBytes_bad_length
    (pkSeed pkRoot message sig : Bytes)
    (hne : sig.size ≠ 3688) :
    execC13Concrete pkSeed pkRoot message sig =
      ByteLevel.verifyBytes c13Primitives c13 pkSeed pkRoot message sig :=
  C13BridgePrep.runC13BodyObserved_revert_on_bad_length
    pkSeed pkRoot message sig hne

/-- C12: the concrete observable runner and byte spec agree on every malformed
signature length. -/
theorem execC12_agrees_verifyBytes_bad_length
    (pkSeed pkRoot message sig : Bytes)
    (hne : sig.size ≠ 6512) :
    execC12 pkSeed pkRoot message sig =
      ByteLevel.verifyBytes c12Primitives c12 pkSeed pkRoot message sig :=
  SegmentRejectSpec.execC12_revert_on_bad_length
    pkSeed pkRoot message sig hne

/-- C13 bridge reducer: once the good-length branch is covered for every input,
the malformed-length theorem above supplies the complement and yields the full
byte-verifier implementation statement.  This records the exact remaining
MODEL-EXEC-BRIDGE obligation without adding an axiom. -/
theorem c13_refines_byte_spec_of_good_length_cover
    (hGood :
      ∀ pkSeed pkRoot message sig,
        sig.size = 3688 →
        execC13Concrete pkSeed pkRoot message sig =
          ByteLevel.verifyBytes c13Primitives c13 pkSeed pkRoot message sig) :
    ByteLevel.ImplementsByteVerifier c13Primitives c13 execC13Concrete := by
  intro pkSeed pkRoot message sig
  by_cases hLen : sig.size = 3688
  · exact hGood pkSeed pkRoot message sig hLen
  · exact execC13Concrete_agrees_verifyBytes_bad_length pkSeed pkRoot message sig hLen

/-- C13 bridge reducer after discharging the forced-zero reject branch.  Once
the forced-zero-true branch is covered for every parsed good-length input, the
proved bad-length bridge and the proved forced-zero-false bridge supply the
complementary cases and yield the full byte-verifier implementation statement. -/
theorem c13_refines_byte_spec_of_forced_zero_true_cover
    (hTrue :
      ∀ pkSeed pkRoot message sig sigParsed,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        execC13Concrete pkSeed pkRoot message sig =
          ByteLevel.verifyBytes c13Primitives c13 pkSeed pkRoot message sig) :
    ByteLevel.ImplementsByteVerifier c13Primitives c13 execC13Concrete := by
  apply c13_refines_byte_spec_of_good_length_cover
  intro pkSeed pkRoot message sig hLen
  have hLenC13 : sig.size = c13.sigBytes := by
    simpa [c13] using hLen
  obtain ⟨sigParsed, hParse⟩ :=
    C13Concrete.parseSignatureC13_some_of_size (v := c13) (sig := sig) hLenC13
  cases hZero : forcedZeroOk c13
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) with
  | false =>
      exact
        C13BridgePrep.runC13BodyObserved_revert_on_forced_zero_false_of_parse
          pkSeed pkRoot message sig sigParsed hParse hZero
  | true =>
      exact hTrue pkSeed pkRoot message sig sigParsed hParse hZero

/-- C13 bridge reducer after discharging C13's total FORS reconstruction.  The
remaining cover obligation starts at parsed, forced-zero-true inputs with the
concrete C13 FORS public key fixed to its named compression output. -/
theorem c13_refines_byte_spec_of_fors_some_cover
    (hSome :
      ∀ pkSeed pkRoot message sig sigParsed forsPk,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        execC13Concrete pkSeed pkRoot message sig =
          ByteLevel.verifyBytes c13Primitives c13 pkSeed pkRoot message sig) :
    ByteLevel.ImplementsByteVerifier c13Primitives c13 execC13Concrete := by
  apply c13_refines_byte_spec_of_forced_zero_true_cover
  intro pkSeed pkRoot message sig sigParsed hParse hZero
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  let forsPk := C13Concrete.hash16OfWord
    (C13Concrete.forsPkWordC13 pk digest sigParsed.fors)
  have hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13 pk digest
      sigParsed.fors = some forsPk := by
    simpa [pk, digest, forsPk, C13Concrete.c13PrimitivesConcrete] using
      C13Concrete.forsPkFromSigC13_eq_named c13 pk digest sigParsed.fors
  exact hSome pkSeed pkRoot message sig sigParsed forsPk hParse hZero hFors

/-- C13 bridge reducer after splitting the concrete C13 hypertree fold.  Parsed
C13 signatures rule out the `.rejected` branch, so the remaining proof surface is
only the successful `.ok root` branch and the executable-revert `.reverted`
branch. -/
theorem c13_refines_byte_spec_of_fold_result_cover
    (hOk :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        execC13Concrete pkSeed pkRoot message sig =
          ByteLevel.verifyBytes c13Primitives c13 pkSeed pkRoot message sig)
    (hReverted :
      ∀ pkSeed pkRoot message sig sigParsed forsPk,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .reverted →
        execC13Concrete pkSeed pkRoot message sig =
          ByteLevel.verifyBytes c13Primitives c13 pkSeed pkRoot message sig) :
    ByteLevel.ImplementsByteVerifier c13Primitives c13 execC13Concrete := by
  apply c13_refines_byte_spec_of_fors_some_cover
  intro pkSeed pkRoot message sig sigParsed forsPk hParse hZero hFors
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  cases hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13 pk digest
      forsPk sigParsed.layers with
  | ok specRoot =>
      exact hOk pkSeed pkRoot message sig sigParsed forsPk specRoot
        hParse hZero (by simpa [pk, digest] using hFors)
        (by simpa [pk, digest] using hFold)
  | reverted =>
      exact hReverted pkSeed pkRoot message sig sigParsed forsPk
        hParse hZero (by simpa [pk, digest] using hFors)
        (by simpa [pk, digest] using hFold)
  | rejected =>
      have hNotRejected :
          foldHypertree C13Concrete.c13PrimitivesConcrete c13 pk digest
            forsPk sigParsed.layers ≠ .rejected :=
        C13Concrete.foldHypertree_c13_ne_rejected_of_parse hParse pk digest forsPk
      exact False.elim (hNotRejected hFold)

/-- The first C13 layer-loop guard state, in the exact shape consumed by the
revert bridge. -/
def c13FirstLayerGuardState
    (pkSeed pkRoot message sig : Bytes) : RuntimeState :=
  ClimbLoopGuarded.loopState "layer"
    { (SegmentCompose.afterSeed (mkC13State pkSeed pkRoot message sig)) with
      bindings :=
        bindValue
          (SegmentCompose.afterSeed
            (mkC13State pkSeed pkRoot message sig)).bindings
          "layer" (wordNormalize 0) } 0

/-- The second C13 layer-loop guard state, in the exact shape consumed by the
revert bridge. -/
def c13SecondLayerGuardState
    (pkSeed pkRoot message sig : Bytes) : RuntimeState :=
  ClimbLoopGuarded.loopState "layer"
    (SegmentLayer3.stepLayer
      (c13FirstLayerGuardState pkSeed pkRoot message sig)) 1

/-- The first guard state used by the revert bridge is the same concrete layer-0
state used by the accept-side current-node facts. -/
theorem c13FirstLayerGuardState_eq_c13LayerLoopState0
    (pkSeed pkRoot message sig : Bytes) :
    c13FirstLayerGuardState pkSeed pkRoot message sig =
      CurrentNodeFrame.c13LayerLoopState0
        (mkC13State pkSeed pkRoot message sig) := rfl

/-- The second guard state used by the revert bridge is the same concrete layer-1
state used by the accept-side current-node facts. -/
theorem c13SecondLayerGuardState_eq_c13LayerLoopState1
    (pkSeed pkRoot message sig : Bytes) :
    c13SecondLayerGuardState pkSeed pkRoot message sig =
      CurrentNodeFrame.c13LayerLoopState1
        (mkC13State pkSeed pkRoot message sig) := rfl

/-- Remaining concrete data needed for the C13 `.ok` fold branch at the current
node boundary. -/
def C13FoldOkCurrentNodeWordcmpData
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes) : Prop :=
  SegmentLayer3.layerGuard
    (CurrentNodeFrame.c13LayerLoopState0
      (mkC13State pkSeed pkRoot message sig)) = true ∧
  lookupValue
      (SegmentLayer3.stepLayer
        (CurrentNodeFrame.c13LayerLoopState0
          (mkC13State pkSeed pkRoot message sig))).bindings
      "currentNode"
    =
      C13Concrete.wordOfHash16
        (SegmentAcceptSpec.c13HypertreeSpecStepAtLayer
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.layers 0 forsPk) ∧
  SegmentLayer3.layerGuard
    (CurrentNodeFrame.c13LayerLoopState1
      (mkC13State pkSeed pkRoot message sig)) = true ∧
  lookupValue
      (SegmentLayer3.stepLayer
        (CurrentNodeFrame.c13LayerLoopState1
          (mkC13State pkSeed pkRoot message sig))).bindings
      "currentNode"
    = C13Concrete.wordOfHash16 specRoot ∧
  decide (C13Concrete.wordOfHash16 specRoot = C13Concrete.wordOfHash16 pkRoot)
    = rootMatchesPk c13 specRoot pkRoot

/-- Successful C13 fold data with the byte-shaped public-key root width exposed
instead of the final word-comparison equation.  The comparison follows from
`pkRoot.size = 16` plus the C13-produced `specRoot` roundtrip. -/
def C13FoldOkCurrentNodePkRootSizeData
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes) : Prop :=
  SegmentLayer3.layerGuard
    (CurrentNodeFrame.c13LayerLoopState0
      (mkC13State pkSeed pkRoot message sig)) = true ∧
  lookupValue
      (SegmentLayer3.stepLayer
        (CurrentNodeFrame.c13LayerLoopState0
          (mkC13State pkSeed pkRoot message sig))).bindings
      "currentNode"
    =
      C13Concrete.wordOfHash16
        (SegmentAcceptSpec.c13HypertreeSpecStepAtLayer
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.layers 0 forsPk) ∧
  SegmentLayer3.layerGuard
    (CurrentNodeFrame.c13LayerLoopState1
      (mkC13State pkSeed pkRoot message sig)) = true ∧
  lookupValue
      (SegmentLayer3.stepLayer
        (CurrentNodeFrame.c13LayerLoopState1
          (mkC13State pkSeed pkRoot message sig))).bindings
      "currentNode"
    = C13Concrete.wordOfHash16 specRoot ∧
  pkRoot.size = 16

/-- Package the current concrete two-step layer facts into the `.ok` branch data
shape consumed by the C13 byte-refinement reducer. -/
theorem c13FoldOkCurrentNodePkRootSizeData_of_current_node_facts
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hGuard0 :
      SegmentLayer3.layerGuard
        (CurrentNodeFrame.c13LayerLoopState0
          (mkC13State pkSeed pkRoot message sig)) = true)
    (hCurrent0 :
      lookupValue
          (SegmentLayer3.stepLayer
            (CurrentNodeFrame.c13LayerLoopState0
              (mkC13State pkSeed pkRoot message sig))).bindings
          "currentNode"
        =
          C13Concrete.wordOfHash16
            (SegmentAcceptSpec.c13HypertreeSpecStepAtLayer
              { pkSeed := pkSeed, pkRoot := pkRoot }
              (C13Concrete.c13PrimitivesConcrete.hMsg c13
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
              sigParsed.layers 0 forsPk))
    (hGuard1 :
      SegmentLayer3.layerGuard
        (CurrentNodeFrame.c13LayerLoopState1
          (mkC13State pkSeed pkRoot message sig)) = true)
    (hCurrent1 :
      lookupValue
          (SegmentLayer3.stepLayer
            (CurrentNodeFrame.c13LayerLoopState1
              (mkC13State pkSeed pkRoot message sig))).bindings
          "currentNode"
        = C13Concrete.wordOfHash16 specRoot)
    (hPkRootSize : pkRoot.size = 16) :
    C13FoldOkCurrentNodePkRootSizeData
      pkSeed pkRoot message sig sigParsed forsPk specRoot :=
  ⟨hGuard0, hCurrent0, hGuard1, hCurrent1, hPkRootSize⟩

/-- Package the current concrete two-step layer facts into the `.ok` branch data
shape whose final comparison uses the C13 public-key root projection.  The
comparison follows from the C13-produced `specRoot` roundtrip; it no longer needs
any public-key-root size premise. -/
theorem c13FoldOkCurrentNodeWordcmpData_of_current_node_facts
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        sigParsed.fors = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hGuard0 :
      SegmentLayer3.layerGuard
        (CurrentNodeFrame.c13LayerLoopState0
          (mkC13State pkSeed pkRoot message sig)) = true)
    (hCurrent0 :
      lookupValue
          (SegmentLayer3.stepLayer
            (CurrentNodeFrame.c13LayerLoopState0
              (mkC13State pkSeed pkRoot message sig))).bindings
          "currentNode"
        =
          C13Concrete.wordOfHash16
            (SegmentAcceptSpec.c13HypertreeSpecStepAtLayer
              { pkSeed := pkSeed, pkRoot := pkRoot }
              (C13Concrete.c13PrimitivesConcrete.hMsg c13
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
              sigParsed.layers 0 forsPk))
    (hGuard1 :
      SegmentLayer3.layerGuard
        (CurrentNodeFrame.c13LayerLoopState1
          (mkC13State pkSeed pkRoot message sig)) = true)
    (hCurrent1 :
      lookupValue
          (SegmentLayer3.stepLayer
            (CurrentNodeFrame.c13LayerLoopState1
              (mkC13State pkSeed pkRoot message sig))).bindings
          "currentNode"
        = C13Concrete.wordOfHash16 specRoot) :
    C13FoldOkCurrentNodeWordcmpData
      pkSeed pkRoot message sig sigParsed forsPk specRoot :=
  ⟨hGuard0, hCurrent0, hGuard1, hCurrent1,
    SegmentAcceptSpec.wordCmp_of_wordOfHash16_rootMatchesPk_c13 specRoot pkRoot
      (SegmentAcceptSpec.specRoot_roundtrip_of_c13_fors_fold hFors hFold)⟩

/-- Convert the bounded accept-side two-step current-node observation package
into the exact successful C13 fold data consumed by the word-comparison bridge
boundary.  The package's legacy `pkRoot.size = 16` field is intentionally unused:
the final comparison is discharged from the C13 `specRoot` roundtrip instead. -/
theorem c13FoldOkCurrentNodeWordcmpData_of_two_step_obligations
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk specRoot : Bytes)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        sigParsed.fors = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hObs : SegmentAcceptSpec.C13SeedNamedAcceptConcreteLayerCurrentNodeTwoStepObligations
        pkSeed pkRoot message sig sigParsed forsPk) :
    C13FoldOkCurrentNodeWordcmpData
      pkSeed pkRoot message sig sigParsed forsPk specRoot := by
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  let specStep := SegmentAcceptSpec.c13HypertreeSpecStepAtLayer pk digest sigParsed.layers
  rcases hObs.hSuccessCurrent0 with
    ⟨lsig0, wotsPk0, root0, hLayer0, hGrinding0, hWots0, hXmss0, hCurrent0⟩
  rcases hObs.hSuccessCurrent1 with
    ⟨lsig1, wotsPk1, root1, hLayer1, hGrinding1, hWots1, hXmss1, hCurrent1⟩
  have hStep0Eq : specStep 0 forsPk = root0 := by
    exact SegmentAcceptSpec.c13HypertreeSpecStepAtLayer_eq_root_of_success
      pk digest sigParsed.layers 0 forsPk wotsPk0 root0 lsig0 hLayer0
      (by simpa [pk, digest, specStep] using hGrinding0)
      (by simpa [pk, digest, specStep] using hWots0)
      (by simpa [pk, digest, specStep] using hXmss0)
  have hStep1Eq : specStep 1 (specStep 0 forsPk) = root1 := by
    exact SegmentAcceptSpec.c13HypertreeSpecStepAtLayer_eq_root_of_success
      pk digest sigParsed.layers 1 (specStep 0 forsPk) wotsPk1 root1 lsig1 hLayer1
      (by simpa [pk, digest, specStep] using hGrinding1)
      (by simpa [pk, digest, specStep] using hWots1)
      (by simpa [pk, digest, specStep] using hXmss1)
  have hTwo : wordNormalize 2 = 2 :=
    SegmentS2.wordNormalize_of_lt (by decide : 2 < 2 ^ 256)
  have hSpecFold :
      ClimbLoop.specFold specStep forsPk 0 (wordNormalize 2) = specRoot := by
    simpa [pk, digest, specStep] using
      SegmentAcceptSpec.specFold_c13HypertreeSpecStepAtLayer_eq_of_foldHypertree_ok
        pk digest forsPk specRoot sigParsed.layers hFold
  have hStep1Root0 : specStep 1 root0 = root1 := by
    simpa [hStep0Eq] using hStep1Eq
  have hRoot1 : root1 = specRoot := by
    simpa [ClimbLoop.specFold, hTwo, hStep0Eq, hStep1Root0] using hSpecFold
  refine
    c13FoldOkCurrentNodeWordcmpData_of_current_node_facts
      pkSeed pkRoot message sig sigParsed forsPk specRoot hFors hFold
      hObs.hGuard0 ?_ hObs.hGuard1 ?_
  · change
      lookupValue
          (SegmentLayer3.stepLayer
            (CurrentNodeFrame.c13LayerLoopState0
              (mkC13State pkSeed pkRoot message sig))).bindings
          "currentNode" = C13Concrete.wordOfHash16 (specStep 0 forsPk)
    rw [hStep0Eq]
    simpa [pk, digest, specStep, CurrentNodeFrame.c13LayerLoopState0,
      CurrentNodeFrame.c13LayerStartState] using hCurrent0
  · rw [← hRoot1]
    simpa [pk, digest, specStep, CurrentNodeFrame.c13LayerLoopState1,
      CurrentNodeFrame.c13LayerAfterStep0, hStep0Eq] using hCurrent1

/-- Remaining concrete guard data needed for the C13 `.reverted` fold branch. -/
def C13FoldRevertedGuardData
    (pkSeed pkRoot message sig : Bytes) : Prop :=
  SegmentLayer3.layerGuard
      (c13FirstLayerGuardState pkSeed pkRoot message sig) = false ∨
  (SegmentLayer3.layerGuard
      (c13FirstLayerGuardState pkSeed pkRoot message sig) = true ∧
    SegmentLayer3.layerGuard
      (c13SecondLayerGuardState pkSeed pkRoot message sig) = false)

/-- Reverted-branch executable checksum data.  These are the concrete layer facts
needed to turn the spec-side C13 grinding failure exposed by
`foldHypertree ... = .reverted` into the executable layer guard failure. -/
def C13FoldRevertedDigitSumData
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk : Bytes) : Prop :=
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  (∀ d : C13Concrete.FoldHypertreeC13RevertedLayer0Data
      pk digest forsPk sigParsed.layers,
      lookupValue
          (SegmentLayer3.afterDigit
            (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
          "digitSum"
        =
          C13Concrete.wotsDigitSum
            (C13Concrete.wotsDigest
              (C13Concrete.wordOfHash16 pkSeed) 0
              (digest.hyperIndex / 2048)
              (digest.hyperIndex % 2048)
              d.lsig0.wots.count
              (C13Concrete.wordOfHash16 forsPk))) ∧
  (∀ d : C13Concrete.FoldHypertreeC13RevertedLayer1Data
      pk digest forsPk sigParsed.layers,
      lookupValue
          (SegmentLayer3.afterDigit
            (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
          "digitSum"
        =
          C13Concrete.wotsDigitSum
            (C13Concrete.wotsDigest
              (C13Concrete.wordOfHash16 pkSeed) 0
              (digest.hyperIndex / 2048)
              (digest.hyperIndex % 2048)
              d.lsig0.wots.count
              (C13Concrete.wordOfHash16 forsPk)) ∧
      lookupValue
          (SegmentLayer3.afterDigit
            (c13SecondLayerGuardState pkSeed pkRoot message sig)).bindings
          "digitSum"
        =
          C13Concrete.wotsDigitSum
            (C13Concrete.wotsDigest
              (C13Concrete.wordOfHash16 pkSeed) 1
              ((digest.hyperIndex / 2048) / 2048)
              ((digest.hyperIndex / 2048) % 2048)
              d.lsig1.wots.count
              (C13Concrete.wordOfHash16 d.root0)))

/-- Reverted-branch pre-checksum digest data.  This is the remaining
straight-line obligation before the executable 43-step checksum fold can be
reduced to `C13Concrete.wotsDigitSum`. -/
def C13FoldRevertedBeforeDigitData
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk : Bytes) : Prop :=
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  (∀ d : C13Concrete.FoldHypertreeC13RevertedLayer0Data
      pk digest forsPk sigParsed.layers,
      lookupValue
          (SegmentLayer3.beforeDigitLoop
            (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
          "d"
        =
          C13Concrete.wotsDigest
            (C13Concrete.wordOfHash16 pkSeed) 0
            (digest.hyperIndex / 2048)
            (digest.hyperIndex % 2048)
            d.lsig0.wots.count
            (C13Concrete.wordOfHash16 forsPk)) ∧
  (∀ d : C13Concrete.FoldHypertreeC13RevertedLayer1Data
      pk digest forsPk sigParsed.layers,
      lookupValue
          (SegmentLayer3.beforeDigitLoop
            (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
          "d"
        =
          C13Concrete.wotsDigest
            (C13Concrete.wordOfHash16 pkSeed) 0
            (digest.hyperIndex / 2048)
            (digest.hyperIndex % 2048)
            d.lsig0.wots.count
            (C13Concrete.wordOfHash16 forsPk) ∧
      lookupValue
          (SegmentLayer3.beforeDigitLoop
            (c13SecondLayerGuardState pkSeed pkRoot message sig)).bindings
          "d"
        =
          C13Concrete.wotsDigest
            (C13Concrete.wordOfHash16 pkSeed) 1
            ((digest.hyperIndex / 2048) / 2048)
            ((digest.hyperIndex / 2048) % 2048)
            d.lsig1.wots.count
            (C13Concrete.wordOfHash16 d.root0))

/-- Reverted-branch WOTS digest scratch data.  These are the four words consumed
by `keccak256(0x00, 0x80)` immediately before the executable prefix binds
`"d"`: seed, WOTS hash address, current node, and WOTS count. -/
def C13FoldRevertedDigestScratchData
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk : Bytes) : Prop :=
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  (∀ d : C13Concrete.FoldHypertreeC13RevertedLayer0Data
      pk digest forsPk sigParsed.layers,
      let st := SegmentLayer3.beforeDigest
        (c13FirstLayerGuardState pkSeed pkRoot message sig)
      (st.world.memory 0x00).val = C13Concrete.wordOfHash16 pkSeed ∧
      (st.world.memory 0x20).val =
        C13Concrete.adrsWotsHashBase 0
          (digest.hyperIndex / 2048)
          (digest.hyperIndex % 2048) ∧
      (st.world.memory 0x40).val = C13Concrete.wordOfHash16 forsPk ∧
      (st.world.memory 0x60).val = d.lsig0.wots.count) ∧
  (∀ d : C13Concrete.FoldHypertreeC13RevertedLayer1Data
      pk digest forsPk sigParsed.layers,
      let st0 := SegmentLayer3.beforeDigest
        (c13FirstLayerGuardState pkSeed pkRoot message sig)
      let st1 := SegmentLayer3.beforeDigest
        (c13SecondLayerGuardState pkSeed pkRoot message sig)
      (st0.world.memory 0x00).val = C13Concrete.wordOfHash16 pkSeed ∧
      (st0.world.memory 0x20).val =
        C13Concrete.adrsWotsHashBase 0
          (digest.hyperIndex / 2048)
          (digest.hyperIndex % 2048) ∧
      (st0.world.memory 0x40).val = C13Concrete.wordOfHash16 forsPk ∧
      (st0.world.memory 0x60).val = d.lsig0.wots.count ∧
      (st1.world.memory 0x00).val = C13Concrete.wordOfHash16 pkSeed ∧
      (st1.world.memory 0x20).val =
        C13Concrete.adrsWotsHashBase 1
          ((digest.hyperIndex / 2048) / 2048)
          ((digest.hyperIndex / 2048) % 2048) ∧
      (st1.world.memory 0x40).val = C13Concrete.wordOfHash16 d.root0 ∧
      (st1.world.memory 0x60).val = d.lsig1.wots.count)

/-- The generic Layer-3 pre-digest theorem turns concrete scratch-cell data into
the `"d" = C13Concrete.wotsDigest ...` facts required by the checksum reducer. -/
theorem c13FoldRevertedBeforeDigitData_of_digest_scratch_data
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk : Bytes)
    (hScratch : C13FoldRevertedDigestScratchData
        pkSeed pkRoot message sig sigParsed forsPk) :
    C13FoldRevertedBeforeDigitData pkSeed pkRoot message sig sigParsed forsPk := by
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  refine ⟨?_, ?_⟩
  · intro d
    rcases hScratch.1 d with ⟨hSeed, hAdrs, hNode, hCount⟩
    exact SegmentLayer3.beforeDigitLoop_d_eq_wotsDigest_of_scratch
      (c13FirstLayerGuardState pkSeed pkRoot message sig)
      (C13Concrete.wordOfHash16 pkSeed) 0
      (digest.hyperIndex / 2048)
      (digest.hyperIndex % 2048)
      d.lsig0.wots.count
      (C13Concrete.wordOfHash16 forsPk)
      hSeed hAdrs hNode hCount
  · intro d
    rcases hScratch.2 d with
      ⟨hSeed0, hAdrs0, hNode0, hCount0, hSeed1, hAdrs1, hNode1, hCount1⟩
    constructor
    · exact SegmentLayer3.beforeDigitLoop_d_eq_wotsDigest_of_scratch
        (c13FirstLayerGuardState pkSeed pkRoot message sig)
        (C13Concrete.wordOfHash16 pkSeed) 0
        (digest.hyperIndex / 2048)
        (digest.hyperIndex % 2048)
        d.lsig0.wots.count
        (C13Concrete.wordOfHash16 forsPk)
        hSeed0 hAdrs0 hNode0 hCount0
    · exact SegmentLayer3.beforeDigitLoop_d_eq_wotsDigest_of_scratch
        (c13SecondLayerGuardState pkSeed pkRoot message sig)
        (C13Concrete.wordOfHash16 pkSeed) 1
        ((digest.hyperIndex / 2048) / 2048)
        ((digest.hyperIndex / 2048) % 2048)
        d.lsig1.wots.count
        (C13Concrete.wordOfHash16 d.root0)
        hSeed1 hAdrs1 hNode1 hCount1

private theorem c13_wotsDigest_lt
    (seed : C13Concrete.Word) (layer idxTree idxLeaf count node : Nat) :
    C13Concrete.wotsDigest seed layer idxTree idxLeaf count node < 2 ^ 256 := by
  simpa [C13Concrete.wotsDigest, Compiler.Constants.evmModulus] using
    SphincsMinusVerifiers.KeccakBridge.keccakWords_lt
      [seed, C13Concrete.adrsWotsHashBase layer idxTree idxLeaf, node, count]

/-- The executable checksum fold computes exactly the spec-side WOTS+C digit
sum once the straight-line prefix has bound `"d"` to the layer digest. -/
theorem c13FoldRevertedDigitSumData_of_before_digit_data
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk : Bytes)
    (hBefore : C13FoldRevertedBeforeDigitData
        pkSeed pkRoot message sig sigParsed forsPk) :
    C13FoldRevertedDigitSumData pkSeed pkRoot message sig sigParsed forsPk := by
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  refine ⟨?_, ?_⟩
  · intro d
    exact SegmentLayer3.afterDigit_digitSum_eq_wotsDigitSum_of_beforeDigitLoop
      (c13FirstLayerGuardState pkSeed pkRoot message sig)
      (C13Concrete.wotsDigest
        (C13Concrete.wordOfHash16 pkSeed) 0
        (digest.hyperIndex / 2048)
        (digest.hyperIndex % 2048)
        d.lsig0.wots.count
        (C13Concrete.wordOfHash16 forsPk))
      (by simpa [pk, digest] using hBefore.1 d)
      (c13_wotsDigest_lt
        (C13Concrete.wordOfHash16 pkSeed) 0
        (digest.hyperIndex / 2048)
        (digest.hyperIndex % 2048)
        d.lsig0.wots.count
        (C13Concrete.wordOfHash16 forsPk))
  · intro d
    constructor
    · exact SegmentLayer3.afterDigit_digitSum_eq_wotsDigitSum_of_beforeDigitLoop
        (c13FirstLayerGuardState pkSeed pkRoot message sig)
        (C13Concrete.wotsDigest
          (C13Concrete.wordOfHash16 pkSeed) 0
          (digest.hyperIndex / 2048)
          (digest.hyperIndex % 2048)
          d.lsig0.wots.count
          (C13Concrete.wordOfHash16 forsPk))
        (by simpa [pk, digest] using (hBefore.2 d).1)
        (c13_wotsDigest_lt
          (C13Concrete.wordOfHash16 pkSeed) 0
          (digest.hyperIndex / 2048)
          (digest.hyperIndex % 2048)
          d.lsig0.wots.count
          (C13Concrete.wordOfHash16 forsPk))
    · exact SegmentLayer3.afterDigit_digitSum_eq_wotsDigitSum_of_beforeDigitLoop
        (c13SecondLayerGuardState pkSeed pkRoot message sig)
        (C13Concrete.wotsDigest
          (C13Concrete.wordOfHash16 pkSeed) 1
          ((digest.hyperIndex / 2048) / 2048)
          ((digest.hyperIndex / 2048) % 2048)
          d.lsig1.wots.count
          (C13Concrete.wordOfHash16 d.root0))
        (by simpa [pk, digest] using (hBefore.2 d).2)
        (c13_wotsDigest_lt
          (C13Concrete.wordOfHash16 pkSeed) 1
          ((digest.hyperIndex / 2048) / 2048)
          ((digest.hyperIndex / 2048) % 2048)
          d.lsig1.wots.count
          (C13Concrete.wordOfHash16 d.root0))

/-- A C13 spec-side `.reverted` fold plus executable checksum correspondence is
enough to produce the raw guard-failure data consumed by the existing revert
bridges. -/
theorem c13FoldRevertedGuardData_of_digit_sum_data
    (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk : Bytes)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        forsPk sigParsed.layers = .reverted)
    (hDigit : C13FoldRevertedDigitSumData
        pkSeed pkRoot message sig sigParsed forsPk) :
    C13FoldRevertedGuardData pkSeed pkRoot message sig := by
  let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
  let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
  cases C13Concrete.foldHypertree_c13_reverted_two_layer_data
      pk digest forsPk sigParsed.layers (by simpa [pk, digest] using hFold) with
  | layer0 d =>
      have hNe :
          C13Concrete.wotsDigitSum
              (C13Concrete.wotsDigest (C13Concrete.wordOfHash16 pkSeed) 0
                (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
                d.lsig0.wots.count (C13Concrete.wordOfHash16 forsPk)) ≠ 208 :=
        C13Concrete.wotsDigitSum_ne_of_wotsGrindingFailsC13AtLayer_true
          (layer := 0) (pk := pk)
          (treeIdx := digest.hyperIndex / 2048)
          (leafIdx := digest.hyperIndex % 2048)
          (node := forsPk) (wots := d.lsig0.wots)
          d.hGrinding0
      have hExecNe :
          lookupValue
              (SegmentLayer3.afterDigit
                (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
              "digitSum" ≠ 208 := by
        rw [hDigit.1 d]
        simpa [pk, digest] using hNe
      exact Or.inl
        (SegmentLayer3.layerGuard_of_afterDigit_digitSum_ne
          (c13FirstLayerGuardState pkSeed pkRoot message sig) hExecNe)
  | layer1 d =>
      have hSum0 :
          C13Concrete.wotsDigitSum
              (C13Concrete.wotsDigest (C13Concrete.wordOfHash16 pkSeed) 0
                (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
                d.lsig0.wots.count (C13Concrete.wordOfHash16 forsPk)) = 208 := by
        exact C13Concrete.wotsDigitSum_eq_of_wotsGrindingFailsC13AtLayer_false
          (layer := 0) (pk := pk)
          (treeIdx := digest.hyperIndex / 2048)
          (leafIdx := digest.hyperIndex % 2048)
          (node := forsPk) (wots := d.lsig0.wots)
          d.hGrinding0
      have hExecEq0 :
          lookupValue
              (SegmentLayer3.afterDigit
                (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
              "digitSum" = 208 := by
        rw [(hDigit.2 d).1]
        simpa [pk, digest] using hSum0
      have hGuard0 :
          SegmentLayer3.layerGuard
            (c13FirstLayerGuardState pkSeed pkRoot message sig) = true :=
        SegmentLayer3.layerGuard_of_afterDigit_digitSum_eq
          (c13FirstLayerGuardState pkSeed pkRoot message sig) hExecEq0
      have hNe1 :
          C13Concrete.wotsDigitSum
              (C13Concrete.wotsDigest (C13Concrete.wordOfHash16 pkSeed) 1
                ((digest.hyperIndex / 2048) / 2048)
                ((digest.hyperIndex / 2048) % 2048)
                d.lsig1.wots.count (C13Concrete.wordOfHash16 d.root0)) ≠ 208 :=
        C13Concrete.wotsDigitSum_ne_of_wotsGrindingFailsC13AtLayer_true
          (layer := 1) (pk := pk)
          (treeIdx := (digest.hyperIndex / 2048) / 2048)
          (leafIdx := (digest.hyperIndex / 2048) % 2048)
          (node := d.root0) (wots := d.lsig1.wots)
          d.hGrinding1
      have hExecNe1 :
          lookupValue
              (SegmentLayer3.afterDigit
                (c13SecondLayerGuardState pkSeed pkRoot message sig)).bindings
              "digitSum" ≠ 208 := by
        rw [(hDigit.2 d).2]
        simpa [pk, digest] using hNe1
      exact Or.inr ⟨hGuard0,
        SegmentLayer3.layerGuard_of_afterDigit_digitSum_ne
          (c13SecondLayerGuardState pkSeed pkRoot message sig) hExecNe1⟩

/-- C13 bridge reducer at the current concrete data boundary.  The proved
bad-length, forced-zero-false, FORS-totality, and no-`.rejected` facts are
discharged internally.  The remaining assumptions are exactly the concrete data
facts needed by the existing `.ok` and `.reverted` body bridges. -/
theorem c13_refines_byte_spec_of_current_node_and_reverted_guard_cover
    (hOkData :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        C13FoldOkCurrentNodeWordcmpData
          pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hRevertedData :
      ∀ pkSeed pkRoot message sig sigParsed forsPk,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .reverted →
        C13FoldRevertedGuardData pkSeed pkRoot message sig) :
    ByteLevel.ImplementsByteVerifier c13Primitives c13 execC13Concrete := by
  apply c13_refines_byte_spec_of_fold_result_cover
  · intro pkSeed pkRoot message sig sigParsed forsPk specRoot hParse hZero hFors hFold
    rcases hOkData pkSeed pkRoot message sig sigParsed forsPk specRoot
        hParse hZero hFors hFold with
      ⟨hGuard0, hCurrent0, hGuard1, hCurrent1, hWordCmp⟩
    exact
      C13BridgePrep.runC13BodyObserved_accept_from_fold_ok_current_nodes_wordcmp
        pkSeed pkRoot message sig sigParsed forsPk specRoot
        hParse hZero hFors hFold hGuard0 hCurrent0 hGuard1 hCurrent1 hWordCmp
  · intro pkSeed pkRoot message sig sigParsed forsPk hParse hZero hFors hFold
    have hg3 :
        SegmentS3.s3Guard
          (SegmentCompose.afterS2 (mkC13State pkSeed pkRoot message sig)) = 0 :=
      SegmentAcceptSpec.c13_s3Guard_of_parse_forcedZero
        pkSeed pkRoot message sig
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed rfl hParse hZero
    cases hRevertedData pkSeed pkRoot message sig sigParsed forsPk
        hParse hZero hFors hFold with
    | inl hFirst =>
        exact
          C13BridgePrep.runC13BodyObserved_revert_on_layer_first_guard_of_fold_reverted
            pkSeed pkRoot message sig sigParsed forsPk
            hParse hg3 (by simpa [c13FirstLayerGuardState] using hFirst)
            hZero hFors hFold
    | inr hSecond =>
        rcases hSecond with ⟨hGuard0, hGuard1⟩
        exact
          C13BridgePrep.runC13BodyObserved_revert_on_layer_second_guard_of_fold_reverted
            pkSeed pkRoot message sig sigParsed forsPk
            hParse hg3
            (by simpa [c13FirstLayerGuardState] using hGuard0)
            (by simpa [c13SecondLayerGuardState, c13FirstLayerGuardState] using hGuard1)
            hZero hFors hFold

/-- C13 bridge reducer with the accept branch left at the exact executable
word-comparison boundary, while the reverted branch is reduced from raw guard
facts to digit-sum correspondence facts.  This is the public-key-shape-free
counterpart of
`c13_refines_byte_spec_of_current_node_pkroot_size_and_reverted_digit_sum_cover`.
-/
theorem c13_refines_byte_spec_of_current_node_wordcmp_and_reverted_digit_sum_cover
    (hOkData :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        C13FoldOkCurrentNodeWordcmpData
          pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hRevertedDigitData :
      ∀ pkSeed pkRoot message sig sigParsed forsPk,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .reverted →
        C13FoldRevertedDigitSumData pkSeed pkRoot message sig sigParsed forsPk) :
    ByteLevel.ImplementsByteVerifier c13Primitives c13 execC13Concrete := by
  refine
    c13_refines_byte_spec_of_current_node_and_reverted_guard_cover
      hOkData ?_
  intro pkSeed pkRoot message sig sigParsed forsPk hParse hZero hFors hFold
  exact
    c13FoldRevertedGuardData_of_digit_sum_data
      pkSeed pkRoot message sig sigParsed forsPk hFold
      (hRevertedDigitData pkSeed pkRoot message sig sigParsed forsPk
        hParse hZero hFors hFold)

/-- C13 bridge reducer with the final comparison reduced to the byte-shape fact
`pkRoot.size = 16`.  This is the strongest currently useful no-axiom reducer:
all C13 branch splitting is internal, and the remaining `.ok` branch data is
guard/current-node correspondence plus the public-key-root width. -/
theorem c13_refines_byte_spec_of_current_node_pkroot_size_and_reverted_guard_cover
    (hOkData :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        C13FoldOkCurrentNodePkRootSizeData
          pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hRevertedData :
      ∀ pkSeed pkRoot message sig sigParsed forsPk,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .reverted →
        C13FoldRevertedGuardData pkSeed pkRoot message sig) :
    ByteLevel.ImplementsByteVerifier c13Primitives c13 execC13Concrete := by
  refine
    c13_refines_byte_spec_of_current_node_and_reverted_guard_cover ?_ hRevertedData
  intro pkSeed pkRoot message sig sigParsed forsPk specRoot hParse hZero hFors hFold
  rcases hOkData pkSeed pkRoot message sig sigParsed forsPk specRoot
      hParse hZero hFors hFold with
    ⟨hGuard0, hCurrent0, hGuard1, hCurrent1, hPkRootSize⟩
  refine ⟨hGuard0, hCurrent0, hGuard1, hCurrent1, ?_⟩
  exact
    SegmentAcceptSpec.wordCmp_of_wordOfHash16_rootMatchesPk_c13 specRoot pkRoot
      (SegmentAcceptSpec.specRoot_roundtrip_of_c13_fors_fold hFors hFold)

/-- C13 bridge reducer with the reverted branch reduced from raw guard-failure
facts to executable checksum correspondence facts. -/
theorem c13_refines_byte_spec_of_current_node_pkroot_size_and_reverted_digit_sum_cover
    (hOkData :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        C13FoldOkCurrentNodePkRootSizeData
          pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hRevertedDigitData :
      ∀ pkSeed pkRoot message sig sigParsed forsPk,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .reverted →
        C13FoldRevertedDigitSumData pkSeed pkRoot message sig sigParsed forsPk) :
    ByteLevel.ImplementsByteVerifier c13Primitives c13 execC13Concrete := by
  refine
    c13_refines_byte_spec_of_current_node_pkroot_size_and_reverted_guard_cover
      hOkData ?_
  intro pkSeed pkRoot message sig sigParsed forsPk hParse hZero hFors hFold
  exact
    c13FoldRevertedGuardData_of_digit_sum_data
      pkSeed pkRoot message sig sigParsed forsPk hFold
      (hRevertedDigitData pkSeed pkRoot message sig sigParsed forsPk
        hParse hZero hFors hFold)

/-- C13 bridge reducer after the executable checksum loop has been discharged:
callers now provide only the straight-line `"d"` digest bindings before the
43-iteration checksum fold. -/
theorem c13_refines_byte_spec_of_current_node_pkroot_size_and_reverted_before_digit_cover
    (hOkData :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        C13FoldOkCurrentNodePkRootSizeData
          pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hRevertedBeforeDigitData :
      ∀ pkSeed pkRoot message sig sigParsed forsPk,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .reverted →
        C13FoldRevertedBeforeDigitData pkSeed pkRoot message sig sigParsed forsPk) :
    ByteLevel.ImplementsByteVerifier c13Primitives c13 execC13Concrete := by
  refine
    c13_refines_byte_spec_of_current_node_pkroot_size_and_reverted_digit_sum_cover
      hOkData ?_
  intro pkSeed pkRoot message sig sigParsed forsPk hParse hZero hFors hFold
  exact
    c13FoldRevertedDigitSumData_of_before_digit_data
      pkSeed pkRoot message sig sigParsed forsPk
      (hRevertedBeforeDigitData pkSeed pkRoot message sig sigParsed forsPk
        hParse hZero hFors hFold)

/-- C13 bridge reducer at the corrected final-comparison boundary after the
executable checksum loop has been discharged: callers provide only the
straight-line `"d"` digest bindings before the 43-iteration checksum fold. -/
theorem c13_refines_byte_spec_of_current_node_wordcmp_and_reverted_before_digit_cover
    (hOkData :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        C13FoldOkCurrentNodeWordcmpData
          pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hRevertedBeforeDigitData :
      ∀ pkSeed pkRoot message sig sigParsed forsPk,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .reverted →
        C13FoldRevertedBeforeDigitData pkSeed pkRoot message sig sigParsed forsPk) :
    ByteLevel.ImplementsByteVerifier c13Primitives c13 execC13Concrete := by
  refine
    c13_refines_byte_spec_of_current_node_wordcmp_and_reverted_digit_sum_cover
      hOkData ?_
  intro pkSeed pkRoot message sig sigParsed forsPk hParse hZero hFors hFold
  exact
    c13FoldRevertedDigitSumData_of_before_digit_data
      pkSeed pkRoot message sig sigParsed forsPk
      (hRevertedBeforeDigitData pkSeed pkRoot message sig sigParsed forsPk
        hParse hZero hFors hFold)

/-- C13 bridge reducer after the executable checksum and pre-digest binding have
been discharged: callers provide only the four WOTS digest scratch words for
each reverting layer. -/
theorem c13_refines_byte_spec_of_current_node_pkroot_size_and_reverted_digest_scratch_cover
    (hOkData :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        C13FoldOkCurrentNodePkRootSizeData
          pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hRevertedScratchData :
      ∀ pkSeed pkRoot message sig sigParsed forsPk,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .reverted →
        C13FoldRevertedDigestScratchData pkSeed pkRoot message sig sigParsed forsPk) :
    ByteLevel.ImplementsByteVerifier c13Primitives c13 execC13Concrete := by
  refine
    c13_refines_byte_spec_of_current_node_pkroot_size_and_reverted_before_digit_cover
      hOkData ?_
  intro pkSeed pkRoot message sig sigParsed forsPk hParse hZero hFors hFold
  exact
    c13FoldRevertedBeforeDigitData_of_digest_scratch_data
      pkSeed pkRoot message sig sigParsed forsPk
      (hRevertedScratchData pkSeed pkRoot message sig sigParsed forsPk
        hParse hZero hFors hFold)

/-- C13 bridge reducer at the corrected final-comparison boundary after the
executable checksum and pre-digest binding have been discharged: callers provide
only the four WOTS digest scratch words for each reverting layer. -/
theorem c13_refines_byte_spec_of_current_node_wordcmp_and_reverted_digest_scratch_cover
    (hOkData :
      ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .ok specRoot →
        C13FoldOkCurrentNodeWordcmpData
          pkSeed pkRoot message sig sigParsed forsPk specRoot)
    (hRevertedScratchData :
      ∀ pkSeed pkRoot message sig sigParsed forsPk,
        C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
        forcedZeroOk c13
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
        C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          sigParsed.fors = some forsPk →
        foldHypertree C13Concrete.c13PrimitivesConcrete c13
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (C13Concrete.c13PrimitivesConcrete.hMsg c13
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
          forsPk sigParsed.layers = .reverted →
        C13FoldRevertedDigestScratchData pkSeed pkRoot message sig sigParsed forsPk) :
    ByteLevel.ImplementsByteVerifier c13Primitives c13 execC13Concrete := by
  refine
    c13_refines_byte_spec_of_current_node_wordcmp_and_reverted_before_digit_cover
      hOkData ?_
  intro pkSeed pkRoot message sig sigParsed forsPk hParse hZero hFors hFold
  exact
    c13FoldRevertedBeforeDigitData_of_digest_scratch_data
      pkSeed pkRoot message sig sigParsed forsPk
      (hRevertedScratchData pkSeed pkRoot message sig sigParsed forsPk
        hParse hZero hFors hFold)

/-- C12 bridge reducer: the full concrete C12 byte-refinement follows from its
good-length branch plus the proved malformed-length observable bridge. -/
theorem c12_refines_byte_spec_of_good_length_cover
    (hGood :
      ∀ pkSeed pkRoot message sig,
        sig.size = 6512 →
        execC12 pkSeed pkRoot message sig =
          ByteLevel.verifyBytes c12Primitives c12 pkSeed pkRoot message sig) :
    ByteLevel.ImplementsByteVerifier c12Primitives c12 execC12 := by
  intro pkSeed pkRoot message sig
  by_cases hLen : sig.size = 6512
  · exact hGood pkSeed pkRoot message sig hLen
  · exact execC12_agrees_verifyBytes_bad_length pkSeed pkRoot message sig hLen

/-- C12 bridge reducer after byte-length parsing.  The concrete C12 parser has
no good-length failure branch, so callers only need to cover parsed signatures. -/
theorem c12_refines_byte_spec_of_parsed_cover
    (hParsed :
      ∀ pkSeed pkRoot message sig sigParsed,
        SphincsMinusVerifierSpec.C12Concrete.parseSignatureC12 c12 sig
          = some sigParsed →
        execC12 pkSeed pkRoot message sig =
          ByteLevel.verifyBytes c12Primitives c12 pkSeed pkRoot message sig) :
    ByteLevel.ImplementsByteVerifier c12Primitives c12 execC12 := by
  apply c12_refines_byte_spec_of_good_length_cover
  intro pkSeed pkRoot message sig hLen
  have hLenC12 : sig.size = c12.sigBytes := by
    simpa [c12] using hLen
  obtain ⟨sigParsed, hParse⟩ :=
    SphincsMinusVerifierSpec.C12Concrete.parseSignatureC12_some_of_size
      (v := c12) (sig := sig) hLenC12
  exact hParsed pkSeed pkRoot message sig sigParsed hParse

/-- C12: on the length-ok branch, byte-level verification reaches the parsed
verifier under the concrete C12 primitive package.  This is the C12 analogue of
the C13 parser bridge in `C13BridgePrep`. -/
theorem c12_verifyBytes_eq_verifyParsed_of_length
    (pkSeed pkRoot message sig : Bytes)
    (hLen : sig.size = c12.sigBytes) :
    ∃ sigParsed,
      SphincsMinusVerifierSpec.C12Concrete.parseSignatureC12 c12 sig = some sigParsed ∧
      ByteLevel.verifyBytes c12Primitives c12 pkSeed pkRoot message sig =
        verifyParsed SphincsMinusVerifierSpec.C12Concrete.c12PrimitivesConcrete c12
          { pkSeed := pkSeed, pkRoot := pkRoot } message sigParsed := by
  obtain ⟨sigParsed, hParse⟩ :=
    SphincsMinusVerifierSpec.C12Concrete.parseSignatureC12_some_of_size
      (v := c12) (sig := sig) hLen
  refine ⟨sigParsed, hParse, ?_⟩
  unfold ByteLevel.verifyBytes
  simp [hLen, SphincsMinusVerifierSpec.C12Concrete.parsePublicKey_c12,
    c12Primitives, SphincsMinusVerifierSpec.C12Concrete.c12PrimitivesConcrete,
    hParse]

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
      rootMatchesPk v root pk.pkRoot = true := by
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
      rootMatchesPk c13 root pk.pkRoot = true :=
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
      rootMatchesPk c12 root pk.pkRoot = true :=
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
      rootMatchesPk slhDsaSha2_128_24 root pk.pkRoot = true :=
  exec_accepts_sound slhDsaSha2_128_24_refines_byte_spec pkSeed pkRoot message sig hAcc

/--
Compilation-model presence checks.  These are small regression anchors: if the
models are renamed or removed, the refinement file stops compiling before any
semantic proof attempt starts.
-/
example : c13Model.name = "SphincsC13Asm_VerityModel" := rfl
example : c12Model.name = "SPHINCs_C12Asm_VerityModel" := rfl
example : slhDsaSha2_128_24_Model.name = "SLH_DSA_SHA2_128_24_VerityModel" := rfl

#print axioms c13_refines_byte_spec_of_good_length_cover
#print axioms c13_refines_byte_spec_of_forced_zero_true_cover
#print axioms c13_refines_byte_spec_of_fors_some_cover
#print axioms c13_refines_byte_spec_of_fold_result_cover
#print axioms c13FirstLayerGuardState_eq_c13LayerLoopState0
#print axioms c13SecondLayerGuardState_eq_c13LayerLoopState1
#print axioms c13FoldOkCurrentNodePkRootSizeData_of_current_node_facts
#print axioms c13FoldOkCurrentNodeWordcmpData_of_current_node_facts
#print axioms c13FoldOkCurrentNodeWordcmpData_of_two_step_obligations
#print axioms c13_refines_byte_spec_of_current_node_and_reverted_guard_cover
#print axioms c13_refines_byte_spec_of_current_node_wordcmp_and_reverted_digit_sum_cover
#print axioms c13_refines_byte_spec_of_current_node_pkroot_size_and_reverted_guard_cover
#print axioms c13FoldRevertedBeforeDigitData_of_digest_scratch_data
#print axioms c13FoldRevertedDigitSumData_of_before_digit_data
#print axioms c13FoldRevertedGuardData_of_digit_sum_data
#print axioms c13_refines_byte_spec_of_current_node_pkroot_size_and_reverted_digit_sum_cover
#print axioms c13_refines_byte_spec_of_current_node_pkroot_size_and_reverted_before_digit_cover
#print axioms c13_refines_byte_spec_of_current_node_pkroot_size_and_reverted_digest_scratch_cover
#print axioms c13_refines_byte_spec_of_current_node_wordcmp_and_reverted_before_digit_cover
#print axioms c13_refines_byte_spec_of_current_node_wordcmp_and_reverted_digest_scratch_cover
#print axioms c12_refines_byte_spec_of_good_length_cover
#print axioms c12_refines_byte_spec_of_parsed_cover

end SphincsMinusVerifiers
