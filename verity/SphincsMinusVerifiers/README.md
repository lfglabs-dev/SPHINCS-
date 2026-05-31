# SPHINCS- Verity Models

This folder is the verification workbench for the three verifier contracts in
`src/`:

- `SphincsC13Asm_VerityModel` models `SPHINCs-C13Asm.sol`.
- `SPHINCs_C12Asm_VerityModel` models `SPHINCs-C12Asm.sol`.
- `SLH_DSA_SHA2_128_24_VerityModel` models `SLH-DSA-SHA2-128-24verifier.sol`.

The specs are layered in `SphincsMinusVerifierSpec/Spec.lean`:

- `verifyParsed` is the algorithmic spec over a parsed public key and parsed
  signature.
- `ByteLevel.verifyBytes` is the contract-facing spec for `pkSeed`, `pkRoot`,
  `message`, and `sig` bytes.  It owns signature length checks, public-key
  canonicality, signature parsing, and malformed-input behavior.
- `Model.lean` is the Verity implementation model.  It owns memory layout,
  scratch offsets, loops, low-level calls, and raw-Yul revert boundaries.

`Proofs.lean` contains **no `sorry`**.  The per-verifier refinement theorems are
unconditional; their only model-specific assumptions are three explicitly named
bridge axioms.

- `byteVerifier_refines_spec` proves, for *any* observable semantics `exec`,
  that a byte-level refinement composes with `verifyBytes_eq_verifySpec` into an
  abstract-spec refinement.  This is fully proved (`#print axioms` → `propext`).
- `c13_refines_byte_spec`, `c12_refines_byte_spec`, and
  `slhDsaSha2_128_24_refines_byte_spec` are **named axioms**: each asserts that
  one compiled Verity model refines its byte-level spec.  They are the Lean-level
  form of the `proofStatus := .assumed` local obligations already attached to the
  models in `Model.lean`, and they sit in the trust surface alongside the repo's
  keccak collision-resistance axioms.
- `c13_refines_spec`, `c12_refines_spec`, and `slhDsaSha2_128_24_refines_spec`
  (and their `*_implements_spec` forms) then conclude the abstract-spec
  refinement for each compiled model unconditionally, by feeding the matching
  bridge axiom into `byteVerifier_refines_spec`.

The primitive packages are deliberately not universally quantified: C13, C12,
and SHA2 use different hash/address/signature parsing semantics, and a single
compiled verifier cannot refine every possible `Primitives` instance.

The proof chain is:

```text
Verity implementation model
  refines                       ← assumed: *_refines_byte_spec axioms (MODEL-EXEC-BRIDGE)
ByteLevel.verifyBytes
  refines by construction       ← proved: byteVerifier_refines_spec
verifyParsed
```

## Current Fidelity

`Model.lean` uses Verity's ABI-aware `Bytes` parameter locals:

- `sig_length` corresponds to Solidity assembly `sig.length`.
- `sig_data_offset` corresponds to Solidity assembly `sig.offset`.

The C13 model expands the main Hmsg, FORS+C, WOTS+C, and hypertree assembly
shape in the Verity EDSL.  It preserves the scratch-memory addresses, masks,
loop bounds, digest bit extraction, branchless Merkle swaps, and final
`mstore(0x00, valid); return(0x00, 0x20)` behavior.

The C12 model expands the plain FORS, FORS-root compression, WOTS+ checksum and
chains, WOTS public-key compression, and five XMSS layers.  It follows the
Solidity memory offsets and signature offsets directly.

The SHA2 model expands the Hmsg precompile calls, FORS, WOTS+, WOTS public-key
compression, and XMSS climb.  It is structurally line-by-line, but it still
depends on a Verity-level SHA-256 precompile postcondition before the proof can
connect `mload` of the output buffer to the digest written by precompile `0x02`.

## Blockers

- `SHA2-PRECOMPILE`: the SHA2 verifier relies on repeated `staticcall(gas(),
  0x02, ...)`.  Verity can emit precompile calls, but the proof needs a stable
  postcondition tying output memory to SHA-256 over the exact input slice.
- `SHA2-PACKED-MEMORY`: the SHA2 verifier writes 16-byte values at unaligned
  offsets such as `0x56` and `0x66`.  The model can express this, but proofs need
  byte-slice memory lemmas, not just word-oriented `mstore` reasoning.
- `RAW-YUL-FIDELITY`: addressed on the companion Verity branch by adding typed
  `Stmt.unsafeYul` / `RawYul` fragments.  The models use this for Solidity
  `revert(0,0)` and for the hand-written `Error(string)` length/public-key
  checks, with local obligations attached at each raw-Yul boundary.  Remaining
  revert work is proving exact observable revert-data equivalence in Verity's
  executable semantics.
- `INLINE-YUL-FRONTEND`: this repository needs either direct inline-Yul syntax
  in Verity or an importer from Solidity/Yul into `CompilationModel.Stmt` /
  `Compiler.Yul.YulStmt`.  Hand translation is now present for all three linked
  verifiers, but it remains too error-prone for long-term maintenance.
- `MODEL-EXEC-BRIDGE`: the model-to-byte refinement is currently the named axiom
  `*_refines_byte_spec` for each verifier.  Replacing the axiom with a proof
  requires running Verity's compiled-contract executable semantics
  (`Compiler/.../SourceSemantics.lean`: `execStmtList` / `execStmt` / `evalExpr`
  over a `RuntimeState`) on each `*VerifyBody` and proving the result equals
  `ByteLevel.verifyBytes`.  That interpreter *does* model the raw calldata surface
  (`evalExpr` handles `.calldataload` / `.calldatasize` / `.param` / `.localVar`),
  so the reject/revert subdomain is provable through it (see below).  The
  **accept** subdomain now splits by hash family.  `SourceSemantics.lean`'s
  `evalExpr` models the native `keccak256` opcode as the *computed* 32-byte
  digest of the word-aligned memory slice (`keccakMemorySlice`, backed by the
  in-tree pure `KeccakEngine`) — no longer `none`.  So the **keccak-family**
  bodies (C13, C12) no longer revert at their first hash; their accept subdomain
  is *reachable* through the real interpreter, and the residual work there is
  proof size: the line-by-line equivalence of the full hypertree climb against
  `ByteLevel.verifyBytes`, a self-contained proof effort inside this workbench.
  The **SHA-256 precompile** (`staticcall` to `0x02`) is still modeled as `none`
  (`evalExpr_staticcall = none`): a faithful model is blocked by the word-keyed
  `RuntimeState` memory vs. the SLH-DSA body's overlapping sub-word `mstore`s
  (the `linear_memory_aliasing` obligation), so the SHA-2 body still reverts at
  its first precompile call and that accept subdomain stays out of reach pending
  a byte-addressed memory model (`SHA2-PRECOMPILE`).

  **Proved slice (sound, machine-checked).**  `Model.lean` now discharges one
  unconditional piece of this bridge directly through the interpreter:
  `c13VerifyBody_reverts_on_bad_length`, `c12VerifyBody_reverts_on_bad_length`,
  and `slhDsaSha2VerifyBody_reverts_on_bad_length` prove that running the *actual*
  compiled body (with the production `fields := []` layout) **reverts** whenever
  the ABI-decoded `sig_length` local is not the verifier's expected signature
  length (3688 / 6512 / 3856).  These run the real `execStmtList`/`execStmt`/
  `evalExpr` over the `*VerifyBody` terms — no `exec... := verifyBytes` shortcut,
  no `sorry`.  `#print axioms` shows only Lean's foundational
  `[propext, Classical.choice, Quot.sound]` (no `sorryAx`, no bridge axiom).  This
  is the length-guard fragment of the eventual `define exec... ; prove
  *_refines_byte_spec` programme; the accept path remains the carried axiom.

  The dual direction — the first **accept**-path step — is also discharged:
  `c13VerifyBody_passes_length_guard`, `c12VerifyBody_passes_length_guard`, and
  `slhDsaSha2VerifyBody_passes_length_guard` prove that when `sig_length` *does*
  equal the expected length the guard is a no-op (`evalExpr` returns `0`, the
  else-branch is `[]`) and the real interpreter falls through to the body tail
  (`execStmtList [] st body = execStmtList [] st body.tail`).  Same axiom
  footprint (`[propext, Classical.choice, Quot.sound]`, no bridge axiom).  These
  make the accept subdomain *reachable* — the precondition for the keccak-family
  climb-equivalence proof that replaces the carried axiom.

  **Accept-path keccak step (`Model.lean`).**  Two further unconditional lemmas
  carry the accept path past its first hash.  `execStmtList_cons_continue` is the
  forward continue-step combinator (dual of `execStmtList_cons_revert`): a head
  statement that steps to `.continue st'` advances the interpreter to `st'` over
  the tail.  `c13_keccak_letVar_binds_real_digest` then runs the *actual* C13 Hmsg
  keccak statement (`.letVar "digest" (.keccak256 (.literal 0x00) (.literal 0xA0))`)
  through the real `execStmt`/`evalExpr` and proves the bound local `"digest"`
  equals `keccakMemorySlice st.world.memory 0 0xA0` — the **genuine** Keccak-256
  digest of the 0xA0-byte input slice, not `none`/revert.  This is the concrete
  payoff of modeling `keccak256` in `evalExpr`: the accept path's first hash is now
  *computed*.  Same axiom footprint (`[propext, Classical.choice, Quot.sound]`, no
  bridge axiom).  Threading the full straight-line prefix end-to-end into a single
  reachability term is deferred — not for soundness reasons but because the
  per-statement `whnf` cost of the interpreter over the giant `c13VerifyBody` term
  makes the closed-form composition heartbeat-prohibitive; the step combinator plus
  this digest lemma capture the same content compositionally.

  **Bytes-level two-sided agreement (`Proofs.lean`).**  The interpreter-side
  revert lemmas above are lifted to the `Bytes` boundary and paired with the
  spec-side `ByteLevel.verifyBytes_bad_length` into
  `c13_interp_agrees_verifyBytes_bad_length`,
  `c12_interp_agrees_verifyBytes_bad_length`, and
  `slhDsaSha2_128_24_interp_agrees_verifyBytes_bad_length`.  Each proves that, on a
  concrete `RuntimeState` (`badLenState`) whose ABI-decoded `sig_length` local is
  the calldata signature length, a wrong length makes the *real* compiled body run
  `execStmtList ... = .revert` **and** makes `ByteLevel.verifyBytes ... = none` —
  i.e. the compiled model and the byte spec *agree* (both reject) across the entire
  malformed-length subdomain.  This is a genuine slice of the `*_refines_byte_spec`
  equality, *proved* over a concrete state rather than assumed.  `#print axioms`:
  `[propext, Classical.choice, Quot.sound, <variant>Primitives]` — **no bridge
  axiom, no `sorryAx`** (the `Primitives` constant appears only in the statement's
  `verifyBytes` arguments).  The accept path remains the carried axiom.

## Build

```bash
cd verity
lake build SphincsMinusVerifiers
```

Expected status right now: build succeeds with **no `sorry` warnings**.
`Proofs.lean` proves `byteVerifier_refines_spec` outright and derives the
unconditional per-verifier `*_refines_spec` theorems from the three named
`*_refines_byte_spec` bridge axioms (MODEL-EXEC-BRIDGE).
