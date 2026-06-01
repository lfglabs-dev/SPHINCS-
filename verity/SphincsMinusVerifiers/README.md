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

**Phase 0 (STRATEGY §1) — concrete C13 primitives (done).** `c13Primitives` is
no longer `axiom c13Primitives : Primitives`; it is now
`def c13Primitives := C13Concrete.c13PrimitivesConcrete`
(`SphincsMinusVerifierSpec/C13Concrete.lean`), whose every hash is routed through
the SAME pure `KeccakEngine.keccak256` over the SAME big-endian word-aligned
preimage the Verity interpreter feeds it (`memorySliceBytesBE` /
`byteArrayToNatBE`). This is the go/no-go gate for the model→byte bridge: the
spec's hash is now a concrete equation the bridge proof can rewrite against,
rather than an opaque constant with no connection to the interpreter's keccak.
`#print axioms c13_refines_spec` is now
`[propext, Quot.sound, c13_refines_byte_spec]` — the opaque `c13Primitives`
axiom is **gone**; only the MODEL-EXEC-BRIDGE bridge axiom remains. `c12Primitives`
and `slhDsaSha2_128_24_Primitives` are still axioms (C12 pending Phase 4; SHA-2
out of scope).

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

  **Accept-path segment threading (Phase-2 bricks, axiom-clean).**  The
  straight-line/loop body of `c13VerifyBody` is now decomposed into per-segment
  control-flow lemmas, each proved against the *real* `execStmtList`/`execStmt`/
  `evalExpr` over the actual statement slice (machine-checked faithful by a `rfl`
  `*_eq_slice` against `c13VerifyBody.drop k |>.take n`), each axiom-clean
  (`[propext, Classical.choice, Quot.sound]`, no `sorry`, no bridge axiom):

  - `SegmentS2.execS2` — H_msg digest block, stmts 1..9, `→ .continue (s2Step ·)`.
  - `SegmentS3.execSegmentS3` — htIdx/dVal/forced-zero-guard/sigBase, stmts 10..13,
    `→ if s3Guard = 0 then .continue (stepS3 ·) else .revert`.
  - `SegmentS4Fors.execForsOuter` — FORS tree-root `forEach "i" 6`, stmt 14,
    `→ .continue (foldLoop "i" forsLeafStep ·)` via the generic `ClimbLoop` engine.
  - `SegmentS4Finalize.execForsFinalize` — FORS finalize block (forced 7th leaf,
    copy loop, forsPk), stmts 15..21, `→ .continue (forsFinalizeStep ·)`.
  - `SegmentSeed.execSegmentSeed` — currentNode/idxTree/sigOff seed, stmts 22..24,
    `→ .continue (stepSeed ·)`.
  - `SegmentLayer3.execLayerLoop` — the hypertree-climb `forEach "layer" 2`,
    stmt 25, the only *guarded* loop (the WOTS checksum `digitSum = 208` guard
    mid-body).  Its body lemma `execLayerBody` proves
    `execStmtList [] ls layerBody = if layerGuard ls then .continue (stepLayer ls)
    else .revert`, and `execLayerLoop` lifts it across the loop via the new
    guarded loop-threading engine `ClimbLoopGuarded.execStmt_forEach_of_guarded_step`
    (`execForEachLoop_of_guarded_step` + `allGuardsPass`), folding to a pure
    `foldLoop "layer" stepLayer` once the per-iteration guards are discharged.

  - `SegmentCompose.execC13Body_thread` — the **full-body composition**.  Under
    the length guard, the FORS forced-zero guard, and the WOTS-checksum climb
    guards, it threads all six segment lemmas in sequence (a machine-checked
    `body_reshape` `rfl` re-associates `c13VerifyBody` into the named segments),
    reducing the entire `c13VerifyBody` run to the 3-statement return tail
    (`drop 26`) over one composite accept state `afterLayer st`.  It touches
    neither `execC13` nor the bridge axiom — pure control-flow backbone,
    `#print axioms` → `[propext, Classical.choice, Quot.sound]`.
  - `SegmentCompose.execC13Body_returns` — threads the 3-statement return tail
    (`letVar "valid" (currentNode == root)`, `mstore`, `return mload`) on top of
    `execC13Body_thread`, reducing the **entire** body to a single
    `.return (wordNormalize (acceptWord st)) finalState`, where `acceptWord st`
    is the EVM boolean word of the final `currentNode == root` comparison.  This
    closes the control-flow side **end-to-end** (body ⟶ returned boolean); the
    sole remaining obligation is the data correspondence: `acceptWord st` equals
    `ByteLevel.verifyBytes`'s accept decision.  Also axiom-clean.
  - `SegmentAcceptSpec.accept_path_returns_verifyParsed_bool` — the Phase-3
    **compose stub** (STRATEGY §2, "stub the compose early to catch drift").  It
    pins `execC13Body_returns`'s output to the **spec** side: under the three
    control-flow guards AND one explicit hypothesis `hCmp` (the model's final
    `currentNode == root` word comparison decides the same boolean
    `verifyParsed c13PrimitivesConcrete c13 …` returns), the whole-body run over
    `mkC13State …` returns the EVM-word encoding of exactly that boolean.  `hCmp`
    is the residual Phase-3b data-correspondence obligation surfaced as a named
    hypothesis — it is **not** discharged here.  Phrased against the real
    `verifyParsed`/`mkC13State`/`c13VerifyBody` defs so any return-shape or
    accept-shape drift breaks compilation.  Touches neither `execC13` nor the
    bridge axiom; `#print axioms` → `[propext, Classical.choice, Quot.sound]`.

  - `ClimbLoop.foldLoop_preserves_lookup` — the Phase-3b *frame* engine.  Given a
    `step` that preserves some binding `key` and a loop variable `varName ≠ key`,
    the whole `foldLoop` carries that binding through every iteration untouched.
    It never evaluates a bound *value* (so it composes loops over keccak-laden
    step transformers without forcing them); proved by induction on the iteration
    count.  This is the reusable tool a `"root"`-binding correspondence
    (`lookupValue (afterLayer st).bindings "root" = wordOfHash16 pkRoot`) is built
    on, once the per-step bindings-frame lemmas for the `match execStmtList` step
    forms (`s2Step` sets `root`; `forsLeafStep`/`stepLayer` preserve it) are in
    hand.  Axiom-clean.

  - `ClimbLoop.{specFold, foldLoop_invariant}` — the Phase-3b *correspondence*
    engine (the `frame`'s counterpart).  `specFold specStep a index remaining` is the
    pure spec-side image of `foldLoop` (the `Nat` index carries the loop counter the
    spec address words depend on).  `foldLoop_invariant` folds a relation
    `R : RuntimeState → α → Prop` through `foldLoop` and `specFold` in lockstep,
    reducing the *entire* climb-loop correspondence to one per-iteration preservation
    hypothesis `hstep` (the interpreter's `step`, after the loop-variable bind,
    advances `R` together with the spec step).  This is the induction skeleton the
    eventual Merkle/WOTS/FORS climb proof plugs into: instantiate `α` with the spec
    `(h, mIdx, node)` tuple, `specStep` with the `xmssClimb`/`forsClimb`/`chainHash`
    step, and discharge `hstep` from the `ClimbMemFrame*` per-step value lemmas
    (`merkle_keccak_value_spec_even/odd`, `stepWots_keccak_value`).  The engine itself
    is a clean `Nat`-induction, axiom-clean (`[propext]`); discharging `hstep` for the
    concrete relation (which requires propagating the per-component value hypotheses —
    `(base 0x00).val = seed`, `wordNormalize vadr = adrs`, … — through the loop
    invariant) is the residual open work (#20).

  - `ClimbLoop.foldLoop_invariant_cond` — the *conditional* climb-induction engine:
    same fold skeleton as `foldLoop_invariant`, but the per-iteration `hstep` may depend
    on an index-indexed data predicate `D : Nat → Prop`, and the whole-climb conclusion is
    gated on `D` holding across the climb range (`∀ i, index ≤ i → i < index + remaining →
    D i`).  This is the honest shape for the climb: `ClimbMemFrameMerkle.MerkleClimbRel_step`
    needs a per-iteration data bundle (`StepDataObligations`, bottoming out at the masked
    calldata word at `authPtr+16·i` = `wordOfHash16 auth[i]` — blocker #20), and that
    obligation is *naturally indexed by climb height*.  With this engine the entire climb
    threads `R` with `specFold` conditional on exactly a *range* of those per-iteration data
    facts — collapsing blocker #20 for the whole loop into the single range hypothesis,
    rather than re-deriving it per iteration.  `D := fun _ => True` recovers
    `foldLoop_invariant`.  Pure `Nat`-induction, axiom-clean (`[propext, Quot.sound]`).

  - `BindingFrame.*` — the keccak-free per-statement / per-list / per-`forEach`
    bindings-frame kit that supplies exactly those per-step lemmas.  Every lemma
    `cases`-es on the *abstract* `evalExpr [] st e` result, so a body the loop
    never *reads* (e.g. `"root"`, written once in S2) is carried through untouched
    without forcing the body's keccak values (STRATEGY §5 risk #1).
    `execStmt_letVar_preserves_lookup` / `execStmt_assignVar_preserves_lookup`
    (key ≠ written name) and `execStmt_mstore_preserves_lookup` (mstore touches
    only `world.memory`) are the straight-line bricks;
    `execStmtList_preserves_lookup` lifts them over any body by induction;
    `execForEachLoop_preserves_lookup` + `execStmt_forEach_preserves_lookup`
    compose with `ClimbLoop.foldLoop_preserves_lookup` for loop-containing bodies.
    All six axiom-clean (`[propext, Classical.choice, Quot.sound]`).

  - `RootFrame.stepLayer_preserves_root` — the first *consumer* of the
    `BindingFrame` kit: one accepting Layer-3 hypertree-climb iteration carries the
    `"root"` binding through untouched.  `root` is written exactly once (in S2,
    `Model.lean:101`) and the layer body never touches it, so this is proved
    keccak-free by discharging a per-statement `"root"`-frame for every body in the
    iteration — `prefix11`, `suffix14`, and the inner `digitSum`/`wotsChain`/
    `wotsOuter`/`copy`/`merkleClimb` loop bodies (the loop variables `"ii"`/`"i"`/
    `"h"`/`"step"` and the climb's `"merkleNode"`/`"mIdx"` are all literally
    distinct from `"root"`).  `RootFrame.afterLayer_preserves_root` then composes
    this per-iteration frame over the whole guarded `forEach "layer"` fold via
    `ClimbLoop.foldLoop_preserves_lookup`, giving
    `lookupValue (afterLayer st).bindings "root" = lookupValue (afterSeed st).bindings "root"`.

  - `RootFrame.afterLayer_root_eq_afterS2` — the bounded half of the residual
    `hCmp` obligation, now **fully closed** across the entire post-S2 path.  The
    per-segment frames `afterSeed_preserves_root` (Seed setup),
    `afterFinalize_preserves_root` (FORS finalize compression block),
    `afterFors_preserves_root` (the FORS outer `forEach "i"` fold over
    `forsLeafStep`, whose body contains the inner `merkleClimb` loop),
    `afterS3_preserves_root` (the S3 forced-zero guard's direct `bindValue`
    chain), and `afterLayer_preserves_root` (above) compose by `rw` into
    `lookupValue (afterLayer st).bindings "root" = lookupValue (afterS2 st).bindings "root"`.
    Every segment body writes only names literally distinct from `"root"`
    (`"sigBase"`/`"dVal"`/`"htIdx"`, `"sigOff"`/`"idxTree"`/`"currentNode"`, the
    FORS leaf/finalize locals, the loop vars `"i"`/`"h"`/`"layer"`/`"step"`), so the
    whole chain is proved keccak-free by the `BindingFrame` kit.  `root` is written
    exactly once (in S2, `Model.lean:101`) and never touched again, so the `root`
    operand of the final `currentNode == root` compare provably still holds its
    post-S2 `pkRoot` value at the moment of comparison.
    The *other* half — that `currentNode` equals the spec's climbed root — is the
    keccak data correspondence and stays open.  Axiom-clean
    (`[propext, Classical.choice, Quot.sound]`).

  - `RootFrame.afterLayer_root_mkC13State` — the **bounded (right-operand) half of
    the residual `hCmp` is now fully closed** over the frozen Phase-1 entry.
    Composing `afterLayer_root_eq_afterS2` (above) with
    `SegmentS2.s2Step_root_mkC13State` (S2 binds `root` to `wordOfHash16 pkRoot`,
    via `MkC13State.mkC13State_resolves_pkRoot`) gives
    `lookupValue (afterLayer (mkC13State pkSeed pkRoot message sig)).bindings "root" = wordOfHash16 pkRoot`
    — i.e. at the final `currentNode == root` compare the right operand provably
    holds the public key's root word.  `afterS2 = s2Step` definitionally, so the
    two compose by a single `rw`.  Axiom-clean
    (`[propext, Classical.choice, Quot.sound]`).  **Only the left operand
    (`currentNode` = the spec's climbed root, the keccak data correspondence) now
    stands between the frame work and the bounded `hCmp`; that half stays open and
    keeps `c13_refines_byte_spec` an `axiom`.**

  - `SegmentLayer3.stepLayer_currentNode_eq_merkleNode` — the first Phase-3b
    sub-brick on the *left* operand.  `suffix14`'s last two statements are
    `currentNode := merkleNode; sigOff := …`, and neither reassigns `merkleNode`, so
    `lookupValue (stepLayer ls).bindings "currentNode" = lookupValue (stepLayer ls).bindings "merkleNode"`
    — the compare's left operand is the Merkle-climb `forEach "h"` output, pinned
    *structurally* (the climbed value is an opaque bound term, peeled by key only, no
    keccak evaluated).  Axiom-clean (`[propext, Classical.choice, Quot.sound]`).  This
    isolates the remaining open obligation precisely: identify that climbed
    `merkleNode` term with the abstract spec's `foldHypertree`/`xmssRootFromSig` root.
    That value identification is the genuine keccak data correspondence (the FORS
    double-loop feeding `wotsPk`, then the 11-step XMSS climb per layer, across both
    hypertree layers) — months-scale per STRATEGY §5, and the sole remaining blocker
    before `c13_refines_byte_spec` can flip from `axiom` to `theorem`.

  - `ClimbStepSpec.{xmssClimb_succ, xmssClimb_zero, forsClimb_succ, forsClimb_zero}`
    — the **spec-side induction anchors** for that open correspondence.  Each names
    the per-iteration combine the fuel-bounded climb applies
    (`xmssClimbStep`/`forsClimbStep`: `maskN (keccakWords [seed, adrs, node, sibling])`
    branchless-swapped by index parity) and proves the fuel-`succ`/`zero` unfold by
    `simp only` on the climb def — no keccak evaluated.  These are the exact shape the
    interpreter's `merkleClimbBody` realises (`nodeVar := (keccak 0x00 0x80) & N_MASK`
    over the `0x40^s`/`0x60^s`-swapped scratch); the remaining work is to match *one*
    interpreter `stepMerkle`/`forsLeafStep` to *one* `xmssClimbStep`/`forsClimbStep`
    (forcing the keccak over the swapped memory) and fold by induction on fuel through
    these `_succ` equations.  Spec-only, asserts nothing about the interpreter.
    Axiom-clean (`[propext, Quot.sound]`).

  - `ClimbKeccakStep.{evalExpr_bitAnd_literal, evalExpr_maskedKeccak_eq_maskN}`
    — the **masking glue** that closes the gap between the interpreter's
    `and(keccak256(off, 32*k), N_MASK)` and the spec's `maskN (keccakWords ws)`.
    `evalExpr_bitAnd_literal` proves the interpreter's `Uint256.and` (which reduces
    mod 2^256) is the identity on already-`< 2^256` operands, so `and(e, literal m)`
    is `Nat.land k m`.  `evalExpr_maskedKeccak_eq_maskN` composes that with
    `KeccakBridge.evalExpr_keccak256_eq_keccakWords`: given the covered scratch cells
    hold `ws`, the real interpreter resolves the masked keccak to exactly
    `maskN (keccakWords ws)`.  This is the single reusable *combine* each per-step
    Merkle/FORS/WOTS keccak correspondence consumes — it evaluates no keccak and
    leaves the memory-frame (which words sit in scratch) as the open hypothesis
    `hmem`.  Axiom-clean (`[propext, Classical.choice, Quot.sound]`).

  - `ClimbKeccakStep.{evalExpr_bitOr_bounded, evalExpr_shl_bounded, evalExpr_shr_bounded, evalExpr_add_bounded}`
    — the **address-word combinators**, the `or`/`shl`/`shr`/`add` analogues of
    `evalExpr_bitAnd_literal`.  The spec kernel assembles each tweak's ADRS word as
    `treeAdrs ||| ((h+1) <<< 32) ||| parentIdx`; the matching interpreter terms are
    `bitOr`/`shl`/`add`, whose `Uint256.or`/`Uint256.shl`/`Uint256.add` reduce mod
    `2^256`.  `evalExpr_bitOr_bounded` shows that on `< 2^256` operands `or(a,b)`
    resolves to bare `Nat.lor k l` (outer mod killed by `Nat.bitwise_lt_two_pow`);
    `evalExpr_shl_bounded` shows `shl(s,v)` resolves to `v <<< s` once the shifted
    result is supplied `< 2^256`; `evalExpr_shr_bounded` shows `shr(s,v)` resolves to
    `v >>> s` with no extra bound (`v >>> s ≤ v`), resolving stmt 2's
    `parentIdx = idxVar >>> 1`; `evalExpr_add_bounded` shows `add(a,b)` resolves to
    `k + l` once the sum is supplied `< 2^256` (for the additively-assembled sub-words
    `h+1`, `digit+step`).  Each keeps its bound as an explicit hypothesis so the caller
    discharges it from the concrete tiny literals when the real ADRS AST is known (part
    of the open `R`/`hstep` assembly, #20 — the combinators themselves assert nothing
    about that AST).  Axiom-clean (`[propext, Classical.choice, Quot.sound]`).

  - `ClimbKeccakStep.evalExpr_merkleAdrsWord`
    — the **composed ADRS-word resolution**, connecting the three combinators above
    to the *actual* climb-body AST.  `ClimbKit.merkleClimbBody` stmt 3 assembles the
    per-step ADRS word as the interpreter term
    `or(adrsBase, or(shl(32, add(h, 1)), parentIdx))` — note the interpreter nests the
    `or` **right**-associatively, while the spec's `treeAdrs ||| ((h+1)<<<32) ||| pi`
    parses **left**-associatively.  This lemma threads `add`→`shl`→`bitOr`→`bitOr`
    (resolving the `0x20`-literal shift and the `h+1` increment from `wordNormalize`)
    and bridges the associativity gap with `Nat.lor_assoc`, landing exactly the spec's
    left-assoc `Nat.lor (Nat.lor tb ((h+1)<<<32)) pi`.  Operands stay generic
    (`baseE`/`hE`/`piE`) so the single lemma serves both the XMSS and FORS climbs (which
    share `merkleClimbBody`); the `< 2^256` operand/shift bounds are explicit hypotheses
    the per-step `R`/`hstep` will discharge from the concrete word ranges.  This closes
    the *interpreter-side* ADRS-word identity — one of the value sub-identities the open
    #20 `hstep` needs (the still-open remainder being the sibling/chain-word
    `calldataload`↔`wordOfHash16 auth[h]` correspondence and `R`-maintenance across
    iterations).  Axiom-clean (`[propext, Classical.choice, Quot.sound]`).

  - `ClimbKeccakStep.evalExpr_maskedCalldata`
    — the **masked-calldata sibling word**, the `calldataload` twin of
    `evalExpr_maskedKeccak_eq_maskN`.  `ClimbKit.merkleClimbBody` stmt 1 binds the
    climb's sibling as `and(calldataload(authPtr + (4 << h)), N_MASK)` — a raw
    signature word masked to its high 16 bytes, matching the spec kernel's
    `wordOfHash16 ((auth[h]?).getD ⟨#[]⟩)`.  This lemma proves the *masking* half:
    once the `calldataload` resolves to some `cw < 2^256`, the masked term is
    `maskN cw` (same bounded-`Uint256.and` identity, specialised to the calldata
    operand).  It deliberately leaves *which* word `cw` is — and the deeper
    `cw = wordOfHash16 auth[h]` source→model data correspondence — as the open
    hypothesis `hcw`, which is the still-unproved #20 obligation (the contract reads
    the auth path straight from the raw `bytes`-calldata surface; relating that to the
    abstract `auth : List Bytes` is the months-scale fidelity gap).  Together with
    `evalExpr_merkleAdrsWord` this closes the *interpreter-side* halves of both operands
    the per-step `R`/`hstep` feeds into the keccak combine; the open remainder is the
    data correspondence behind `hcw` and `R`-maintenance across iterations.  Axiom-clean
    (`[propext, Classical.choice, Quot.sound]`).

  - `ClimbKeccakStep.evalExpr_siblingOffset`
    — the **sibling calldata-offset** that `evalExpr_maskedCalldata`'s `offE` reads
    from (`ClimbKit.merkleClimbBody` stmt 1: `add(authPtr, shl(4, h))`).  With C13's
    `n=128` parameters each auth-path node is a 16-byte word, so the per-height stride
    is `h << 4 = 16*h`; the lemma threads `shl`→`add` to resolve the offset to bare
    `ap + hval <<< 4`.  This pins the *interpreter-side* index arithmetic into the raw
    `bytes`-calldata surface; the residual is still the data side — *which* 16 bytes at
    that offset, and that they equal `wordOfHash16 auth[h]` (the open `hcw` of
    `evalExpr_maskedCalldata`).  Axiom-clean (`[propext, Classical.choice, Quot.sound]`).

  - `ClimbMemFrame.{stepWots_memory, stepWots_hmem}`
    — the **WOTS per-step memory-frame** that discharges the keccak bridge's open
    `hmem` for the cleanest climb case (`ClimbKit.wotsChainBody`: three statements,
    a keccak over the 3-word `[0x00, 0x60)` window, no branchless parity swap).
    `stepWots_memory` pins `(stepWots st).world.memory` as the double
    `memUpdate` (`0x20 ↦ v1`, `0x40 ↦ val`); the trailing `assignVar "val"` never
    touches memory, so this is exactly the window the body's `keccak 0x00 0x60`
    reads.  `stepWots_hmem` repackages it into the
    `∀ i < 3, (memory (0 + 32*i)).val = (wotsScratchWords st v1)[i]` shape
    `evalExpr_maskedKeccak_eq_maskN` consumes — cell `0x00` the untouched base word
    (materialised seed), cell `0x20` the resolved address word, cell `0x40` the
    prior chain word.  Axiom-clean (`[propext, Classical.choice, Quot.sound]`).
    `ClimbMemFrame.{wots_maskedKeccak_value, stepWots_keccak_value}` then close the
    WOTS body **end to end**: specialising the masking glue to the concrete chain
    literals (`keccak 0x00 0x60` over the 3-word window, `0x60 = 32*3`,
    `ClimbKit.N_MASK = C13Concrete.nMask`) and feeding it `stepWots_hmem`, the
    interpreter's post-step `and(keccak256 0x00 0x60, N_MASK)` resolves to exactly
    `maskN (keccakWords (wotsScratchWords st v1))` — the `chainHash` keccak preimage
    `[seed, chainBase ||| (digit+step), val]`.  Axiom-clean
    (`[propext, Classical.choice, Quot.sound]`).
    `ClimbMemFrame.{wotsSpecStep, chainHash_eq_specFold}` close the WOTS **spec-side
    normalization** (the analogue of `xmssClimb_eq_specFold`): the spec chain
    `chainHash seed chainBase digit fuel step val` equals a `ClimbLoop.specFold` over
    `wotsSpecStep` (loop index carrying the chain `step`; accumulator is just the
    `Word`, no projection).  Pure `fuel`-induction (`[propext, Quot.sound]`); lets
    `foldLoop_invariant`'s `specFold` conclusion rewrite into `chainHash`, hence
    `wotsPkWord`.

  - `ClimbMemFrameMerkle.stepMerkle_memory`
    — the **branchless-Merkle per-step memory-frame**, the parity-swap companion
    to the WOTS one for `ClimbKit.merkleClimbBody` (six binding/memory statements,
    a keccak over the 4-word `[0x00, 0x80)` window).  It pins
    `(stepMerkle …).world.memory` as the three writes `0x20 ↦ vadr`, `o5 ↦ vnode`,
    `o6 ↦ vsib` applied in order, given the resolved address word, the
    parity-xored child-slot offsets `o5 = 0x40 xor s` / `o6 = 0x60 xor s`
    (`s = (idx & 1) << 5`), and the node/sibling values.  The trailing masked-keccak
    `assignVar` and the `idx := parentIdx` update never touch memory, so this triple
    update is exactly the body's `keccak 0x00 0x80` read window.  This is the
    parity-agnostic frame; resolving `s ∈ {0, 0x20}` into the spec word order
    (even → `[node, sibling]`, odd → `[sibling, node]`) is the consumer's step.
    Axiom-clean (`[propext, Classical.choice, Quot.sound]`).
    `ClimbMemFrameMerkle.{merkle_hmem_even, merkle_hmem_odd}` then resolve that
    parity, reading the triple-write memory back in the
    `∀ i < 4, (memory (0 + 32*i)).val = (merkleScratchWords … parity)[i]` shape
    `evalExpr_maskedKeccak_eq_maskN` consumes — even (`o5=0x40, o6=0x60`) yields
    `[seed, adrs, node, sibling]`, odd (`o5=0x60, o6=0x40`) the swapped
    `[seed, adrs, sibling, node]`.  Both axiom-clean (`[propext, Quot.sound]`).
    `ClimbMemFrameMerkle.{merkle_maskedKeccak_value, merkle_keccak_value_even,
    merkle_keccak_value_odd}` close the Merkle body end-to-end, mirroring the WOTS
    `stepWots_keccak_value`: the 4-word (`keccak 0x00 0x80`) specialization of the
    masking glue, composed with the parity `hmem` lemmas, proves the interpreter's
    masked-keccak read resolves to `maskN (keccakWords (merkleScratchWords … parity))`
    for either parity.  All axiom-clean (`[propext, Classical.choice, Quot.sound]`).
    `ClimbMemFrameMerkle.{merkleScratchWords_eq_spec_even, merkleScratchWords_eq_spec_odd}`
    then identify the interpreter scratch list with the spec `xmssClimb`/`forsClimb`
    keccak preimage `[seed, adrs, node, sibling]` (even) / `[seed, adrs, sibling, node]`
    (odd) under per-component value equalities — pure list rewrites
    (`[propext]`).  `ClimbMemFrameMerkle.{merkle_keccak_value_spec_even,
    merkle_keccak_value_spec_odd}` compose those with the value closure so the
    interpreter's masked-keccak read equals the spec body's `node'` directly
    (`maskN (keccakWords [seed, adrs, node, sibling])` etc.) — the algebraic half of
    the Phase-3b per-step data correspondence.  Axiom-clean
    (`[propext, Classical.choice, Quot.sound]`).  What remains is the *inductive fold*
    over all climb fuel iterations (and the WOTS/FORS analogues), plus establishing
    the per-component value hypotheses from the loop invariant.
    `ClimbMemFrameMerkle.{merkleSpecStep, xmssClimb_eq_specFold}` close the
    **spec-side normalization**: the recursive spec climb `xmssClimb seed treeAdrs
    fuel h mIdx node auth` equals the second projection of a `ClimbLoop.specFold`
    over `merkleSpecStep` (the spec's one-step `(mIdx, node)` transformer, loop index
    carrying the tree height `h`).  Pure structural `fuel`-induction
    (`[propext, Quot.sound]`).  This is the piece that lets `foldLoop_invariant`'s
    `specFold` conclusion rewrite directly into `xmssClimb`, hence into
    `xmssRootFromSigC13`.
    `ClimbMemFrameMerkle.{parentIdx_shiftRight, merkle_selector_even/odd,
    merkle_offsets_even/odd}` are the **branchless-swap offset arithmetic**: pure
    `Nat` facts (`Nat.and_one_is_mod`, `Nat.shiftRight_eq_div_pow`) that resolve the
    interpreter's `idx >>> 1` to the spec's `mIdx / 2`, and the swap selector
    `s = (idx &&& 1) <<< 5` to `0` (even) / `0x20` (odd), so the parity-agnostic
    `stepMerkle_memory` offsets `o5 = 0x40 ^^^ s` / `o6 = 0x60 ^^^ s` resolve to the
    `merkle_*_even` (`0x40↦node, 0x60↦sibling`) / `merkle_*_odd` (swapped) consumers.
    Axiom-clean.
    `ClimbMemFrameMerkle.stepMerkle_node_binding` is the **binding-projection
    companion** to `stepMerkle_memory`: where the memory-frame lemma pins the
    scratch window, this pins the *output* of the step — the `nodeVar` binding after
    `stepMerkle`.  Statement 7 (`assignVar nodeVar (and (keccak 0x00 0x80) N_MASK)`)
    sets `nodeVar` to the masked-keccak read of the triple-write window; statement 8
    only rebinds `idxVar` (distinct from `nodeVar`, hence the `nodeVar ≠ idxVar`
    hypothesis), so `lookupValue (stepMerkle …).bindings nodeVar` is exactly that
    masked keccak over `memUpdate (memUpdate (memUpdate mem 0x20 vadr) o5 vnode) o6
    vsib2`.  Same eight `evalExpr` resolution hypotheses as `stepMerkle_memory`
    (discharged by `rfl` at the call site); composed with
    `merkle_keccak_value_spec_even/odd` it gives the new node value of one climb step
    — the spec-fold `node'` accumulator component, isolated as a named lemma.  Pure
    state threading, no keccak evaluated.  Axiom-clean
    (`[propext, Classical.choice, Quot.sound]`).
    `ClimbMemFrameMerkle.{stepMerkle_node_value_spec_even, stepMerkle_node_value_spec_odd}`
    are the **welded** per-step node-output lemmas: they compose
    `stepMerkle_node_binding` (binding-projection) with
    `merkle_keccak_value_spec_even/odd` (masked-keccak = `maskN (keccakWords …)`) so
    that, given the parity-resolved child-slot offsets (`o5/o6 ∈ {0x40, 0x60}`, from
    `merkle_offsets_even/odd`) and the per-component value equalities, the `nodeVar`
    output of one climb step *is* the spec body's `node'` directly —
    `maskN (keccakWords [seed, adrs, node, sibling])` (even) /
    `[…, sibling, node]` (odd).  This is the exact per-step accumulator-component the
    `foldLoop` relation `R` carries, now in spec word order with no `evalExpr` or
    memory-frame residue.  Both axiom-clean (`[propext, Classical.choice, Quot.sound]`).
    `ClimbMemFrameMerkle.{stepMerkle_node_eq_specStep_even, stepMerkle_node_eq_specStep_odd}`
    take the final step of the per-step node algebra: they identify the interpreter
    step's `nodeVar` output with the **second component of `merkleSpecStep`** — the
    spec one-step `(mIdx, node) ↦ (parentIdx, node')` transformer that
    `xmssClimb_eq_specFold` folds.  The spec dispatches `node'` on `mIdx % 2`, the
    interpreter on the resolved child-slot offsets `o5/o6`; given the matching parity
    hypothesis (from `merkle_offsets_even/odd`) and the spec-shaped value equalities
    (`adrs = treeAdrs ||| ((h+1)<<<32) ||| mIdx/2`, `sibling = wordOfHash16 auth[h]`),
    both reduce to the same `maskN (keccakWords …)`.  This is exactly the `node` half
    of one `foldLoop` step relation `R`, now phrased against `merkleSpecStep` itself —
    so `foldLoop_invariant`'s per-iteration `hstep` need only supply the value
    equalities (the data-correspondence hypotheses) and the parity.  Both axiom-clean
    (`[propext, Classical.choice, Quot.sound]`).
    `ClimbMemFrameMerkle.stepMerkle_idx_binding` is the **index-component (`.1`)
    twin** of `stepMerkle_node_binding`: where the node lemma projects the `nodeVar`
    output, this projects the `idxVar` output.  Statement 2 binds `"parentIdx"` to the
    resolved `idx >>> 1`; statements 3–7 never touch that binding; statement 8 rebinds
    `idxVar ↦ lookupValue … "parentIdx"`, which is therefore still `vpar`.  The
    `nodeVar ≠ "parentIdx"` hypothesis lets the survival read skip the statement-7
    `nodeVar` bind (the `"s"`/`"sibling"` skips fall to `decide`).  So
    `lookupValue (stepMerkle …).bindings idxVar = vpar`; composed downstream with
    `parentIdx_shiftRight` (`idx >>> 1 = idx / 2`) it yields the spec `parentIdx`
    accumulator component `mIdx / 2` — the *first* half of the `foldLoop` step relation,
    completing the per-step pair the loop invariant carries.  Pure state threading, no
    keccak evaluated.  Axiom-clean (`[propext, Classical.choice, Quot.sound]`).
    `ClimbMemFrameMerkle.stepMerkle_idx_eq_specStep` is the `.1` companion of
    `stepMerkle_node_eq_specStep_even/odd`: it identifies the interpreter step's
    `idxVar` output with the **first component of `merkleSpecStep`**.  Because
    `merkleSpecStep`'s first component (`parentIdx = mIdx / 2`) does *not* dispatch on
    index parity (only `node'` does), a single lemma — with no `hpar` hypothesis —
    covers both even and odd, needing only the index data-correspondence
    `vpar = mIdx / 2`.  Together with the node lemmas this yields the **complete**
    per-step pair `(stepMerkle …) ↦ merkleSpecStep …`, i.e. exactly the relation
    `foldLoop_invariant`'s per-iteration `hstep` must establish; what remains for the
    `hstep` is supplying the value-equality (data-correspondence) hypotheses each
    iteration.  Axiom-clean (`[propext, Classical.choice, Quot.sound]`).
    `ClimbMemFrameMerkle.{stepMerkle_eq_merkleSpecStep_even, stepMerkle_eq_merkleSpecStep_odd}`
    are the **combined per-step accumulator equality**: the *pair* of interpreter
    outputs `(idxVar binding, nodeVar binding)` after `stepMerkle` equals
    `merkleSpecStep` applied to the accumulator `(mIdx, node)` — exactly the shape
    `foldLoop_invariant`'s `hstep` consumes (the spec step over α = `Nat × Nat`).
    Assembled by `Prod.ext` from the two component lemmas
    (`stepMerkle_idx_eq_specStep` for `.1`, `stepMerkle_node_eq_specStep_even/odd`
    for `.2`), so they inherit exactly those hypotheses: parity (`hpar` + matching
    `o5/o6` offsets) and the per-component data-correspondence equalities
    (`hseed/hadr/hnode/hsib/hvpar`).  Every control-flow/state-threading obligation of
    one climb step is now discharged into a single named equality; the *only* residual
    an eventual `hstep` must still supply is the per-iteration data correspondence
    itself (blocker #20).  Both axiom-clean (`[propext, Classical.choice, Quot.sound]`).
    `ClimbMemFrameMerkle.stepMerkle_eq_merkleSpecStep` is the **parity-unified** form:
    a single lemma covering both index parities, dispatched by one disjunction
    hypothesis `hparOff` that couples the index parity to the resolved child-slot
    offsets (`(mIdx % 2 = 0 ∧ o5 = 0x40 ∧ o6 = 0x60) ∨ (mIdx % 2 = 1 ∧ o5 = 0x60 ∧
    o6 = 0x40)`) — exactly the coherence `merkle_offsets_even/odd` establish from the
    index parity.  `Or.elim` routes to the even/odd combined lemmas, so an eventual
    `hstep` supplies one disjunction instead of pre-committing to a branch.  The
    per-step interface is now a single named equality whose *only* open inputs are the
    data-correspondence value equalities (blocker #20).  Axiom-clean
    (`[propext, Classical.choice, Quot.sound]`).
    `ClimbMemFrameMerkle.stepMerkle_sibling_reread_eq` collapses the per-step
    interface's separate sibling-scratch variable: the value re-read in statement 6
    (`vsib2`, from `mstore (xor 0x60 s) (localVar "sibling")`) is structurally the
    value *loaded* in statement 1 (`vsib`, from `letVar "sibling" (and (cdload …)
    N_MASK)`), because statements 2–5 bind only `"parentIdx"`/`"s"` and mutate only
    memory — the `"sibling"` binding is untouched between load and re-read, so
    `vsib2 = vsib`.  This lets an eventual `hstep` discharge the *crux* sibling
    data-correspondence `hsib : wordNormalize vsib2 = wordOfHash16 auth[h]` directly
    against the calldata load `h1` (the masked word at `authPtr + 16·h`) — the
    raw-`bytes`-surface ↔ abstract-`auth` link — with no intermediate scratch-word
    residue.  Pure binding read, no keccak.  Axiom-clean
    (`[propext, Classical.choice, Quot.sound]`).
    `ClimbMemFrameMerkle.{wordNormalize_maskN, wordNormalize_wordOfHash16}` strip the
    interpreter's outer `wordNormalize` (`mod 2^256`) from *both* sides of the sibling
    data-correspondence `wordNormalize vsib2 = wordOfHash16 auth[h]`: a masked word
    `maskN w = w &&& nMask ≤ nMask < 2^256` and a spec hash word
    `wordOfHash16 b = (baToNatBE b % 2^128) * 2^128 < 2^256` are both already
    EVM-normalized, so `wordNormalize` is the identity on each.  With
    `stepMerkle_sibling_reread_eq` (`vsib2 = vsib`) and `h1` (`vsib = maskN` of the
    calldata word) this reduces the crux correspondence to the bare
    `maskN (calldataload (authPtr + 16·h)) = wordOfHash16 (read16 sig off)` — pure
    bytes-surface arithmetic, no `wordNormalize`/scratch residue, the precise shape the
    calldata model (blocker #20) must establish.  Both axiom-clean
    (`wordNormalize_maskN`: `[propext, Quot.sound]`; `wordNormalize_wordOfHash16`:
    `[propext, Classical.choice, Quot.sound]`).
  - `ClimbMemFrameMerkle.SiblingBytesCorrespondence cdval b := maskN cdval = wordOfHash16 b`
    names the *single* bytes-surface obligation the calldata model must establish for one
    climb step, and `ClimbMemFrameMerkle.sibling_correspondence_of_bytes` discharges the
    full sibling data-correspondence `wordNormalize vsib2 = wordOfHash16 auth[h]` *given
    only* that predicate — chaining `stepMerkle_sibling_reread_eq` (`vsib2 = vsib`), the
    statement-1 load shape (`vsib = maskN cdval`), and `wordNormalize_maskN`.  This makes
    the open dependency explicit and minimal: the step lemma is conditional on exactly
    `SiblingBytesCorrespondence` and nothing else, so all surrounding binding/normalize
    bookkeeping is now axiom-free and the lone residue is the raw-calldata `read16` fact
    (blocker #20).  Axiom-clean (`[propext, Classical.choice, Quot.sound]`).
  - `ClimbMemFrameMerkle.StepDataObligations` (+ `.intro`/`.seed`/`.adr`/`.sib`) names the
    *single bundle* of the only genuinely-open per-step data hypotheses of
    `stepMerkle_eq_merkleSpecStep`, for one climb index `h`.  Everything else that step
    lemma consumes is either pure bookkeeping (`hne`, `hparOff`, `hvpar`, the `h1..h6`
    evalExpr facts — all discharged from the frame lemmas) or the *inductive* node input
    `hnode` (carried by `MerkleClimbRel`, not a data fact).  What remains open is exactly
    three: `seed` (mem[0x00] holds the pk-seed word), `adr` (frame's `vadr` equals the pure
    FIPS `tree ‖ (h+1) ‖ parentIdx` word — value core already closed by `merkle_address_word`),
    and `sib` (reread sibling = `wordOfHash16 auth[h]`, the one bottoming out at
    `SiblingBytesCorrespondence` = blocker #20).  Bundling them collapses the whole open
    surface of a single climb step into one `Prop`, so a future `MerkleClimbRel`-preservation
    lemma can be stated conditional on exactly `StepDataObligations` (plus the inductive
    `MerkleClimbRel` and bookkeeping) — making blocker #20 a single named hypothesis rather
    than three scattered ones.  Pure definitional bundle + projections.  Axiom-clean
    (`[propext, Quot.sound]`).
  - `ClimbMemFrameMerkle.MerkleClimbData` (+ `MerkleClimbData_iff`) names the
    *index-indexed* data-obligation family for the whole Merkle climb, in exactly the
    `D : Nat → Prop` shape `ClimbLoop.foldLoop_invariant_cond` ranges its range hypothesis
    over.  For a calldata reader `cdAt : Nat → Nat` (the masked auth-path word loaded at
    climb height `idx`, i.e. the value at `authPtr + 16·idx`), height `idx`'s obligation is
    exactly `SiblingBytesCorrespondence (cdAt idx) auth[idx]` — the lone open per-iteration
    data fact `StepDataObligations.sib` bottoms out at (blocker #20).  Naming the whole
    climb's data surface as this single `Nat`-indexed family is what lets the conditional
    engine collapse blocker #20 for the entire loop into one *range* hypothesis
    `∀ i ∈ [0, h), MerkleClimbData auth cdAt i` — precisely what the calldata model must
    eventually supply, and nothing more.  `MerkleClimbData_iff` unfolds it to the masked-word
    ↦ `wordOfHash16` equality at one height.  Axiom-clean (`[propext, Quot.sound]`).
  - `ClimbMemFrameMerkle.merkleClimbData_to_sib` is the state-dependent seam joining the
    index-indexed family `MerkleClimbData auth cdAt h` to the state-side sibling component of
    `StepDataObligations` (`wordNormalize vsib2 = wordOfHash16 auth[h]`).  Given the frame
    load fact `vsib = maskN (cdAt h)` (statement-1 masked calldata read) and the statement-6
    re-read `h6val`, the single per-height fact `MerkleClimbData auth cdAt h` — definitionally
    `SiblingBytesCorrespondence (cdAt h) auth[h]` — discharges exactly the `.sib` field via
    `sibling_correspondence_of_bytes`.  This lets the range hypothesis
    `∀ i ∈ [0,h), MerkleClimbData auth cdAt i` (fed to `foldLoop_invariant_cond`) supply the
    per-step bundle's sibling obligation, with the calldata-model content isolated entirely in
    `MerkleClimbData`.  Pure specialisation, no re-evaluation.  Axiom-clean (`[propext,
    Classical.choice, Quot.sound]`).
  - `ClimbMemFrameMerkle.stepDataObligations_of_calldata` is the assembly seam: it builds
    the full per-step bundle `StepDataObligations` from the two frame facts that survive as
    ordinary materialisation obligations (`hseed`: cell `0x00` holds the seed word; `hadr`:
    the assembled ADRS frame value equals the FIPS layout word) plus the single
    calldata-model family fact `MerkleClimbData auth cdAt h`, routed through
    `merkleClimbData_to_sib` for the sibling component.  It exhibits precisely how the
    index-indexed `D`-family entry (the *only* blocker-#20 content) combines with frame
    bookkeeping to produce the bundle `MerkleClimbRel_step` consumes — so a future
    climb-specialisation constructs each iteration's `StepDataObligations` from
    `(hseed, hadr, hload)` (frame, generic) and the range entry `MerkleClimbData auth cdAt h`
    (the lone open per-height datum).  Pure constructor application.  Axiom-clean
    (`[propext, Classical.choice, Quot.sound]`).
  - `ClimbMemFrameMerkle.sibling_load_eq_maskN` discharges the `hload` premise of
    `stepDataObligations_of_calldata` (`vsib = maskN (cdAt h)`) as a *pure interpreter fact*,
    with `cdAt h` taken to be the raw `calldataload` value `k`.  Statement 1 of the climb body
    is `and(calldataload(authPtr + 16·h), N_MASK)`; the interpreter's masked load resolves to
    `maskN k` (`ClimbKeccakStep.evalExpr_bitAnd_literal`, with `N_MASK = nMask` and
    `maskN k = Nat.land k nMask` definitionally), so matching against statement 1's bound value
    `vsib` gives `vsib = maskN k`.  This is *not* blocker #20: it needs only the raw load value
    `k` (an abstract interpreter read) and the calldata-word bound `k < 2^256` (a standing
    interpreter invariant).  Isolating it shrinks the per-step `hstep` premises so that
    `MerkleClimbData` (the masked-word ↦ `wordOfHash16` content) is the *sole* standing
    blocker-#20 assumption of the per-step bundle.  Axiom-clean (`[propext, Classical.choice,
    Quot.sound]`).
  - `ClimbMemFrameMerkle.MerkleClimbRel_step` is the per-iteration climb-invariant advance
    stated with the entire open per-step data surface collapsed into the single
    `StepDataObligations` bundle: given the bookkeeping hypotheses of
    `stepMerkle_eq_merkleSpecStep` (all `hne`/`hparOff`/`hvpar` + the `h1..h6` evalExpr frame
    facts, discharged from the frame lemmas) and the inductive node input `hnode`, plus the
    one data bundle `hdata`, the post-state relates by `MerkleClimbRel` to the spec-advanced
    accumulator `merkleSpecStep …`.  This is exactly the `hstep` shape
    `ClimbLoop.foldLoop_invariant` consumes for `R = MerkleClimbRel`, with blocker #20 now
    isolated as the *one* named data premise `hdata` (whose `.sib` projection bottoms out at
    `SiblingBytesCorrespondence`).  Proof = unbundle `hdata`, run the existing control-flow
    step lemma to the pair equality, lift through `MerkleClimbRel_of_pair`.  No new
    interpreter evaluation; pure composition.  Axiom-clean (`[propext, Classical.choice,
    Quot.sound]`).
  - `ClimbMemFrameMerkle.MerkleClimbRel_of_pair` welds the per-step accumulator *pair*
    equality from `stepMerkle_eq_merkleSpecStep` (`(lookupValue … idxVar, lookupValue …
    nodeVar) = merkleSpecStep …`) into the frozen relational `Post_i` shape `MerkleClimbRel
    nodeVar idxVar s' (merkleSpecStep …)`: index component is the pair's `.1`; node
    component lifts the `.2` through `wordNormalize` and closes via
    `merkleSpecStep_snd_normalized`.  This is the lemma that lets the existing control-flow
    step lemma feed `ClimbLoop.foldLoop_invariant` directly — with it the `foldLoop`
    `hstep` for `MerkleClimbRel` follows from the hypotheses of `stepMerkle_eq_merkleSpecStep`
    (all bookkeeping plus the single open per-step data bundle `hseed/hadr/hsib`, the last
    bottoming out at one `SiblingBytesCorrespondence`).  Pure repackaging, no interpreter
    re-evaluation.  Axiom-clean (`[propext, Quot.sound]`).
  - `ClimbMemFrameMerkle.merkleSpecStep_snd_normalized` is the spec-side bridge that lifts
    the *raw* per-step node equality `stepMerkle_node_eq_specStep_even/odd`
    (`lookupValue (stepMerkle …).bindings nodeVar = merkleSpecStep.2`) into the
    `wordNormalize`-wrapped shape `MerkleClimbRel.node` demands: `merkleSpecStep.2` is
    `maskN (keccakWords …)` in both parity branches, so `wordNormalize merkleSpecStep.2 =
    merkleSpecStep.2` by `wordNormalize_maskN`.  Apply `wordNormalize` to the raw equality
    and rewrite the RHS by this lemma and the node component of the climb relation closes
    (modulo the still-open per-step data hypotheses).  Pure spec arithmetic, no interpreter
    state.  Axiom-clean (`[propext, Quot.sound]`).
  - `ClimbMemFrameMerkle.MerkleClimbRel` (+ `.intro`/`.idx`/`.node`) freezes the per-step
    climb-invariant **interface contract** in exactly the shape `ClimbLoop.foldLoop_invariant`
    demands for its relational argument `R : RuntimeState → α → Prop` (α = `Nat × Nat` =
    `(mIdx, node)`): a state relates to `(mIdx, node)` iff its `idxVar` binding is `mIdx`
    and its `nodeVar` binding EVM-normalises to `node`.  This is the Phase-1 boss
    deliverable (freeze `Pre_i/Post_i` before the climb induction): every step lemma above
    is phrased so that, given a per-iteration `SiblingBytesCorrespondence` plus the frame
    facts, the `foldLoop_invariant` `hstep` advancing *this* `R` by one `merkleSpecStep`
    discharges the whole climb.  The index/node components are pure binding bookkeeping
    (axiom-clean above); the lone open per-iteration dependency is the masked sibling word
    (blocker #20).  Axiom-clean (`[propext]`).
  - `ClimbMemFrameMerkle.stepMerkle_node_read_eq` pins the **inductive** half of the
    per-step interface: the climbing node read in statement 5 (`mstore (xor 0x40 s)
    nodeVar`) is exactly the *entry* binding `lookupValue st.bindings nodeVar` (statements
    1–4 bind only `sibling`/`parentIdx`/`s`, distinct from the `forEach` accumulator name,
    and mutate only memory).  This is the structural counterpart of
    `stepMerkle_sibling_reread_eq`, but with a key asymmetry: where the sibling/seed words
    each need a fresh bytes-surface obligation, the node input carries **no** bytes or
    keccak content of its own — the step's `hnode : wordNormalize vnode = node` discharges
    directly against `wordNormalize (lookupValue st.bindings nodeVar) = node`, i.e. the
    climb-fold invariant's node component as left by the *previous* step's output.  That
    asymmetry is precisely what makes the climb a genuine `foldLoop_invariant` induction
    rather than a per-step recomputation: each step's only *new* unknowns are the masked
    sibling word (one `SiblingBytesCorrespondence` instance) and the pure-arithmetic
    address word (already closed).  Axiom-clean (`[propext, Classical.choice, Quot.sound]`).
  - `ClimbMemFrameMerkle.seed_correspondence_of_bytes` consolidates a *second* climb hash
    word onto that same predicate: the materialised seed cell `(base 0x00).val` (carried
    into the keccak preimage with no `wordNormalize` wrapper, a `Uint256.val` being already
    `< 2^256`) matches the spec `seed = wordOfHash16 pk.pkSeed` given only
    `SiblingBytesCorrespondence cdval b` plus the frame fact `seedWord.val = maskN cdval`.
    Unlike the sibling there is no per-step re-read (the seed is set once at frame setup),
    so the reduction is a bare transitivity.  Net effect: both the seed cell and the
    per-step sibling now bottom out at one identical calldata-model obligation shape — the
    lone blocker-#20 residue is shared, not multiplied.  Axiom-clean (`[propext,
    Quot.sound]`).
  - `ClimbMemFrameMerkle.{uint256_or_val, merkle_address_word}` close the **address-word**
    correspondence's value core — and, unlike the sibling/seed hash words, this piece is
    **not** part of blocker #20: the statement-3 ADRS word `adrsBase | ((h+1)<<32 |
    parentIdx)` is pure bitwise-OR *integer* arithmetic with no keccak and no
    calldata-bytes dependency.  `uint256_or_val` (`(Uint256.or a b).val = a.val ||| b.val`,
    via `Nat.or_lt_two_pow` so the `ofNat` truncation vanishes — the EVM-word analogue of
    `wordNormalize_maskN`) plus `Nat.lor_assoc` reconcile the source's right-nested
    `adrsBase | (sh | parentIdx)` with the spec's left-assoc `treeAdrs ||| ((h+1)<<<32) |||
    parentIdx`, giving `merkle_address_word : (Uint256.or adrsBase (Uint256.or sh
    parentIdx)).val = adrsBase.val ||| sh.val ||| parentIdx.val`.  The only remaining
    address obligations are the ordinary frame-materialisation facts `adrsBase.val =
    treeAdrs` and `sh = (h+1)<<<32`, which carry no hash/calldata content — so the address
    correspondence closes completely without touching the months-scale data correspondence.
    Both axiom-clean (`uint256_or_val`: `[propext, Quot.sound]`; `merkle_address_word`:
    `[propext, Classical.choice, Quot.sound]`).

  These give the full **control-flow** thread of the accept path (every loop and
  guard, all the way to the `valid` letVar and `return`).  The residual gap before
  the axiom can flip to a theorem is the **data correspondence**: proving each
  symbolic step transformer's keccak-computed values (`s2Step`'s digest,
  `forsLeafStep`/`forsFinalizeStep`'s FORS pk, `stepLayer`'s climbed node) equal
  the abstract spec functions (`hMsg`, `forsPkFromSig`, `foldHypertree`) so the
  final `currentNode == root` word equals `ByteLevel.verifyBytes`'s accept
  decision.  Until that full equality is in hand, `execC13` stays `opaque` and
  `c13_refines_byte_spec` stays an `axiom` (defining `execC13` concretely while the
  bridge is still assumed would convert a safe existential into a possibly-false
  closed claim — unsound).

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
  `[propext, Classical.choice, Quot.sound]` for C13 (its `Primitives` is now the
  concrete Phase-0 def, so no opaque-primitives constant appears) and
  `[propext, Classical.choice, Quot.sound, <variant>Primitives]` for C12/SHA-2
  (whose `Primitives` are still axioms) — **no bridge axiom, no `sorryAx`**.  The
  accept path remains the carried axiom.

  **Pre-flight (STRATEGY §4) — end-to-end executable, PASS.**  Before investing
  in the climb-equivalence proof, `PreflightC13.lean` de-risks the accept path by
  running the *entire* compiled `c13VerifyBody` (all 29 statements) through the
  real `execStmtList` interpreter on a concrete C13 test vector — not just past
  the first hash.  `#eval runFull stateAccept = some true` (the genuine accept
  case terminates with `valid = 1`, never reverting), and `#eval runFull
  stateCorrupt = none` (a single-byte WOTS corruption is rejected).  The corrupt
  case reverts at prefix-26 — the WOTS+C grinding guard (`digitSum != 208`),
  because the corrupted layer-0 word desynchronises layer-1's recomputed node from
  the ground count — and `ByteLevel.verifyBytes` maps that same grinding miss to
  `none` (`HyperResult.reverted`), so the model and the byte spec **agree** (both
  reject) on the corrupt subdomain with no divergence.  This is `#eval`-only
  scaffolding (`PreflightC13.lean` is not a lakefile root and touches no proof
  term); it confirms the accept subdomain is reachable *end-to-end* through the
  real interpreter, which is the go condition for the line-by-line bridge proof.

## Build

```bash
cd verity
lake build SphincsMinusVerifiers
```

Expected status right now: build succeeds with **no `sorry` warnings**.
`Proofs.lean` proves `byteVerifier_refines_spec` outright and derives the
unconditional per-verifier `*_refines_spec` theorems from the three named
`*_refines_byte_spec` bridge axioms (MODEL-EXEC-BRIDGE).
