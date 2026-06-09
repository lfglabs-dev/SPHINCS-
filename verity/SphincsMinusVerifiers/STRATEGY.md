# Strategy: Discharge the C13/C12 MODEL-EXEC-BRIDGE accept path

This document is the implementation strategy for turning the three
`*_refines_byte_spec` **axioms** (the MODEL-EXEC-BRIDGE) into **theorems** for the
keccak-family verifiers (C13, then C12). It is written to be executed by an
orchestrator agent coordinating many sub-workers. SHA-2 is explicitly out of
scope (blocked on a byte-addressed memory model).

## 0. Objective, stated as the end-state

Replace:

```lean
opaque execC13 : Bytes → Bytes → Bytes → Bytes → Option Bool
axiom c13_refines_byte_spec : ByteLevel.ImplementsByteVerifier c13Primitives c13 execC13
```

with:

```lean
def execC13 (pkSeed pkRoot message sig : Bytes) : Option Bool :=
  interpretReturn (execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody)
theorem c13_refines_byte_spec : ByteLevel.ImplementsByteVerifier c13Primitives c13 execC13 := …
```

and have `#print axioms c13_refines_spec` show **only**
`[propext, Classical.choice, Quot.sound, <keccak-CR>]` — bridge axiom gone, no
`sorry`, no opaque-Primitives axiom.

### Hard soundness rule (every worker, non-negotiable)

The concrete `def execC13` and the `theorem c13_refines_byte_spec` must land in
the **same** change. Defining `execC13` concretely while the bridge is still an
`axiom` converts a safe existential assumption into a closed claim that could be
false — unsound. Until integration, `execC13` stays `opaque` and the axiom stays
an axiom; all worker lemmas are proved as **standalone** theorems that never
touch either. No `sorry`, ever. No `exec := verifyBytes` shortcut, ever.

## 1. Critical-path prerequisite (do first — this is the go/no-go gate)

`c13Primitives` / `c12Primitives` are themselves **axioms** (`Proofs.lean`). The
spec `verifyBytes` hashes via `c13Primitives.hash`; the interpreter hashes via
the concrete `KeccakEngine` (`keccakMemorySlice`). You cannot prove "model
computes the spec" while the spec's hash is an opaque axiom — there is no
equation connecting the two.

**Phase 0:** replace `axiom c13Primitives : Primitives` with a concrete
`def c13Primitives : Primitives` whose hash/address functions are defined from
the same `KeccakEngine` the interpreter uses, and re-prove any spec lemma that
referenced the axiom. Same for C12. If this cannot be matched exactly, the whole
bridge is unprovable — stop, keep the axiom, report honestly. **This is the
first gate; nothing else proceeds until it passes.**

## 2. Architecture: three horizontal layers + a spec mirror

The proof composes **iff** there is a clean interface contract between segments.
The boss defines this contract type up front; it is the API every worker codes
against.

```
Layer 1  Interpreter/memory primitives    (framework-level, shared, foundational)
Layer 2  Straight-line prefix segments     (parallelizable, 6 segments)
Layer 3  Hypertree climb loop              (one invariant + one step lemma)
Layer 4  Integration: def + theorem + axiom removal
   ‖
Spec mirror: refactor verifyBytes into named intermediates matching each segment
```

### Layer 1 — interpreter & memory (Worker A, foundational, blocks others)

Word-keyed memory reasoning is the mechanical bedrock. Build/locate:

- `mload_mstore_same`, `mload_mstore_diff` (read-after-write, same/different word).
- An address-disequality discharger (simp set / `decide`) for the concrete C13
  offsets (0x00, 0x20, 0x40, 0xA0, scratch slots).
- `execStmtList_append` — split the body into named segments.
- Reuse the landed combinators `execStmtList_cons_continue`,
  `execStmtList_cons_revert`.
- A **symbolic-state** abstraction: post-segment memory as a finite
  `(addr, value)` association list, so later reads resolve by lookup, never by
  replaying history. This is what keeps reduction cost bounded and kills the
  heartbeat wall.

Reusable across C13, C12, and any future keccak verifier. Must stabilize before
Layer 2 starts.

### Spec mirror — refactor `verifyBytes` (Worker D, early, coordinated)

Factor `verifyBytes` into named intermediates with the **same boundaries** as the
code segments: `forsRootBytes`, `wotsPkBytes`, `htLeafBytes`, `htClimb i node`,
`finalRootBytes`. Prove `verifyBytes = (compose of these)` once. Each segment
lemma's RHS is then one named intermediate. Without this the segment proofs have
nothing to equal and won't compose. Worker D + boss own the interface contract.

### Layer 2 — straight-line prefix (Workers B1..B6, parallel)

Split the pre-loop body into 6 segments, each a standalone lemma:

> Given a state whose symbolic memory satisfies `Pre_i`, `execStmtList [] s
> segment_i = .continue s'`, `s'`'s memory satisfies `Post_i`, and the produced
> value equals `<spec intermediate>_i`.

| Seg | Code does | Proves equal to |
|---|---|---|
| S1 | ABI decode + length guard | done (reject/pass lemmas) |
| S2 | Hmsg keccak → digest | `digestBytes` (first-keccak lemma done) |
| S3 | digest → FORS/leaf/tree indices | index extraction in spec |
| S4 | FORS+C reconstruction → FORS root | `forsRootBytes` |
| S5 | WOTS+C on FORS root → WOTS pk | `wotsPkBytes` |
| S6 | WOTS pk compress → first HT leaf | `htLeafBytes` |

Independent **given the `Pre_i`/`Post_i` contracts**, so B1..B6 run in parallel.
S1/S2 are partly done and serve as worked examples.

### Layer 3 — hypertree climb (Worker C, hardest single lemma)

The `forEach` (Model.lean ~152-180). Use the existing inductive kit
(`execForEachLoop_succ_continue`, `_succ_continue_iff`, `_congr`,
`_zero_continue_state`):

1. Extract the per-iteration body as a pure transformer `stepLayer : RuntimeState
   → RuntimeState`; prove `body ≡ .continue (stepLayer s)` via Layer 1. The
   branchless Merkle swap means **no case split** — exploit it.
2. Invariant `Inv i s : node-cell s = htClimb i (htLeafBytes …) ∧ bindings match`.
3. `Inv 0` from S6's `Post`; `Inv i → Inv (i+1)` from `stepLayer` matching the
   spec's per-layer combine; conclude `Inv h` by induction over height.
4. Final: `node-cell = finalRootBytes`; the compare to `pkRoot` returns the right
   boolean.

### Layer 4 — integration (Worker E, owns soundness)

Compose S1..S6 + the loop invariant into the full-body equality. Then, in **one
atomic change**: drop `opaque`, add `def execC13`, turn the axiom into the
theorem, and commit `#print axioms` output as evidence. Keep
`AUDIT.md`/`TRUST_ASSUMPTIONS.md`/`AXIOMS.md`/README synced (a CLAUDE.md
non-negotiable). Account for the now-concrete `c13Primitives`.

### C12 (Worker F, after C13 proves the pattern)

Replicate: different ADRS, plain FORS (no +C), 5 XMSS layers. **First task:** C12
truncates keccak to 16 bytes; confirm its memory writes are word-aligned. If
unaligned, C12 hits the same byte-vs-word wall as SHA-2 → C12 stays an axiom,
only C13 lands. Report before committing to the full C12 proof.

## 3. Sequencing & parallelism

```
Phase 0:  Worker D0 — concretize c13Primitives/c12Primitives          [GATE]
Phase 1:  Worker A  — Layer 1 memory/interpreter kit                  ┐ parallel
          Worker D  — spec mirror refactor + interface contracts      ┘
Phase 2:  Workers B1..B6 — prefix segments    (need A + D contracts)  ] parallel
          Worker C — loop step + invariant     (needs A + D + S6)
Phase 3:  Worker E — integration, def+theorem, #print axioms, docs
Phase 4:  Worker F — C12 (after C13; early word-alignment check)
```

Boss owns: the interface-contract type, the `#print axioms` gate on every merge,
and the soundness rule (no concrete `execC13` before the theorem).

## 4. Pre-flight de-risk (cheap; Phase 0/1, before sinking proof effort)

Make the model **executable** on the existing `test_vector.json` / known-good
signature: run the interpreter on `c13VerifyBody` over a concrete valid input and
check it returns `some true`, over a corrupted one `some false`. If the model
disagrees with the real contract on a test vector, the proof is impossible and
the **model** is wrong — fix it first. A one-day sanity gate that protects months
of effort and independently exercises the hand-translation-fidelity gap.

## 5. Risks and backups

| Risk | Mitigation / backup |
|---|---|
| **Heartbeat/whnf blowup** on the giant `c13VerifyBody` term (hit at ~11 statements) | Never `rfl` the whole body. Use `cons_continue` + `generalize` the tail so reduction can't force it. Symbolic-memory list. Sub-split a segment if it still explodes. #1 practical risk; symbolic-state discipline is the defense. |
| **Primitives won't concretize** to match interpreter keccak (Phase 0 fails) | Bridge unprovable; stop, keep axiom, report. This is *the* go/no-go gate — run first. |
| **C12 16-byte truncation** → sub-word writes | Confirm alignment first; if unaligned, C12 stays axiom (same class as SHA-2), only C13 lands. |
| **Loop step lemma intractable** (body too branchy) | Branchless Merkle swap → no path split. Extract `stepLayer` as a pure function, prove `body ≡ stepLayer`, then `execForEachLoop_congr` to a clean recurrence. |
| **Segments don't compose** (interface drift) | Boss-frozen `Pre_i`/`Post_i` contract before B-workers start; changes go through the boss. Worker E stubs the compose early to catch drift. |
| **Hand-translation fidelity** (model ≠ real Solidity) — *not closed by this proof* | Out of scope; state in docs. Backup: differential testing (§4) and, longer term, the INLINE-YUL-FRONTEND importer. This proof closes model→byte, not source→model. |
| **SHA-2 scope creep** | Explicitly out. Blocked on byte-addressed memory, a separate project. Do not let a worker wander in. |

## 6. Definition of done

- `c13_refines_byte_spec` (ideally `c12_`) is a `theorem`, not an `axiom`.
- `execC13` is a concrete `def` (interpreter run), introduced atomically with the
  theorem.
- `#print axioms c13_refines_spec` = `[propext, Classical.choice, Quot.sound,
  <keccak-CR>]` — no bridge axiom, no `sorryAx`, no opaque-Primitives axiom.
- `lake build SphincsMinusVerifiers` green; `AUDIT.md`/`TRUST_ASSUMPTIONS.md`/
  `AXIOMS.md`/README synced.
- Honest scope note recorded: source→model fidelity remains a separate, untouched
  assumption.
## Climb engine factoring (June 2026)

See Verity PR #1983 (minimal `Compiler/Proofs/Frames.lean`) and the
companion SPHINCS- PR on this repo.

Desired split (least change to Verity):
- Verity: generic frame preservation (`PreservesBindingsExcept`,
  `PreservesSelectorCalldata`) and (in future) generic climb loop lift.
- SPHINCS-: supplies the concrete `stepMerkle` / runBody, the spec steps,
  the data/range suppliers (from hauth + frozen calldata), and the
  SPHINCS-specific memory layout / segment characterisations.

The `SphincsMinusVerifierSpec/` (additive concrete C13Concrete etc.)
and the thin observable top-level claim are unaffected.

This addresses the RAM blowup when agents previously tried to prove
the remaining bridge axioms with monolithic strategies.
