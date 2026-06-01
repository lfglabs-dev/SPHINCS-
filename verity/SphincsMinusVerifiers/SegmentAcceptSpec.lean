/-
  SegmentAcceptSpec — the compose-stub mandated by STRATEGY (§2, "Worker E stubs
  the compose early to catch drift").

  `SegmentCompose.execC13Body_returns` already reduces the *entire* `c13VerifyBody`
  run, under the three control-flow guards, to a single `.return` whose payload is
  the EVM boolean word of the model's final `currentNode == root` comparison
  (`acceptWord st`).  That closes the **control-flow** side end-to-end.

  This file ties that returned boolean to the **spec** side: `verifyParsed`'s
  accept decision.  It does so under ONE explicit hypothesis, `hCmp`, which states
  that the model's final node/root word comparison agrees with the boolean
  `verifyParsed` returns.  `hCmp` is precisely the residual Phase-3b
  data-correspondence obligation (the months-scale FORS double-loop + hypertree
  keccak matching), surfaced here as a named hypothesis rather than discharged.

  The value of this stub is drift-detection: it is phrased against the REAL
  `verifyParsed`, `c13PrimitivesConcrete`, `c13`, `mkC13State`, and `c13VerifyBody`
  definitions, so any change to the model's return structure or the spec's accept
  shape breaks compilation here.  It touches neither `execC13` nor the bridge
  axiom, and discharges no data correspondence.  No `sorry`, no new `axiom`,
  no `native_decide`.
-/

import SphincsMinusVerifiers.SegmentCompose
import SphincsMinusVerifiers.MkC13State
import SphincsMinusVerifierSpec.Spec
import SphincsMinusVerifierSpec.C13Concrete

namespace SphincsMinusVerifiers.SegmentAcceptSpec

open Compiler.Proofs.IRGeneration.SourceSemantics
open Compiler.CompilationModel (Expr Stmt)
open SphincsMinusVerifiers
open SphincsMinusVerifiers.SegmentCompose
open SphincsMinusVerifiers.MkC13State
open SphincsMinusVerifierSpec
open SphincsMinusVerifierSpec.C13Concrete

/-- **`accept_path_returns_verifyParsed_bool`** — under the three control-flow
guards (length, FORS forced-zero, WOTS-checksum climb) AND the single residual
data-correspondence hypothesis `hCmp` (the model's final `currentNode == root`
word comparison decides the same boolean `verifyParsed` returns on this input),
the whole compiled `c13VerifyBody` run over `mkC13State …` returns the EVM-word
encoding of exactly the boolean `verifyParsed` yields.

This is the Phase-3 *compose stub*: it pins the model's observable return to the
spec's accept decision, catching any drift between the two.  It does NOT discharge
`hCmp` — that is the months-scale FORS/hypertree keccak correspondence — and it
neither defines `execC13` nor flips the bridge axiom.  Axiom-clean
(`[propext, Classical.choice, Quot.sound]`). -/
theorem accept_path_returns_verifyParsed_bool
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (sigParsed : Signature) (specBool : Bool)
    (hlen : lookupValue (mkC13State pkSeed pkRoot message sig).bindings "sig_length"
              = wordNormalize 3688)
    (hg3 : SegmentS3.s3Guard (afterS2 (mkC13State pkSeed pkRoot message sig)) = 0)
    (hgL : ClimbLoopGuarded.allGuardsPass "layer" SegmentLayer3.stepLayer SegmentLayer3.layerGuard
        { (afterSeed (mkC13State pkSeed pkRoot message sig)) with
            bindings := bindValue
              (afterSeed (mkC13State pkSeed pkRoot message sig)).bindings "layer" (wordNormalize 0) }
        0 (wordNormalize 2))
    (hSpec : verifyParsed C13Concrete.c13PrimitivesConcrete c13 pk message sigParsed
              = some specBool)
    (hCmp : decide
        (lookupValue (afterLayer (mkC13State pkSeed pkRoot message sig)).bindings "currentNode"
          = lookupValue (afterLayer (mkC13State pkSeed pkRoot message sig)).bindings "root")
        = specBool) :
    ∃ finalState,
      verifyParsed C13Concrete.c13PrimitivesConcrete c13 pk message sigParsed = some specBool ∧
      execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody
        = .return (wordNormalize (boolWord specBool)) finalState := by
  obtain ⟨fs, hfs⟩ := execC13Body_returns (mkC13State pkSeed pkRoot message sig) hlen hg3 hgL
  have hAcc : acceptWord (mkC13State pkSeed pkRoot message sig) = boolWord specBool := by
    unfold acceptWord; rw [hCmp]
  refine ⟨fs, hSpec, ?_⟩
  rw [hfs, hAcc]

/-- **`accept_path_returns_verifyParsed_bool_linked`** — the same compose stub as
`accept_path_returns_verifyParsed_bool`, but with the spec-side inputs *pinned to
the byte inputs* via two linkage hypotheses:

* `hPk : pk = { pkSeed := pkSeed, pkRoot := pkRoot }` — the public key is exactly
  what `ByteLevel.parsePublicKey`/`verifyBytes` reconstructs from the two `bytes32`
  arguments (Spec.lean:347–350).
* `hSig : parseSignatureC13 c13 sig = some sigParsed` — the parsed signature is
  exactly what `c13PrimitivesConcrete.parseSignature` yields on the raw bytes.

With these, `specBool` (constrained by `hSpec` over `pk`/`sigParsed`) becomes a
*function of the byte inputs alone*, the same bytes the model's
`currentNode`/`root` bindings are computed from.  This makes the residual
data-correspondence goal `decide (currentNode = root) = specBool` **well-posed**
(both sides range over the same `pkSeed pkRoot message sig`), closing *Blocker A*
(the floating-`pk`/`sigParsed` ill-posedness).  It still carries `hCmp` and does
not discharge the keccak correspondence (*Blocker B*).  Axiom-clean. -/
theorem accept_path_returns_verifyParsed_bool_linked
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (sigParsed : Signature) (specBool : Bool)
    (_hPk : pk = { pkSeed := pkSeed, pkRoot := pkRoot })
    (_hSig : parseSignatureC13 c13 sig = some sigParsed)
    (hlen : lookupValue (mkC13State pkSeed pkRoot message sig).bindings "sig_length"
              = wordNormalize 3688)
    (hg3 : SegmentS3.s3Guard (afterS2 (mkC13State pkSeed pkRoot message sig)) = 0)
    (hgL : ClimbLoopGuarded.allGuardsPass "layer" SegmentLayer3.stepLayer SegmentLayer3.layerGuard
        { (afterSeed (mkC13State pkSeed pkRoot message sig)) with
            bindings := bindValue
              (afterSeed (mkC13State pkSeed pkRoot message sig)).bindings "layer" (wordNormalize 0) }
        0 (wordNormalize 2))
    (hSpec : verifyParsed C13Concrete.c13PrimitivesConcrete c13 pk message sigParsed
              = some specBool)
    (hCmp : decide
        (lookupValue (afterLayer (mkC13State pkSeed pkRoot message sig)).bindings "currentNode"
          = lookupValue (afterLayer (mkC13State pkSeed pkRoot message sig)).bindings "root")
        = specBool) :
    ∃ finalState,
      verifyParsed C13Concrete.c13PrimitivesConcrete c13 pk message sigParsed = some specBool ∧
      execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody
        = .return (wordNormalize (boolWord specBool)) finalState := by
  -- The linkage hypotheses pin the spec inputs to the bytes (Blocker A); the proof
  -- itself is the same as the unlinked stub.
  exact accept_path_returns_verifyParsed_bool
    pkSeed pkRoot message sig pk sigParsed specBool hlen hg3 hgL hSpec hCmp

/-! ## Axiom audit. -/

#print axioms accept_path_returns_verifyParsed_bool
#print axioms accept_path_returns_verifyParsed_bool_linked

end SphincsMinusVerifiers.SegmentAcceptSpec
