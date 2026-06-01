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
import SphincsMinusVerifiers.RootFrame
import SphincsMinusVerifiers.CurrentNodeFrame
import SphincsMinusVerifierSpec.Spec
import SphincsMinusVerifierSpec.C13Concrete

namespace SphincsMinusVerifiers.SegmentAcceptSpec

open Compiler.Proofs.IRGeneration.SourceSemantics
open Compiler.CompilationModel (Expr Stmt)
open SphincsMinusVerifiers
open SphincsMinusVerifiers.SegmentCompose
open SphincsMinusVerifiers.MkC13State
open SphincsMinusVerifiers.RootFrame
open SphincsMinusVerifiers.CurrentNodeFrame
open SphincsMinusVerifierSpec
open SphincsMinusVerifierSpec.C13Concrete

/-! ## Residual `hCmp` factoring. -/

/-- When the parsed verifier reaches the final `.ok root` branch, its observable
boolean is exactly `root == pk.pkRoot`.  This is the spec-side branch equation
needed by the model-side final-word comparison. -/
theorem verifyParsed_ok_branch
    (p : Primitives) (v : Variant)
    (pk : PublicKey) (message : ByteArray) (sigParsed : Signature)
    (forsPk root : ByteArray)
    (hShape : signatureShapeOk v sigParsed = true)
    (hZero : forcedZeroOk v (p.hMsg v pk sigParsed.R message) = true)
    (hFors : p.forsPkFromSig v pk (p.hMsg v pk sigParsed.R message) sigParsed.fors
              = some forsPk)
    (hFold : foldHypertree p v pk (p.hMsg v pk sigParsed.R message) forsPk sigParsed.layers
              = .ok root) :
    verifyParsed p v pk message sigParsed = some (root == pk.pkRoot) := by
  unfold verifyParsed
  simp [hShape, hZero, hFors, hFold]

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

/-- **`accept_path_returns_verifyParsed_bool_from_root`** — a sharper compose
adapter for the residual `hCmp`: if the left operand of the final model compare is
the word image of the spec's final root, and byte equality at the spec boundary is
represented by the corresponding word equality, then the existing accept-path
composition returns the `verifyParsed` boolean.

The right operand is no longer a hypothesis here: it is supplied by
`RootFrame.afterLayer_root_mkC13State`, which proves the final `"root"` binding is
`wordOfHash16 pkRoot`.  The only remaining substantive obligations are therefore:

* `hCurrent`: the post-layer `"currentNode"` binding equals `wordOfHash16 specRoot`;
* `hWordCmp`: the word-level equality test agrees with the spec byte equality.

This is the bounded form of `hCmp` that the FORS/hypertree correspondence should
eventually discharge.  It still does not touch `execC13` or the bridge axiom. -/
theorem accept_path_returns_verifyParsed_bool_from_root
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (hPk : pk = { pkSeed := pkSeed, pkRoot := pkRoot })
    (hShape : signatureShapeOk c13 sigParsed = true)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hlen : lookupValue (mkC13State pkSeed pkRoot message sig).bindings "sig_length"
              = wordNormalize 3688)
    (hg3 : SegmentS3.s3Guard (afterS2 (mkC13State pkSeed pkRoot message sig)) = 0)
    (hgL : ClimbLoopGuarded.allGuardsPass "layer" SegmentLayer3.stepLayer SegmentLayer3.layerGuard
        { (afterSeed (mkC13State pkSeed pkRoot message sig)) with
            bindings := bindValue
              (afterSeed (mkC13State pkSeed pkRoot message sig)).bindings "layer" (wordNormalize 0) }
        0 (wordNormalize 2))
    (hCurrent :
        lookupValue (afterLayer (mkC13State pkSeed pkRoot message sig)).bindings "currentNode"
          = wordOfHash16 specRoot)
    (hWordCmp : decide (wordOfHash16 specRoot = wordOfHash16 pkRoot)
          = (specRoot == pkRoot)) :
    ∃ finalState,
      verifyParsed C13Concrete.c13PrimitivesConcrete c13 pk message sigParsed
        = some (specRoot == pk.pkRoot) ∧
      execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody
        = .return (wordNormalize (boolWord (specRoot == pk.pkRoot))) finalState := by
  subst hPk
  have hSpec : verifyParsed C13Concrete.c13PrimitivesConcrete c13
        { pkSeed := pkSeed, pkRoot := pkRoot } message sigParsed
        = some (specRoot == pkRoot) :=
    verifyParsed_ok_branch C13Concrete.c13PrimitivesConcrete c13
      { pkSeed := pkSeed, pkRoot := pkRoot } message sigParsed forsPk specRoot
      hShape hZero hFors hFold
  have hRoot :
      lookupValue (afterLayer (mkC13State pkSeed pkRoot message sig)).bindings "root"
        = wordOfHash16 pkRoot :=
    afterLayer_root_mkC13State pkSeed pkRoot message sig
  have hCmp : decide
      (lookupValue (afterLayer (mkC13State pkSeed pkRoot message sig)).bindings "currentNode"
        = lookupValue (afterLayer (mkC13State pkSeed pkRoot message sig)).bindings "root")
      = (specRoot == pkRoot) := by
    rw [hCurrent, hRoot, hWordCmp]
  exact accept_path_returns_verifyParsed_bool
    pkSeed pkRoot message sig { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed
    (specRoot == pkRoot) hlen hg3 hgL hSpec hCmp

/-- A compact way to discharge the final `hWordCmp` premise: if the word encoding
is injective for the two byte roots in question, then the model's word equality
decision agrees with the spec's `ByteArray` equality test. -/
theorem wordCmp_of_wordOfHash16_iff
    (specRoot pkRoot : ByteArray)
    (hIff : (wordOfHash16 specRoot = wordOfHash16 pkRoot) ↔ specRoot = pkRoot)
    (hBeq : (specRoot == pkRoot) = decide (specRoot = pkRoot)) :
    decide (wordOfHash16 specRoot = wordOfHash16 pkRoot) = (specRoot == pkRoot) := by
  rw [hBeq]
  by_cases hWord : wordOfHash16 specRoot = wordOfHash16 pkRoot
  · have hBytes : specRoot = pkRoot := hIff.mp hWord
    simp [hBytes]
  · have hBytes : specRoot ≠ pkRoot := by
      intro hEq
      exact hWord (hIff.mpr hEq)
    simp [hWord, hBytes]

/-- **Layer-step form of the final accept adapter.**  This replaces the raw
`hCurrent` hypothesis of `accept_path_returns_verifyParsed_bool_from_root` with
the two facts the hypertree proof is expected to produce:

* S4/FORS finalize binds `"forsPk"` to the word image of the spec FORS public key;
* one `stepLayer` iteration preserves the `"currentNode"` ↔ spec-node relation,
  so `CurrentNodeFrame.afterLayer_currentNode_wordOfHash16_of_forsPk_step` lifts it
  across the two-layer C13 loop.

The per-layer correspondence is still a hypothesis here; this theorem only
performs the segment composition from that correspondence to the final
`verifyParsed` boolean. -/
theorem accept_path_returns_verifyParsed_bool_from_layer_step
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray)
    (hPk : pk = { pkSeed := pkSeed, pkRoot := pkRoot })
    (hShape : signatureShapeOk c13 sigParsed = true)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hlen : lookupValue (mkC13State pkSeed pkRoot message sig).bindings "sig_length"
              = wordNormalize 3688)
    (hg3 : SegmentS3.s3Guard (afterS2 (mkC13State pkSeed pkRoot message sig)) = 0)
    (hgL : ClimbLoopGuarded.allGuardsPass "layer" SegmentLayer3.stepLayer SegmentLayer3.layerGuard
        { (afterSeed (mkC13State pkSeed pkRoot message sig)) with
            bindings := bindValue
              (afterSeed (mkC13State pkSeed pkRoot message sig)).bindings "layer" (wordNormalize 0) }
        0 (wordNormalize 2))
    (hForsPkWord :
        lookupValue (afterFinalize (mkC13State pkSeed pkRoot message sig)).bindings "forsPk"
          = wordOfHash16 forsPk)
    (hLayerStep : ∀ (s : RuntimeState) (node : ByteArray) (idx : Nat),
        CurrentNodeRel wordOfHash16 s node →
        CurrentNodeRel wordOfHash16
          (SegmentLayer3.stepLayer
            { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) })
          (specStep idx node))
    (hSpecFold : ClimbLoop.specFold specStep forsPk 0 (wordNormalize 2) = specRoot)
    (hWordCmp : decide (wordOfHash16 specRoot = wordOfHash16 pkRoot)
          = (specRoot == pkRoot)) :
    ∃ finalState,
      verifyParsed C13Concrete.c13PrimitivesConcrete c13 pk message sigParsed
        = some (specRoot == pk.pkRoot) ∧
      execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody
        = .return (wordNormalize (boolWord (specRoot == pk.pkRoot))) finalState := by
  have hCurrent :
      lookupValue (afterLayer (mkC13State pkSeed pkRoot message sig)).bindings "currentNode"
        = wordOfHash16 specRoot :=
    CurrentNodeFrame.afterLayer_currentNode_wordOfHash16_of_forsPk_step
      (mkC13State pkSeed pkRoot message sig) specStep forsPk specRoot
      hForsPkWord hLayerStep hSpecFold
  exact accept_path_returns_verifyParsed_bool_from_root
    pkSeed pkRoot message sig pk sigParsed forsPk specRoot hPk hShape hZero hFors hFold
    hlen hg3 hgL hCurrent hWordCmp

/-- Same as `accept_path_returns_verifyParsed_bool_from_layer_step`, but the S4
premise is the concrete masked FORS-compression word rather than the already-bound
`"forsPk"` lookup.  This is the handoff shape for the forthcoming S4/FORS root
correspondence proof. -/
theorem accept_path_returns_verifyParsed_bool_from_fors_compress_and_layer_step
    (pkSeed pkRoot message sig : ByteArray)
    (pk : PublicKey) (sigParsed : Signature) (forsPk specRoot : ByteArray)
    (specStep : Nat → ByteArray → ByteArray)
    (hPk : pk = { pkSeed := pkSeed, pkRoot := pkRoot })
    (hShape : signatureShapeOk c13 sigParsed = true)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) = true)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message) sigParsed.fors
          = some forsPk)
    (hFold : foldHypertree C13Concrete.c13PrimitivesConcrete c13 pk
        (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message)
        forsPk sigParsed.layers = .ok specRoot)
    (hlen : lookupValue (mkC13State pkSeed pkRoot message sig).bindings "sig_length"
              = wordNormalize 3688)
    (hg3 : SegmentS3.s3Guard (afterS2 (mkC13State pkSeed pkRoot message sig)) = 0)
    (hgL : ClimbLoopGuarded.allGuardsPass "layer" SegmentLayer3.stepLayer SegmentLayer3.layerGuard
        { (afterSeed (mkC13State pkSeed pkRoot message sig)) with
            bindings := bindValue
              (afterSeed (mkC13State pkSeed pkRoot message sig)).bindings "layer" (wordNormalize 0) }
        0 (wordNormalize 2))
    (hForsCompress :
        CurrentNodeFrame.forsPkCompressWord
          (afterFors (mkC13State pkSeed pkRoot message sig)) = wordOfHash16 forsPk)
    (hLayerStep : ∀ (s : RuntimeState) (node : ByteArray) (idx : Nat),
        CurrentNodeRel wordOfHash16 s node →
        CurrentNodeRel wordOfHash16
          (SegmentLayer3.stepLayer
            { s with bindings := bindValue s.bindings "layer" (wordNormalize idx) })
          (specStep idx node))
    (hSpecFold : ClimbLoop.specFold specStep forsPk 0 (wordNormalize 2) = specRoot)
    (hWordCmp : decide (wordOfHash16 specRoot = wordOfHash16 pkRoot)
          = (specRoot == pkRoot)) :
    ∃ finalState,
      verifyParsed C13Concrete.c13PrimitivesConcrete c13 pk message sigParsed
        = some (specRoot == pk.pkRoot) ∧
      execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody
        = .return (wordNormalize (boolWord (specRoot == pk.pkRoot))) finalState := by
  have hForsPkWord :
      lookupValue (afterFinalize (mkC13State pkSeed pkRoot message sig)).bindings "forsPk"
        = wordOfHash16 forsPk :=
    CurrentNodeFrame.afterFinalize_forsPk_of_compress
      (mkC13State pkSeed pkRoot message sig) forsPk hForsCompress
  exact accept_path_returns_verifyParsed_bool_from_layer_step
    pkSeed pkRoot message sig pk sigParsed forsPk specRoot specStep hPk
    hShape hZero hFors hFold hlen hg3 hgL hForsPkWord hLayerStep hSpecFold hWordCmp

/-! ## Axiom audit. -/

#print axioms accept_path_returns_verifyParsed_bool
#print axioms accept_path_returns_verifyParsed_bool_linked
#print axioms verifyParsed_ok_branch
#print axioms accept_path_returns_verifyParsed_bool_from_root
#print axioms wordCmp_of_wordOfHash16_iff
#print axioms accept_path_returns_verifyParsed_bool_from_layer_step
#print axioms accept_path_returns_verifyParsed_bool_from_fors_compress_and_layer_step

end SphincsMinusVerifiers.SegmentAcceptSpec
