/-
  C12BridgePrep — bridge-facing reducers for the concrete `execC12`.

  This file mirrors the C13 bridge-prep shape at the narrower C12 boundary that
  is currently available: malformed lengths are already proved against the real
  interpreter, and the good-length byte spec reduces to `verifyParsed` through
  the concrete C12 parser.  The remaining executable obligation is therefore the
  parsed correspondence theorem stated below as a premise, not an assumed constant.
-/

import SphincsMinusVerifiers.ProofCore
import SphincsMinusVerifiers.C12SegmentSeed
import SphincsMinusVerifiers.C12SegmentFors
import SphincsMinusVerifiers.C12SegmentForsCompress
import SphincsMinusVerifiers.C12SegmentWotsSetup
import SphincsMinusVerifiers.C12SegmentFinal
import SphincsMinusVerifiers.MemoryKit
import SphincsMinusVerifiers.SegmentAcceptSpec
import SphincsMinusVerifiers.ClimbMemFrameMerkle

namespace SphincsMinusVerifiers.C12BridgePrep

open Compiler.Proofs.IRGeneration.SourceSemantics
open SphincsMinusVerifiers
open SphincsMinusVerifierSpec

/-- The concrete body runner under the C12 bridge-prep name. -/
def runC12BodyObserved
    (pkSeed pkRoot message sig : ByteArray) : Option Bool :=
  execC12 pkSeed pkRoot message sig

/-- Malformed C12 lengths are already discharged locally: the concrete body
reverts at the length guard, and the byte spec returns `none`. -/
theorem runC12BodyObserved_revert_on_bad_length
    (pkSeed pkRoot message sig : ByteArray)
    (hLen : sig.size ≠ c12.sigBytes) :
    runC12BodyObserved pkSeed pkRoot message sig =
      ByteLevel.verifyBytes c12Primitives c12 pkSeed pkRoot message sig := by
  have hBody :
      execStmtList [] (MkC13State.mkC13State pkSeed pkRoot message sig) c12VerifyBody =
        .revert := by
    apply c12VerifyBody_reverts_on_bad_length
    show sig.size ≠ wordNormalize 6512
    simpa [c12] using hLen
  have hSpec :
      ByteLevel.verifyBytes c12Primitives c12 pkSeed pkRoot message sig = none :=
    ByteLevel.verifyBytes_bad_length c12Primitives c12 pkSeed pkRoot message sig hLen
  unfold runC12BodyObserved execC12
  rw [hBody, hSpec]
  rfl

/-- A successful concrete C12 parse exposes the byte length expected by the
variant.  The parser's only failure branch is its length guard. -/
theorem parseSignatureC12_size_of_some
    {v : Variant} {sig : ByteArray} {sigParsed : Signature}
    (hParse : C12Concrete.parseSignatureC12 v sig = some sigParsed) :
    sig.size = v.sigBytes := by
  unfold C12Concrete.parseSignatureC12 at hParse
  by_cases hLen : sig.size = v.sigBytes
  · exact hLen
  · simp [hLen] at hParse

/-- Successful concrete C12 parsing pins the ABI `sig_length` local to the C12
model length guard.  This is the C12 analogue of the C13 bridge-prep length
handoff, specialized to the frozen byte-facing entry state. -/
theorem c12_sig_length_of_parseSignatureC12
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature)
    (hParse : C12Concrete.parseSignatureC12 c12 sig = some sigParsed) :
    lookupValue (MkC13State.mkC13State pkSeed pkRoot message sig).bindings "sig_length"
      = wordNormalize 6512 := by
  have hSize : sig.size = c12.sigBytes :=
    parseSignatureC12_size_of_some hParse
  rw [show lookupValue (MkC13State.mkC13State pkSeed pkRoot message sig).bindings
      "sig_length" = sig.size by rfl, hSize]
  rfl

/-- First concrete C12 executable segment: after a successful parse, the real
`c12VerifyBody` length guard passes and the observed runner is exactly the
observation of the post-length body tail.  The remaining executable
correspondence starts at this `c12VerifyBody.tail` boundary. -/
theorem runC12BodyObserved_passes_length_guard_of_parse
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature)
    (hParse : C12Concrete.parseSignatureC12 c12 sig = some sigParsed) :
    runC12BodyObserved pkSeed pkRoot message sig =
      observeStmtResultBool
        (execStmtList [] (MkC13State.mkC13State pkSeed pkRoot message sig)
          c12VerifyBody.tail) := by
  unfold runC12BodyObserved execC12
  rw [c12VerifyBody_passes_length_guard
    (MkC13State.mkC13State pkSeed pkRoot message sig)
    (c12_sig_length_of_parseSignatureC12 pkSeed pkRoot message sig sigParsed hParse)]

/-- Exact C12 parsed executable correspondence reduced to the next executable
boundary after the concrete length guard.  This names the minimal next missing
correspondence theorem: prove the observed `c12VerifyBody.tail` run equals
`verifyParsed` for a successfully parsed C12 signature. -/
theorem runC12BodyObserved_eq_verifyParsed_of_parse_and_tail
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature)
    (hParse : C12Concrete.parseSignatureC12 c12 sig = some sigParsed)
    (hTail :
      observeStmtResultBool
          (execStmtList [] (MkC13State.mkC13State pkSeed pkRoot message sig)
            c12VerifyBody.tail)
        =
          verifyParsed C12Concrete.c12PrimitivesConcrete c12
            { pkSeed := pkSeed, pkRoot := pkRoot } message sigParsed) :
    runC12BodyObserved pkSeed pkRoot message sig =
      verifyParsed C12Concrete.c12PrimitivesConcrete c12
        { pkSeed := pkSeed, pkRoot := pkRoot } message sigParsed := by
  rw [runC12BodyObserved_passes_length_guard_of_parse
    pkSeed pkRoot message sig sigParsed hParse, hTail]

/-- Exact C12 parsed executable correspondence reduced to the next executable
boundary after the seed setup segment. This names the minimal next missing
correspondence theorem: prove the observed `c12AfterSeedSetup` run equals
`verifyParsed` for a successfully parsed C12 signature. -/
theorem runC12BodyObserved_eq_verifyParsed_of_parse_and_after_seed
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature)
    (hParse : C12Concrete.parseSignatureC12 c12 sig = some sigParsed)
    (hTail :
      observeStmtResultBool
          (execStmtList [] (C12SegmentSeed.c12StepSeed
              (MkC13State.mkC13State pkSeed pkRoot message sig))
            C12SegmentSeed.c12AfterSeedSetup)
        =
          verifyParsed C12Concrete.c12PrimitivesConcrete c12
            { pkSeed := pkSeed, pkRoot := pkRoot } message sigParsed) :
    runC12BodyObserved pkSeed pkRoot message sig =
      verifyParsed C12Concrete.c12PrimitivesConcrete c12
        { pkSeed := pkSeed, pkRoot := pkRoot } message sigParsed := by
  apply runC12BodyObserved_eq_verifyParsed_of_parse_and_tail pkSeed pkRoot message sig sigParsed hParse
  rw [C12SegmentSeed.c12VerifyBody_tail_eq]
  have hSeed := C12SegmentSeed.execC12SeedSetup (MkC13State.mkC13State pkSeed pkRoot message sig)
  rw [MemoryKit.execStmtList_append_continue _ _ _ _ hSeed]
  exact hTail

/-- Exact C12 parsed executable correspondence reduced to the next executable
boundary after the FORS root-reconstruction loop. This advances the
post-`c12StepSeed` obligation by proving the interpreter effect of the first
statement in `c12AfterSeedSetup`. -/
theorem runC12BodyObserved_eq_verifyParsed_of_parse_and_after_fors
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature)
    (hParse : C12Concrete.parseSignatureC12 c12 sig = some sigParsed)
    (hTail :
      observeStmtResultBool
          (execStmtList [] (C12SegmentFors.c12StepFors
              (C12SegmentSeed.c12StepSeed
                (MkC13State.mkC13State pkSeed pkRoot message sig)))
            C12SegmentFors.c12AfterFors)
        =
          verifyParsed C12Concrete.c12PrimitivesConcrete c12
            { pkSeed := pkSeed, pkRoot := pkRoot } message sigParsed) :
    runC12BodyObserved pkSeed pkRoot message sig =
      verifyParsed C12Concrete.c12PrimitivesConcrete c12
        { pkSeed := pkSeed, pkRoot := pkRoot } message sigParsed := by
  apply runC12BodyObserved_eq_verifyParsed_of_parse_and_after_seed
    pkSeed pkRoot message sig sigParsed hParse
  rw [C12SegmentFors.c12AfterSeedSetup_observed_eq_after_fors]
  exact hTail

/-- Exact C12 parsed executable correspondence reduced to the next executable
boundary after FORS-root compression and hypertree-loop setup. This advances the
post-`c12StepFors` obligation by proving the interpreter effect of the concrete
FORS roots compression segment. -/
theorem runC12BodyObserved_eq_verifyParsed_of_parse_and_after_fors_compress
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature)
    (hParse : C12Concrete.parseSignatureC12 c12 sig = some sigParsed)
    (hTail :
      observeStmtResultBool
          (execStmtList [] (C12SegmentForsCompress.c12StepForsCompress
              (C12SegmentFors.c12StepFors
                (C12SegmentSeed.c12StepSeed
                  (MkC13State.mkC13State pkSeed pkRoot message sig))))
            C12SegmentForsCompress.c12AfterForsCompress)
        =
          verifyParsed C12Concrete.c12PrimitivesConcrete c12
            { pkSeed := pkSeed, pkRoot := pkRoot } message sigParsed) :
    runC12BodyObserved pkSeed pkRoot message sig =
      verifyParsed C12Concrete.c12PrimitivesConcrete c12
        { pkSeed := pkSeed, pkRoot := pkRoot } message sigParsed := by
  apply runC12BodyObserved_eq_verifyParsed_of_parse_and_after_fors
    pkSeed pkRoot message sig sigParsed hParse
  rw [C12SegmentForsCompress.c12AfterFors_observed_eq_after_fors_compress]
  exact hTail

/-- Exact C12 parsed executable correspondence reduced to the tail after the
five-layer WOTS/XMSS hypertree loop. This advances the post-FORS-compression
obligation by proving the interpreter effect of the concrete C12 layer loop. -/
theorem runC12BodyObserved_eq_verifyParsed_of_parse_and_after_layer_loop
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature)
    (hParse : C12Concrete.parseSignatureC12 c12 sig = some sigParsed)
    (hTail :
      observeStmtResultBool
          (execStmtList [] (C12SegmentWotsSetup.c12StepLayerLoop
              (C12SegmentForsCompress.c12StepForsCompress
                (C12SegmentFors.c12StepFors
                  (C12SegmentSeed.c12StepSeed
                    (MkC13State.mkC13State pkSeed pkRoot message sig)))))
            C12SegmentWotsSetup.c12AfterLayerLoop)
        =
          verifyParsed C12Concrete.c12PrimitivesConcrete c12
            { pkSeed := pkSeed, pkRoot := pkRoot } message sigParsed) :
    runC12BodyObserved pkSeed pkRoot message sig =
      verifyParsed C12Concrete.c12PrimitivesConcrete c12
        { pkSeed := pkSeed, pkRoot := pkRoot } message sigParsed := by
  apply runC12BodyObserved_eq_verifyParsed_of_parse_and_after_fors_compress
    pkSeed pkRoot message sig sigParsed hParse
  rw [C12SegmentWotsSetup.c12AfterForsCompress_observed_eq_after_layer_loop]
  exact hTail

/-- Exact C12 parsed executable correspondence reduced past the final executable
root-comparison/return tail. This advances the post-layer-loop obligation by
proving that the concrete tail observes exactly the runtime `currentNode == root`
comparison result. -/
theorem runC12BodyObserved_eq_verifyParsed_of_parse_and_final_result
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature)
    (hParse : C12Concrete.parseSignatureC12 c12 sig = some sigParsed)
    (specRoot : ByteArray)
    (hSpec :
      verifyParsed C12Concrete.c12PrimitivesConcrete c12
        { pkSeed := pkSeed, pkRoot := pkRoot } message sigParsed =
          some (rootMatchesPk c12 specRoot pkRoot))
    (hCurrent :
      lookupValue
        (C12SegmentWotsSetup.c12StepLayerLoop
          (C12SegmentForsCompress.c12StepForsCompress
            (C12SegmentFors.c12StepFors
              (C12SegmentSeed.c12StepSeed
                (MkC13State.mkC13State pkSeed pkRoot message sig))))).bindings
          "currentNode" =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 specRoot)
    (hRoot :
      lookupValue
        (C12SegmentWotsSetup.c12StepLayerLoop
          (C12SegmentForsCompress.c12StepForsCompress
            (C12SegmentFors.c12StepFors
              (C12SegmentSeed.c12StepSeed
                (MkC13State.mkC13State pkSeed pkRoot message sig))))).bindings
          "root" =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkRoot)
    (hWordCmp :
      decide
          (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 specRoot =
            SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkRoot) =
        rootMatchesPk c12 specRoot pkRoot) :
    runC12BodyObserved pkSeed pkRoot message sig =
      verifyParsed C12Concrete.c12PrimitivesConcrete c12
        { pkSeed := pkSeed, pkRoot := pkRoot } message sigParsed := by
  apply runC12BodyObserved_eq_verifyParsed_of_parse_and_after_layer_loop
    pkSeed pkRoot message sig sigParsed hParse
  rw [C12SegmentFinal.c12AfterLayerLoop_observed_eq_final_result]
  unfold C12SegmentFinal.c12FinalResult
  rw [hCurrent, hRoot, hWordCmp, hSpec]

/-- On a parsed C12 signature, byte-level verification is exactly the parsed
algorithmic verifier under the concrete C12 primitive package. -/
theorem c12_verifyBytes_eq_verifyParsed_of_parse
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature)
    (hParse : C12Concrete.parseSignatureC12 c12 sig = some sigParsed) :
    ByteLevel.verifyBytes c12Primitives c12 pkSeed pkRoot message sig =
      verifyParsed C12Concrete.c12PrimitivesConcrete c12
        { pkSeed := pkSeed, pkRoot := pkRoot } message sigParsed := by
  have hLen : sig.size = c12.sigBytes :=
    parseSignatureC12_size_of_some hParse
  unfold ByteLevel.verifyBytes
  simp [hLen, C12Concrete.parsePublicKey_c12, c12Primitives,
    C12Concrete.c12PrimitivesConcrete, hParse]

/-- Parsed executable correspondence, packaged as the minimal remaining C12
MODEL-EXEC-BRIDGE obligation.

Proving this premise for the real `c12VerifyBody` closes the good-length branch:
the byte-spec side has already been reduced to `verifyParsed`, and the malformed
length branch is supplied by `runC12BodyObserved_revert_on_bad_length`. -/
theorem runC12BodyObserved_eq_verifyBytes_of_parse_and_verifyParsed
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature)
    (hParse : C12Concrete.parseSignatureC12 c12 sig = some sigParsed)
    (hExec :
      runC12BodyObserved pkSeed pkRoot message sig =
        verifyParsed C12Concrete.c12PrimitivesConcrete c12
          { pkSeed := pkSeed, pkRoot := pkRoot } message sigParsed) :
    runC12BodyObserved pkSeed pkRoot message sig =
      ByteLevel.verifyBytes c12Primitives c12 pkSeed pkRoot message sig := by
  rw [hExec, c12_verifyBytes_eq_verifyParsed_of_parse
    pkSeed pkRoot message sig sigParsed hParse]

/-- C12 bridge reducer whose caller no longer supplies the raw executable/spec
equality.  The remaining surface is split into the parsed verifier's produced
root, the final model `currentNode` and `root` bindings, and the word-vs-byte
root comparison. -/
theorem runC12BodyObserved_eq_verifyBytes_of_parse_and_final_semantics
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature)
    (hParse : C12Concrete.parseSignatureC12 c12 sig = some sigParsed)
    (specRoot : ByteArray)
    (hSpec :
      verifyParsed C12Concrete.c12PrimitivesConcrete c12
        { pkSeed := pkSeed, pkRoot := pkRoot } message sigParsed =
          some (rootMatchesPk c12 specRoot pkRoot))
    (hCurrent :
      lookupValue
        (C12SegmentWotsSetup.c12StepLayerLoop
          (C12SegmentForsCompress.c12StepForsCompress
            (C12SegmentFors.c12StepFors
              (C12SegmentSeed.c12StepSeed
                (MkC13State.mkC13State pkSeed pkRoot message sig))))).bindings
          "currentNode" =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 specRoot)
    (hRoot :
      lookupValue
        (C12SegmentWotsSetup.c12StepLayerLoop
          (C12SegmentForsCompress.c12StepForsCompress
            (C12SegmentFors.c12StepFors
              (C12SegmentSeed.c12StepSeed
                (MkC13State.mkC13State pkSeed pkRoot message sig))))).bindings
          "root" =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkRoot)
    (hWordCmp :
      decide
          (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 specRoot =
            SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkRoot) =
        rootMatchesPk c12 specRoot pkRoot) :
    runC12BodyObserved pkSeed pkRoot message sig =
      ByteLevel.verifyBytes c12Primitives c12 pkSeed pkRoot message sig := by
  exact
    runC12BodyObserved_eq_verifyBytes_of_parse_and_verifyParsed
      pkSeed pkRoot message sig sigParsed hParse
      (runC12BodyObserved_eq_verifyParsed_of_parse_and_final_result
        pkSeed pkRoot message sig sigParsed hParse specRoot
        hSpec hCurrent hRoot hWordCmp)

/-- Local C12 final comparison bridge used by the direct bridge-prep check.  It
matches `C12SegmentFinal.wordCmp_of_wordOfHash16_rootMatchesPk_c12`, but is kept
in this file so `lake env lean C12BridgePrep.lean` does not depend on rebuilt
oleans for edited imports. -/
theorem wordCmp_of_wordOfHash16_rootMatchesPk_c12
    (specRoot pkRoot : ByteArray)
    (hSpec :
      SphincsMinusVerifierSpec.C13Concrete.hash16OfWord
        (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 specRoot) =
        specRoot) :
    decide
        (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 specRoot =
          SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkRoot)
      = rootMatchesPk c12 specRoot pkRoot := by
  rw [← SegmentAcceptSpec.wordOfHash16_lowBytesProjection16 pkRoot]
  unfold rootMatchesPk comparePkRootBytes
  simp [c12]
  exact SegmentAcceptSpec.wordCmp_of_wordOfHash16_roundtrip
    specRoot (lowBytesProjection 16 pkRoot) hSpec
    (SegmentAcceptSpec.hash16OfWord_wordOfHash16_of_size
      (lowBytesProjection 16 pkRoot) (by
        simp [lowBytesProjection, bytesOfNatBE, ByteArray.size]))

/-- The concrete C12 parser constructs a parsed signature with exactly the
scheme shape expected by `verifyParsed`. -/
theorem c12_signatureShapeOk_of_parse
    (sig : ByteArray) (sigParsed : Signature)
    (hParse : C12Concrete.parseSignatureC12 c12 sig = some sigParsed) :
    signatureShapeOk c12 sigParsed = true := by
  unfold C12Concrete.parseSignatureC12 at hParse
  by_cases hLen : sig.size = c12.sigBytes
  · simp [hLen] at hParse
    rw [← hParse]
    simp [signatureShapeOk, allSized, allAuthSized, c12,
      C12Concrete.read32, C13Concrete.read16, ByteArray.size]
  · simp [hLen] at hParse

/-- Under a successful concrete C12 parse, the parsed verifier always reaches a
final hypertree root, and that produced root is canonical as a 16-byte
`wordOfHash16` roundtrip.  This closes the parsed-verifier and canonicality parts
of the former monolithic `hParsedRoot` premise. -/
theorem c12_verifyParsed_root_roundtrip_of_parse
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature)
    (hParse : C12Concrete.parseSignatureC12 c12 sig = some sigParsed) :
    ∃ specRoot,
      verifyParsed C12Concrete.c12PrimitivesConcrete c12
        { pkSeed := pkSeed, pkRoot := pkRoot } message sigParsed =
          some (rootMatchesPk c12 specRoot pkRoot) ∧
      SphincsMinusVerifierSpec.C13Concrete.hash16OfWord
        (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 specRoot) =
        specRoot := by
  unfold C12Concrete.parseSignatureC12 at hParse
  by_cases hLen : sig.size = c12.sigBytes
  · simp [hLen] at hParse
    rw [← hParse]
    unfold verifyParsed
    simp [signatureShapeOk, allSized, allAuthSized, c12,
      C12Concrete.read32, C13Concrete.read16, ByteArray.size,
      forcedZeroOk, C12Concrete.c12PrimitivesConcrete,
      C12Concrete.forsPkFromSigC12, foldHypertree, foldHypertreeAux,
      C12Concrete.wotsPkFromSigC12AtLayer,
      C12Concrete.xmssRootFromSigC12AtLayer, wotsGrindingFailsAtLayer]
    refine ⟨_, rfl, ?_⟩
    exact SegmentAcceptSpec.hash16OfWord_wordOfHash16_hash16OfWord _
  · simp [hLen] at hParse

/-- Under a successful concrete C12 parse, the parsed verifier reaches an
`.ok` hypertree root.  This names the exact spec-side root selected by the C12
fold, so executable current-node obligations do not have to quantify over every
byte array that happens to make the final boolean have the same value. -/
theorem c12_verifyParsed_root_roundtrip_and_fold_ok_of_parse
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature)
    (hParse : C12Concrete.parseSignatureC12 c12 sig = some sigParsed) :
    ∃ specRoot,
      verifyParsed C12Concrete.c12PrimitivesConcrete c12
        { pkSeed := pkSeed, pkRoot := pkRoot } message sigParsed =
          some (rootMatchesPk c12 specRoot pkRoot) ∧
      foldHypertree C12Concrete.c12PrimitivesConcrete c12
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C12Concrete.hMsgC12 c12
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        ((C12Concrete.forsPkFromSigC12 c12
            { pkSeed := pkSeed, pkRoot := pkRoot }
            (C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
            sigParsed.fors).getD ⟨#[]⟩)
        sigParsed.layers = .ok specRoot ∧
      SphincsMinusVerifierSpec.C13Concrete.hash16OfWord
        (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 specRoot) =
        specRoot := by
  unfold C12Concrete.parseSignatureC12 at hParse
  by_cases hLen : sig.size = c12.sigBytes
  · simp [hLen] at hParse
    rw [← hParse]
    unfold verifyParsed
    simp [signatureShapeOk, allSized, allAuthSized, c12,
      C12Concrete.read32, C13Concrete.read16, ByteArray.size,
      forcedZeroOk, C12Concrete.c12PrimitivesConcrete,
      C12Concrete.forsPkFromSigC12, foldHypertree, foldHypertreeAux,
      C12Concrete.wotsPkFromSigC12AtLayer,
      C12Concrete.xmssRootFromSigC12AtLayer, wotsGrindingFailsAtLayer]
    exact SegmentAcceptSpec.hash16OfWord_wordOfHash16_hash16OfWord _
  · simp [hLen] at hParse

/-- Empty layer used only as the total default in the unrolled C12 fold helper.
Successful C12 parsing supplies all five concrete layers, so this default is not
observed in the parsed reduction theorem below. -/
def c12EmptyXmssLayerSig : XmssLayerSig :=
  { wots := { chains := [], count := 0 }, authPath := [] }

/-- One successful C12 hypertree layer, written as the byte root produced by the
concrete spec primitives. -/
def c12FoldLayerRoot
    (pkSeed : ByteArray) (layer idxTree : Nat) (node : ByteArray)
    (lsig : XmssLayerSig) : ByteArray :=
  let idxLeaf := idxTree % 16
  let nextTree := idxTree / 16
  let wotsPk :=
    SphincsMinusVerifierSpec.C13Concrete.hash16OfWord
      (C12Concrete.wotsPkWordC12
        (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed)
        layer nextTree idxLeaf
        (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 node)
        lsig.wots)
  SphincsMinusVerifierSpec.C13Concrete.hash16OfWord
    (SphincsMinusVerifierSpec.C13Concrete.xmssClimb
      (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed)
      (C12Concrete.xmssBaseC12 layer nextTree)
      4 0 idxLeaf
      (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 wotsPk)
      lsig.authPath)

/-- Layer-indexed WOTS/XMSS byte-root roundtrip helper.  Once an executable
XMSS loop has been reduced to the raw word-level `xmssClimb` for a concrete
C12 hypertree layer, this theorem wraps it back into the `wordOfHash16
(c12FoldLayerRoot ...)` form used by the unrolled C12 root definitions.

The proof is independent of the executable state and the layer number. -/
theorem c12_wots_xmss_roundtrip_of_raw_xmssClimb_at_layer
    (pkSeed : ByteArray) (layer idxTree : Nat) (node : ByteArray)
    (lsig : XmssLayerSig) (actual : Nat)
    (hRaw :
      actual =
        SphincsMinusVerifierSpec.C13Concrete.xmssClimb
          (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed)
          (C12Concrete.xmssBaseC12 layer (idxTree / 16))
          4 0 (idxTree % 16)
          (C12Concrete.wotsPkWordC12
            (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed)
            layer (idxTree / 16) (idxTree % 16)
            (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 node)
            lsig.wots)
          lsig.authPath) :
    actual =
      SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
        (c12FoldLayerRoot pkSeed layer idxTree node lsig) := by
  let seedWord := SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed
  let nodeWord := SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 node
  let nextTree := idxTree / 16
  let idxLeaf := idxTree % 16
  let wotsWord :=
    C12Concrete.wotsPkWordC12 seedWord layer nextTree idxLeaf nodeWord lsig.wots
  rw [hRaw]
  have hWotsRoundtrip :
      SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          (SphincsMinusVerifierSpec.C13Concrete.hash16OfWord wotsWord) =
        wotsWord := by
    unfold wotsWord C12Concrete.wotsPkWordC12
    exact SegmentAcceptSpec.wordOfHash16_hash16OfWord_maskN_of_lt _ (by
      simpa [Compiler.Constants.evmModulus] using
        SphincsMinusVerifiers.KeccakBridge.keccakWords_lt
          (seedWord ::
            C12Concrete.wotsPkAdrsC12 layer nextTree idxLeaf ::
            (List.range 45).map (fun i =>
              let digit :=
                if i < 42 then
                  C12Concrete.wotsDigitC12 nodeWord i
                else
                  ((C12Concrete.wotsCsumC12 nodeWord <<< 7) >>>
                      (13 - 3 * (i - 42))) %
                    8
              let steps := 7 - digit
              let val :=
                SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
                  ((lsig.wots.chains[i]?).getD ⟨#[]⟩)
              let chainBase := C12Concrete.wotsBaseC12 layer nextTree idxLeaf ||| (i <<< 64)
              C12Concrete.chainHashC12 seedWord chainBase digit steps 0 val)))
  have hXmssRoundtrip :=
    SegmentAcceptSpec.xmssClimb_roundtrip_of_node_roundtrip
      seedWord (C12Concrete.xmssBaseC12 layer nextTree)
      4 0 idxLeaf wotsWord lsig.authPath hWotsRoundtrip
  unfold c12FoldLayerRoot
  change
    SphincsMinusVerifierSpec.C13Concrete.xmssClimb
      seedWord (C12Concrete.xmssBaseC12 layer nextTree) 4 0 idxLeaf
      wotsWord lsig.authPath =
    SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
      (SphincsMinusVerifierSpec.C13Concrete.hash16OfWord
        (SphincsMinusVerifierSpec.C13Concrete.xmssClimb
          seedWord (C12Concrete.xmssBaseC12 layer nextTree) 4 0 idxLeaf
          (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
            (SphincsMinusVerifierSpec.C13Concrete.hash16OfWord wotsWord))
          lsig.authPath))
  rw [hWotsRoundtrip]
  exact hXmssRoundtrip.symm

/-- The C12 five-layer successful fold, unrolled into named layer roots.  This
is the exact spec-side root expression left for the executable layer loop to
match after the `foldHypertree` result has been eliminated. -/
def c12FoldRootUnrolled5
    (pkSeed : ByteArray) (idxTree : Nat) (startNode : ByteArray)
    (layers : List XmssLayerSig) : ByteArray :=
  let l0 := (layers[0]?).getD c12EmptyXmssLayerSig
  let r0 := c12FoldLayerRoot pkSeed 0 idxTree startNode l0
  let t1 := idxTree / 16
  let l1 := (layers[1]?).getD c12EmptyXmssLayerSig
  let r1 := c12FoldLayerRoot pkSeed 1 t1 r0 l1
  let t2 := t1 / 16
  let l2 := (layers[2]?).getD c12EmptyXmssLayerSig
  let r2 := c12FoldLayerRoot pkSeed 2 t2 r1 l2
  let t3 := t2 / 16
  let l3 := (layers[3]?).getD c12EmptyXmssLayerSig
  let r3 := c12FoldLayerRoot pkSeed 3 t3 r2 l3
  let t4 := t3 / 16
  let l4 := (layers[4]?).getD c12EmptyXmssLayerSig
  c12FoldLayerRoot pkSeed 4 t4 r3 l4

/-! ### Executable five-layer C12 current-node reduction

The bridge's remaining executable fact is easier to discharge one layer at a
time.  The definitions below name the exact runtime states after each concrete
C12 layer iteration and the matching unrolled spec roots. -/

def c12LayerLoopFold (st : RuntimeState) (layers : Nat) : RuntimeState :=
  SphincsMinusVerifiers.ClimbLoop.foldLoop "layer" C12SegmentWotsSetup.c12LayerStep
    { st with bindings := bindValue st.bindings "layer" (wordNormalize 0) }
    0 (wordNormalize layers)

def c12LayerStateAfter0 (st : RuntimeState) : RuntimeState :=
  c12LayerLoopFold st 1

def c12LayerStateAfter1 (st : RuntimeState) : RuntimeState :=
  c12LayerLoopFold st 2

def c12LayerStateAfter2 (st : RuntimeState) : RuntimeState :=
  c12LayerLoopFold st 3

def c12LayerStateAfter3 (st : RuntimeState) : RuntimeState :=
  c12LayerLoopFold st 4

def c12LayerStateAfter4 (st : RuntimeState) : RuntimeState :=
  c12LayerLoopFold st 5

/-- After the first C12 hypertree layer, `"sigOff"` has advanced over one
WOTS/XMSS-auth layer. -/
theorem c12LayerStateAfter0_sigOff_eq_after_fors_compress
    (st : RuntimeState) :
    lookupValue
        (c12LayerStateAfter0 (C12SegmentForsCompress.c12StepForsCompress st)).bindings
        "sigOff" =
      wordNormalize 3376 := by
  unfold c12LayerStateAfter0 c12LayerLoopFold
  rw [show wordNormalize 1 = 1 by rfl]
  rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_succ,
    SphincsMinusVerifiers.ClimbLoop.foldLoop_zero]
  rw [C12SegmentWotsSetup.c12LayerStep_sigOff_eq_of_sigOff]
  simp [MemoryKit.lookupValue_bindValue_ne,
    C12SegmentForsCompress.c12StepForsCompress_sigOff_eq]
  simp only [HAdd.hAdd]
  norm_num [wordNormalize, Compiler.Constants.evmModulus,
    Verity.Core.Uint256.add, Verity.Core.Uint256.ofNat,
    Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS]

/-- After the second C12 hypertree layer, `"sigOff"` has advanced over two
WOTS/XMSS-auth layers. -/
theorem c12LayerStateAfter1_sigOff_eq_after_fors_compress
    (st : RuntimeState) :
    lookupValue
        (c12LayerStateAfter1 (C12SegmentForsCompress.c12StepForsCompress st)).bindings
        "sigOff" =
      wordNormalize 4160 := by
  rw [show c12LayerStateAfter1 (C12SegmentForsCompress.c12StepForsCompress st) =
      C12SegmentWotsSetup.c12LayerStep
        { c12LayerStateAfter0 (C12SegmentForsCompress.c12StepForsCompress st) with
          bindings := bindValue
            (c12LayerStateAfter0 (C12SegmentForsCompress.c12StepForsCompress st)).bindings
            "layer" (wordNormalize 1) } by
    unfold c12LayerStateAfter1 c12LayerStateAfter0 c12LayerLoopFold
    rw [show wordNormalize 2 = 1 + 1 by rfl]
    rw [show wordNormalize 1 = 1 by rfl]
    rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_append]
    rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_succ,
      SphincsMinusVerifiers.ClimbLoop.foldLoop_zero]
    rfl]
  rw [C12SegmentWotsSetup.c12LayerStep_sigOff_eq_of_sigOff]
  simp [MemoryKit.lookupValue_bindValue_ne,
    c12LayerStateAfter0_sigOff_eq_after_fors_compress]
  simp only [HAdd.hAdd]
  norm_num [wordNormalize, Compiler.Constants.evmModulus,
    Verity.Core.Uint256.add, Verity.Core.Uint256.ofNat,
    Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS]

/-- After the third C12 hypertree layer, `"sigOff"` has advanced over three
WOTS/XMSS-auth layers. -/
theorem c12LayerStateAfter2_sigOff_eq_after_fors_compress
    (st : RuntimeState) :
    lookupValue
        (c12LayerStateAfter2 (C12SegmentForsCompress.c12StepForsCompress st)).bindings
        "sigOff" =
      wordNormalize 4944 := by
  rw [show c12LayerStateAfter2 (C12SegmentForsCompress.c12StepForsCompress st) =
      C12SegmentWotsSetup.c12LayerStep
        { c12LayerStateAfter1 (C12SegmentForsCompress.c12StepForsCompress st) with
          bindings := bindValue
            (c12LayerStateAfter1 (C12SegmentForsCompress.c12StepForsCompress st)).bindings
            "layer" (wordNormalize 2) } by
    unfold c12LayerStateAfter2 c12LayerStateAfter1 c12LayerLoopFold
    rw [show wordNormalize 3 = 2 + 1 by rfl]
    rw [show wordNormalize 2 = 2 by rfl]
    rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_append]
    rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_succ,
      SphincsMinusVerifiers.ClimbLoop.foldLoop_zero]
    rfl]
  rw [C12SegmentWotsSetup.c12LayerStep_sigOff_eq_of_sigOff]
  simp [MemoryKit.lookupValue_bindValue_ne,
    c12LayerStateAfter1_sigOff_eq_after_fors_compress]
  simp only [HAdd.hAdd]
  norm_num [wordNormalize, Compiler.Constants.evmModulus,
    Verity.Core.Uint256.add, Verity.Core.Uint256.ofNat,
    Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS]

/-- After the fourth C12 hypertree layer, `"sigOff"` is the layer-4 body input
offset. -/
theorem c12LayerStateAfter3_sigOff_eq_after_fors_compress
    (st : RuntimeState) :
    lookupValue
        (c12LayerStateAfter3 (C12SegmentForsCompress.c12StepForsCompress st)).bindings
        "sigOff" =
      wordNormalize 5728 := by
  rw [show c12LayerStateAfter3 (C12SegmentForsCompress.c12StepForsCompress st) =
      C12SegmentWotsSetup.c12LayerStep
        { c12LayerStateAfter2 (C12SegmentForsCompress.c12StepForsCompress st) with
          bindings := bindValue
            (c12LayerStateAfter2 (C12SegmentForsCompress.c12StepForsCompress st)).bindings
            "layer" (wordNormalize 3) } by
    unfold c12LayerStateAfter3 c12LayerStateAfter2 c12LayerLoopFold
    rw [show wordNormalize 4 = 3 + 1 by rfl]
    rw [show wordNormalize 3 = 3 by rfl]
    rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_append]
    rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_succ,
      SphincsMinusVerifiers.ClimbLoop.foldLoop_zero]
    rfl]
  rw [C12SegmentWotsSetup.c12LayerStep_sigOff_eq_of_sigOff]
  simp [MemoryKit.lookupValue_bindValue_ne,
    c12LayerStateAfter2_sigOff_eq_after_fors_compress]
  simp only [HAdd.hAdd]
  norm_num [wordNormalize, Compiler.Constants.evmModulus,
    Verity.Core.Uint256.add, Verity.Core.Uint256.ofNat,
    Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS]

/-- After the first C12 hypertree layer, `"curLeaf"` is the low nibble of the
initial hypertree index. -/
theorem c12LayerStateAfter0_curLeaf_eq_after_fors_compress
    (st : RuntimeState) :
    lookupValue
        (c12LayerStateAfter0 (C12SegmentForsCompress.c12StepForsCompress st)).bindings
        "curLeaf" =
      (Verity.Core.Uint256.and
        (lookupValue st.bindings "treeIdx")
        (wordNormalize 0xF)).val := by
  unfold c12LayerStateAfter0 c12LayerLoopFold
  rw [show wordNormalize 1 = 1 by rfl]
  rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_succ,
    SphincsMinusVerifiers.ClimbLoop.foldLoop_zero]
  rw [C12SegmentWotsSetup.c12LayerStep_curLeaf_eq_of_curTree]
  simp [MemoryKit.lookupValue_bindValue_ne,
    C12SegmentForsCompress.c12StepForsCompress_curTree_eq]

/-- After the first C12 hypertree layer, `"curTree"` has been shifted to the
next layer index. -/
theorem c12LayerStateAfter0_curTree_eq_after_fors_compress
    (st : RuntimeState) :
    lookupValue
        (c12LayerStateAfter0 (C12SegmentForsCompress.c12StepForsCompress st)).bindings
        "curTree" =
      (Verity.Core.Uint256.shr
        (wordNormalize 4)
        (lookupValue st.bindings "treeIdx")).val := by
  unfold c12LayerStateAfter0 c12LayerLoopFold
  rw [show wordNormalize 1 = 1 by rfl]
  rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_succ,
    SphincsMinusVerifiers.ClimbLoop.foldLoop_zero]
  rw [C12SegmentWotsSetup.c12LayerStep_curTree_eq_of_curTree]
  simp [MemoryKit.lookupValue_bindValue_ne,
    C12SegmentForsCompress.c12StepForsCompress_curTree_eq]

/-- After the second C12 hypertree layer, `"curLeaf"` is the next low nibble. -/
theorem c12LayerStateAfter1_curLeaf_eq_after_fors_compress
    (st : RuntimeState) :
    lookupValue
        (c12LayerStateAfter1 (C12SegmentForsCompress.c12StepForsCompress st)).bindings
        "curLeaf" =
      (Verity.Core.Uint256.and
        ((Verity.Core.Uint256.shr
          (wordNormalize 4)
          (lookupValue st.bindings "treeIdx")).val)
        (wordNormalize 0xF)).val := by
  rw [show c12LayerStateAfter1 (C12SegmentForsCompress.c12StepForsCompress st) =
      C12SegmentWotsSetup.c12LayerStep
        { c12LayerStateAfter0 (C12SegmentForsCompress.c12StepForsCompress st) with
          bindings := bindValue
            (c12LayerStateAfter0 (C12SegmentForsCompress.c12StepForsCompress st)).bindings
            "layer" (wordNormalize 1) } by
    unfold c12LayerStateAfter1 c12LayerStateAfter0 c12LayerLoopFold
    rw [show wordNormalize 2 = 1 + 1 by rfl]
    rw [show wordNormalize 1 = 1 by rfl]
    rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_append]
    rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_succ,
      SphincsMinusVerifiers.ClimbLoop.foldLoop_zero]
    rfl]
  rw [C12SegmentWotsSetup.c12LayerStep_curLeaf_eq_of_curTree]
  rw [MemoryKit.lookupValue_bindValue_ne _ "layer" "curTree" _ (by decide)]
  rw [c12LayerStateAfter0_curTree_eq_after_fors_compress]

/-- After the second C12 hypertree layer, `"curTree"` has been shifted twice. -/
theorem c12LayerStateAfter1_curTree_eq_after_fors_compress
    (st : RuntimeState) :
    lookupValue
        (c12LayerStateAfter1 (C12SegmentForsCompress.c12StepForsCompress st)).bindings
        "curTree" =
      (Verity.Core.Uint256.shr
        (wordNormalize 4)
        ((Verity.Core.Uint256.shr
          (wordNormalize 4)
          (lookupValue st.bindings "treeIdx")).val)).val := by
  rw [show c12LayerStateAfter1 (C12SegmentForsCompress.c12StepForsCompress st) =
      C12SegmentWotsSetup.c12LayerStep
        { c12LayerStateAfter0 (C12SegmentForsCompress.c12StepForsCompress st) with
          bindings := bindValue
            (c12LayerStateAfter0 (C12SegmentForsCompress.c12StepForsCompress st)).bindings
            "layer" (wordNormalize 1) } by
    unfold c12LayerStateAfter1 c12LayerStateAfter0 c12LayerLoopFold
    rw [show wordNormalize 2 = 1 + 1 by rfl]
    rw [show wordNormalize 1 = 1 by rfl]
    rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_append]
    rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_succ,
      SphincsMinusVerifiers.ClimbLoop.foldLoop_zero]
    rfl]
  rw [C12SegmentWotsSetup.c12LayerStep_curTree_eq_of_curTree]
  rw [MemoryKit.lookupValue_bindValue_ne _ "layer" "curTree" _ (by decide)]
  rw [c12LayerStateAfter0_curTree_eq_after_fors_compress]

/-- After the third C12 hypertree layer, `"curLeaf"` is the third low nibble. -/
theorem c12LayerStateAfter2_curLeaf_eq_after_fors_compress
    (st : RuntimeState) :
    lookupValue
        (c12LayerStateAfter2 (C12SegmentForsCompress.c12StepForsCompress st)).bindings
        "curLeaf" =
      (Verity.Core.Uint256.and
        ((Verity.Core.Uint256.shr
          (wordNormalize 4)
          ((Verity.Core.Uint256.shr
            (wordNormalize 4)
            (lookupValue st.bindings "treeIdx")).val)).val)
        (wordNormalize 0xF)).val := by
  rw [show c12LayerStateAfter2 (C12SegmentForsCompress.c12StepForsCompress st) =
      C12SegmentWotsSetup.c12LayerStep
        { c12LayerStateAfter1 (C12SegmentForsCompress.c12StepForsCompress st) with
          bindings := bindValue
            (c12LayerStateAfter1 (C12SegmentForsCompress.c12StepForsCompress st)).bindings
            "layer" (wordNormalize 2) } by
    unfold c12LayerStateAfter2 c12LayerStateAfter1 c12LayerLoopFold
    rw [show wordNormalize 3 = 2 + 1 by rfl]
    rw [show wordNormalize 2 = 2 by rfl]
    rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_append]
    rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_succ,
      SphincsMinusVerifiers.ClimbLoop.foldLoop_zero]
    rfl]
  rw [C12SegmentWotsSetup.c12LayerStep_curLeaf_eq_of_curTree]
  rw [MemoryKit.lookupValue_bindValue_ne _ "layer" "curTree" _ (by decide)]
  rw [c12LayerStateAfter1_curTree_eq_after_fors_compress]

/-- After the third C12 hypertree layer, `"curTree"` has been shifted three
times. -/
theorem c12LayerStateAfter2_curTree_eq_after_fors_compress
    (st : RuntimeState) :
    lookupValue
        (c12LayerStateAfter2 (C12SegmentForsCompress.c12StepForsCompress st)).bindings
        "curTree" =
      (Verity.Core.Uint256.shr
        (wordNormalize 4)
        ((Verity.Core.Uint256.shr
          (wordNormalize 4)
          ((Verity.Core.Uint256.shr
            (wordNormalize 4)
            (lookupValue st.bindings "treeIdx")).val)).val)).val := by
  rw [show c12LayerStateAfter2 (C12SegmentForsCompress.c12StepForsCompress st) =
      C12SegmentWotsSetup.c12LayerStep
        { c12LayerStateAfter1 (C12SegmentForsCompress.c12StepForsCompress st) with
          bindings := bindValue
            (c12LayerStateAfter1 (C12SegmentForsCompress.c12StepForsCompress st)).bindings
            "layer" (wordNormalize 2) } by
    unfold c12LayerStateAfter2 c12LayerStateAfter1 c12LayerLoopFold
    rw [show wordNormalize 3 = 2 + 1 by rfl]
    rw [show wordNormalize 2 = 2 by rfl]
    rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_append]
    rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_succ,
      SphincsMinusVerifiers.ClimbLoop.foldLoop_zero]
    rfl]
  rw [C12SegmentWotsSetup.c12LayerStep_curTree_eq_of_curTree]
  rw [MemoryKit.lookupValue_bindValue_ne _ "layer" "curTree" _ (by decide)]
  rw [c12LayerStateAfter1_curTree_eq_after_fors_compress]

/-- After the fourth C12 hypertree layer, `"curLeaf"` is the layer-4 leaf index. -/
theorem c12LayerStateAfter3_curLeaf_eq_after_fors_compress
    (st : RuntimeState) :
    lookupValue
        (c12LayerStateAfter3 (C12SegmentForsCompress.c12StepForsCompress st)).bindings
        "curLeaf" =
      (Verity.Core.Uint256.and
        ((Verity.Core.Uint256.shr
          (wordNormalize 4)
          ((Verity.Core.Uint256.shr
            (wordNormalize 4)
            ((Verity.Core.Uint256.shr
              (wordNormalize 4)
              (lookupValue st.bindings "treeIdx")).val)).val)).val)
        (wordNormalize 0xF)).val := by
  rw [show c12LayerStateAfter3 (C12SegmentForsCompress.c12StepForsCompress st) =
      C12SegmentWotsSetup.c12LayerStep
        { c12LayerStateAfter2 (C12SegmentForsCompress.c12StepForsCompress st) with
          bindings := bindValue
            (c12LayerStateAfter2 (C12SegmentForsCompress.c12StepForsCompress st)).bindings
            "layer" (wordNormalize 3) } by
    unfold c12LayerStateAfter3 c12LayerStateAfter2 c12LayerLoopFold
    rw [show wordNormalize 4 = 3 + 1 by rfl]
    rw [show wordNormalize 3 = 3 by rfl]
    rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_append]
    rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_succ,
      SphincsMinusVerifiers.ClimbLoop.foldLoop_zero]
    rfl]
  rw [C12SegmentWotsSetup.c12LayerStep_curLeaf_eq_of_curTree]
  rw [MemoryKit.lookupValue_bindValue_ne _ "layer" "curTree" _ (by decide)]
  rw [c12LayerStateAfter2_curTree_eq_after_fors_compress]

/-- After the fourth C12 hypertree layer, `"curTree"` has advanced to the
layer-4 parent tree. -/
theorem c12LayerStateAfter3_curTree_eq_after_fors_compress
    (st : RuntimeState) :
    lookupValue
        (c12LayerStateAfter3 (C12SegmentForsCompress.c12StepForsCompress st)).bindings
        "curTree" =
      (Verity.Core.Uint256.shr
        (wordNormalize 4)
        ((Verity.Core.Uint256.shr
          (wordNormalize 4)
          ((Verity.Core.Uint256.shr
            (wordNormalize 4)
            ((Verity.Core.Uint256.shr
              (wordNormalize 4)
              (lookupValue st.bindings "treeIdx")).val)).val)).val)).val := by
  rw [show c12LayerStateAfter3 (C12SegmentForsCompress.c12StepForsCompress st) =
      C12SegmentWotsSetup.c12LayerStep
        { c12LayerStateAfter2 (C12SegmentForsCompress.c12StepForsCompress st) with
          bindings := bindValue
            (c12LayerStateAfter2 (C12SegmentForsCompress.c12StepForsCompress st)).bindings
            "layer" (wordNormalize 3) } by
    unfold c12LayerStateAfter3 c12LayerStateAfter2 c12LayerLoopFold
    rw [show wordNormalize 4 = 3 + 1 by rfl]
    rw [show wordNormalize 3 = 3 by rfl]
    rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_append]
    rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_succ,
      SphincsMinusVerifiers.ClimbLoop.foldLoop_zero]
    rfl]
  rw [C12SegmentWotsSetup.c12LayerStep_curTree_eq_of_curTree]
  rw [MemoryKit.lookupValue_bindValue_ne _ "layer" "curTree" _ (by decide)]
  rw [c12LayerStateAfter2_curTree_eq_after_fors_compress]

/-- The executable five-iteration C12 layer loop is exactly the explicitly named
state obtained by running layer indices `0..4`. -/
theorem c12StepLayerLoop_eq_layerStateAfter4 (st : RuntimeState) :
    C12SegmentWotsSetup.c12StepLayerLoop st = c12LayerStateAfter4 st := by
  unfold C12SegmentWotsSetup.c12StepLayerLoop C12SegmentWotsSetup.c12LayerStmt
  rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ _
    (SphincsMinusVerifiers.ClimbLoop.execStmt_forEach_of_step
      "layer" _ C12SegmentWotsSetup.c12LayerBody st (wordNormalize 5)
      C12SegmentWotsSetup.c12LayerStep rfl
      C12SegmentWotsSetup.execC12LayerBody)]
  unfold c12LayerStateAfter4 c12LayerLoopFold
  rfl

def c12UnrolledLayerRoot0
    (pkSeed : ByteArray) (idxTree : Nat) (startNode : ByteArray)
    (layers : List XmssLayerSig) : ByteArray :=
  c12FoldLayerRoot pkSeed 0 idxTree startNode
    ((layers[0]?).getD c12EmptyXmssLayerSig)

def c12UnrolledLayerRoot1
    (pkSeed : ByteArray) (idxTree : Nat) (startNode : ByteArray)
    (layers : List XmssLayerSig) : ByteArray :=
  let r0 := c12UnrolledLayerRoot0 pkSeed idxTree startNode layers
  c12FoldLayerRoot pkSeed 1 (idxTree / 16) r0
    ((layers[1]?).getD c12EmptyXmssLayerSig)

def c12UnrolledLayerRoot2
    (pkSeed : ByteArray) (idxTree : Nat) (startNode : ByteArray)
    (layers : List XmssLayerSig) : ByteArray :=
  let t1 := idxTree / 16
  let r1 := c12UnrolledLayerRoot1 pkSeed idxTree startNode layers
  c12FoldLayerRoot pkSeed 2 (t1 / 16) r1
    ((layers[2]?).getD c12EmptyXmssLayerSig)

def c12UnrolledLayerRoot3
    (pkSeed : ByteArray) (idxTree : Nat) (startNode : ByteArray)
    (layers : List XmssLayerSig) : ByteArray :=
  let t1 := idxTree / 16
  let t2 := t1 / 16
  let r2 := c12UnrolledLayerRoot2 pkSeed idxTree startNode layers
  c12FoldLayerRoot pkSeed 3 (t2 / 16) r2
    ((layers[3]?).getD c12EmptyXmssLayerSig)

def c12UnrolledLayerRoot4
    (pkSeed : ByteArray) (idxTree : Nat) (startNode : ByteArray)
    (layers : List XmssLayerSig) : ByteArray :=
  let t1 := idxTree / 16
  let t2 := t1 / 16
  let t3 := t2 / 16
  let r3 := c12UnrolledLayerRoot3 pkSeed idxTree startNode layers
  c12FoldLayerRoot pkSeed 4 (t3 / 16) r3
    ((layers[4]?).getD c12EmptyXmssLayerSig)

def c12Layer4IdxTree (idxTree : Nat) : Nat :=
  (((idxTree / 16) / 16) / 16) / 16

def c12Layer4NextTree (idxTree : Nat) : Nat :=
  c12Layer4IdxTree idxTree / 16

def c12Layer4Leaf (idxTree : Nat) : Nat :=
  c12Layer4IdxTree idxTree % 16

def c12Layer4WotsPkBytes
    (pkSeed : ByteArray) (idxTree : Nat) (node : ByteArray)
    (layer4Sig : XmssLayerSig) : ByteArray :=
  SphincsMinusVerifierSpec.C13Concrete.hash16OfWord
    (C12Concrete.wotsPkWordC12
      (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed)
      4
      (c12Layer4NextTree idxTree)
      (c12Layer4Leaf idxTree)
      (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 node)
      layer4Sig.wots)

/-- The 45 C12 WOTS chain ends, extracted in the same shape as
`C12Concrete.wotsPkWordC12`'s internal final-Keccak preimage. -/
def c12WotsChainsEnd
    (seed : Nat) (layer treeIdx leafIdx node : Nat) (wots : WotsSig) :
    List Nat :=
  let wotsBase := C12Concrete.wotsBaseC12 layer treeIdx leafIdx
  let csum := C12Concrete.wotsCsumC12 node
  let csumShifted := csum <<< 7
  (List.range 45).map (fun i =>
    let digit :=
      if i < 42 then
        C12Concrete.wotsDigitC12 node i
      else
        (csumShifted >>> (13 - 3 * (i - 42))) % 8
    let steps := 7 - digit
    let val :=
      SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
        ((wots.chains[i]?).getD ⟨#[]⟩)
    let chainBase := wotsBase ||| (i <<< 64)
    C12Concrete.chainHashC12 seed chainBase digit steps 0 val)

theorem c12WotsChainsEnd_length
    (seed : Nat) (layer treeIdx leafIdx node : Nat) (wots : WotsSig) :
    (c12WotsChainsEnd seed layer treeIdx leafIdx node wots).length = 45 := by
  simp [c12WotsChainsEnd]

theorem nat_land_low3 (x : Nat) : Nat.land x 0x7 = x % 8 := by
  change (x &&& (2 ^ 3 - 1)) = x % 2 ^ 3
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_land]
  by_cases hi : i < 3
  · have hmask : (2 ^ 3 - 1).testBit i = true := by
      rw [Nat.testBit_two_pow_sub_one]
      exact decide_eq_true hi
    rw [hmask, Bool.and_true]
    rw [Nat.testBit_mod_two_pow]
    simp [hi]
  · have hmask : (2 ^ 3 - 1).testBit i = false := by
      rw [Nat.testBit_two_pow_sub_one]
      exact decide_eq_false hi
    rw [hmask, Bool.and_false]
    rw [Nat.testBit_mod_two_pow]
    simp [hi]

theorem c12WotsChainsEnd_getElem_message
    (seed : Nat) (layer treeIdx leafIdx node : Nat) (wots : WotsSig)
    (j : Nat) (hj : j < 42) :
    (c12WotsChainsEnd seed layer treeIdx leafIdx node wots)[j]'(by
        rw [c12WotsChainsEnd_length]
        omega) =
      C12Concrete.chainHashC12 seed
        (C12Concrete.wotsBaseC12 layer treeIdx leafIdx ||| (j <<< 64))
        ((node >>> (128 + 3 * j)) &&& 7)
        (7 - ((node >>> (128 + 3 * j)) &&& 7)) 0
        (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          ((wots.chains[j]?).getD ⟨#[]⟩)) := by
  unfold c12WotsChainsEnd C12Concrete.wotsDigitC12
  simp only [List.getElem_map, List.getElem_range]
  have hDigit : (node >>> (128 + 3 * j)) % 8 =
      (node >>> (128 + 3 * j)) &&& 7 := by
    change (node >>> (128 + 3 * j)) % 8 =
      Nat.land (node >>> (128 + 3 * j)) 7
    rw [nat_land_low3]
  rw [hDigit]
  simp [hj]

theorem c12WotsChainsEnd_getElem_checksum
    (seed : Nat) (layer treeIdx leafIdx node : Nat) (wots : WotsSig)
    (j : Nat) (hj : j < 3) :
    (c12WotsChainsEnd seed layer treeIdx leafIdx node wots)[42 + j]'(by
        rw [c12WotsChainsEnd_length]
        omega) =
      C12Concrete.chainHashC12 seed
        (C12Concrete.wotsBaseC12 layer treeIdx leafIdx ||| ((42 + j) <<< 64))
        (((C12Concrete.wotsCsumC12 node <<< 7) >>> (13 - 3 * j)) &&& 7)
        (7 - (((C12Concrete.wotsCsumC12 node <<< 7) >>> (13 - 3 * j)) &&& 7)) 0
        (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          ((wots.chains[42 + j]?).getD ⟨#[]⟩)) := by
  unfold c12WotsChainsEnd
  simp only [List.getElem_map, List.getElem_range]
  have hNot : ¬ 42 + j < 42 := by omega
  have hSub : 42 + j - 42 = j := by omega
  have hDigit :
      ((C12Concrete.wotsCsumC12 node <<< 7) >>> (13 - 3 * j)) % 8 =
        ((C12Concrete.wotsCsumC12 node <<< 7) >>> (13 - 3 * j)) &&& 7 := by
    change ((C12Concrete.wotsCsumC12 node <<< 7) >>> (13 - 3 * j)) % 8 =
      Nat.land (((C12Concrete.wotsCsumC12 node <<< 7) >>> (13 - 3 * j))) 7
    rw [nat_land_low3]
  simp [hNot, hSub, hDigit]

/-- `wotsPkWordC12` is definitionally the masked Keccak over
`seed || WOTS_PK_ADRS || chain_0..chain_44`. -/
theorem c12WotsPkWord_eq
    (seed : Nat) (layer treeIdx leafIdx node : Nat) (wots : WotsSig) :
    C12Concrete.wotsPkWordC12 seed layer treeIdx leafIdx node wots =
      SphincsMinusVerifierSpec.C13Concrete.maskN
        (SphincsMinusVerifierSpec.C13Concrete.keccakWords
          (seed :: C12Concrete.wotsPkAdrsC12 layer treeIdx leafIdx ::
            c12WotsChainsEnd seed layer treeIdx leafIdx node wots)) := rfl

theorem c12Layer4WotsPkBytes_wordOfHash16
    (pkSeed : ByteArray) (idxTree : Nat) (node : ByteArray)
    (layer4Sig : XmssLayerSig) :
    SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
        (c12Layer4WotsPkBytes pkSeed idxTree node layer4Sig) =
      C12Concrete.wotsPkWordC12
        (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed)
        4
        (c12Layer4NextTree idxTree)
        (c12Layer4Leaf idxTree)
        (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 node)
        layer4Sig.wots := by
  unfold c12Layer4WotsPkBytes
  rw [c12WotsPkWord_eq]
  exact SegmentAcceptSpec.wordOfHash16_hash16OfWord_maskN_of_lt _ (by
    exact
      SphincsMinusVerifiers.KeccakBridge.keccakWords_lt
        (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed ::
          C12Concrete.wotsPkAdrsC12 4
            (c12Layer4NextTree idxTree)
            (c12Layer4Leaf idxTree) ::
          c12WotsChainsEnd
            (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed)
            4
            (c12Layer4NextTree idxTree)
            (c12Layer4Leaf idxTree)
            (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 node)
            layer4Sig.wots))

/-- C12's WOTS public-key final Keccak over the 47-word scratch image.  This
keeps the executable Keccak bridge separate from the harder memory-frame fact
that the WOTS message/checksum loops have populated the 45 chain-end words. -/
theorem c12_wots_pk_node_eq
    (st : RuntimeState) (seed pkAdrs : Nat) (chainsEnd : List Nat)
    (hlen : chainsEnd.length = 45)
    (hm0 : (st.world.memory 0).val = seed)
    (hm1 : (st.world.memory 0x20).val = pkAdrs)
    (hmC : ∀ j, (h : j < 45) →
      (st.world.memory (0x40 + 32 * j)).val = chainsEnd[j]) :
    evalExpr [] st
        (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x5E0))
          (.literal SphincsMinusVerifierSpec.C13Concrete.nMask))
      = some
        (SphincsMinusVerifierSpec.C13Concrete.maskN
          (SphincsMinusVerifierSpec.C13Concrete.keccakWords
            (seed :: pkAdrs :: chainsEnd))) := by
  have hoff : wordNormalize (0 : Nat) = 0 := by
    rw [wordNormalize_eq_mod]
    exact Nat.zero_mod _
  have hlen47 : (seed :: pkAdrs :: chainsEnd).length = 47 := by
    simp only [List.length_cons, hlen]
  have hszlt : 32 * (seed :: pkAdrs :: chainsEnd).length < 2 ^ 256 := by
    rw [hlen47]
    decide
  have hmem : ∀ i, (h : i < (seed :: pkAdrs :: chainsEnd).length) →
      (st.world.memory (0 + 32 * i)).val = (seed :: pkAdrs :: chainsEnd)[i] := by
    intro i hi
    match i with
    | 0 => simpa using hm0
    | 1 => simpa using hm1
    | j + 2 =>
        have hj : j < 45 := by
          rw [hlen47] at hi
          omega
        have hoffj : (0 : Nat) + 32 * (j + 2) = 0x40 + 32 * j := by
          omega
        rw [hoffj]
        show (st.world.memory (0x40 + 32 * j)).val = chainsEnd[j]
        exact hmC j hj
  have key :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_maskedKeccak_eq_maskN
      st 0 (seed :: pkAdrs :: chainsEnd) hoff hszlt hmem
  have hsz : 32 * (seed :: pkAdrs :: chainsEnd).length = 0x5E0 := by
    rw [hlen47]
  rw [hsz] at key
  exact key

/-- Spec-shaped C12 WOTS public-key final Keccak: once the scratch image holds
the public seed, WOTS-PK address, and 45 reconstructed chain ends, the executable
masked Keccak is exactly `wotsPkWordC12`. -/
theorem c12_wots_pk_node_eq_spec
    (st : RuntimeState) (seed : Nat)
    (layer treeIdx leafIdx node : Nat) (wots : WotsSig)
    (hm0 : (st.world.memory 0).val = seed)
    (hm1 : (st.world.memory 0x20).val =
      C12Concrete.wotsPkAdrsC12 layer treeIdx leafIdx)
    (hmC : ∀ j, (h : j < 45) →
      (st.world.memory (0x40 + 32 * j)).val =
        (c12WotsChainsEnd seed layer treeIdx leafIdx node wots)[j]) :
    evalExpr [] st
        (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x5E0))
          (.literal SphincsMinusVerifierSpec.C13Concrete.nMask))
      = some
        (C12Concrete.wotsPkWordC12 seed layer treeIdx leafIdx node wots) := by
  rw [c12WotsPkWord_eq]
  exact c12_wots_pk_node_eq st seed
    (C12Concrete.wotsPkAdrsC12 layer treeIdx leafIdx)
    (c12WotsChainsEnd seed layer treeIdx leafIdx node wots)
    (c12WotsChainsEnd_length seed layer treeIdx leafIdx node wots)
    hm0 hm1 hmC

/-- Smaller WOTS-PK handoff for any C12 layer body input: the public
`BeforeAuthOff` `"wotsPk"` binding follows from the exact post-copy-loop scratch
image at `c12LayerStateBeforeWotsPk`. -/
theorem c12LayerStateBeforeAuthOff_wotsPk_eq_wotsPkWord_of_beforeWotsPk_memory
    (st : RuntimeState) (seed : Nat)
    (layer treeIdx leafIdx node : Nat) (wots : WotsSig)
    (hm0 :
      ((C12SegmentWotsSetup.c12LayerStateBeforeWotsPk st).world.memory 0).val =
        seed)
    (hm1 :
      ((C12SegmentWotsSetup.c12LayerStateBeforeWotsPk st).world.memory 0x20).val =
        C12Concrete.wotsPkAdrsC12 layer treeIdx leafIdx)
    (hmC : ∀ j, (h : j < 45) →
      ((C12SegmentWotsSetup.c12LayerStateBeforeWotsPk st).world.memory
          (0x40 + 32 * j)).val =
        (c12WotsChainsEnd seed layer treeIdx leafIdx node wots)[j]) :
    lookupValue
        (C12SegmentWotsSetup.c12LayerStateBeforeAuthOff st).bindings
        "wotsPk" =
      C12Concrete.wotsPkWordC12 seed layer treeIdx leafIdx node wots := by
  rw [C12SegmentWotsSetup.c12LayerStateBeforeAuthOff_wotsPk_eq_beforeWotsPk_keccak]
  have hEval :=
    c12_wots_pk_node_eq_spec
      (C12SegmentWotsSetup.c12LayerStateBeforeWotsPk st)
      seed layer treeIdx leafIdx node wots hm0 hm1 hmC
  change
    (evalExpr [] (C12SegmentWotsSetup.c12LayerStateBeforeWotsPk st)
      (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x5E0))
        (.literal SphincsMinusVerifierSpec.C13Concrete.nMask))).getD 0 =
      C12Concrete.wotsPkWordC12 seed layer treeIdx leafIdx node wots
  rw [hEval]
  rfl

theorem c12FoldRootUnrolled5_eq_layerRoot4
    (pkSeed : ByteArray) (idxTree : Nat) (startNode : ByteArray)
    (layers : List XmssLayerSig) :
    c12FoldRootUnrolled5 pkSeed idxTree startNode layers =
      c12UnrolledLayerRoot4 pkSeed idxTree startNode layers := by
  rfl

theorem c12_unrolled5_current_node_of_layer_root4_current_node
    (hLayerRoot4 :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (C12SegmentWotsSetup.c12StepLayerLoop
            (C12SegmentForsCompress.c12StepForsCompress
              (C12SegmentFors.c12StepFors
                (C12SegmentSeed.c12StepSeed
                  (MkC13State.mkC13State pkSeed pkRoot message sig))))).bindings
          "currentNode" =
          SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
            (c12UnrolledLayerRoot4 pkSeed
          (C12Concrete.hMsgC12 c12
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex
          ((C12Concrete.forsPkFromSigC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot }
                  (C12Concrete.hMsgC12 c12
                    { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
                  sigParsed.fors).getD ⟨#[]⟩)
              sigParsed.layers)) :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (C12SegmentWotsSetup.c12StepLayerLoop
            (C12SegmentForsCompress.c12StepForsCompress
              (C12SegmentFors.c12StepFors
                (C12SegmentSeed.c12StepSeed
                  (MkC13State.mkC13State pkSeed pkRoot message sig))))).bindings
          "currentNode" =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          (c12FoldRootUnrolled5 pkSeed
            (C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex
            ((C12Concrete.forsPkFromSigC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot }
                (C12Concrete.hMsgC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
                sigParsed.fors).getD ⟨#[]⟩)
            sigParsed.layers) := by
  intro pkSeed pkRoot message sig sigParsed hParse
  rw [c12FoldRootUnrolled5_eq_layerRoot4]
  exact hLayerRoot4 pkSeed pkRoot message sig sigParsed hParse

/-- The final layer-loop executable-currentNode premise follows from the named
state-after-layer-4 fact.  This exposes the concrete execution-shape reduction:
only the layer-body data correspondence remains. -/
theorem c12_layer_root4_current_node_of_layer_state_after4_current_node
    (hAfter4 :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (c12LayerStateAfter4
            (C12SegmentForsCompress.c12StepForsCompress
              (C12SegmentFors.c12StepFors
                (C12SegmentSeed.c12StepSeed
                  (MkC13State.mkC13State pkSeed pkRoot message sig))))).bindings
          "currentNode" =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          (c12UnrolledLayerRoot4 pkSeed
            (C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex
            ((C12Concrete.forsPkFromSigC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot }
                (C12Concrete.hMsgC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
                sigParsed.fors).getD ⟨#[]⟩)
            sigParsed.layers)) :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (C12SegmentWotsSetup.c12StepLayerLoop
            (C12SegmentForsCompress.c12StepForsCompress
              (C12SegmentFors.c12StepFors
                (C12SegmentSeed.c12StepSeed
                  (MkC13State.mkC13State pkSeed pkRoot message sig))))).bindings
          "currentNode" =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          (c12UnrolledLayerRoot4 pkSeed
            (C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex
            ((C12Concrete.forsPkFromSigC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot }
                (C12Concrete.hMsgC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
                sigParsed.fors).getD ⟨#[]⟩)
            sigParsed.layers) := by
  intro pkSeed pkRoot message sig sigParsed hParse
  rw [c12StepLayerLoop_eq_layerStateAfter4]
  exact hAfter4 pkSeed pkRoot message sig sigParsed hParse

def c12LayerBodyInput4 (st : RuntimeState) : RuntimeState :=
  let s := c12LayerStateAfter3 st
  { s with bindings := bindValue s.bindings "layer" (wordNormalize 4) }

def c12LayerBodyInput0 (st : RuntimeState) : RuntimeState :=
  { st with bindings := bindValue st.bindings "layer" (wordNormalize 0) }

private theorem c12_bindValue_shadow_same
    (bs : List (String × Nat)) (key : String) (val : Nat) :
    bindValue (bindValue bs key val) key val = bindValue bs key val := by
  unfold bindValue
  simp

/-- The first C12 layer state is exactly one `c12LayerStep` from the layer-0
body input. -/
theorem c12LayerStateAfter0_eq_layerBodyInput0_step (st : RuntimeState) :
    c12LayerStateAfter0 st =
      C12SegmentWotsSetup.c12LayerStep (c12LayerBodyInput0 st) := by
  unfold c12LayerStateAfter0 c12LayerLoopFold c12LayerBodyInput0
  rw [show wordNormalize 1 = 1 by rfl]
  rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_succ,
    SphincsMinusVerifiers.ClimbLoop.foldLoop_zero]
  change C12SegmentWotsSetup.c12LayerStep
      { st with
        bindings :=
          bindValue (bindValue st.bindings "layer" (wordNormalize 0))
            "layer" (wordNormalize 0) } =
    C12SegmentWotsSetup.c12LayerStep
      { st with bindings := bindValue st.bindings "layer" (wordNormalize 0) }
  simp [c12_bindValue_shadow_same]

/-- After the first C12 layer, `"currentNode"` is the `"merkleNode"` computed by
the layer-0 WOTS/XMSS body prefix. -/
theorem c12LayerStateAfter0_currentNode_eq_layer0_beforeCurrentNode_merkleNode
    (st : RuntimeState) :
    lookupValue (c12LayerStateAfter0 st).bindings "currentNode" =
      lookupValue
        (C12SegmentWotsSetup.c12LayerStateBeforeCurrentNode
          (c12LayerBodyInput0 st)).bindings
        "merkleNode" := by
  rw [c12LayerStateAfter0_eq_layerBodyInput0_step]
  exact C12SegmentWotsSetup.c12LayerStep_currentNode_eq_beforeCurrentNode_merkleNode
    (c12LayerBodyInput0 st)

/-- Preparing the layer-4 body only rebinds `"layer"`; the `"curLeaf"` handoff
from the previous layer is already present in `c12LayerStateAfter3`. -/
theorem c12LayerBodyInput4_curLeaf_eq (st : RuntimeState) :
    lookupValue (c12LayerBodyInput4 st).bindings "curLeaf" =
      lookupValue (c12LayerStateAfter3 st).bindings "curLeaf" := by
  unfold c12LayerBodyInput4
  rw [MemoryKit.lookupValue_bindValue_ne _ "layer" "curLeaf" _ (by decide)]

/-- Preparing the layer-4 body binds `"layer"` to the concrete layer index. -/
theorem c12LayerBodyInput4_layer_eq (st : RuntimeState) :
    lookupValue (c12LayerBodyInput4 st).bindings "layer" =
      wordNormalize 4 := by
  unfold c12LayerBodyInput4
  rw [MemoryKit.lookupValue_bindValue_self]

/-- Preparing the layer-4 body only rebinds `"layer"`; the `"curTree"` handoff
from the previous layer is already present in `c12LayerStateAfter3`. -/
theorem c12LayerBodyInput4_curTree_eq (st : RuntimeState) :
    lookupValue (c12LayerBodyInput4 st).bindings "curTree" =
      lookupValue (c12LayerStateAfter3 st).bindings "curTree" := by
  unfold c12LayerBodyInput4
  rw [MemoryKit.lookupValue_bindValue_ne _ "layer" "curTree" _ (by decide)]

/-- Preparing the layer-4 body only rebinds `"layer"`; the `"sigOff"` handoff
from the previous layer is already present in `c12LayerStateAfter3`. -/
theorem c12LayerBodyInput4_sigOff_eq (st : RuntimeState) :
    lookupValue (c12LayerBodyInput4 st).bindings "sigOff" =
      lookupValue (c12LayerStateAfter3 st).bindings "sigOff" := by
  unfold c12LayerBodyInput4
  rw [MemoryKit.lookupValue_bindValue_ne _ "layer" "sigOff" _ (by decide)]

/-- Preparing the layer-4 body only rebinds `"layer"`; the `"sigBase"` handoff
from the previous layer is already present in `c12LayerStateAfter3`. -/
theorem c12LayerBodyInput4_sigBase_eq (st : RuntimeState) :
    lookupValue (c12LayerBodyInput4 st).bindings "sigBase" =
      lookupValue (c12LayerStateAfter3 st).bindings "sigBase" := by
  unfold c12LayerBodyInput4
  rw [MemoryKit.lookupValue_bindValue_ne _ "layer" "sigBase" _ (by decide)]

/-- Preparing the layer-4 body only rebinds `"layer"`; the `"currentNode"`
handoff from the previous layer is already present in `c12LayerStateAfter3`. -/
theorem c12LayerBodyInput4_currentNode_eq (st : RuntimeState) :
    lookupValue (c12LayerBodyInput4 st).bindings "currentNode" =
      lookupValue (c12LayerStateAfter3 st).bindings "currentNode" := by
  unfold c12LayerBodyInput4
  rw [MemoryKit.lookupValue_bindValue_ne _ "layer" "currentNode" _ (by decide)]

/-- The layer-4 body input receives the layer-3 semantic root as its
`"currentNode"` whenever the named post-layer-3 state has that root.  This is
the exact executable handoff introduced by the layer-4 `"layer"` rebinding. -/
theorem c12LayerBodyInput4_currentNode_eq_unrolledLayerRoot3_of_after3_currentNode
    (hAfter3 :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (c12LayerStateAfter3
            (C12SegmentForsCompress.c12StepForsCompress
              (C12SegmentFors.c12StepFors
                (C12SegmentSeed.c12StepSeed
                  (MkC13State.mkC13State pkSeed pkRoot message sig))))).bindings
          "currentNode" =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          (c12UnrolledLayerRoot3 pkSeed
            (C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex
            ((C12Concrete.forsPkFromSigC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot }
                (C12Concrete.hMsgC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
                sigParsed.fors).getD ⟨#[]⟩)
            sigParsed.layers)) :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (c12LayerBodyInput4
            (C12SegmentForsCompress.c12StepForsCompress
              (C12SegmentFors.c12StepFors
                (C12SegmentSeed.c12StepSeed
                  (MkC13State.mkC13State pkSeed pkRoot message sig))))).bindings
          "currentNode" =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          (c12UnrolledLayerRoot3 pkSeed
            (C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex
            ((C12Concrete.forsPkFromSigC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot }
                (C12Concrete.hMsgC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
                sigParsed.fors).getD ⟨#[]⟩)
            sigParsed.layers) := by
  intro pkSeed pkRoot message sig sigParsed hParse
  rw [c12LayerBodyInput4_currentNode_eq]
  exact hAfter3 pkSeed pkRoot message sig sigParsed hParse

theorem c12LayerStateAfter4_currentNode_eq_layer4_beforeCurrentNode_merkleNode
    (st : RuntimeState) :
    lookupValue (c12LayerStateAfter4 st).bindings "currentNode" =
      lookupValue
        (C12SegmentWotsSetup.c12LayerStateBeforeCurrentNode
          (c12LayerBodyInput4 st)).bindings
        "merkleNode" := by
  rw [show c12LayerStateAfter4 st =
      C12SegmentWotsSetup.c12LayerStep (c12LayerBodyInput4 st) by
    unfold c12LayerStateAfter4 c12LayerLoopFold c12LayerBodyInput4
    rw [show wordNormalize 5 = 4 + 1 by rfl]
    rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_append
      "layer" C12SegmentWotsSetup.c12LayerStep
      { st with bindings := bindValue st.bindings "layer" (wordNormalize 0) } 0 4 1]
    rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_succ,
      SphincsMinusVerifiers.ClimbLoop.foldLoop_zero]
    rw [show wordNormalize (0 + 4) = 4 by rfl]
    unfold c12LayerStateAfter3 c12LayerLoopFold
    rw [show wordNormalize 4 = 4 by rfl]]
  exact C12SegmentWotsSetup.c12LayerStep_currentNode_eq_beforeCurrentNode_merkleNode
    (c12LayerBodyInput4 st)

/-- At the layer-4 XMSS boundary, the executable `"merkleNode"` seed is reduced
to the smaller WOTS public-key semantic fact for the same boundary.  The
remaining premise is exactly the computed `"wotsPk"` binding, before the XMSS
loop consumes the auth path. -/
theorem c12_layer4_before_xmss_merkleNode_of_wotsPk
    (hLayer4WotsPk :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (C12SegmentWotsSetup.c12LayerStateBeforeXmssLoop
            (c12LayerBodyInput4
              (C12SegmentForsCompress.c12StepForsCompress
                (C12SegmentFors.c12StepFors
                  (C12SegmentSeed.c12StepSeed
                    (MkC13State.mkC13State pkSeed pkRoot message sig)))))).bindings
          "wotsPk" =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          (c12Layer4WotsPkBytes pkSeed
            (C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex
            (c12UnrolledLayerRoot3 pkSeed
              (C12Concrete.hMsgC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex
              ((C12Concrete.forsPkFromSigC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot }
                  (C12Concrete.hMsgC12 c12
                    { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
                  sigParsed.fors).getD ⟨#[]⟩)
              sigParsed.layers)
            ((sigParsed.layers[4]?).getD c12EmptyXmssLayerSig))) :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (C12SegmentWotsSetup.c12LayerStateBeforeXmssLoop
            (c12LayerBodyInput4
              (C12SegmentForsCompress.c12StepForsCompress
                (C12SegmentFors.c12StepFors
                  (C12SegmentSeed.c12StepSeed
                    (MkC13State.mkC13State pkSeed pkRoot message sig)))))).bindings
          "merkleNode" =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          (c12Layer4WotsPkBytes pkSeed
            (C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex
            (c12UnrolledLayerRoot3 pkSeed
              (C12Concrete.hMsgC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex
              ((C12Concrete.forsPkFromSigC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot }
                  (C12Concrete.hMsgC12 c12
                    { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
                  sigParsed.fors).getD ⟨#[]⟩)
              sigParsed.layers)
            ((sigParsed.layers[4]?).getD c12EmptyXmssLayerSig)) := by
  intro pkSeed pkRoot message sig sigParsed hParse
  rw [C12SegmentWotsSetup.c12LayerStateBeforeXmssLoop_merkleNode_eq_wotsPk]
  exact hLayer4WotsPk pkSeed pkRoot message sig sigParsed hParse

/-- Local bridge copy of the exact executable fact that the final
`"merkleNode"`/`"mIdx"` setup bindings leave `"wotsPk"` unchanged.  Keeping this
in the bridge file makes `lean C12BridgePrep.lean` independent of rebuilt
dependency `.olean`s. -/
theorem c12LayerStateBeforeXmssLoop_wotsPk_eq_beforeXmssNode_wotsPk
    (st : RuntimeState) :
    lookupValue (C12SegmentWotsSetup.c12LayerStateBeforeXmssLoop st).bindings "wotsPk" =
      lookupValue (C12SegmentWotsSetup.c12LayerStateBeforeXmssNode st).bindings
        "wotsPk" := by
  unfold C12SegmentWotsSetup.c12LayerStateBeforeXmssLoop
  rw [C12SegmentWotsSetup.c12LayerBodyBeforeXmssLoop_eq_beforeNode_append]
  rw [MemoryKit.execStmtList_append_continue _ _ _ _
    (C12SegmentWotsSetup.execC12LayerBodyBeforeXmssNode st)]
  rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue
      (C12SegmentWotsSetup.c12LayerStateBeforeXmssNode st) "merkleNode" _ _ rfl)]
  rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "mIdx" _ _ rfl)]
  change
    lookupValue
        (bindValue
          (bindValue (C12SegmentWotsSetup.c12LayerStateBeforeXmssNode st).bindings "merkleNode"
            (lookupValue (C12SegmentWotsSetup.c12LayerStateBeforeXmssNode st).bindings "wotsPk"))
          "mIdx"
          (lookupValue
            (bindValue (C12SegmentWotsSetup.c12LayerStateBeforeXmssNode st).bindings "merkleNode"
              (lookupValue (C12SegmentWotsSetup.c12LayerStateBeforeXmssNode st).bindings "wotsPk"))
            "curLeaf"))
        "wotsPk" =
      lookupValue (C12SegmentWotsSetup.c12LayerStateBeforeXmssNode st).bindings "wotsPk"
  rw [MemoryKit.lookupValue_bindValue_ne _ "mIdx" "wotsPk" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "merkleNode" "wotsPk" _ (by decide)]

/-- The exact final-Keccak boundary for layer-4 WOTS-PK is before the auth
offset setup.  The pre-XMSS-node boundary only appends address setup bindings,
so it preserves the computed `"wotsPk"` value. -/
theorem c12_layer4_before_xmss_node_wotsPk_of_before_authOff
    (hLayer4WotsPkBeforeAuthOff :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (C12SegmentWotsSetup.c12LayerStateBeforeAuthOff
            (c12LayerBodyInput4
              (C12SegmentForsCompress.c12StepForsCompress
                (C12SegmentFors.c12StepFors
                  (C12SegmentSeed.c12StepSeed
                    (MkC13State.mkC13State pkSeed pkRoot message sig)))))).bindings
          "wotsPk" =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          (c12Layer4WotsPkBytes pkSeed
            (C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex
            (c12UnrolledLayerRoot3 pkSeed
              (C12Concrete.hMsgC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex
              ((C12Concrete.forsPkFromSigC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot }
                  (C12Concrete.hMsgC12 c12
                    { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
                  sigParsed.fors).getD ⟨#[]⟩)
              sigParsed.layers)
            ((sigParsed.layers[4]?).getD c12EmptyXmssLayerSig))) :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (C12SegmentWotsSetup.c12LayerStateBeforeXmssNode
            (c12LayerBodyInput4
              (C12SegmentForsCompress.c12StepForsCompress
                (C12SegmentFors.c12StepFors
                  (C12SegmentSeed.c12StepSeed
                    (MkC13State.mkC13State pkSeed pkRoot message sig)))))).bindings
          "wotsPk" =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          (c12Layer4WotsPkBytes pkSeed
            (C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex
            (c12UnrolledLayerRoot3 pkSeed
              (C12Concrete.hMsgC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex
              ((C12Concrete.forsPkFromSigC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot }
                  (C12Concrete.hMsgC12 c12
                    { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
                  sigParsed.fors).getD ⟨#[]⟩)
              sigParsed.layers)
            ((sigParsed.layers[4]?).getD c12EmptyXmssLayerSig)) := by
  intro pkSeed pkRoot message sig sigParsed hParse
  let st :=
    c12LayerBodyInput4
      (C12SegmentForsCompress.c12StepForsCompress
        (C12SegmentFors.c12StepFors
          (C12SegmentSeed.c12StepSeed
            (MkC13State.mkC13State pkSeed pkRoot message sig))))
  have hPres :=
    C12SegmentWotsSetup.c12LayerStateBeforeXmssNode_wotsPk_eq_beforeAuthOff st
  exact Eq.trans hPres
    (hLayer4WotsPkBeforeAuthOff pkSeed pkRoot message sig sigParsed hParse)

/-- The layer-4 `"wotsPk"` semantic fact can be proved at the smaller exact
executable boundary before `"merkleNode"`/`"mIdx"` are introduced; those two
setup bindings leave `"wotsPk"` unchanged. -/
theorem c12_layer4_wotsPk_of_before_xmss_node_wotsPk
    (hLayer4WotsPkBeforeNode :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (C12SegmentWotsSetup.c12LayerStateBeforeXmssNode
            (c12LayerBodyInput4
              (C12SegmentForsCompress.c12StepForsCompress
                (C12SegmentFors.c12StepFors
                  (C12SegmentSeed.c12StepSeed
                    (MkC13State.mkC13State pkSeed pkRoot message sig)))))).bindings
          "wotsPk" =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          (c12Layer4WotsPkBytes pkSeed
            (C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex
            (c12UnrolledLayerRoot3 pkSeed
              (C12Concrete.hMsgC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex
              ((C12Concrete.forsPkFromSigC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot }
                  (C12Concrete.hMsgC12 c12
                    { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
                  sigParsed.fors).getD ⟨#[]⟩)
              sigParsed.layers)
            ((sigParsed.layers[4]?).getD c12EmptyXmssLayerSig))) :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (C12SegmentWotsSetup.c12LayerStateBeforeXmssLoop
            (c12LayerBodyInput4
              (C12SegmentForsCompress.c12StepForsCompress
                (C12SegmentFors.c12StepFors
                  (C12SegmentSeed.c12StepSeed
                    (MkC13State.mkC13State pkSeed pkRoot message sig)))))).bindings
          "wotsPk" =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          (c12Layer4WotsPkBytes pkSeed
            (C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex
            (c12UnrolledLayerRoot3 pkSeed
              (C12Concrete.hMsgC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex
              ((C12Concrete.forsPkFromSigC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot }
                  (C12Concrete.hMsgC12 c12
                    { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
                  sigParsed.fors).getD ⟨#[]⟩)
              sigParsed.layers)
            ((sigParsed.layers[4]?).getD c12EmptyXmssLayerSig)) := by
  intro pkSeed pkRoot message sig sigParsed hParse
  rw [c12LayerStateBeforeXmssLoop_wotsPk_eq_beforeXmssNode_wotsPk]
  exact hLayer4WotsPkBeforeNode pkSeed pkRoot message sig sigParsed hParse

/-- Combining the executable `"wotsPk"` preservation with the existing
`"merkleNode"` seed equality reduces the layer-4 pre-XMSS semantic fact to the
pre-node WOTS-public-key value. -/
theorem c12_layer4_before_xmss_merkleNode_of_before_xmss_node_wotsPk
    (hLayer4WotsPkBeforeNode :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (C12SegmentWotsSetup.c12LayerStateBeforeXmssNode
            (c12LayerBodyInput4
              (C12SegmentForsCompress.c12StepForsCompress
                (C12SegmentFors.c12StepFors
                  (C12SegmentSeed.c12StepSeed
                    (MkC13State.mkC13State pkSeed pkRoot message sig)))))).bindings
          "wotsPk" =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          (c12Layer4WotsPkBytes pkSeed
            (C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex
            (c12UnrolledLayerRoot3 pkSeed
              (C12Concrete.hMsgC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex
              ((C12Concrete.forsPkFromSigC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot }
                  (C12Concrete.hMsgC12 c12
                    { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
                  sigParsed.fors).getD ⟨#[]⟩)
              sigParsed.layers)
            ((sigParsed.layers[4]?).getD c12EmptyXmssLayerSig))) :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (C12SegmentWotsSetup.c12LayerStateBeforeXmssLoop
            (c12LayerBodyInput4
              (C12SegmentForsCompress.c12StepForsCompress
                (C12SegmentFors.c12StepFors
                  (C12SegmentSeed.c12StepSeed
                    (MkC13State.mkC13State pkSeed pkRoot message sig)))))).bindings
          "merkleNode" =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          (c12Layer4WotsPkBytes pkSeed
            (C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex
            (c12UnrolledLayerRoot3 pkSeed
              (C12Concrete.hMsgC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex
              ((C12Concrete.forsPkFromSigC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot }
                  (C12Concrete.hMsgC12 c12
                    { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
                  sigParsed.fors).getD ⟨#[]⟩)
              sigParsed.layers)
            ((sigParsed.layers[4]?).getD c12EmptyXmssLayerSig)) := by
  exact c12_layer4_before_xmss_merkleNode_of_wotsPk
    (c12_layer4_wotsPk_of_before_xmss_node_wotsPk hLayer4WotsPkBeforeNode)

/-- Bridge-local copy of the C12 XMSS loop shape, so direct checking this file
does not depend on rebuilt dependency `.olean`s. -/
theorem c12LayerStateAfterXmssLoop_eq_merkleFold
    (st : RuntimeState) :
    C12SegmentWotsSetup.c12LayerStateAfterXmssLoop st =
      SphincsMinusVerifiers.ClimbLoop.foldLoop "h"
        (SphincsMinusVerifiers.ClimbKit.stepMerkle
          "merkleNode" "mIdx" "xmssBase" "authPtr")
        { st with bindings := bindValue st.bindings "h" (wordNormalize 0) }
        0 (wordNormalize 4) := by
  unfold C12SegmentWotsSetup.c12LayerStateAfterXmssLoop
  congr

def c12Layer4PreBodyState
    (pkSeed pkRoot message sig : ByteArray) : RuntimeState :=
  c12LayerBodyInput4
    (C12SegmentForsCompress.c12StepForsCompress
      (C12SegmentFors.c12StepFors
        (C12SegmentSeed.c12StepSeed
          (MkC13State.mkC13State pkSeed pkRoot message sig))))

/-- The layer-4 body starts after four C12 hypertree layers, so its incoming
`"sigOff"` is the FORS-compress offset plus four WOTS/XMSS-auth spans. -/
theorem c12Layer4PreBodyState_sigOff_eq
    (pkSeed pkRoot message sig : ByteArray) :
    lookupValue
        (c12Layer4PreBodyState pkSeed pkRoot message sig).bindings "sigOff" =
      wordNormalize 5728 := by
  unfold c12Layer4PreBodyState
  rw [c12LayerBodyInput4_sigOff_eq]
  exact c12LayerStateAfter3_sigOff_eq_after_fors_compress
    (C12SegmentFors.c12StepFors
      (C12SegmentSeed.c12StepSeed
        (MkC13State.mkC13State pkSeed pkRoot message sig)))

/-- The layer-4 body input still carries the ABI signature-data base installed
by seed setup.  FORS reconstruction, FORS-root compression, and the first four
WOTS/XMSS layers do not rebind `"sigBase"`. -/
theorem c12Layer4PreBodyState_sigBase_eq
    (pkSeed pkRoot message sig : ByteArray) :
    lookupValue
        (c12Layer4PreBodyState pkSeed pkRoot message sig).bindings "sigBase" =
      MkC13State.sigDataOffset := by
  unfold c12Layer4PreBodyState
  rw [c12LayerBodyInput4_sigBase_eq]
  unfold c12LayerStateAfter3 c12LayerLoopFold
  rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_preserves_lookup
    "layer" "sigBase" C12SegmentWotsSetup.c12LayerStep
    (by decide) C12SegmentWotsSetup.c12LayerStep_preserves_sigBase]
  rw [MemoryKit.lookupValue_bindValue_ne _ "layer" "sigBase" _ (by decide)]
  rw [C12SegmentForsCompress.c12StepForsCompress_preserves_sigBase]
  rw [C12SegmentFors.c12StepFors_preserves_sigBase]
  exact C12SegmentSeed.c12StepSeed_sigBase_mkC13State pkSeed pkRoot message sig

/-- At the layer-4 WOTS setup entry, evaluating `sigBase + sigOff` gives the
C12 layer-4 WOTS signature pointer. -/
theorem c12Layer4PreBodyState_wotsPtr_eval
    (pkSeed pkRoot message sig : ByteArray) :
    evalExpr [] (c12Layer4PreBodyState pkSeed pkRoot message sig)
        (.add (.localVar "sigBase") (.localVar "sigOff")) =
      some (MkC13State.sigDataOffset + (2592 + 784 * 4)) := by
  have hBase : evalExpr [] (c12Layer4PreBodyState pkSeed pkRoot message sig)
      (.localVar "sigBase") = some MkC13State.sigDataOffset := by
    show some (lookupValue
      (c12Layer4PreBodyState pkSeed pkRoot message sig).bindings "sigBase") =
        some MkC13State.sigDataOffset
    rw [c12Layer4PreBodyState_sigBase_eq]
  have hOff : evalExpr [] (c12Layer4PreBodyState pkSeed pkRoot message sig)
      (.localVar "sigOff") = some 5728 := by
    show some (lookupValue
      (c12Layer4PreBodyState pkSeed pkRoot message sig).bindings "sigOff") =
        some 5728
    rw [c12Layer4PreBodyState_sigOff_eq]
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide)]
  have hAdd :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_add_bounded
      (c12Layer4PreBodyState pkSeed pkRoot message sig)
      (.localVar "sigBase") (.localVar "sigOff")
      MkC13State.sigDataOffset 5728 hBase hOff
      (by norm_num [MkC13State.sigDataOffset])
      (by norm_num)
      (by norm_num [MkC13State.sigDataOffset])
  convert hAdd using 1

/-- Binding `"wotsBase"` during the layer-4 WOTS setup does not affect
`sigBase + sigOff`, so the intermediate state still evaluates the layer-4 WOTS
signature pointer. -/
theorem c12Layer4PreBodyState_wotsPtr_eval_after_wotsBase_bind
    (pkSeed pkRoot message sig : ByteArray) (wotsBase : Nat) :
    evalExpr []
      { c12Layer4PreBodyState pkSeed pkRoot message sig with
        bindings :=
          bindValue (c12Layer4PreBodyState pkSeed pkRoot message sig).bindings
            "wotsBase" wotsBase }
      (.add (.localVar "sigBase") (.localVar "sigOff")) =
      some (MkC13State.sigDataOffset + (2592 + 784 * 4)) := by
  let st := c12Layer4PreBodyState pkSeed pkRoot message sig
  have hBase : evalExpr []
      { st with bindings := bindValue st.bindings "wotsBase" wotsBase }
      (.localVar "sigBase") = some MkC13State.sigDataOffset := by
    show some (lookupValue (bindValue st.bindings "wotsBase" wotsBase) "sigBase") =
      some MkC13State.sigDataOffset
    rw [MemoryKit.lookupValue_bindValue_ne _ "wotsBase" "sigBase" _ (by decide)]
    dsimp [st]
    rw [c12Layer4PreBodyState_sigBase_eq]
  have hOff : evalExpr []
      { st with bindings := bindValue st.bindings "wotsBase" wotsBase }
      (.localVar "sigOff") = some 5728 := by
    show some (lookupValue (bindValue st.bindings "wotsBase" wotsBase) "sigOff") =
      some 5728
    rw [MemoryKit.lookupValue_bindValue_ne _ "wotsBase" "sigOff" _ (by decide)]
    dsimp [st]
    rw [c12Layer4PreBodyState_sigOff_eq]
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide)]
  have hAdd :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_add_bounded
      { st with bindings := bindValue st.bindings "wotsBase" wotsBase }
      (.localVar "sigBase") (.localVar "sigOff")
      MkC13State.sigDataOffset 5728 hBase hOff
      (by norm_num [MkC13State.sigDataOffset])
      (by norm_num)
      (by norm_num [MkC13State.sigDataOffset])
  simpa [st] using hAdd

/-- The executable C12 layer fold preserves the public-seed scratch cell for any
number of layer iterations. -/
theorem c12LayerLoopFold_preserves_memory_zero
    (st : RuntimeState) (layers : Nat) :
    ((c12LayerLoopFold st layers).world.memory 0x00).val =
      (st.world.memory 0x00).val := by
  unfold c12LayerLoopFold
  rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_preserves_memory_val
    "layer" C12SegmentWotsSetup.c12LayerStep 0x00
    C12SegmentWotsSetup.c12LayerStep_preserves_memory_zero
    { st with bindings := bindValue st.bindings "layer" (wordNormalize 0) }
    0 (wordNormalize layers)]

/-- The first four C12 hypertree layer iterations preserve the public-seed
scratch cell. -/
theorem c12LayerStateAfter3_preserves_memory_zero (st : RuntimeState) :
    ((c12LayerStateAfter3 st).world.memory 0x00).val =
      (st.world.memory 0x00).val := by
  unfold c12LayerStateAfter3
  exact c12LayerLoopFold_preserves_memory_zero st 4

/-- Preparing the layer-4 body only rebinds `"layer"` after the first four
layer iterations, so it preserves the public-seed scratch cell. -/
theorem c12LayerBodyInput4_preserves_memory_zero (st : RuntimeState) :
    ((c12LayerBodyInput4 st).world.memory 0x00).val =
      (st.world.memory 0x00).val := by
  unfold c12LayerBodyInput4
  rw [MemoryKit.withBindings_preserves_memory_val]
  exact c12LayerStateAfter3_preserves_memory_zero st

def c12Layer4ParsedSeed (pkSeed : ByteArray) : Nat :=
  SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed

/-- The layer-4 pre-body state still carries the public seed word in
`mem[0x00]` from the initial C12 runtime state. -/
theorem c12Layer4PreBodyState_preserves_memory_zero
    (pkSeed pkRoot message sig : ByteArray) :
    ((c12Layer4PreBodyState pkSeed pkRoot message sig).world.memory 0x00).val =
      c12Layer4ParsedSeed pkSeed := by
  unfold c12Layer4PreBodyState
  rw [c12LayerBodyInput4_preserves_memory_zero]
  rw [C12SegmentForsCompress.c12StepForsCompress_preserves_memory_zero]
  rw [C12SegmentFors.c12StepFors_preserves_memory_zero]
  exact C12SegmentSeed.c12StepSeed_memory_zero_mkC13State pkSeed pkRoot message sig

def c12Layer4XmssEntryState
    (pkSeed pkRoot message sig : ByteArray) : RuntimeState :=
  C12SegmentWotsSetup.c12LayerStateBeforeXmssLoop
    (c12Layer4PreBodyState pkSeed pkRoot message sig)

/-- Layer-4 entry `"authPtr"` reduced to the remaining segment-level
`"sigBase"` fact. -/
theorem c12Layer4EntryAuthPtr_of_prebody_sigBase
    (pkSeed pkRoot message sig : ByteArray)
    (hSigBase :
      lookupValue
          (c12Layer4PreBodyState pkSeed pkRoot message sig).bindings "sigBase" =
        MkC13State.sigDataOffset) :
    lookupValue
        (c12Layer4XmssEntryState pkSeed pkRoot message sig).bindings "authPtr" =
      MkC13State.sigDataOffset + (2592 + 784 * 4 + 720) := by
  unfold c12Layer4XmssEntryState
  rw [C12SegmentWotsSetup.c12LayerStateBeforeXmssLoop_authPtr_eq_beforeXmssNode_authPtr]
  rw [C12SegmentWotsSetup.c12LayerStateBeforeXmssNode_authPtr_eq_sigBase_sigOff]
  rw [hSigBase, c12Layer4PreBodyState_sigOff_eq]
  simp only [HAdd.hAdd]
  norm_num [wordNormalize, Compiler.Constants.evmModulus,
    Verity.Core.Uint256.add, Verity.Core.Uint256.ofNat,
    Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS,
    MkC13State.sigDataOffset]

/-- Layer-4 XMSS entry uses the C12 signature offset plus the first four
complete WOTS/XMSS-auth spans and the layer-4 WOTS span. -/
theorem c12Layer4EntryAuthPtr
    (pkSeed pkRoot message sig : ByteArray) :
    lookupValue
        (c12Layer4XmssEntryState pkSeed pkRoot message sig).bindings "authPtr" =
      MkC13State.sigDataOffset + (2592 + 784 * 4 + 720) := by
  exact c12Layer4EntryAuthPtr_of_prebody_sigBase pkSeed pkRoot message sig
    (c12Layer4PreBodyState_sigBase_eq pkSeed pkRoot message sig)

def c12Layer4ParsedMessage
    (pkSeed pkRoot message : ByteArray) (sigParsed : Signature) :=
  C12Concrete.hMsgC12 c12
    { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message

/-- Alias-shaped layer-4 WOTS setup handoff: the named pre-body state carries
the layer-3 unrolled root in `"currentNode"` as soon as the named post-layer-3
state has that semantic root. -/
theorem c12Layer4PreBodyState_currentNode_eq_unrolledLayerRoot3_of_after3_currentNode
    (hAfter3 :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (c12LayerStateAfter3
            (C12SegmentForsCompress.c12StepForsCompress
              (C12SegmentFors.c12StepFors
                (C12SegmentSeed.c12StepSeed
                  (MkC13State.mkC13State pkSeed pkRoot message sig))))).bindings
          "currentNode" =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          (c12UnrolledLayerRoot3 pkSeed
            (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex
            ((C12Concrete.forsPkFromSigC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot }
                (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed)
                sigParsed.fors).getD ⟨#[]⟩)
            sigParsed.layers)) :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (c12Layer4PreBodyState pkSeed pkRoot message sig).bindings
          "currentNode" =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          (c12UnrolledLayerRoot3 pkSeed
            (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex
            ((C12Concrete.forsPkFromSigC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot }
                (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed)
                sigParsed.fors).getD ⟨#[]⟩)
            sigParsed.layers) := by
  intro pkSeed pkRoot message sig sigParsed hParse
  unfold c12Layer4PreBodyState
  exact
    c12LayerBodyInput4_currentNode_eq_unrolledLayerRoot3_of_after3_currentNode
      hAfter3 pkSeed pkRoot message sig sigParsed hParse

/-- Layer-4 XMSS entry preserves the pre-body seed cell through the WOTS setup
prefix.  This reduces the bridge-facing `hLayer4EntrySeed` premise to the
remaining pre-body seed handoff (the first four complete layer iterations). -/
theorem c12Layer4EntrySeed_of_prebody_seed
    (pkSeed pkRoot message sig : ByteArray) (_sigParsed : Signature)
    (hSeed :
      ((c12Layer4PreBodyState pkSeed pkRoot message sig).world.memory 0x00).val =
        c12Layer4ParsedSeed pkSeed) :
    ((c12Layer4XmssEntryState pkSeed pkRoot message sig).world.memory 0x00).val =
      c12Layer4ParsedSeed pkSeed := by
  unfold c12Layer4XmssEntryState
  rw [C12SegmentWotsSetup.c12LayerStateBeforeXmssLoop_preserves_memory_zero]
  exact hSeed

/-- Layer-4 XMSS entry carries the parsed public seed in `mem[0x00]` without a
bridge premise. -/
theorem c12Layer4EntrySeed
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature) :
    ((c12Layer4XmssEntryState pkSeed pkRoot message sig).world.memory 0x00).val =
      c12Layer4ParsedSeed pkSeed := by
  exact c12Layer4EntrySeed_of_prebody_seed pkSeed pkRoot message sig sigParsed
    (c12Layer4PreBodyState_preserves_memory_zero pkSeed pkRoot message sig)

def c12Layer4ParsedBase
    (pkSeed pkRoot message : ByteArray) (sigParsed : Signature) : Nat :=
  C12Concrete.xmssBaseC12 4
    (c12Layer4NextTree
      (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)

def c12Layer4ParsedStartNode
    (pkSeed pkRoot message : ByteArray) (sigParsed : Signature) : Nat :=
  C12Concrete.wotsPkWordC12
    (c12Layer4ParsedSeed pkSeed)
    4
    (c12Layer4NextTree
      (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
    (c12Layer4Leaf
      (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
    (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
      (c12UnrolledLayerRoot3 pkSeed
        (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex
        ((C12Concrete.forsPkFromSigC12 c12
            { pkSeed := pkSeed, pkRoot := pkRoot }
            (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed)
            sigParsed.fors).getD ⟨#[]⟩)
        sigParsed.layers))
    ((sigParsed.layers[4]?).getD c12EmptyXmssLayerSig).wots

def c12Layer4ParsedAuth (sigParsed : Signature) :
    List SphincsMinusVerifierSpec.Bytes :=
  ((sigParsed.layers[4]?).getD c12EmptyXmssLayerSig).authPath

def c12Layer4ParsedAuthCdAt
    (pkSeed pkRoot message sig : ByteArray) (i : Nat) : Nat :=
  Compiler.Proofs.YulGeneration.calldataloadWord 0
    (MkC13State.headWords pkSeed pkRoot message sig.size ++
      MkC13State.bytesToWords sig)
    (MkC13State.sigDataOffset + (2592 + 784 * 4 + 720 + 16 * i))

/-- Layer 4's concrete auth calldata reader discharges the generic
`MerkleClimbData` obligation once the parsed auth entry is known to be the
16-byte signature slice at the same byte offset.  This removes the calldata
masking/read side of the layer-4 `hDdata` residual; the remaining fact is the
pure parsed-auth extraction equality. -/
theorem c12_layer4_MerkleClimbData_of_authPath_read16
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature) (i : Nat)
    (hauth :
      ((c12Layer4ParsedAuth sigParsed)[i]?).getD ⟨#[]⟩ =
        SphincsMinusVerifierSpec.C13Concrete.read16 sig
          (2592 + 784 * 4 + 720 + 16 * i)) :
    SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
      (c12Layer4ParsedAuth sigParsed)
      (c12Layer4ParsedAuthCdAt pkSeed pkRoot message sig) i := by
  refine
    SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleClimbData_of_frozenCalldata
      pkSeed pkRoot message sig
      (c12Layer4ParsedAuth sigParsed)
      (c12Layer4ParsedAuthCdAt pkSeed pkRoot message sig)
      i (2592 + 784 * 4 + 720 + 16 * i) ?_ hauth
  rfl

/-- Successful C12 parsing identifies each layer-4 auth node with the matching
16-byte signature slice from C12's XMSS layout. -/
theorem c12_layer4_authPath_read16_range_of_parse
    (sig : ByteArray) (sigParsed : Signature)
    (hParse : C12Concrete.parseSignatureC12 c12 sig = some sigParsed) :
    ∀ i, i < wordNormalize 4 →
      ((c12Layer4ParsedAuth sigParsed)[i]?).getD ⟨#[]⟩ =
        SphincsMinusVerifierSpec.C13Concrete.read16 sig
          (2592 + 784 * 4 + 720 + 16 * i) := by
  intro i hi
  have hi4 : i < 4 := by
    simpa using hi
  have hSize : sig.size = c12.sigBytes :=
    parseSignatureC12_size_of_some hParse
  unfold C12Concrete.parseSignatureC12 at hParse
  simp only [hSize, ne_eq, not_true_eq_false, if_false, Option.some.injEq] at hParse
  subst hParse
  unfold c12Layer4ParsedAuth
  rw [SphincsMinusVerifierSpec.C13Concrete.getElem?_map_range _ (by decide : 4 < 5)]
  simp only [Option.getD_some]
  rw [SphincsMinusVerifierSpec.C13Concrete.getElem?_map_range _ hi4]
  rfl

/-- Range form of `c12_layer4_MerkleClimbData_of_authPath_read16`, matching the
layer-4 fold's `hDdata` premise. -/
theorem c12_layer4_hDdata_of_authPath_read16_range
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature)
    (hauth :
      ∀ i, i < wordNormalize 4 →
        ((c12Layer4ParsedAuth sigParsed)[i]?).getD ⟨#[]⟩ =
          SphincsMinusVerifierSpec.C13Concrete.read16 sig
            (2592 + 784 * 4 + 720 + 16 * i)) :
    ∀ i, i < wordNormalize 4 →
      SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
        (c12Layer4ParsedAuth sigParsed)
        (c12Layer4ParsedAuthCdAt pkSeed pkRoot message sig) i := by
  intro i hi
  exact c12_layer4_MerkleClimbData_of_authPath_read16
    pkSeed pkRoot message sig sigParsed i (hauth i hi)

/-- Parser-backed layer-4 `hDdata`: the parsed auth extraction premise is
discharged by the concrete C12 parser's layer indexing. -/
theorem c12_layer4_hDdata_of_parse
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature)
    (hParse : C12Concrete.parseSignatureC12 c12 sig = some sigParsed) :
    ∀ i, i < wordNormalize 4 →
      SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
        (c12Layer4ParsedAuth sigParsed)
        (c12Layer4ParsedAuthCdAt pkSeed pkRoot message sig) i := by
  exact c12_layer4_hDdata_of_authPath_read16_range
    pkSeed pkRoot message sig sigParsed
    (c12_layer4_authPath_read16_range_of_parse sig sigParsed hParse)

/-- The parsed layer-4 WOTS chain entries — the C12 parser's 45-entry chain list
extracted from the layer-4 XMSS slice.  Mirrors `c12Layer4ParsedAuth`. -/
def c12Layer4ParsedWotsChains (sigParsed : Signature) :
    List SphincsMinusVerifierSpec.Bytes :=
  ((sigParsed.layers[4]?).getD c12EmptyXmssLayerSig).wots.chains

/-- Successful C12 parsing identifies each layer-4 WOTS chain entry with the
matching 16-byte signature slice from C12's XMSS layout.  The layer-4 chains
region begins at signature byte offset `2592 + 784*4` with a 16-byte stride
across the 45 chain words. -/
theorem c12_layer4_wotsChain_read16_of_parse
    (sig : ByteArray) (sigParsed : Signature)
    (hParse : C12Concrete.parseSignatureC12 c12 sig = some sigParsed) :
    ∀ k, k < 45 →
      ((c12Layer4ParsedWotsChains sigParsed)[k]?).getD ⟨#[]⟩ =
        SphincsMinusVerifierSpec.C13Concrete.read16 sig
          (2592 + 784 * 4 + 16 * k) := by
  intro k hk
  have hSize : sig.size = c12.sigBytes :=
    parseSignatureC12_size_of_some hParse
  unfold C12Concrete.parseSignatureC12 at hParse
  simp only [hSize, ne_eq, not_true_eq_false, if_false, Option.some.injEq] at hParse
  subst hParse
  unfold c12Layer4ParsedWotsChains
  rw [SphincsMinusVerifierSpec.C13Concrete.getElem?_map_range _ (by decide : 4 < 5)]
  simp only [Option.getD_some]
  rw [SphincsMinusVerifierSpec.C13Concrete.getElem?_map_range _ hk]
  rfl

/-- Raw frozen-calldata read for a layer-4 C12 WOTS chain entry.  This extracts
the unmasked `calldataload` part used by the WOTS message/checksum loop
invariants, leaving masking and parser lookup to separate lemmas. -/
theorem c12_layer4_wots_raw_read_eq_frozen
    (st : RuntimeState)
    (wotsPtrE iE : Compiler.CompilationModel.Expr)
    (pkSeed pkRoot message sig : ByteArray)
    (k ap hval : Nat)
    (hsel : st.selector = 0)
    (hcd : st.world.calldata =
      MkC13State.headWords pkSeed pkRoot message sig.size ++
        MkC13State.bytesToWords sig)
    (hap : evalExpr [] st wotsPtrE = some ap)
    (hi : evalExpr [] st iE = some hval)
    (haplt : ap < 2 ^ 256) (hhlt : hval < 2 ^ 256)
    (hshift : hval <<< 4 < 2 ^ 256)
    (hsum : ap + hval <<< 4 < 2 ^ 256)
    (hoff : ap + hval <<< 4 =
      MkC13State.sigDataOffset + (2592 + 784 * 4 + 16 * k)) :
    evalExpr [] st
        (.calldataload (.add wotsPtrE (.shl (.literal 4) iE))) =
      some
        (Compiler.Proofs.YulGeneration.calldataloadWord 0
          (MkC13State.headWords pkSeed pkRoot message sig.size ++
            MkC13State.bytesToWords sig)
          (MkC13State.sigDataOffset + (2592 + 784 * 4 + 16 * k))) := by
  have hoffset := SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_siblingOffset
    st wotsPtrE iE ap hval hap hi haplt hhlt hshift hsum
  show (evalExpr [] st (.add wotsPtrE (.shl (.literal 4) iE))).bind
        (fun ro => some (Compiler.Proofs.YulGeneration.calldataloadWord
          st.selector st.world.calldata ro)) = _
  rw [hoffset]
  show some _ = _
  rw [hsel, hcd, hoff]

theorem calldataloadWord_eq_selector_zero_of_ge4
    (sel : Nat) (cd : List Nat) (off : Nat) (hoff : 4 ≤ off) :
    Compiler.Proofs.YulGeneration.calldataloadWord sel cd off =
      Compiler.Proofs.YulGeneration.calldataloadWord 0 cd off := by
  unfold Compiler.Proofs.YulGeneration.calldataloadWord
  simp [show off ≠ 0 by omega, show ¬ off < 4 by omega]

/-- Raw frozen-calldata read for a layer-4 C12 WOTS chain entry at offsets past
the ABI selector word.  The selector is irrelevant once the resolved offset is
at least four bytes into calldata, which is the shape needed by generic loop
invariants that quantify over states with only frozen world/binding facts. -/
theorem c12_layer4_wots_raw_read_eq_frozen_any_selector
    (st : RuntimeState)
    (wotsPtrE iE : Compiler.CompilationModel.Expr)
    (pkSeed pkRoot message sig : ByteArray)
    (k ap hval : Nat)
    (hcd : st.world.calldata =
      MkC13State.headWords pkSeed pkRoot message sig.size ++
        MkC13State.bytesToWords sig)
    (hap : evalExpr [] st wotsPtrE = some ap)
    (hi : evalExpr [] st iE = some hval)
    (haplt : ap < 2 ^ 256) (hhlt : hval < 2 ^ 256)
    (hshift : hval <<< 4 < 2 ^ 256)
    (hsum : ap + hval <<< 4 < 2 ^ 256)
    (hoff : ap + hval <<< 4 =
      MkC13State.sigDataOffset + (2592 + 784 * 4 + 16 * k)) :
    evalExpr [] st
        (.calldataload (.add wotsPtrE (.shl (.literal 4) iE))) =
      some
        (Compiler.Proofs.YulGeneration.calldataloadWord 0
          (MkC13State.headWords pkSeed pkRoot message sig.size ++
            MkC13State.bytesToWords sig)
          (MkC13State.sigDataOffset + (2592 + 784 * 4 + 16 * k))) := by
  have hoffset := SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_siblingOffset
    st wotsPtrE iE ap hval hap hi haplt hhlt hshift hsum
  have hoff4 :
      4 ≤ MkC13State.sigDataOffset + (2592 + 784 * 4 + 16 * k) := by
    show 4 ≤ 164 + (2592 + 784 * 4 + 16 * k)
    omega
  show (evalExpr [] st (.add wotsPtrE (.shl (.literal 4) iE))).bind
        (fun ro => some (Compiler.Proofs.YulGeneration.calldataloadWord
          st.selector st.world.calldata ro)) = _
  rw [hoffset]
  show some _ = _
  rw [hcd, hoff]
  rw [calldataloadWord_eq_selector_zero_of_ge4 st.selector _ _ hoff4]

/-- **Layer-4 WOTS calldata correspondence** — the per-chain kernel of the WOTS
scratch read for layer 4.  Under the frozen-C13 selector/calldata frame and
pointer/index evaluations, the masked `calldataload` at
`wotsPtr + (i << 4)` evaluates to `wordOfHash16` of the parsed WOTS chain entry
at index `k`.

The proof composes `evalExpr_siblingOffset` (the `add`/`shl` offset arithmetic
to `ap + hval<<<4`), `evalExpr_maskedCalldata` (the literal-`N_MASK` `bitAnd`
becomes `maskN`), and `SiblingCalldata.masked_sig_read_eq_wordOfHash16_gen`
(the calldata-image `maskN` equals the 16-byte signature read), then rewrites
the read using `hauth` (the parser fact).  This is the analog of
`merkle_sibling_read_frozen` specialised to the WOTS scratch with a generic
index-expression `iE` instead of the climb's hardcoded `localVar "h"`. -/
theorem c12_layer4_masked_wots_read_eq_wordOfHash16
    (st : RuntimeState)
    (wotsPtrE iE : Compiler.CompilationModel.Expr)
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature)
    (k ap hval : Nat)
    (hk : k < 45)
    (hsel : st.selector = 0)
    (hcd : st.world.calldata
            = MkC13State.headWords pkSeed pkRoot message sig.size
                ++ MkC13State.bytesToWords sig)
    (hap : evalExpr [] st wotsPtrE = some ap)
    (hi : evalExpr [] st iE = some hval)
    (haplt : ap < 2 ^ 256) (hhlt : hval < 2 ^ 256)
    (hshift : hval <<< 4 < 2 ^ 256) (hsum : ap + hval <<< 4 < 2 ^ 256)
    (hoff : ap + hval <<< 4
              = MkC13State.sigDataOffset + (2592 + 784 * 4 + 16 * k))
    (hauth : ((c12Layer4ParsedWotsChains sigParsed)[k]?).getD ⟨#[]⟩
              = SphincsMinusVerifierSpec.C13Concrete.read16 sig
                  (2592 + 784 * 4 + 16 * k)) :
    evalExpr [] st
        (.bitAnd (.calldataload (.add wotsPtrE (.shl (.literal 4) iE)))
          (.literal SphincsMinusVerifiers.ClimbKit.N_MASK))
      = some (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          (((c12Layer4ParsedWotsChains sigParsed)[k]?).getD ⟨#[]⟩)) := by
  have hoffset := SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_siblingOffset
    st wotsPtrE iE ap hval hap hi haplt hhlt hshift hsum
  have hcdl : evalExpr [] st
      (.calldataload (.add wotsPtrE (.shl (.literal 4) iE)))
        = some (Compiler.Proofs.YulGeneration.calldataloadWord 0
            (MkC13State.headWords pkSeed pkRoot message sig.size
              ++ MkC13State.bytesToWords sig)
            (MkC13State.sigDataOffset + (2592 + 784 * 4 + 16 * k))) := by
    show (evalExpr [] st (.add wotsPtrE (.shl (.literal 4) iE))).bind
          (fun ro => some (Compiler.Proofs.YulGeneration.calldataloadWord
            st.selector st.world.calldata ro)) = _
    rw [hoffset]; show some _ = _; rw [hsel, hcd, hoff]
  have hoff4 :
      4 ≤ MkC13State.sigDataOffset + (2592 + 784 * 4 + 16 * k) := by
    show 4 ≤ 164 + (2592 + 784 * 4 + 16 * k); omega
  have hbound :=
    SphincsMinusVerifiers.ClimbMemFrameMerkle.calldataloadWord_lt_of_ge4 0
      (MkC13State.headWords pkSeed pkRoot message sig.size
        ++ MkC13State.bytesToWords sig)
      (MkC13State.sigDataOffset + (2592 + 784 * 4 + 16 * k)) hoff4
  have hmasked := SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_maskedCalldata st
    (.add wotsPtrE (.shl (.literal 4) iE)) _ hcdl hbound
  have hgen := SphincsMinusVerifiers.SiblingCalldata.masked_sig_read_eq_wordOfHash16_gen
    pkSeed pkRoot message sig (2592 + 784 * 4 + 16 * k)
  show evalExpr [] st
      (.bitAnd (.calldataload (.add wotsPtrE (.shl (.literal 4) iE)))
        (.literal SphincsMinusVerifierSpec.C13Concrete.nMask)) = _
  rw [hmasked, hauth]
  exact congrArg some hgen

/-- The parsed layer-4 WOTS start node is already an EVM-normalized word: it is
definitionally a masked Keccak word. -/
theorem c12Layer4ParsedStartNode_normalized
    (pkSeed pkRoot message : ByteArray) (sigParsed : Signature) :
    wordNormalize (c12Layer4ParsedStartNode pkSeed pkRoot message sigParsed) =
      c12Layer4ParsedStartNode pkSeed pkRoot message sigParsed := by
  unfold c12Layer4ParsedStartNode C12Concrete.wotsPkWordC12
  exact SphincsMinusVerifiers.ClimbMemFrameMerkle.wordNormalize_maskN _

/-- The layer-4 XMSS initial raw relation reduces to the exact entry-state
`"curLeaf"` and pre-node `"wotsPk"` boundary facts.  The final setup bindings
copy those values into `"mIdx"`/`"merkleNode"` and injecting `"h"` leaves them
unchanged. -/
theorem c12_layer4_initial_raw_rel_of_entry_bindings
    (hLayer4CurLeafBeforeNode :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (C12SegmentWotsSetup.c12LayerStateBeforeXmssNode
            (c12LayerBodyInput4
              (C12SegmentForsCompress.c12StepForsCompress
                (C12SegmentFors.c12StepFors
                  (C12SegmentSeed.c12StepSeed
                    (MkC13State.mkC13State pkSeed pkRoot message sig)))))).bindings
          "curLeaf" =
        c12Layer4Leaf
          (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
    (hLayer4WotsPkBeforeNode :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (C12SegmentWotsSetup.c12LayerStateBeforeXmssNode
            (c12LayerBodyInput4
              (C12SegmentForsCompress.c12StepForsCompress
                (C12SegmentFors.c12StepFors
                  (C12SegmentSeed.c12StepSeed
                    (MkC13State.mkC13State pkSeed pkRoot message sig)))))).bindings
          "wotsPk" =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          (c12Layer4WotsPkBytes pkSeed
            (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex
            (c12UnrolledLayerRoot3 pkSeed
              (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex
              ((C12Concrete.forsPkFromSigC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot }
                  (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed)
                  sigParsed.fors).getD ⟨#[]⟩)
              sigParsed.layers)
            ((sigParsed.layers[4]?).getD c12EmptyXmssLayerSig))) :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
          "merkleNode" "mIdx"
          { (c12Layer4XmssEntryState pkSeed pkRoot message sig) with
            bindings :=
              bindValue
                (c12Layer4XmssEntryState pkSeed pkRoot message sig).bindings
                "h" (wordNormalize 0) }
          (c12Layer4Leaf
            (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex,
            c12Layer4ParsedStartNode pkSeed pkRoot message sigParsed) := by
  intro pkSeed pkRoot message sig sigParsed hParse
  let st0 :=
    C12SegmentWotsSetup.c12LayerStateBeforeXmssNode
      (c12Layer4PreBodyState pkSeed pkRoot message sig)
  have hIdx :
      lookupValue
          (bindValue (c12Layer4XmssEntryState pkSeed pkRoot message sig).bindings
            "h" (wordNormalize 0))
          "mIdx" =
        c12Layer4Leaf
          (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex := by
    unfold c12Layer4XmssEntryState C12SegmentWotsSetup.c12LayerStateBeforeXmssLoop
    rw [C12SegmentWotsSetup.c12LayerBodyBeforeXmssLoop_eq_beforeNode_append]
    rw [MemoryKit.execStmtList_append_continue _ _ _ _
      (C12SegmentWotsSetup.execC12LayerBodyBeforeXmssNode _)]
    rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ _
      (MemoryKit.execStmt_letVar_continue st0 "merkleNode" _ _ rfl)]
    rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ _
      (MemoryKit.execStmt_letVar_continue _ "mIdx" _ _ rfl)]
    change
      lookupValue
          (bindValue
            (bindValue
              (bindValue st0.bindings "merkleNode" (lookupValue st0.bindings "wotsPk"))
              "mIdx"
              (lookupValue
                (bindValue st0.bindings "merkleNode" (lookupValue st0.bindings "wotsPk"))
                "curLeaf"))
            "h" (wordNormalize 0))
          "mIdx" =
        c12Layer4Leaf
          (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex
    rw [MemoryKit.lookupValue_bindValue_ne _ "h" "mIdx" _ (by decide)]
    rw [MemoryKit.lookupValue_bindValue_self]
    rw [MemoryKit.lookupValue_bindValue_ne _ "merkleNode" "curLeaf" _ (by decide)]
    exact hLayer4CurLeafBeforeNode pkSeed pkRoot message sig sigParsed hParse
  have hNode :
      lookupValue
          (bindValue (c12Layer4XmssEntryState pkSeed pkRoot message sig).bindings
            "h" (wordNormalize 0))
          "merkleNode" =
        c12Layer4ParsedStartNode pkSeed pkRoot message sigParsed := by
    unfold c12Layer4XmssEntryState C12SegmentWotsSetup.c12LayerStateBeforeXmssLoop
    rw [C12SegmentWotsSetup.c12LayerBodyBeforeXmssLoop_eq_beforeNode_append]
    rw [MemoryKit.execStmtList_append_continue _ _ _ _
      (C12SegmentWotsSetup.execC12LayerBodyBeforeXmssNode _)]
    rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ _
      (MemoryKit.execStmt_letVar_continue st0 "merkleNode" _ _ rfl)]
    rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ _
      (MemoryKit.execStmt_letVar_continue _ "mIdx" _ _ rfl)]
    change
      lookupValue
          (bindValue
            (bindValue
              (bindValue st0.bindings "merkleNode" (lookupValue st0.bindings "wotsPk"))
              "mIdx"
              (lookupValue
                (bindValue st0.bindings "merkleNode" (lookupValue st0.bindings "wotsPk"))
                "curLeaf"))
            "h" (wordNormalize 0))
          "merkleNode" =
        c12Layer4ParsedStartNode pkSeed pkRoot message sigParsed
    rw [MemoryKit.lookupValue_bindValue_ne _ "h" "merkleNode" _ (by decide)]
    rw [MemoryKit.lookupValue_bindValue_ne _ "mIdx" "merkleNode" _ (by decide)]
    rw [MemoryKit.lookupValue_bindValue_self]
    let digest := c12Layer4ParsedMessage pkSeed pkRoot message sigParsed
    let nextTree := c12Layer4NextTree digest.hyperIndex
    let idxLeaf := c12Layer4Leaf digest.hyperIndex
    let node :=
      c12UnrolledLayerRoot3 pkSeed digest.hyperIndex
        ((C12Concrete.forsPkFromSigC12 c12
            { pkSeed := pkSeed, pkRoot := pkRoot } digest sigParsed.fors).getD ⟨#[]⟩)
        sigParsed.layers
    let layer4Sig := (sigParsed.layers[4]?).getD c12EmptyXmssLayerSig
    let wotsWord :=
      C12Concrete.wotsPkWordC12
        (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed)
        4 nextTree idxLeaf
        (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 node)
        layer4Sig.wots
    have hRoundtrip :
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
            (SphincsMinusVerifierSpec.C13Concrete.hash16OfWord wotsWord) =
          wotsWord := by
      unfold wotsWord C12Concrete.wotsPkWordC12
      exact SegmentAcceptSpec.wordOfHash16_hash16OfWord_maskN_of_lt _ (by
        simpa [Compiler.Constants.evmModulus] using
          SphincsMinusVerifiers.KeccakBridge.keccakWords_lt
            ((SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed) ::
              C12Concrete.wotsPkAdrsC12 4 nextTree idxLeaf ::
              (List.range 45).map (fun i =>
                let digit :=
                  if i < 42 then
                    C12Concrete.wotsDigitC12
                      (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 node) i
                  else
                    ((C12Concrete.wotsCsumC12
                          (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 node) <<< 7) >>>
                        (13 - 3 * (i - 42))) %
                      8
                let steps := 7 - digit
                let val :=
                  SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
                    ((layer4Sig.wots.chains[i]?).getD ⟨#[]⟩)
                let chainBase := C12Concrete.wotsBaseC12 4 nextTree idxLeaf ||| (i <<< 64)
                C12Concrete.chainHashC12
                  (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed)
                  chainBase digit steps 0 val)))
    change lookupValue st0.bindings "wotsPk" = wotsWord
    rw [← hRoundtrip]
    change lookupValue st0.bindings "wotsPk" =
      SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
        (c12Layer4WotsPkBytes pkSeed digest.hyperIndex node layer4Sig)
    exact hLayer4WotsPkBeforeNode pkSeed pkRoot message sig sigParsed hParse
  exact SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel.intro
    hIdx hNode (c12Layer4ParsedStartNode_normalized pkSeed pkRoot message sigParsed)

/-- Variant of `c12_layer4_initial_raw_rel_of_entry_bindings` that discharges
the `"curLeaf"` part through the WOTS setup prefix frame.  The remaining
`"curLeaf"` fact is now at the layer-4 body input, before the WOTS setup prefix
runs; `"wotsPk"` remains the exact computed pre-node binding. -/
theorem c12_layer4_initial_raw_rel_of_input_curLeaf_and_wotsPk
    (hLayer4CurLeafInput :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (c12LayerBodyInput4
            (C12SegmentForsCompress.c12StepForsCompress
              (C12SegmentFors.c12StepFors
                (C12SegmentSeed.c12StepSeed
                  (MkC13State.mkC13State pkSeed pkRoot message sig))))).bindings
          "curLeaf" =
        c12Layer4Leaf
          (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
    (hLayer4WotsPkBeforeNode :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (C12SegmentWotsSetup.c12LayerStateBeforeXmssNode
            (c12LayerBodyInput4
              (C12SegmentForsCompress.c12StepForsCompress
                (C12SegmentFors.c12StepFors
                  (C12SegmentSeed.c12StepSeed
                    (MkC13State.mkC13State pkSeed pkRoot message sig)))))).bindings
          "wotsPk" =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          (c12Layer4WotsPkBytes pkSeed
            (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex
            (c12UnrolledLayerRoot3 pkSeed
              (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex
              ((C12Concrete.forsPkFromSigC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot }
                  (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed)
                  sigParsed.fors).getD ⟨#[]⟩)
              sigParsed.layers)
            ((sigParsed.layers[4]?).getD c12EmptyXmssLayerSig))) :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
          "merkleNode" "mIdx"
          { (c12Layer4XmssEntryState pkSeed pkRoot message sig) with
            bindings :=
              bindValue
                (c12Layer4XmssEntryState pkSeed pkRoot message sig).bindings
                "h" (wordNormalize 0) }
          (c12Layer4Leaf
            (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex,
            c12Layer4ParsedStartNode pkSeed pkRoot message sigParsed) := by
  apply c12_layer4_initial_raw_rel_of_entry_bindings
  · intro pkSeed pkRoot message sig sigParsed hParse
    rw [C12SegmentWotsSetup.c12LayerStateBeforeXmssNode_curLeaf_eq]
    exact hLayer4CurLeafInput pkSeed pkRoot message sig sigParsed hParse
  · exact hLayer4WotsPkBeforeNode

/-- Raw Merkle-climb step preservation in exactly the shape required by the
layer-4 fold residual.  This is the raw counterpart of the shared normalized
`MerkleClimbRel_step`: the executable pair equality from
`stepMerkle_eq_merkleSpecStep` is welded directly into `MerkleClimbRawRel`. -/
theorem c12_layer4_MerkleClimbRawRel_step
    (nodeVar idxVar adrsBaseVar authPtrVar : String)
    (st : RuntimeState) (vsib vpar vadr sval o5 vnode o6 vsib2 : Nat)
    (seed treeAdrs h mIdx node : Nat)
    (auth : List SphincsMinusVerifierSpec.Bytes)
    (hne : nodeVar ≠ idxVar) (hne2 : nodeVar ≠ "parentIdx")
    (hparOff : (mIdx % 2 = 0 ∧ o5 = 0x40 ∧ o6 = 0x60)
             ∨ (mIdx % 2 = 1 ∧ o5 = 0x60 ∧ o6 = 0x40))
    (hvpar : vpar = mIdx / 2)
    (hnode : wordNormalize vnode = node)
    (hdata :
      SphincsMinusVerifiers.ClimbMemFrameMerkle.StepDataObligations
        st vadr vsib2 seed treeAdrs h mIdx auth)
    (h1 : evalExpr [] st
            (.bitAnd (.calldataload (.add (.localVar authPtrVar)
              (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK)) = some vsib)
    (h2 : evalExpr [] { st with bindings := bindValue st.bindings "sibling" vsib }
            (.shr (.literal 1) (.localVar idxVar)) = some vpar)
    (h3 : evalExpr []
            { st with bindings :=
              bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.bitOr (.localVar adrsBaseVar)
              (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
                (.localVar "parentIdx"))) = some vadr)
    (h4 : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
            (.shl (.literal 5) (.bitAnd (.localVar idxVar) (.literal 1))) = some sval)
    (h5off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x40) (.localVar "s")) = some o5)
    (h5val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate st.world.memory 0x20 vadr },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar nodeVar) = some vnode)
    (h6off : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.bitXor (.literal 0x60) (.localVar "s")) = some o6)
    (h6val : evalExpr []
            { st with
              world := { st.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode },
              bindings :=
                bindValue (bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar) "s" sval }
            (.localVar "sibling") = some vsib2) :
    SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel nodeVar idxVar
      (SphincsMinusVerifiers.ClimbKit.stepMerkle
        nodeVar idxVar adrsBaseVar authPtrVar st)
      (SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleSpecStep
        seed treeAdrs auth h (mIdx, node)) := by
  obtain ⟨hseed, hadr, hsib⟩ := hdata
  refine SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel_of_pair
    nodeVar idxVar
    (SphincsMinusVerifiers.ClimbKit.stepMerkle
      nodeVar idxVar adrsBaseVar authPtrVar st)
    seed treeAdrs h mIdx node auth ?_
  exact SphincsMinusVerifiers.ClimbMemFrameMerkle.stepMerkle_eq_merkleSpecStep
    nodeVar idxVar adrsBaseVar authPtrVar st
    vsib vpar vadr sval o5 vnode o6 vsib2 seed treeAdrs h mIdx node auth
    hne hne2 hparOff hvpar hseed hadr hnode hsib
    h1 h2 h3 h4 h5off h5val h6off h6val

def c12Layer4StepArithmeticObligations
    (a : Nat × Nat) (vpar vnode o5 o6 : Nat) : Prop :=
    ((a.1 % 2 = 0 ∧ o5 = 0x40 ∧ o6 = 0x60)
       ∨ (a.1 % 2 = 1 ∧ o5 = 0x60 ∧ o6 = 0x40))
    ∧ vpar = a.1 / 2
    ∧ wordNormalize vnode = a.2

def c12Layer4StepDataObligations
    (pkSeed pkRoot message _sig : ByteArray) (sigParsed : Signature)
    (s : RuntimeState) (a : Nat × Nat) (idx vadr vsib2 : Nat) : Prop :=
  SphincsMinusVerifiers.ClimbMemFrameMerkle.StepDataObligations
        { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
        vadr vsib2
        (c12Layer4ParsedSeed pkSeed)
        (c12Layer4ParsedBase pkSeed pkRoot message sigParsed)
        idx a.1 (c12Layer4ParsedAuth sigParsed)

def c12Layer4StepLocalEvalObligations
    (s : RuntimeState) (_a : Nat × Nat) (idx : Nat)
    (vsib vpar vadr sval o5 vnode o6 vsib2 : Nat) : Prop :=
  evalExpr []
        { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
        (.bitAnd (.calldataload (.add (.localVar "authPtr")
          (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK)) = some vsib
    ∧ evalExpr []
        { { s with bindings := bindValue s.bindings "h" (wordNormalize idx) } with
          bindings :=
            bindValue
              ({ s with bindings := bindValue s.bindings "h" (wordNormalize idx) }).bindings
              "sibling" vsib }
        (.shr (.literal 1) (.localVar "mIdx")) = some vpar
    ∧ evalExpr []
        { { s with bindings := bindValue s.bindings "h" (wordNormalize idx) } with
          bindings :=
            bindValue
              (bindValue
                ({ s with bindings := bindValue s.bindings "h" (wordNormalize idx) }).bindings
                "sibling" vsib)
              "parentIdx" vpar }
        (.bitOr (.localVar "xmssBase")
          (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
            (.localVar "parentIdx"))) = some vadr
    ∧ evalExpr []
        { { s with bindings := bindValue s.bindings "h" (wordNormalize idx) } with
          world :=
            { ({ s with bindings := bindValue s.bindings "h" (wordNormalize idx) }).world with
              memory :=
                MemoryKit.memUpdate
                  ({ s with bindings := bindValue s.bindings "h" (wordNormalize idx) }).world.memory
                  0x20 vadr },
          bindings :=
            bindValue
              (bindValue
                ({ s with bindings := bindValue s.bindings "h" (wordNormalize idx) }).bindings
                "sibling" vsib)
              "parentIdx" vpar }
        (.shl (.literal 5) (.bitAnd (.localVar "mIdx") (.literal 1))) = some sval
    ∧ evalExpr []
        { { s with bindings := bindValue s.bindings "h" (wordNormalize idx) } with
          world :=
            { ({ s with bindings := bindValue s.bindings "h" (wordNormalize idx) }).world with
              memory :=
                MemoryKit.memUpdate
                  ({ s with bindings := bindValue s.bindings "h" (wordNormalize idx) }).world.memory
                  0x20 vadr },
          bindings :=
            bindValue
              (bindValue
                (bindValue
                  ({ s with bindings := bindValue s.bindings "h" (wordNormalize idx) }).bindings
                  "sibling" vsib)
                "parentIdx" vpar)
              "s" sval }
        (.bitXor (.literal 0x40) (.localVar "s")) = some o5
    ∧ evalExpr []
        { { s with bindings := bindValue s.bindings "h" (wordNormalize idx) } with
          world :=
            { ({ s with bindings := bindValue s.bindings "h" (wordNormalize idx) }).world with
              memory :=
                MemoryKit.memUpdate
                  ({ s with bindings := bindValue s.bindings "h" (wordNormalize idx) }).world.memory
                  0x20 vadr },
          bindings :=
            bindValue
              (bindValue
                (bindValue
                  ({ s with bindings := bindValue s.bindings "h" (wordNormalize idx) }).bindings
                  "sibling" vsib)
                "parentIdx" vpar)
              "s" sval }
        (.localVar "merkleNode") = some vnode
    ∧ evalExpr []
        { { s with bindings := bindValue s.bindings "h" (wordNormalize idx) } with
          world :=
            { ({ s with bindings := bindValue s.bindings "h" (wordNormalize idx) }).world with
              memory :=
                MemoryKit.memUpdate
                  (MemoryKit.memUpdate
                    ({ s with bindings := bindValue s.bindings "h" (wordNormalize idx) }).world.memory
                    0x20 vadr)
                  o5 vnode },
          bindings :=
            bindValue
              (bindValue
                (bindValue
                  ({ s with bindings := bindValue s.bindings "h" (wordNormalize idx) }).bindings
                  "sibling" vsib)
                "parentIdx" vpar)
              "s" sval }
        (.bitXor (.literal 0x60) (.localVar "s")) = some o6
    ∧ evalExpr []
        { { s with bindings := bindValue s.bindings "h" (wordNormalize idx) } with
          world :=
            { ({ s with bindings := bindValue s.bindings "h" (wordNormalize idx) }).world with
              memory :=
                MemoryKit.memUpdate
                  (MemoryKit.memUpdate
                    ({ s with bindings := bindValue s.bindings "h" (wordNormalize idx) }).world.memory
                    0x20 vadr)
                  o5 vnode },
          bindings :=
            bindValue
              (bindValue
                (bindValue
                  ({ s with bindings := bindValue s.bindings "h" (wordNormalize idx) }).bindings
                  "sibling" vsib)
                "parentIdx" vpar)
              "s" sval }
        (.localVar "sibling") = some vsib2

/-- Concrete per-step obligations for the layer-4 generic XMSS bridge.  This is
the executable/evaluation surface needed by `c12_layer4_MerkleClimbRawRel_step`;
the package is split into arithmetic, auth-data, and local statement-evaluation
facts so the remaining residual can be attacked in smaller pieces. -/
def c12Layer4StepEvalObligations
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature)
    (s : RuntimeState) (a : Nat × Nat) (idx : Nat) : Prop :=
  ∃ vsib vpar vadr sval o5 vnode o6 vsib2,
    c12Layer4StepArithmeticObligations a vpar vnode o5 o6
    ∧ c12Layer4StepDataObligations
        pkSeed pkRoot message sig sigParsed s a idx vadr vsib2
    ∧ c12Layer4StepLocalEvalObligations
        s a idx vsib vpar vadr sval o5 vnode o6 vsib2

/-- The layer-4 sibling component of `StepDataObligations` follows from the
generic per-height calldata/auth correspondence once the local masked load has
been identified with C12's concrete layer-4 auth reader. -/
theorem c12Layer4StepSibling_of_local_load_data
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature)
    (s : RuntimeState) (a : Nat × Nat) (idx : Nat)
    (vsib vpar vadr sval o5 vnode o6 vsib2 : Nat)
    (hData :
      SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
        (c12Layer4ParsedAuth sigParsed)
        (c12Layer4ParsedAuthCdAt pkSeed pkRoot message sig) idx)
    (hLoad :
      vsib =
        SphincsMinusVerifierSpec.C13Concrete.maskN
          (c12Layer4ParsedAuthCdAt pkSeed pkRoot message sig idx))
    (hEval :
      c12Layer4StepLocalEvalObligations
        s a idx vsib vpar vadr sval o5 vnode o6 vsib2) :
    wordNormalize vsib2 =
      SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
        (((c12Layer4ParsedAuth sigParsed)[idx]?).getD ⟨#[]⟩) := by
  dsimp [c12Layer4StepLocalEvalObligations] at hEval
  rcases hEval with ⟨_h1, _h2, _h3, _h4, _h5off, _h5val, _h6off, h6val⟩
  exact SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleClimbData_to_sib
    (c12Layer4ParsedAuth sigParsed)
    (c12Layer4ParsedAuthCdAt pkSeed pkRoot message sig)
    idx
    { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
    vsib vpar vadr sval o5 vnode vsib2 h6val hLoad hData

/-- Data-obligation reduction for one layer-4 Merkle step.  The bundled
`c12Layer4StepDataObligations` is assembled from the two static frame facts
(`seed` cell and ADRS word) plus the existing per-height `MerkleClimbData` fact
and the local masked-load identification. -/
theorem c12Layer4StepDataObligations_of_frame_load
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature)
    (s : RuntimeState) (a : Nat × Nat) (idx : Nat)
    (vsib vpar vadr sval o5 vnode o6 vsib2 : Nat)
    (hData :
      SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
        (c12Layer4ParsedAuth sigParsed)
        (c12Layer4ParsedAuthCdAt pkSeed pkRoot message sig) idx)
    (hSeed :
      ({ s with bindings := bindValue s.bindings "h" (wordNormalize idx) }.world.memory
        0x00).val =
        c12Layer4ParsedSeed pkSeed)
    (hAdr :
      wordNormalize vadr =
        c12Layer4ParsedBase pkSeed pkRoot message sigParsed |||
          ((idx + 1) <<< 32) ||| a.1 / 2)
    (hLoad :
      vsib =
        SphincsMinusVerifierSpec.C13Concrete.maskN
          (c12Layer4ParsedAuthCdAt pkSeed pkRoot message sig idx))
    (hEval :
      c12Layer4StepLocalEvalObligations
        s a idx vsib vpar vadr sval o5 vnode o6 vsib2) :
    c12Layer4StepDataObligations
      pkSeed pkRoot message sig sigParsed s a idx vadr vsib2 := by
  dsimp [c12Layer4StepDataObligations]
  exact SphincsMinusVerifiers.ClimbMemFrameMerkle.StepDataObligations.intro
    hSeed hAdr
    (c12Layer4StepSibling_of_local_load_data
      pkSeed pkRoot message sig sigParsed s a idx
      vsib vpar vadr sval o5 vnode o6 vsib2 hData hLoad hEval)

/-- The arithmetic part of a layer-4 Merkle step is pure interpreter arithmetic:
`parentIdx` is `mIdx >>> 1 = mIdx / 2`, the selector swaps the two child slots by
the parity of `mIdx`, and the raw node read is already the accumulator node. -/
theorem c12Layer4StepArithmeticObligations_of_raw_local
    (s : RuntimeState) (a : Nat × Nat) (idx : Nat)
    (vsib vpar vadr sval o5 vnode o6 vsib2 : Nat)
    (hIdxLt : a.1 < 2 ^ 256)
    (hRaw :
      SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
        "merkleNode" "mIdx" s a)
    (hEval :
      c12Layer4StepLocalEvalObligations
        s a idx vsib vpar vadr sval o5 vnode o6 vsib2) :
    c12Layer4StepArithmeticObligations a vpar vnode o5 o6 := by
  dsimp [c12Layer4StepLocalEvalObligations] at hEval
  rcases hEval with ⟨_h1, h2, _h3, h4, h5off, h5val, h6off, _h6val⟩
  let stH : RuntimeState :=
    { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
  have hIdxH : lookupValue stH.bindings "mIdx" = a.1 := by
    dsimp [stH]
    rw [MemoryKit.lookupValue_bindValue_ne _ "h" "mIdx" _ (by decide)]
    exact hRaw.idx
  have h2' :
      evalExpr []
        { stH with bindings := bindValue stH.bindings "sibling" vsib }
        (.shr (.literal 1) (.localVar "mIdx")) = some (a.1 >>> 1) := by
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_parentIdx_shr
      "mIdx" { stH with bindings := bindValue stH.bindings "sibling" vsib }
      a.1
      (by
        dsimp [stH]
        rw [MemoryKit.lookupValue_bindValue_ne _ "sibling" "mIdx" _ (by decide)]
        rw [MemoryKit.lookupValue_bindValue_ne _ "h" "mIdx" _ (by decide)]
        exact hRaw.idx)
      hIdxLt
  have hvparShift : vpar = a.1 >>> 1 := by
    rw [h2] at h2'
    exact Option.some.inj h2'
  have h4' :
      evalExpr []
        { stH with
          world := { stH.world with memory := MemoryKit.memUpdate stH.world.memory 0x20 vadr },
          bindings := bindValue (bindValue stH.bindings "sibling" vsib) "parentIdx" vpar }
        (.shl (.literal 5) (.bitAnd (.localVar "mIdx") (.literal 1))) =
      some ((a.1 &&& 1) <<< 5) := by
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_selector_shl
      "mIdx"
      { stH with
        world := { stH.world with memory := MemoryKit.memUpdate stH.world.memory 0x20 vadr },
        bindings := bindValue (bindValue stH.bindings "sibling" vsib) "parentIdx" vpar }
      a.1
      (by
        dsimp [stH]
        rw [MemoryKit.lookupValue_bindValue_ne _ "parentIdx" "mIdx" _ (by decide)]
        rw [MemoryKit.lookupValue_bindValue_ne _ "sibling" "mIdx" _ (by decide)]
        rw [MemoryKit.lookupValue_bindValue_ne _ "h" "mIdx" _ (by decide)]
        exact hRaw.idx)
      hIdxLt
  have hsval : sval = (a.1 &&& 1) <<< 5 := by
    rw [h4] at h4'
    exact Option.some.inj h4'
  have hsvalLt : sval < 2 ^ 256 := by
    rw [hsval, Nat.shiftLeft_eq]
    exact Nat.lt_of_le_of_lt
      (Nat.mul_le_mul Nat.and_le_right (le_refl _)) (by decide)
  have h5off' :
      evalExpr []
        { stH with
          world := { stH.world with memory := MemoryKit.memUpdate stH.world.memory 0x20 vadr },
          bindings := bindValue
            (bindValue (bindValue stH.bindings "sibling" vsib) "parentIdx" vpar)
            "s" sval }
        (.bitXor (.literal 0x40) (.localVar "s")) = some ((0x40 : Nat) ^^^ sval) := by
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_childOffset_xor
      { stH with
        world := { stH.world with memory := MemoryKit.memUpdate stH.world.memory 0x20 vadr },
        bindings := bindValue
          (bindValue (bindValue stH.bindings "sibling" vsib) "parentIdx" vpar)
          "s" sval }
      0x40 sval
      (by rw [MemoryKit.lookupValue_bindValue_self])
      (by decide) hsvalLt
  have ho5 : o5 = (0x40 : Nat) ^^^ sval := by
    rw [h5off] at h5off'
    exact Option.some.inj h5off'
  have h6off' :
      evalExpr []
        { stH with
          world := { stH.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate stH.world.memory 0x20 vadr) o5 vnode },
          bindings := bindValue
            (bindValue (bindValue stH.bindings "sibling" vsib) "parentIdx" vpar)
            "s" sval }
        (.bitXor (.literal 0x60) (.localVar "s")) = some ((0x60 : Nat) ^^^ sval) := by
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_childOffset_xor
      { stH with
        world := { stH.world with memory := MemoryKit.memUpdate (MemoryKit.memUpdate stH.world.memory 0x20 vadr) o5 vnode },
        bindings := bindValue
          (bindValue (bindValue stH.bindings "sibling" vsib) "parentIdx" vpar)
          "s" sval }
      0x60 sval
      (by rw [MemoryKit.lookupValue_bindValue_self])
      (by decide) hsvalLt
  have ho6 : o6 = (0x60 : Nat) ^^^ sval := by
    rw [h6off] at h6off'
    exact Option.some.inj h6off'
  have h5val' :
      evalExpr []
        { stH with
          world := { stH.world with memory := MemoryKit.memUpdate stH.world.memory 0x20 vadr },
          bindings := bindValue
            (bindValue (bindValue stH.bindings "sibling" vsib) "parentIdx" vpar)
            "s" sval }
        (.localVar "merkleNode") = some a.2 := by
    show some
        (lookupValue
          (bindValue
            (bindValue (bindValue stH.bindings "sibling" vsib) "parentIdx" vpar)
            "s" sval)
          "merkleNode") = some a.2
    dsimp [stH]
    rw [MemoryKit.lookupValue_bindValue_ne _ "s" "merkleNode" _ (by decide)]
    rw [MemoryKit.lookupValue_bindValue_ne _ "parentIdx" "merkleNode" _ (by decide)]
    rw [MemoryKit.lookupValue_bindValue_ne _ "sibling" "merkleNode" _ (by decide)]
    rw [MemoryKit.lookupValue_bindValue_ne _ "h" "merkleNode" _ (by decide)]
    exact congrArg some hRaw.node
  have hvnode : vnode = a.2 := by
    rw [h5val] at h5val'
    exact Option.some.inj h5val'
  refine ⟨?_, ?_, ?_⟩
  · rcases Nat.mod_two_eq_zero_or_one a.1 with hpar | hpar
    · left
      have hs0 := SphincsMinusVerifiers.ClimbMemFrameMerkle.merkle_selector_even a.1 hpar
      have hoff := SphincsMinusVerifiers.ClimbMemFrameMerkle.merkle_offsets_even a.1 hpar
      rw [ho5, ho6, hsval, hoff.1, hoff.2]
      exact ⟨hpar, rfl, rfl⟩
    · right
      have hs1 := SphincsMinusVerifiers.ClimbMemFrameMerkle.merkle_selector_odd a.1 hpar
      have hoff := SphincsMinusVerifiers.ClimbMemFrameMerkle.merkle_offsets_odd a.1 hpar
      rw [ho5, ho6, hsval, hoff.1, hoff.2]
      exact ⟨hpar, rfl, rfl⟩
  · rw [hvparShift]
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.parentIdx_shiftRight a.1
  · rw [hvnode]
    exact hRaw.node_norm

/-- Layer-4 step advance reduced to concrete statement-evaluation facts plus the
shared `StepDataObligations` bundle. -/
theorem c12_layer4_stepRawAdvance_of_eval_obligations
    (hLayer4StepEvalObligations :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
          ∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat),
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
              (c12Layer4ParsedAuth sigParsed)
              (c12Layer4ParsedAuthCdAt pkSeed pkRoot message sig) idx →
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
              "merkleNode" "mIdx" s a →
            c12Layer4StepEvalObligations pkSeed pkRoot message sig sigParsed s a idx) :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
          ∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat),
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
              (c12Layer4ParsedAuth sigParsed)
              (c12Layer4ParsedAuthCdAt pkSeed pkRoot message sig) idx →
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
              "merkleNode" "mIdx" s a →
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
              "merkleNode" "mIdx"
                (SphincsMinusVerifiers.ClimbKit.stepMerkle
                  "merkleNode" "mIdx" "xmssBase" "authPtr"
                  { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
                (SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleSpecStep
                  (c12Layer4ParsedSeed pkSeed)
                  (c12Layer4ParsedBase pkSeed pkRoot message sigParsed)
                  (c12Layer4ParsedAuth sigParsed) idx a) := by
  intro pkSeed pkRoot message sig sigParsed hParse s a idx hData hRaw
  rcases hLayer4StepEvalObligations pkSeed pkRoot message sig sigParsed hParse
      s a idx hData hRaw with
    ⟨vsib, vpar, vadr, sval, o5, vnode, o6, vsib2,
      hArith, hStepData, hEval⟩
  dsimp [c12Layer4StepArithmeticObligations] at hArith
  dsimp [c12Layer4StepDataObligations] at hStepData
  dsimp [c12Layer4StepLocalEvalObligations] at hEval
  rcases hArith with ⟨hparOff, hvpar, hnode⟩
  rcases hEval with ⟨h1, h2, h3, h4, h5off, h5val, h6off, h6val⟩
  exact c12_layer4_MerkleClimbRawRel_step
    "merkleNode" "mIdx" "xmssBase" "authPtr"
    { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
    vsib vpar vadr sval o5 vnode o6 vsib2
    (c12Layer4ParsedSeed pkSeed)
    (c12Layer4ParsedBase pkSeed pkRoot message sigParsed)
    idx a.1 a.2 (c12Layer4ParsedAuth sigParsed)
    (by decide) (by decide) hparOff hvpar hnode hStepData
    h1 h2 h3 h4 h5off h5val h6off h6val

/-- Same layer-4 step advance, with the arithmetic bundle discharged from the
raw relation and local expression facts.  The remaining step residual is now the
data/local evaluation package plus the explicit EVM-word bound for `mIdx`. -/
theorem c12_layer4_stepRawAdvance_of_data_local_obligations
    (hLayer4StepDataLocalObligations :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
          ∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat),
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
              (c12Layer4ParsedAuth sigParsed)
              (c12Layer4ParsedAuthCdAt pkSeed pkRoot message sig) idx →
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
              "merkleNode" "mIdx" s a →
            ∃ vsib vpar vadr sval o5 vnode o6 vsib2,
              a.1 < 2 ^ 256
              ∧ c12Layer4StepDataObligations
                  pkSeed pkRoot message sig sigParsed s a idx vadr vsib2
              ∧ c12Layer4StepLocalEvalObligations
                  s a idx vsib vpar vadr sval o5 vnode o6 vsib2) :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
          ∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat),
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
              (c12Layer4ParsedAuth sigParsed)
              (c12Layer4ParsedAuthCdAt pkSeed pkRoot message sig) idx →
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
              "merkleNode" "mIdx" s a →
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
              "merkleNode" "mIdx"
                (SphincsMinusVerifiers.ClimbKit.stepMerkle
                  "merkleNode" "mIdx" "xmssBase" "authPtr"
                  { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
                (SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleSpecStep
                  (c12Layer4ParsedSeed pkSeed)
                  (c12Layer4ParsedBase pkSeed pkRoot message sigParsed)
                  (c12Layer4ParsedAuth sigParsed) idx a) := by
  refine c12_layer4_stepRawAdvance_of_eval_obligations ?_
  intro pkSeed pkRoot message sig sigParsed hParse s a idx hData hRaw
  rcases hLayer4StepDataLocalObligations pkSeed pkRoot message sig sigParsed hParse
      s a idx hData hRaw with
    ⟨vsib, vpar, vadr, sval, o5, vnode, o6, vsib2, hIdxLt, hStepData, hEval⟩
  exact ⟨vsib, vpar, vadr, sval, o5, vnode, o6, vsib2,
    c12Layer4StepArithmeticObligations_of_raw_local
      s a idx vsib vpar vadr sval o5 vnode o6 vsib2 hIdxLt hRaw hEval,
    hStepData, hEval⟩

/-- Layer-4 step advance with the data bundle reduced to frame/load facts.  The
remaining per-step data surface is the seed cell, the normalized ADRS word, and
the equality identifying the local masked sibling load with C12's concrete
layer-4 auth calldata reader; `MerkleClimbData` supplies the parsed-auth
correspondence already available in the fold. -/
theorem c12_layer4_stepRawAdvance_of_frame_local_obligations
    (hLayer4StepFrameLocalObligations :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
          ∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat),
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
              (c12Layer4ParsedAuth sigParsed)
              (c12Layer4ParsedAuthCdAt pkSeed pkRoot message sig) idx →
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
              "merkleNode" "mIdx" s a →
            ∃ vsib vpar vadr sval o5 vnode o6 vsib2,
              a.1 < 2 ^ 256
              ∧ ({ s with bindings := bindValue s.bindings "h" (wordNormalize idx) }.world.memory
                    0x00).val =
                  c12Layer4ParsedSeed pkSeed
              ∧ wordNormalize vadr =
                  c12Layer4ParsedBase pkSeed pkRoot message sigParsed |||
                    ((idx + 1) <<< 32) ||| a.1 / 2
              ∧ vsib =
                  SphincsMinusVerifierSpec.C13Concrete.maskN
                    (c12Layer4ParsedAuthCdAt pkSeed pkRoot message sig idx)
              ∧ c12Layer4StepLocalEvalObligations
                  s a idx vsib vpar vadr sval o5 vnode o6 vsib2) :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
          ∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat),
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
              (c12Layer4ParsedAuth sigParsed)
              (c12Layer4ParsedAuthCdAt pkSeed pkRoot message sig) idx →
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
              "merkleNode" "mIdx" s a →
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
              "merkleNode" "mIdx"
                (SphincsMinusVerifiers.ClimbKit.stepMerkle
                  "merkleNode" "mIdx" "xmssBase" "authPtr"
                  { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
                (SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleSpecStep
                  (c12Layer4ParsedSeed pkSeed)
                  (c12Layer4ParsedBase pkSeed pkRoot message sigParsed)
                  (c12Layer4ParsedAuth sigParsed) idx a) := by
  refine c12_layer4_stepRawAdvance_of_data_local_obligations ?_
  intro pkSeed pkRoot message sig sigParsed hParse s a idx hData hRaw
  rcases hLayer4StepFrameLocalObligations pkSeed pkRoot message sig sigParsed hParse
      s a idx hData hRaw with
    ⟨vsib, vpar, vadr, sval, o5, vnode, o6, vsib2,
      hIdxLt, hSeed, hAdr, hLoad, hEval⟩
  exact ⟨vsib, vpar, vadr, sval, o5, vnode, o6, vsib2, hIdxLt,
    c12Layer4StepDataObligations_of_frame_load
      pkSeed pkRoot message sig sigParsed s a idx
      vsib vpar vadr sval o5 vnode o6 vsib2
      hData hSeed hAdr hLoad hEval,
    hEval⟩

/-- The eight `c12Layer4StepLocalEvalObligations` evaluations follow from the
masked sibling-load eval (`h1`) and the address-assembly eval (`h3`) once the
raw relation supplies `"mIdx" ↦ a.1` and `"merkleNode" ↦ a.2` plus the EVM
bound `a.1 < 2 ^ 256`.  The remaining six derivations are pure expression
evaluations on bound-and-overlaid lookups, discharged by the shared
`eval_parentIdx_shr`, `eval_selector_shl`, and `eval_childOffset_xor`
combinators plus the lookup-frame `lookupValue_bindValue_*` lemmas. -/
theorem c12Layer4StepLocalEvalObligations_of_raw_load_adr
    (s : RuntimeState) (a : Nat × Nat) (idx vsib vadr : Nat)
    (hRaw :
      SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
        "merkleNode" "mIdx" s a)
    (hIdxLt : a.1 < 2 ^ 256)
    (h1 :
      evalExpr []
        { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
        (.bitAnd (.calldataload (.add (.localVar "authPtr")
          (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK)) = some vsib)
    (h3 :
      evalExpr []
        { s with bindings := bindValue (bindValue (bindValue s.bindings "h" (wordNormalize idx)) "sibling" vsib) "parentIdx" (a.1 >>> 1) }
        (.bitOr (.localVar "xmssBase")
          (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
            (.localVar "parentIdx"))) = some vadr) :
    c12Layer4StepLocalEvalObligations s a idx vsib (a.1 >>> 1) vadr
      ((Nat.land a.1 1) <<< 5)
      (Nat.xor 0x40 ((Nat.land a.1 1) <<< 5))
      a.2
      (Nat.xor 0x60 ((Nat.land a.1 1) <<< 5))
      vsib := by
  let stH : RuntimeState :=
    { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
  let vpar : Nat := a.1 >>> 1
  let sval : Nat := (Nat.land a.1 1) <<< 5
  let o5 : Nat := Nat.xor 0x40 sval
  let o6 : Nat := Nat.xor 0x60 sval
  have hmIdxH : lookupValue stH.bindings "mIdx" = a.1 := by
    show lookupValue (bindValue s.bindings "h" (wordNormalize idx)) "mIdx" = a.1
    rw [MemoryKit.lookupValue_bindValue_ne _ "h" "mIdx" _ (by decide)]
    exact hRaw.idx
  have hmIdx1 :
      lookupValue (bindValue stH.bindings "sibling" vsib) "mIdx" = a.1 := by
    rw [MemoryKit.lookupValue_bindValue_ne _ "sibling" "mIdx" _ (by decide)]
    exact hmIdxH
  have h2 :
      evalExpr []
        { stH with bindings := bindValue stH.bindings "sibling" vsib }
        (.shr (.literal 1) (.localVar "mIdx")) = some vpar := by
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_parentIdx_shr
      "mIdx" { stH with bindings := bindValue stH.bindings "sibling" vsib }
      a.1 hmIdx1 hIdxLt
  have hmIdx2 :
      lookupValue
        (bindValue (bindValue stH.bindings "sibling" vsib) "parentIdx" vpar)
        "mIdx" = a.1 := by
    rw [MemoryKit.lookupValue_bindValue_ne _ "parentIdx" "mIdx" _ (by decide)]
    exact hmIdx1
  have h4 :
      evalExpr []
        { stH with
          world := { stH.world with memory := MemoryKit.memUpdate stH.world.memory 0x20 vadr },
          bindings :=
            bindValue (bindValue stH.bindings "sibling" vsib) "parentIdx" vpar }
        (.shl (.literal 5) (.bitAnd (.localVar "mIdx") (.literal 1))) = some sval := by
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_selector_shl
      "mIdx"
      { stH with
        world := { stH.world with memory := MemoryKit.memUpdate stH.world.memory 0x20 vadr },
        bindings :=
          bindValue (bindValue stH.bindings "sibling" vsib) "parentIdx" vpar }
      a.1 hmIdx2 hIdxLt
  have hsvalLt : sval < 2 ^ 256 := by
    show (Nat.land a.1 1) <<< 5 < 2 ^ 256
    rw [Nat.shiftLeft_eq]
    exact Nat.lt_of_le_of_lt
      (Nat.mul_le_mul Nat.and_le_right (le_refl _)) (by decide)
  have hs4 :
      lookupValue
        (bindValue
          (bindValue (bindValue stH.bindings "sibling" vsib) "parentIdx" vpar)
          "s" sval)
        "s" = sval :=
    MemoryKit.lookupValue_bindValue_self _ "s" sval
  have h5off :
      evalExpr []
        { stH with
          world := { stH.world with memory := MemoryKit.memUpdate stH.world.memory 0x20 vadr },
          bindings :=
            bindValue
              (bindValue (bindValue stH.bindings "sibling" vsib) "parentIdx" vpar)
              "s" sval }
        (.bitXor (.literal 0x40) (.localVar "s")) = some o5 := by
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_childOffset_xor
      { stH with
        world := { stH.world with memory := MemoryKit.memUpdate stH.world.memory 0x20 vadr },
        bindings :=
          bindValue
            (bindValue (bindValue stH.bindings "sibling" vsib) "parentIdx" vpar)
            "s" sval }
      0x40 sval hs4 (by decide) hsvalLt
  have hmerkleNode_s :
      lookupValue
        (bindValue
          (bindValue (bindValue stH.bindings "sibling" vsib) "parentIdx" vpar)
          "s" sval)
        "merkleNode" = a.2 := by
    rw [MemoryKit.lookupValue_bindValue_ne _ "s" "merkleNode" _ (by decide)]
    rw [MemoryKit.lookupValue_bindValue_ne _ "parentIdx" "merkleNode" _ (by decide)]
    rw [MemoryKit.lookupValue_bindValue_ne _ "sibling" "merkleNode" _ (by decide)]
    show lookupValue (bindValue s.bindings "h" (wordNormalize idx)) "merkleNode" = a.2
    rw [MemoryKit.lookupValue_bindValue_ne _ "h" "merkleNode" _ (by decide)]
    exact hRaw.node
  have h5val :
      evalExpr []
        { stH with
          world := { stH.world with memory := MemoryKit.memUpdate stH.world.memory 0x20 vadr },
          bindings :=
            bindValue
              (bindValue (bindValue stH.bindings "sibling" vsib) "parentIdx" vpar)
              "s" sval }
        (.localVar "merkleNode") = some a.2 := by
    show some
        (lookupValue
          (bindValue
            (bindValue (bindValue stH.bindings "sibling" vsib) "parentIdx" vpar)
            "s" sval)
          "merkleNode") = some a.2
    exact congrArg some hmerkleNode_s
  have hs5 :
      lookupValue
        (bindValue
          (bindValue (bindValue stH.bindings "sibling" vsib) "parentIdx" vpar)
          "s" sval)
        "s" = sval :=
    MemoryKit.lookupValue_bindValue_self _ "s" sval
  have h6off :
      evalExpr []
        { stH with
          world := { stH.world with
            memory :=
              MemoryKit.memUpdate
                (MemoryKit.memUpdate stH.world.memory 0x20 vadr) o5 a.2 },
          bindings :=
            bindValue
              (bindValue (bindValue stH.bindings "sibling" vsib) "parentIdx" vpar)
              "s" sval }
        (.bitXor (.literal 0x60) (.localVar "s")) = some o6 := by
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_childOffset_xor
      { stH with
        world := { stH.world with
          memory :=
            MemoryKit.memUpdate
              (MemoryKit.memUpdate stH.world.memory 0x20 vadr) o5 a.2 },
        bindings :=
          bindValue
            (bindValue (bindValue stH.bindings "sibling" vsib) "parentIdx" vpar)
            "s" sval }
      0x60 sval hs5 (by decide) hsvalLt
  have hsibling_s :
      lookupValue
        (bindValue
          (bindValue (bindValue stH.bindings "sibling" vsib) "parentIdx" vpar)
          "s" sval)
        "sibling" = vsib := by
    rw [MemoryKit.lookupValue_bindValue_ne _ "s" "sibling" _ (by decide)]
    rw [MemoryKit.lookupValue_bindValue_ne _ "parentIdx" "sibling" _ (by decide)]
    exact MemoryKit.lookupValue_bindValue_self _ "sibling" vsib
  have h6val :
      evalExpr []
        { stH with
          world := { stH.world with
            memory :=
              MemoryKit.memUpdate
                (MemoryKit.memUpdate stH.world.memory 0x20 vadr) o5 a.2 },
          bindings :=
            bindValue
              (bindValue (bindValue stH.bindings "sibling" vsib) "parentIdx" vpar)
              "s" sval }
        (.localVar "sibling") = some vsib := by
    show some
        (lookupValue
          (bindValue
            (bindValue (bindValue stH.bindings "sibling" vsib) "parentIdx" vpar)
            "s" sval)
          "sibling") = some vsib
    exact congrArg some hsibling_s
  exact ⟨h1, h2, h3, h4, h5off, h5val, h6off, h6val⟩

/-- The C12 message digest produces a 20-bit hypertree index: the spec computes
`hyperIndex = (treeIdx <<< 4) ||| leafIdx` where `treeIdx = dVal >>> 140 % 2^16`
and `leafIdx = dVal >>> 156 % 2^4`, so `treeIdx <<< 4 < 2^20` and `leafIdx <
2^4 ≤ 2^20`. -/
theorem hMsgC12_hyperIndex_lt
    (v : Variant) (pk : PublicKey) (R message : ByteArray) :
    (C12Concrete.hMsgC12 v pk R message).hyperIndex < 2 ^ 20 := by
  unfold C12Concrete.hMsgC12
  refine Nat.bitwise_lt_two_pow ?_ ?_
  · rw [Nat.shiftLeft_eq]
    refine lt_of_lt_of_le
      (Nat.mul_lt_mul_of_pos_right
        (Nat.mod_lt _ (show (0 : Nat) < 2 ^ 16 by decide)) (by decide : 0 < 2 ^ 4))
      ?_
    decide
  · refine lt_of_lt_of_le
      (Nat.mod_lt _ (show (0 : Nat) < 2 ^ 4 by decide)) ?_
    decide

/-- The layer-4 parsed message's hypertree index is 20-bit; a direct corollary
of `hMsgC12_hyperIndex_lt`. -/
theorem c12Layer4ParsedMessage_hyperIndex_lt
    (pkSeed pkRoot message : ByteArray) (sigParsed : Signature) :
    (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex < 2 ^ 20 :=
  hMsgC12_hyperIndex_lt c12 _ sigParsed.R message

/-- The layer-4 next-tree index collapses to `0`: the hypertree index is 20-bit
and `c12Layer4NextTree x = x / 2^20`. -/
theorem c12Layer4NextTree_of_parsed_eq_zero
    (pkSeed pkRoot message : ByteArray) (sigParsed : Signature) :
    c12Layer4NextTree
        (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex = 0 := by
  unfold c12Layer4NextTree c12Layer4IdxTree
  have := c12Layer4ParsedMessage_hyperIndex_lt pkSeed pkRoot message sigParsed
  omega

private theorem c12_u256_val_of_lt {n : Nat} (h : n < 2 ^ 256) :
    (Verity.Core.Uint256.ofNat n).val = n := by
  show n % Verity.Core.Uint256.modulus = n
  rw [show Verity.Core.Uint256.modulus = 2 ^ 256 from rfl]
  exact Nat.mod_eq_of_lt h

private theorem c12_uint256_shr4_nat (a : Nat) (ha : a < 2 ^ 256) :
    (Verity.Core.Uint256.shr (wordNormalize 4) (a : Verity.Core.Uint256)).val =
      a / 16 := by
  unfold Verity.Core.Uint256.shr
  rw [show wordNormalize 4 = 4 by rfl]
  rw [c12_u256_val_of_lt ha]
  rw [c12_u256_val_of_lt (by decide : 4 < 2 ^ 256)]
  rw [Nat.shiftRight_eq_div_pow]
  exact c12_u256_val_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self a (2 ^ 4)) ha)

private theorem c12_nat_land_low4 (x : Nat) :
    Nat.land x 0xF = x % 2 ^ 4 := by
  change (x &&& (2 ^ 4 - 1)) = x % 2 ^ 4
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_land]
  by_cases hi : i < 4
  · have hmask : (2 ^ 4 - 1).testBit i = true := by
      rw [Nat.testBit_two_pow_sub_one]
      exact decide_eq_true hi
    rw [hmask, Bool.and_true]
    rw [Nat.testBit_mod_two_pow]
    simp [hi]
  · have hmask : (2 ^ 4 - 1).testBit i = false := by
      rw [Nat.testBit_two_pow_sub_one]
      exact decide_eq_false hi
    rw [hmask, Bool.and_false]
    rw [Nat.testBit_mod_two_pow]
    simp [hi]

private theorem c12_uint256_and15_nat (a : Nat) (ha : a < 2 ^ 256) :
    (Verity.Core.Uint256.and (a : Verity.Core.Uint256) (wordNormalize 0xF)).val =
      a % 16 := by
  unfold Verity.Core.Uint256.and
  rw [show wordNormalize 0xF = 15 by rfl]
  rw [c12_u256_val_of_lt ha]
  rw [c12_u256_val_of_lt (by decide : 15 < 2 ^ 256)]
  rw [c12_nat_land_low4]
  show (a % 2 ^ 4) % Verity.Core.Uint256.modulus = a % 16
  rw [show Verity.Core.Uint256.modulus = 2 ^ 256 from rfl]
  rw [Nat.mod_eq_of_lt
    (lt_trans (Nat.mod_lt _ (by decide : 0 < 2 ^ 4)) (by decide : 2 ^ 4 < 2 ^ 256))]
  rfl

private theorem c12_layer4_curLeaf_expr_of_treeIdx (treeIdx : Nat)
    (hTree : treeIdx < 2 ^ 16) :
    (Verity.Core.Uint256.and
        ((Verity.Core.Uint256.shr
        (wordNormalize 4)
        ((Verity.Core.Uint256.shr
          (wordNormalize 4)
          ((Verity.Core.Uint256.shr
            (wordNormalize 4)
            treeIdx).val)).val)).val)
      (wordNormalize 0xF)).val =
      (((treeIdx / 16) / 16) / 16) % 16 := by
  have hTree256 : treeIdx < 2 ^ 256 :=
    lt_trans hTree (by decide : 2 ^ 16 < 2 ^ 256)
  rw [c12_uint256_shr4_nat treeIdx hTree256]
  have h1 : treeIdx / 16 < 2 ^ 256 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self treeIdx 16) hTree256
  rw [c12_uint256_shr4_nat (treeIdx / 16) h1]
  have h2 : treeIdx / 16 / 16 < 2 ^ 256 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self (treeIdx / 16) 16) h1
  rw [c12_uint256_shr4_nat (treeIdx / 16 / 16) h2]
  have h3 : treeIdx / 16 / 16 / 16 < 2 ^ 256 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self (treeIdx / 16 / 16) 16) h2
  rw [c12_uint256_and15_nat (treeIdx / 16 / 16 / 16) h3]

private theorem c12_layer4_curTree_expr_of_treeIdx (treeIdx : Nat)
    (hTree : treeIdx < 2 ^ 16) :
    (Verity.Core.Uint256.shr
        (wordNormalize 4)
        ((Verity.Core.Uint256.shr
          (wordNormalize 4)
          ((Verity.Core.Uint256.shr
            (wordNormalize 4)
            ((Verity.Core.Uint256.shr
              (wordNormalize 4)
              treeIdx).val)).val)).val)).val = 0 := by
  have hTree256 : treeIdx < 2 ^ 256 :=
    lt_trans hTree (by decide : 2 ^ 16 < 2 ^ 256)
  rw [c12_uint256_shr4_nat treeIdx hTree256]
  have h1 : treeIdx / 16 < 2 ^ 256 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self treeIdx 16) hTree256
  rw [c12_uint256_shr4_nat (treeIdx / 16) h1]
  have h2 : treeIdx / 16 / 16 < 2 ^ 256 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self (treeIdx / 16) 16) h1
  rw [c12_uint256_shr4_nat (treeIdx / 16 / 16) h2]
  have h3 : treeIdx / 16 / 16 / 16 < 2 ^ 256 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self (treeIdx / 16 / 16) 16) h2
  rw [c12_uint256_shr4_nat (treeIdx / 16 / 16 / 16) h3]
  omega

private theorem c12_packed_hyperIndex_div16 (treeIdx leafIdx : Nat)
    (hLeaf : leafIdx < 2 ^ 4) :
    (((treeIdx <<< 4) ||| leafIdx) / 16) = treeIdx := by
  change (((treeIdx <<< 4) ||| leafIdx) / 2 ^ 4) = treeIdx
  rw [← Nat.shiftRight_eq_div_pow]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_shiftRight, Nat.testBit_lor]
  have hLeafBit : leafIdx.testBit (4 + i) = false := by
    exact Nat.testBit_eq_false_of_lt
      (lt_of_lt_of_le hLeaf
        (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_add_right 4 i)))
  rw [hLeafBit, Bool.or_false]
  simp [Nat.testBit_shiftLeft]

private theorem c12Layer4Leaf_packed_hyperIndex (treeIdx leafIdx : Nat)
    (hLeaf : leafIdx < 2 ^ 4) :
    c12Layer4Leaf ((treeIdx <<< 4) ||| leafIdx) =
      (((treeIdx / 16) / 16) / 16) % 16 := by
  unfold c12Layer4Leaf c12Layer4IdxTree
  rw [c12_packed_hyperIndex_div16 treeIdx leafIdx hLeaf]

/-- The layer-4 `"curLeaf"` handoff is the fourth nibble of C12's packed
hypertree index, obtained from the executable seed `treeIdx` and preserved
through FORS/FORS-compress into the layer recurrence. -/
theorem c12Layer4CurLeafAfter3
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature)
    (hParse : C12Concrete.parseSignatureC12 c12 sig = some sigParsed) :
    lookupValue
      (c12LayerStateAfter3
        (C12SegmentForsCompress.c12StepForsCompress
          (C12SegmentFors.c12StepFors
            (C12SegmentSeed.c12StepSeed
              (MkC13State.mkC13State pkSeed pkRoot message sig))))).bindings
      "curLeaf" =
    c12Layer4Leaf
      (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex := by
  let dVal :=
    SphincsMinusVerifierSpec.C13Concrete.keccakWords
      [ SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed
      , SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkRoot
      , SphincsMinusVerifierSpec.C13Concrete.baToNatBE sigParsed.R %
          SphincsMinusVerifierSpec.C13Concrete.wordMod
      , SphincsMinusVerifierSpec.C13Concrete.baToNatBE message %
          SphincsMinusVerifierSpec.C13Concrete.wordMod
      , C12Concrete.hMsgPad ]
  let treeIdx := (dVal >>> 140) % (2 ^ 16)
  let leafIdx := (dVal >>> 156) % (2 ^ 4)
  have hTreeLt : treeIdx < 2 ^ 16 := by
    exact Nat.mod_lt _ (by decide : 0 < 2 ^ 16)
  have hLeafLt : leafIdx < 2 ^ 4 := by
    exact Nat.mod_lt _ (by decide : 0 < 2 ^ 4)
  rw [c12LayerStateAfter3_curLeaf_eq_after_fors_compress]
  rw [C12SegmentFors.c12StepFors_preserves_treeIdx]
  rw [C12SegmentSeed.c12StepSeed_treeIdx_hMsgC12_words pkSeed pkRoot message sig sigParsed hParse]
  change
    (Verity.Core.Uint256.and
      ((Verity.Core.Uint256.shr
        (wordNormalize 4)
        ((Verity.Core.Uint256.shr
          (wordNormalize 4)
          ((Verity.Core.Uint256.shr
            (wordNormalize 4)
            treeIdx).val)).val)).val)
      (wordNormalize 0xF)).val =
    c12Layer4Leaf ((treeIdx <<< 4) ||| leafIdx)
  rw [c12_layer4_curLeaf_expr_of_treeIdx treeIdx hTreeLt,
    c12Layer4Leaf_packed_hyperIndex treeIdx leafIdx hLeafLt]

/-- After the fourth C12 hypertree layer, the 16-bit C12 tree index has been
shifted out completely, so layer 4 enters with `"curTree" = 0`. -/
theorem c12Layer4CurTreeAfter3
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature)
    (hParse : C12Concrete.parseSignatureC12 c12 sig = some sigParsed) :
    lookupValue
      (c12LayerStateAfter3
        (C12SegmentForsCompress.c12StepForsCompress
          (C12SegmentFors.c12StepFors
            (C12SegmentSeed.c12StepSeed
              (MkC13State.mkC13State pkSeed pkRoot message sig))))).bindings
      "curTree" = 0 := by
  let dVal :=
    SphincsMinusVerifierSpec.C13Concrete.keccakWords
      [ SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed
      , SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkRoot
      , SphincsMinusVerifierSpec.C13Concrete.baToNatBE sigParsed.R %
          SphincsMinusVerifierSpec.C13Concrete.wordMod
      , SphincsMinusVerifierSpec.C13Concrete.baToNatBE message %
          SphincsMinusVerifierSpec.C13Concrete.wordMod
      , C12Concrete.hMsgPad ]
  let treeIdx := (dVal >>> 140) % (2 ^ 16)
  have hTreeLt : treeIdx < 2 ^ 16 := by
    exact Nat.mod_lt _ (by decide : 0 < 2 ^ 16)
  rw [c12LayerStateAfter3_curTree_eq_after_fors_compress]
  rw [C12SegmentFors.c12StepFors_preserves_treeIdx]
  rw [C12SegmentSeed.c12StepSeed_treeIdx_hMsgC12_words
    pkSeed pkRoot message sig sigParsed hParse]
  change
    (Verity.Core.Uint256.shr
        (wordNormalize 4)
        ((Verity.Core.Uint256.shr
          (wordNormalize 4)
          ((Verity.Core.Uint256.shr
            (wordNormalize 4)
            ((Verity.Core.Uint256.shr
              (wordNormalize 4)
              treeIdx).val)).val)).val)).val = 0
  exact c12_layer4_curTree_expr_of_treeIdx treeIdx hTreeLt

/-- Layer-4 XMSS entry binds `"xmssBase"` to the parsed C12 layer-4 XMSS base.
This discharges the former public entry-site base premise. -/
theorem c12Layer4EntryXmssBase
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature)
    (hParse : C12Concrete.parseSignatureC12 c12 sig = some sigParsed) :
    lookupValue
      (c12Layer4XmssEntryState pkSeed pkRoot message sig).bindings "xmssBase" =
      c12Layer4ParsedBase pkSeed pkRoot message sigParsed := by
  unfold c12Layer4XmssEntryState
  rw [C12SegmentWotsSetup.c12LayerStateBeforeXmssLoop_xmssBase_eq_beforeXmssNode_xmssBase]
  rw [C12SegmentWotsSetup.c12LayerStateBeforeXmssNode_xmssBase_eq_beforeAuthOff]
  rw [C12SegmentWotsSetup.c12LayerStateBeforeAuthOff_layer_eq]
  rw [C12SegmentWotsSetup.c12LayerStateBeforeAuthOff_curTree_eq]
  unfold c12Layer4PreBodyState
  rw [c12LayerBodyInput4_layer_eq]
  rw [c12LayerBodyInput4_curTree_eq]
  rw [c12Layer4CurTreeAfter3 pkSeed pkRoot message sig sigParsed hParse]
  unfold c12Layer4ParsedBase C12Concrete.xmssBaseC12
  rw [c12Layer4NextTree_of_parsed_eq_zero]
  decide

/-- `c12Layer4ParsedBase` is naturally bounded below `2 ^ 256`: with the
next-tree index collapsing to `0`, the parsed base is `(4 <<< 224) | (2 <<<
128)`, a concrete value with only the 226th and 129th bits set. -/
theorem c12Layer4ParsedBase_lt
    (pkSeed pkRoot message : ByteArray) (sigParsed : Signature) :
    c12Layer4ParsedBase pkSeed pkRoot message sigParsed < 2 ^ 256 := by
  unfold c12Layer4ParsedBase C12Concrete.xmssBaseC12
  rw [c12Layer4NextTree_of_parsed_eq_zero]
  decide

/-- The layer-4 ADRS-assembly evaluation (`h3`) together with the matching
ADRS-frame equality `wordNormalize vadr = c12Layer4ParsedBase ... ||| ((idx + 1)
<<< 32) ||| a.1 / 2` follow from the parsed-base binding `"xmssBase" ↦
c12Layer4ParsedBase ...`, the EVM bound on the parsed base, the per-step climb
height bound `idx < 4`, and the EVM bound on the moving index `a.1`.  The
shared three-operand ADRS-word combinator
`ClimbKeccakStep.evalExpr_merkleAdrsWord` delivers the evaluation; the spec's
left-assoc grouping is reconciled by `Nat.lor_assoc` baked into that combinator,
and `a.1 >>> 1 = a.1 / 2` follows from `Nat.shiftRight_eq_div_pow`. -/
theorem c12Layer4StepAdr_h3_and_frame_of_xmssBase
    (pkSeed pkRoot message : ByteArray) (sigParsed : Signature)
    (s : RuntimeState) (a : Nat × Nat) (idx vsib : Nat)
    (hXmssBase :
      lookupValue s.bindings "xmssBase" =
        c12Layer4ParsedBase pkSeed pkRoot message sigParsed)
    (hBaseLt : c12Layer4ParsedBase pkSeed pkRoot message sigParsed < 2 ^ 256)
    (hIdxLtFour : idx < 4)
    (hMIdxLt : a.1 < 2 ^ 256) :
    ∃ vadr,
      evalExpr []
        { s with bindings := bindValue (bindValue (bindValue s.bindings "h" (wordNormalize idx)) "sibling" vsib) "parentIdx" (a.1 >>> 1) }
        (.bitOr (.localVar "xmssBase")
          (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
            (.localVar "parentIdx"))) = some vadr
      ∧ wordNormalize vadr =
          c12Layer4ParsedBase pkSeed pkRoot message sigParsed |||
            ((idx + 1) <<< 32) ||| a.1 / 2 := by
  let stA : RuntimeState :=
    { s with bindings := bindValue (bindValue (bindValue s.bindings "h" (wordNormalize idx)) "sibling" vsib) "parentIdx" (a.1 >>> 1) }
  let tb : Nat := c12Layer4ParsedBase pkSeed pkRoot message sigParsed
  let pi : Nat := a.1 >>> 1
  have hidx256 : idx < 2 ^ 256 := lt_trans hIdxLtFour (by decide)
  have hbase : evalExpr [] stA (.localVar "xmssBase") = some tb := by
    show some (lookupValue stA.bindings "xmssBase") = some tb
    dsimp [stA]
    rw [MemoryKit.lookupValue_bindValue_ne _ "parentIdx" "xmssBase" _ (by decide)]
    rw [MemoryKit.lookupValue_bindValue_ne _ "sibling" "xmssBase" _ (by decide)]
    rw [MemoryKit.lookupValue_bindValue_ne _ "h" "xmssBase" _ (by decide)]
    rw [hXmssBase]
  have hh : evalExpr [] stA (.localVar "h") = some idx := by
    show some (lookupValue stA.bindings "h") = some idx
    dsimp [stA]
    rw [MemoryKit.lookupValue_bindValue_ne _ "parentIdx" "h" _ (by decide)]
    rw [MemoryKit.lookupValue_bindValue_ne _ "sibling" "h" _ (by decide)]
    rw [MemoryKit.lookupValue_bindValue_self]
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt hidx256]
  have hpi : evalExpr [] stA (.localVar "parentIdx") = some pi := by
    show some (lookupValue stA.bindings "parentIdx") = some pi
    dsimp [stA, pi]
    rw [MemoryKit.lookupValue_bindValue_self]
  have hh1 : idx + 1 < 2 ^ 256 := by
    have : idx < 4 := hIdxLtFour
    omega
  have hshift : (idx + 1) <<< 32 < 2 ^ 256 := by
    rw [Nat.shiftLeft_eq]
    exact lt_of_le_of_lt
      (Nat.mul_le_mul_right (2 ^ 32) (Nat.succ_le_of_lt hIdxLtFour))
      (by decide : 4 * 2 ^ 32 < 2 ^ 256)
  have hpilt : pi < 2 ^ 256 := by
    dsimp [pi]
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.lt_of_le_of_lt (Nat.div_le_self a.1 (2 ^ 1)) hMIdxLt
  have heval :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_merkleAdrsWord
      stA (.localVar "xmssBase") (.localVar "h") (.localVar "parentIdx") tb idx pi
      hbase hh hpi hBaseLt hpilt hh1 hshift
  refine ⟨Nat.lor (Nat.lor tb ((idx + 1) <<< 32)) pi, heval, ?_⟩
  have hvadrLt :
      Nat.lor (Nat.lor tb ((idx + 1) <<< 32)) pi < 2 ^ 256 :=
    Nat.bitwise_lt_two_pow (Nat.bitwise_lt_two_pow hBaseLt hshift) hpilt
  rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
    Nat.mod_eq_of_lt hvadrLt]
  have hShiftEq : a.1 >>> 1 = a.1 / 2 := by
    rw [Nat.shiftRight_eq_div_pow, pow_one]
  show Nat.lor (Nat.lor tb ((idx + 1) <<< 32)) (a.1 >>> 1) =
       tb ||| ((idx + 1) <<< 32) ||| a.1 / 2
  rw [hShiftEq]
  rfl

/-- Layer-4 step advance reduced further: replace the 8-conjunct
`c12Layer4StepLocalEvalObligations` package with the two genuinely
site-specific evaluations — the masked sibling-load (`h1`) and the
address-assembly eval (`h3`) — together with the existing seed/ADRS frame
facts and the EVM bound on `a.1`.  The remaining six per-step evaluations are
pure interpreter arithmetic, discharged by
`c12Layer4StepLocalEvalObligations_of_raw_load_adr`. -/
theorem c12_layer4_stepRawAdvance_of_seed_load_adr_obligations
    (hLayer4StepSeedLoadAdrObligations :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
          ∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat),
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
              (c12Layer4ParsedAuth sigParsed)
              (c12Layer4ParsedAuthCdAt pkSeed pkRoot message sig) idx →
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
              "merkleNode" "mIdx" s a →
            ∃ vsib vadr,
              a.1 < 2 ^ 256
              ∧ ({ s with bindings := bindValue s.bindings "h" (wordNormalize idx) }.world.memory
                    0x00).val =
                  c12Layer4ParsedSeed pkSeed
              ∧ wordNormalize vadr =
                  c12Layer4ParsedBase pkSeed pkRoot message sigParsed |||
                    ((idx + 1) <<< 32) ||| a.1 / 2
              ∧ vsib =
                  SphincsMinusVerifierSpec.C13Concrete.maskN
                    (c12Layer4ParsedAuthCdAt pkSeed pkRoot message sig idx)
              ∧ evalExpr []
                  { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
                  (.bitAnd (.calldataload (.add (.localVar "authPtr")
                    (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK)) =
                  some vsib
              ∧ evalExpr []
                  { s with bindings := bindValue (bindValue (bindValue s.bindings "h" (wordNormalize idx)) "sibling" vsib) "parentIdx" (a.1 >>> 1) }
                  (.bitOr (.localVar "xmssBase")
                    (.bitOr (.shl (.literal 32) (.add (.localVar "h") (.literal 1)))
                      (.localVar "parentIdx"))) = some vadr) :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
          ∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat),
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
              (c12Layer4ParsedAuth sigParsed)
              (c12Layer4ParsedAuthCdAt pkSeed pkRoot message sig) idx →
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
              "merkleNode" "mIdx" s a →
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
              "merkleNode" "mIdx"
                (SphincsMinusVerifiers.ClimbKit.stepMerkle
                  "merkleNode" "mIdx" "xmssBase" "authPtr"
                  { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
                (SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleSpecStep
                  (c12Layer4ParsedSeed pkSeed)
                  (c12Layer4ParsedBase pkSeed pkRoot message sigParsed)
                  (c12Layer4ParsedAuth sigParsed) idx a) := by
  refine c12_layer4_stepRawAdvance_of_frame_local_obligations ?_
  intro pkSeed pkRoot message sig sigParsed hParse s a idx hData hRaw
  rcases hLayer4StepSeedLoadAdrObligations pkSeed pkRoot message sig sigParsed hParse
      s a idx hData hRaw with
    ⟨vsib, vadr, hIdxLt, hSeed, hAdr, hLoad, h1, h3⟩
  refine
    ⟨vsib, a.1 >>> 1, vadr,
      (Nat.land a.1 1) <<< 5,
      Nat.xor 0x40 ((Nat.land a.1 1) <<< 5),
      a.2,
      Nat.xor 0x60 ((Nat.land a.1 1) <<< 5),
      vsib, hIdxLt, hSeed, ?_, hLoad, ?_⟩
  · -- ADRS frame: rewrite `a.1 / 2` to `a.1 >>> 1`
    have hShift : a.1 / 2 = a.1 >>> 1 := by
      rw [Nat.shiftRight_succ, Nat.shiftRight_zero]
    rw [hShift] at hAdr
    exact hAdr
  · exact c12Layer4StepLocalEvalObligations_of_raw_load_adr
      s a idx vsib vadr hRaw hIdxLt h1 h3

/-- Layer-4 step advance with the ADRS bundle reduced to the `"xmssBase"`
binding and a per-step `idx < 4` bound.  Compared with
`c12_layer4_stepRawAdvance_of_seed_load_adr_obligations`, the residual no longer
carries the ADRS-assembly `evalExpr` (`h3`) or the ADRS-frame equality
(`wordNormalize vadr = …`); both are now supplied by
`c12Layer4StepAdr_h3_and_frame_of_xmssBase` from the parsed-base binding plus
EVM bounds.  The remaining per-step residual is the seed cell, the masked
sibling-load eval (`h1`) and the matching parsed-auth identification (`vsib =
maskN …`), the EVM bound on `a.1`, the parsed-base binding `"xmssBase" ↦
c12Layer4ParsedBase …` and its EVM bound, and the height bound `idx < 4`. -/
theorem c12_layer4_stepRawAdvance_of_seed_load_xmssBase_obligations
    (hLayer4StepSeedLoadXmssBaseObligations :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
          ∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat),
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
              (c12Layer4ParsedAuth sigParsed)
              (c12Layer4ParsedAuthCdAt pkSeed pkRoot message sig) idx →
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
              "merkleNode" "mIdx" s a →
            ∃ vsib,
              a.1 < 2 ^ 256
              ∧ ({ s with bindings := bindValue s.bindings "h" (wordNormalize idx) }.world.memory
                    0x00).val =
                  c12Layer4ParsedSeed pkSeed
              ∧ vsib =
                  SphincsMinusVerifierSpec.C13Concrete.maskN
                    (c12Layer4ParsedAuthCdAt pkSeed pkRoot message sig idx)
              ∧ evalExpr []
                  { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
                  (.bitAnd (.calldataload (.add (.localVar "authPtr")
                    (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK)) =
                  some vsib
              ∧ lookupValue s.bindings "xmssBase" =
                  c12Layer4ParsedBase pkSeed pkRoot message sigParsed
              ∧ c12Layer4ParsedBase pkSeed pkRoot message sigParsed < 2 ^ 256
              ∧ idx < 4) :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
          ∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat),
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
              (c12Layer4ParsedAuth sigParsed)
              (c12Layer4ParsedAuthCdAt pkSeed pkRoot message sig) idx →
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
              "merkleNode" "mIdx" s a →
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
              "merkleNode" "mIdx"
                (SphincsMinusVerifiers.ClimbKit.stepMerkle
                  "merkleNode" "mIdx" "xmssBase" "authPtr"
                  { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
                (SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleSpecStep
                  (c12Layer4ParsedSeed pkSeed)
                  (c12Layer4ParsedBase pkSeed pkRoot message sigParsed)
                  (c12Layer4ParsedAuth sigParsed) idx a) := by
  refine c12_layer4_stepRawAdvance_of_seed_load_adr_obligations ?_
  intro pkSeed pkRoot message sig sigParsed hParse s a idx hData hRaw
  rcases hLayer4StepSeedLoadXmssBaseObligations pkSeed pkRoot message sig sigParsed hParse
      s a idx hData hRaw with
    ⟨vsib, hIdxLt, hSeed, hLoad, h1, hXmssBase, hBaseLt, hIdxLtFour⟩
  obtain ⟨vadr, h3, hAdr⟩ :=
    c12Layer4StepAdr_h3_and_frame_of_xmssBase
      pkSeed pkRoot message sigParsed s a idx vsib
      hXmssBase hBaseLt hIdxLtFour hIdxLt
  exact ⟨vsib, vadr, hIdxLt, hSeed, hAdr, hLoad, h1, h3⟩

/-- Substantive closure of the masked sibling-load eval (`h1`) for layer 4 at
the `"h" ↦ wordNormalize idx` injected state.  Given the frozen C13 selector
(`hsel`) / calldata (`hcd`) image and the parsed layer-4 `"authPtr"` binding
`= sigDataOffset + (2592 + 784·4 + 720)`, the masked `calldataload` evaluates
to `maskN (c12Layer4ParsedAuthCdAt … idx)` — directly the value the per-step
masked-load frame fact pins `vsib` to.  Uses the shared
`ClimbMemFrameMerkle.merkle_sibling_read_frozen` to thread the offset-arithmetic
through the frozen image; only the `idx < 4` height bound is needed for the
shift/sum-overflow safety. -/
theorem c12Layer4StepLoad_h1_of_state_shape
    (pkSeed pkRoot message sig : ByteArray)
    (s : RuntimeState) (idx : Nat)
    (hsel : s.selector = 0)
    (hcd :
      s.world.calldata =
        MkC13State.headWords pkSeed pkRoot message sig.size
          ++ MkC13State.bytesToWords sig)
    (hauthPtr :
      lookupValue s.bindings "authPtr" =
        MkC13State.sigDataOffset + (2592 + 784 * 4 + 720))
    (hIdxLt4 : idx < 4) :
    evalExpr []
        { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
        (.bitAnd (.calldataload (.add (.localVar "authPtr")
          (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK)) =
      some (SphincsMinusVerifierSpec.C13Concrete.maskN
              (c12Layer4ParsedAuthCdAt pkSeed pkRoot message sig idx)) := by
  let stH : RuntimeState :=
    { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
  let ap : Nat := MkC13State.sigDataOffset + (2592 + 784 * 4 + 720)
  let sOff : Nat := 2592 + 784 * 4 + 720 + 16 * idx
  have hidx256 : idx < 2 ^ 256 := lt_trans hIdxLt4 (by decide)
  have hselH : stH.selector = 0 := hsel
  have hcdH :
      stH.world.calldata =
        MkC13State.headWords pkSeed pkRoot message sig.size
          ++ MkC13State.bytesToWords sig := hcd
  have hapH : evalExpr [] stH (.localVar "authPtr") = some ap := by
    show some (lookupValue stH.bindings "authPtr") = some ap
    rw [MemoryKit.lookupValue_bindValue_ne _ "h" "authPtr" _ (by decide)]
    exact congrArg some hauthPtr
  have hhH : evalExpr [] stH (.localVar "h") = some idx := by
    show some (lookupValue stH.bindings "h") = some idx
    rw [MemoryKit.lookupValue_bindValue_self]
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt hidx256]
  have haplt : ap < 2 ^ 256 := by
    dsimp [ap, MkC13State.sigDataOffset]; omega
  have hshift : idx <<< 4 < 2 ^ 256 := by
    rw [Nat.shiftLeft_eq]; omega
  have hsum : ap + idx <<< 4 < 2 ^ 256 := by
    dsimp [ap, MkC13State.sigDataOffset]; rw [Nat.shiftLeft_eq]; omega
  have hoff : ap + idx <<< 4 = MkC13State.sigDataOffset + sOff := by
    dsimp [ap, sOff]; rw [Nat.shiftLeft_eq]; omega
  have hoff4 : 4 ≤ MkC13State.sigDataOffset + sOff := by
    dsimp [sOff, MkC13State.sigDataOffset]; omega
  exact SphincsMinusVerifiers.ClimbMemFrameMerkle.merkle_sibling_read_frozen
    stH "authPtr" pkSeed pkRoot message sig ap idx sOff
    hselH hcdH hapH hhH haplt hidx256 hshift hsum hoff hoff4

/-- Frozen C12 layer-4 Merkle-site invariant: bundles the EVM
selector/calldata image, the parsed-base `"authPtr"` binding, the parsed-base
`"xmssBase"` binding, and the seed cell at `mem[0x00]`.  These are all
preserved by one `stepMerkle` step (via the existing
`stepMerkle_selector_calldata`/`_binding_frozen`/`_mem_zero` frame lemmas), so
the consumer supplies the invariant *once* at the fold entry and threads it
through iterations.  Modelled after `SegmentLayer3MerkleFrame.LayerFrozenSite`
and `SegmentS4ForsMerkleFrame.ForsFrozenSite`. -/
def C12Layer4FrozenSite
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature)
    (s : RuntimeState) : Prop :=
  s.selector = 0
  ∧ s.world.calldata =
      MkC13State.headWords pkSeed pkRoot message sig.size
        ++ MkC13State.bytesToWords sig
  ∧ lookupValue s.bindings "authPtr" =
      MkC13State.sigDataOffset + (2592 + 784 * 4 + 720)
  ∧ lookupValue s.bindings "xmssBase" =
      c12Layer4ParsedBase pkSeed pkRoot message sigParsed
  ∧ (s.world.memory 0x00).val = c12Layer4ParsedSeed pkSeed

/-- The frozen-site invariant is preserved by binding `"h" ↦ wordNormalize
idx`: the `"h"` binding is fresh, world fields (`selector`, `calldata`,
`memory`) are untouched, and the four invariant bindings (`authPtr`,
`xmssBase`) are looked up at names distinct from `"h"`. -/
theorem C12Layer4FrozenSite.h_inject
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature)
    (s : RuntimeState) (idx : Nat)
    (hsite : C12Layer4FrozenSite pkSeed pkRoot message sig sigParsed s) :
    C12Layer4FrozenSite pkSeed pkRoot message sig sigParsed
      { s with bindings := bindValue s.bindings "h" (wordNormalize idx) } := by
  obtain ⟨hSel, hCD, hAuthPtr, hXmssBase, hSeed⟩ := hsite
  refine ⟨hSel, hCD, ?_, ?_, hSeed⟩
  · rw [MemoryKit.lookupValue_bindValue_ne _ "h" "authPtr" _ (by decide)]
    exact hAuthPtr
  · rw [MemoryKit.lookupValue_bindValue_ne _ "h" "xmssBase" _ (by decide)]
    exact hXmssBase

/-- Layer-4 step advance with the masked-load eval (`h1`) AND the masked-load
frame (`vsib = maskN …`) jointly reduced to the frozen-calldata state-shape
facts: `selector = 0`, the C13 frozen calldata image, and the parsed-base
`"authPtr"` binding.  The user no longer carries `h1` or the frame
identification — both are derived by `c12Layer4StepLoad_h1_of_state_shape` with
the canonical witness `vsib := maskN (c12Layer4ParsedAuthCdAt … idx)`. -/
theorem c12_layer4_stepRawAdvance_of_seed_xmssBase_calldata_authPtr_obligations
    (hLayer4StepObligations :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
          ∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat),
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
              (c12Layer4ParsedAuth sigParsed)
              (c12Layer4ParsedAuthCdAt pkSeed pkRoot message sig) idx →
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
              "merkleNode" "mIdx" s a →
              a.1 < 2 ^ 256
              ∧ ({ s with bindings := bindValue s.bindings "h" (wordNormalize idx) }.world.memory
                    0x00).val =
                  c12Layer4ParsedSeed pkSeed
              ∧ s.selector = 0
              ∧ s.world.calldata =
                  MkC13State.headWords pkSeed pkRoot message sig.size
                    ++ MkC13State.bytesToWords sig
              ∧ lookupValue s.bindings "authPtr" =
                  MkC13State.sigDataOffset + (2592 + 784 * 4 + 720)
              ∧ lookupValue s.bindings "xmssBase" =
                  c12Layer4ParsedBase pkSeed pkRoot message sigParsed
              ∧ idx < 4) :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
          ∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat),
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
              (c12Layer4ParsedAuth sigParsed)
              (c12Layer4ParsedAuthCdAt pkSeed pkRoot message sig) idx →
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
              "merkleNode" "mIdx" s a →
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
              "merkleNode" "mIdx"
                (SphincsMinusVerifiers.ClimbKit.stepMerkle
                  "merkleNode" "mIdx" "xmssBase" "authPtr"
                  { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
                (SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleSpecStep
                  (c12Layer4ParsedSeed pkSeed)
                  (c12Layer4ParsedBase pkSeed pkRoot message sigParsed)
                  (c12Layer4ParsedAuth sigParsed) idx a) := by
  refine c12_layer4_stepRawAdvance_of_seed_load_xmssBase_obligations ?_
  intro pkSeed pkRoot message sig sigParsed hParse s a idx hData hRaw
  obtain ⟨hIdxLt, hSeed, hSel, hCD, hAuthPtr, hXmssBase, hIdxLtFour⟩ :=
    hLayer4StepObligations pkSeed pkRoot message sig sigParsed hParse s a idx hData hRaw
  refine
    ⟨SphincsMinusVerifierSpec.C13Concrete.maskN
        (c12Layer4ParsedAuthCdAt pkSeed pkRoot message sig idx),
      hIdxLt, hSeed, rfl, ?_, hXmssBase,
      c12Layer4ParsedBase_lt pkSeed pkRoot message sigParsed, hIdxLtFour⟩
  exact c12Layer4StepLoad_h1_of_state_shape
    pkSeed pkRoot message sig s idx hSel hCD hAuthPtr hIdxLtFour

/-- Layer-4 step advance with the five static state-shape per-step facts
(selector, frozen calldata image, `"authPtr"` binding, `"xmssBase"` binding,
and seed cell at `mem[0x00]`) bundled into the single `C12Layer4FrozenSite`
predicate.  The residual now carries the frozen site itself, the EVM bound on
`a.1`, and the per-step height bound `idx < 4`; the seed cell at the
`"h"`-injected state and the four binding/world facts are projected from the
site.  Modelled after the C13/FORS frozen-site reducers in
`SegmentLayer3MerkleFrame` and `SegmentS4ForsMerkleFrame`. -/
theorem c12_layer4_stepRawAdvance_of_frozenSite_obligations
    (hLayer4StepObligations :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
          ∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat),
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
              (c12Layer4ParsedAuth sigParsed)
              (c12Layer4ParsedAuthCdAt pkSeed pkRoot message sig) idx →
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
              "merkleNode" "mIdx" s a →
              a.1 < 2 ^ 256
              ∧ C12Layer4FrozenSite pkSeed pkRoot message sig sigParsed s
              ∧ idx < 4) :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
          ∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat),
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
              (c12Layer4ParsedAuth sigParsed)
              (c12Layer4ParsedAuthCdAt pkSeed pkRoot message sig) idx →
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
              "merkleNode" "mIdx" s a →
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
              "merkleNode" "mIdx"
                (SphincsMinusVerifiers.ClimbKit.stepMerkle
                  "merkleNode" "mIdx" "xmssBase" "authPtr"
                  { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
                (SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleSpecStep
                  (c12Layer4ParsedSeed pkSeed)
                  (c12Layer4ParsedBase pkSeed pkRoot message sigParsed)
                  (c12Layer4ParsedAuth sigParsed) idx a) := by
  refine c12_layer4_stepRawAdvance_of_seed_xmssBase_calldata_authPtr_obligations ?_
  intro pkSeed pkRoot message sig sigParsed hParse s a idx hData hRaw
  obtain ⟨hIdxLt, hSite, hIdxLtFour⟩ :=
    hLayer4StepObligations pkSeed pkRoot message sig sigParsed hParse s a idx hData hRaw
  obtain ⟨hSel, hCD, hAuthPtr, hXmssBase, hSeed⟩ := hSite
  refine ⟨hIdxLt, ?_, hSel, hCD, hAuthPtr, hXmssBase, hIdxLtFour⟩
  exact hSeed

/-- The frozen-site invariant for layer 4 is preserved by one `stepMerkle`
step over the `"h"`-injected state.  Given the raw Merkle climb relation
(`hRaw`), the frozen site at `s` (selector/calldata image, parsed-base
`"authPtr"`/`"xmssBase"` bindings, seed cell at `mem[0x00]`), the EVM bound
`a.1 < 2 ^ 256`, and the per-step height bound `idx < 4`, the stepped state
still satisfies the frame.  The proof composes the existing per-step
preservation lemmas
`ClimbMemFrameMerkle.stepMerkle_selector_calldata` (selector/calldata),
`stepMerkle_binding_frozen` (the `"authPtr"`/`"xmssBase"` bindings), and
`stepMerkle_mem_zero` (the seed cell at `0x00`); the eight `evalExpr` frame
premises are produced from the frozen site itself by
`c12Layer4StepLoad_h1_of_state_shape` and
`c12Layer4StepAdr_h3_and_frame_of_xmssBase`, then packaged via
`c12Layer4StepLocalEvalObligations_of_raw_load_adr`.  The disjointness of the
parity-swapped child offsets `o5 = 0x40 ^^^ sval` and `o6 = 0x60 ^^^ sval`
from `0x00` follows from `Nat.and_le_right` + `omega` case-splitting on
`Nat.land a.1 1 ∈ {0, 1}`. -/
theorem C12Layer4FrozenSite_stepMerkle_preserved
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature)
    (s : RuntimeState) (a : Nat × Nat) (idx : Nat)
    (hRaw :
      SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
        "merkleNode" "mIdx" s a)
    (hSite : C12Layer4FrozenSite pkSeed pkRoot message sig sigParsed s)
    (hIdxLt : a.1 < 2 ^ 256)
    (hIdxLtFour : idx < 4) :
    C12Layer4FrozenSite pkSeed pkRoot message sig sigParsed
      (SphincsMinusVerifiers.ClimbKit.stepMerkle
        "merkleNode" "mIdx" "xmssBase" "authPtr"
        { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }) := by
  obtain ⟨hSel, hCD, hAuthPtr, hXmssBase, hSeed⟩ := hSite
  let stH : RuntimeState :=
    { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
  let vsib : Nat :=
    SphincsMinusVerifierSpec.C13Concrete.maskN
      (c12Layer4ParsedAuthCdAt pkSeed pkRoot message sig idx)
  have h1 := c12Layer4StepLoad_h1_of_state_shape
    pkSeed pkRoot message sig s idx hSel hCD hAuthPtr hIdxLtFour
  obtain ⟨vadr, h3, _hAdr⟩ :=
    c12Layer4StepAdr_h3_and_frame_of_xmssBase
      pkSeed pkRoot message sigParsed s a idx vsib
      hXmssBase
      (c12Layer4ParsedBase_lt pkSeed pkRoot message sigParsed)
      hIdxLtFour hIdxLt
  have hLocal := c12Layer4StepLocalEvalObligations_of_raw_load_adr
    s a idx vsib vadr hRaw hIdxLt h1 h3
  obtain ⟨e1, e2, e3, e4, e5off, e5val, e6off, e6val⟩ := hLocal
  let vpar : Nat := a.1 >>> 1
  let sval : Nat := (Nat.land a.1 1) <<< 5
  let o5 : Nat := Nat.xor 0x40 sval
  let o6 : Nat := Nat.xor 0x60 sval
  have hSC :=
    SphincsMinusVerifiers.ClimbMemFrameMerkle.stepMerkle_selector_calldata
      "merkleNode" "mIdx" "xmssBase" "authPtr" stH
      vsib vpar vadr sval o5 a.2 o6 vsib
      e1 e2 e3 e4 e5off e5val e6off e6val
  have hAuthPtrPres :
      lookupValue
        (SphincsMinusVerifiers.ClimbKit.stepMerkle
          "merkleNode" "mIdx" "xmssBase" "authPtr" stH).bindings "authPtr" =
      lookupValue stH.bindings "authPtr" :=
    SphincsMinusVerifiers.ClimbMemFrameMerkle.stepMerkle_binding_frozen
      "merkleNode" "mIdx" "xmssBase" "authPtr" "authPtr" stH
      vsib vpar vadr sval o5 a.2 o6 vsib
      (by decide) (by decide) (by decide) (by decide) (by decide)
      e1 e2 e3 e4 e5off e5val e6off e6val
  have hXmssBasePres :
      lookupValue
        (SphincsMinusVerifiers.ClimbKit.stepMerkle
          "merkleNode" "mIdx" "xmssBase" "authPtr" stH).bindings "xmssBase" =
      lookupValue stH.bindings "xmssBase" :=
    SphincsMinusVerifiers.ClimbMemFrameMerkle.stepMerkle_binding_frozen
      "merkleNode" "mIdx" "xmssBase" "authPtr" "xmssBase" stH
      vsib vpar vadr sval o5 a.2 o6 vsib
      (by decide) (by decide) (by decide) (by decide) (by decide)
      e1 e2 e3 e4 e5off e5val e6off e6val
  have hand_le : Nat.land a.1 1 ≤ 1 := Nat.and_le_right
  have hand_eq : Nat.land a.1 1 = 0 ∨ Nat.land a.1 1 = 1 := by omega
  have ho5_ne : (0x00 : Nat) ≠ o5 := by
    show (0x00 : Nat) ≠ Nat.xor 0x40 ((Nat.land a.1 1) <<< 5)
    rcases hand_eq with hp | hp
    · rw [hp]; decide
    · rw [hp]; decide
  have ho6_ne : (0x00 : Nat) ≠ o6 := by
    show (0x00 : Nat) ≠ Nat.xor 0x60 ((Nat.land a.1 1) <<< 5)
    rcases hand_eq with hp | hp
    · rw [hp]; decide
    · rw [hp]; decide
  have hMem0Pres :
      (SphincsMinusVerifiers.ClimbKit.stepMerkle
        "merkleNode" "mIdx" "xmssBase" "authPtr" stH).world.memory 0x00 =
      stH.world.memory 0x00 :=
    SphincsMinusVerifiers.ClimbMemFrameMerkle.stepMerkle_mem_zero
      "merkleNode" "mIdx" "xmssBase" "authPtr" stH
      vsib vpar vadr sval o5 a.2 o6 vsib
      ho5_ne ho6_ne
      e1 e2 e3 e4 e5off e5val e6off e6val
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hSC.1]; exact hSel
  · rw [hSC.2]; exact hCD
  · rw [hAuthPtrPres]
    show lookupValue (bindValue s.bindings "h" (wordNormalize idx)) "authPtr" = _
    rw [MemoryKit.lookupValue_bindValue_ne _ "h" "authPtr" _ (by decide)]
    exact hAuthPtr
  · rw [hXmssBasePres]
    show lookupValue (bindValue s.bindings "h" (wordNormalize idx)) "xmssBase" = _
    rw [MemoryKit.lookupValue_bindValue_ne _ "h" "xmssBase" _ (by decide)]
    exact hXmssBase
  · rw [hMem0Pres]
    exact hSeed

/-- **Layer-4 fold loop lift** — the entire `"h"`-fold over `stepMerkle`
advances the combined invariant `MerkleClimbRawRel ∧ C12Layer4FrozenSite ∧
a.1 < 2 ^ 256` from a single entry-state proof, together with the per-step
advance phrased *under the site* (and the four other per-step facts).  The
proof instantiates `ClimbLoop.foldLoop_invariant_cond` with the bundled
invariant and a per-iteration data predicate `MerkleClimbData ∧ idx < 4`;
the site half advances by `C12Layer4FrozenSite_stepMerkle_preserved`, the
EVM bound half by monotonicity of `Nat.div_le_self` against the merkle-spec
step's `mIdx / 2` half.  Closing this loop-level theorem removes the bare
universal per-step requirement of `xmssClimbRaw_model_node`: the consumer
only supplies the step *restricted to states satisfying
`C12Layer4FrozenSite`*. -/
theorem c12Layer4_foldLoopRaw_advances_of_entry_site_and_step
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature)
    (state : RuntimeState) (a : Nat × Nat)
    (hSiteEntry : C12Layer4FrozenSite pkSeed pkRoot message sig sigParsed state)
    (hRawEntry :
      SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
        "merkleNode" "mIdx" state a)
    (hBoundEntry : a.1 < 2 ^ 256)
    (hData :
      ∀ i, i < (4 : Nat) →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
          (c12Layer4ParsedAuth sigParsed)
          (c12Layer4ParsedAuthCdAt pkSeed pkRoot message sig) i)
    (hStep :
      ∀ (s : RuntimeState) (b : Nat × Nat) (idx : Nat),
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
          (c12Layer4ParsedAuth sigParsed)
          (c12Layer4ParsedAuthCdAt pkSeed pkRoot message sig) idx →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
          "merkleNode" "mIdx" s b →
        C12Layer4FrozenSite pkSeed pkRoot message sig sigParsed s →
        b.1 < 2 ^ 256 →
        idx < 4 →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
          "merkleNode" "mIdx"
          (SphincsMinusVerifiers.ClimbKit.stepMerkle
            "merkleNode" "mIdx" "xmssBase" "authPtr"
            { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
          (SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleSpecStep
            (c12Layer4ParsedSeed pkSeed)
            (c12Layer4ParsedBase pkSeed pkRoot message sigParsed)
            (c12Layer4ParsedAuth sigParsed) idx b)) :
    SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
      "merkleNode" "mIdx"
      (SphincsMinusVerifiers.ClimbLoop.foldLoop "h"
        (SphincsMinusVerifiers.ClimbKit.stepMerkle
          "merkleNode" "mIdx" "xmssBase" "authPtr")
        state 0 (wordNormalize 4))
      (SphincsMinusVerifiers.ClimbLoop.specFold
        (SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleSpecStep
          (c12Layer4ParsedSeed pkSeed)
          (c12Layer4ParsedBase pkSeed pkRoot message sigParsed)
          (c12Layer4ParsedAuth sigParsed))
        a 0 (wordNormalize 4)) := by
  let R : RuntimeState → Nat × Nat → Prop := fun s b =>
    SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
      "merkleNode" "mIdx" s b
    ∧ C12Layer4FrozenSite pkSeed pkRoot message sig sigParsed s
    ∧ b.1 < 2 ^ 256
  let D : Nat → Prop := fun i =>
    SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
      (c12Layer4ParsedAuth sigParsed)
      (c12Layer4ParsedAuthCdAt pkSeed pkRoot message sig) i
    ∧ i < 4
  have hstep : ∀ (s : RuntimeState) (b : Nat × Nat) (idx : Nat),
      D idx → R s b →
      R (SphincsMinusVerifiers.ClimbKit.stepMerkle
          "merkleNode" "mIdx" "xmssBase" "authPtr"
          { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
        (SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleSpecStep
          (c12Layer4ParsedSeed pkSeed)
          (c12Layer4ParsedBase pkSeed pkRoot message sigParsed)
          (c12Layer4ParsedAuth sigParsed) idx b) := by
    intro s b idx hDidx hRsb
    obtain ⟨hRaw, hSite, hBound⟩ := hRsb
    obtain ⟨hDataIdx, hIdxLt4⟩ := hDidx
    refine ⟨?_, ?_, ?_⟩
    · exact hStep s b idx hDataIdx hRaw hSite hBound hIdxLt4
    · exact C12Layer4FrozenSite_stepMerkle_preserved
        pkSeed pkRoot message sig sigParsed s b idx hRaw hSite hBound hIdxLt4
    · -- (merkleSpecStep ... idx b).1 = b.1 / 2 ≤ b.1 < 2^256.
      show (SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleSpecStep _ _ _ idx b).1 < 2 ^ 256
      unfold SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleSpecStep
      -- merkleSpecStep is defined by pattern-matching on b = (mIdx, node);
      -- result is (mIdx / 2, _).  So .1 = mIdx / 2 = b.1 / 2.
      exact lt_of_le_of_lt (Nat.div_le_self b.1 2) hBound
  have hD : ∀ i, 0 ≤ i → i < 0 + wordNormalize 4 → D i := by
    intro i _ hi
    have hi4 : i < 4 := by simpa using hi
    exact ⟨hData i hi4, hi4⟩
  have hR : R state a := ⟨hRawEntry, hSiteEntry, hBoundEntry⟩
  have hfold :=
    SphincsMinusVerifiers.ClimbLoop.foldLoop_invariant_cond "h"
      (SphincsMinusVerifiers.ClimbKit.stepMerkle "merkleNode" "mIdx" "xmssBase" "authPtr")
      (SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleSpecStep
        (c12Layer4ParsedSeed pkSeed)
        (c12Layer4ParsedBase pkSeed pkRoot message sigParsed)
        (c12Layer4ParsedAuth sigParsed))
      R D hstep state a 0 (wordNormalize 4) hD hR
  exact hfold.1

/-- **Layer-4 fold loop ⇒ xmssClimb correspondence under the frozen site.**
The `"h"`-fold's `"merkleNode"` binding equals the spec's `xmssClimb`, derived
from the bundled-site step and the entry frame (instead of the bare universal
step required by `xmssClimbRaw_model_node`).  Composes
`c12Layer4_foldLoopRaw_advances_of_entry_site_and_step` (gives
`MerkleClimbRawRel` at the loop output) with `MerkleClimbRawRel.node` (the
exact-node projection) and `xmssClimb_eq_specFold` (the spec-side
`specFold ↔ xmssClimb` rewrite).  This is the direct loop-level
xmssClimb-correspondence consumers want when threading the site invariant. -/
theorem c12Layer4_foldLoop_merkleNode_eq_xmssClimb_of_entry_site_and_step
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature)
    (state : RuntimeState) (initial_mIdx initial_node : Nat)
    (hSiteEntry : C12Layer4FrozenSite pkSeed pkRoot message sig sigParsed state)
    (hRawEntry :
      SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
        "merkleNode" "mIdx" state (initial_mIdx, initial_node))
    (hBoundEntry : initial_mIdx < 2 ^ 256)
    (hData :
      ∀ i, i < (4 : Nat) →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
          (c12Layer4ParsedAuth sigParsed)
          (c12Layer4ParsedAuthCdAt pkSeed pkRoot message sig) i)
    (hStep :
      ∀ (s : RuntimeState) (b : Nat × Nat) (idx : Nat),
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
          (c12Layer4ParsedAuth sigParsed)
          (c12Layer4ParsedAuthCdAt pkSeed pkRoot message sig) idx →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
          "merkleNode" "mIdx" s b →
        C12Layer4FrozenSite pkSeed pkRoot message sig sigParsed s →
        b.1 < 2 ^ 256 →
        idx < 4 →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
          "merkleNode" "mIdx"
          (SphincsMinusVerifiers.ClimbKit.stepMerkle
            "merkleNode" "mIdx" "xmssBase" "authPtr"
            { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
          (SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleSpecStep
            (c12Layer4ParsedSeed pkSeed)
            (c12Layer4ParsedBase pkSeed pkRoot message sigParsed)
            (c12Layer4ParsedAuth sigParsed) idx b)) :
    lookupValue
        (SphincsMinusVerifiers.ClimbLoop.foldLoop "h"
          (SphincsMinusVerifiers.ClimbKit.stepMerkle
            "merkleNode" "mIdx" "xmssBase" "authPtr")
          state 0 (wordNormalize 4)).bindings
        "merkleNode" =
      SphincsMinusVerifierSpec.C13Concrete.xmssClimb
        (c12Layer4ParsedSeed pkSeed)
        (c12Layer4ParsedBase pkSeed pkRoot message sigParsed)
        (wordNormalize 4) 0 initial_mIdx initial_node
        (c12Layer4ParsedAuth sigParsed) := by
  have hrel := c12Layer4_foldLoopRaw_advances_of_entry_site_and_step
    pkSeed pkRoot message sig sigParsed state (initial_mIdx, initial_node)
    hSiteEntry hRawEntry hBoundEntry hData hStep
  rw [SphincsMinusVerifiers.ClimbMemFrameMerkle.xmssClimb_eq_specFold]
  exact hrel.node

/-- Layer-4 step advance with the `c12Layer4ParsedBase < 2 ^ 256` bound
discharged internally from `c12Layer4ParsedBase_lt`.  Compared with
`c12_layer4_stepRawAdvance_of_seed_load_xmssBase_obligations`, the residual no
longer carries the parsed-base bound; the caller supplies only the
`"xmssBase"` binding, the per-step `idx < 4` height bound, the EVM bound on
`a.1`, the seed cell, the masked-load identification, and the masked-load
`evalExpr`. -/
theorem c12_layer4_stepRawAdvance_of_seed_load_xmssBase_no_base_bound
    (hLayer4StepSeedLoadXmssBaseObligations :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
          ∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat),
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
              (c12Layer4ParsedAuth sigParsed)
              (c12Layer4ParsedAuthCdAt pkSeed pkRoot message sig) idx →
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
              "merkleNode" "mIdx" s a →
            ∃ vsib,
              a.1 < 2 ^ 256
              ∧ ({ s with bindings := bindValue s.bindings "h" (wordNormalize idx) }.world.memory
                    0x00).val =
                  c12Layer4ParsedSeed pkSeed
              ∧ vsib =
                  SphincsMinusVerifierSpec.C13Concrete.maskN
                    (c12Layer4ParsedAuthCdAt pkSeed pkRoot message sig idx)
              ∧ evalExpr []
                  { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
                  (.bitAnd (.calldataload (.add (.localVar "authPtr")
                    (.shl (.literal 4) (.localVar "h")))) (.literal N_MASK)) =
                  some vsib
              ∧ lookupValue s.bindings "xmssBase" =
                  c12Layer4ParsedBase pkSeed pkRoot message sigParsed
              ∧ idx < 4) :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
          ∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat),
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
              (c12Layer4ParsedAuth sigParsed)
              (c12Layer4ParsedAuthCdAt pkSeed pkRoot message sig) idx →
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
              "merkleNode" "mIdx" s a →
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
              "merkleNode" "mIdx"
                (SphincsMinusVerifiers.ClimbKit.stepMerkle
                  "merkleNode" "mIdx" "xmssBase" "authPtr"
                  { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
                (SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleSpecStep
                  (c12Layer4ParsedSeed pkSeed)
                  (c12Layer4ParsedBase pkSeed pkRoot message sigParsed)
                  (c12Layer4ParsedAuth sigParsed) idx a) := by
  refine c12_layer4_stepRawAdvance_of_seed_load_xmssBase_obligations ?_
  intro pkSeed pkRoot message sig sigParsed hParse s a idx hData hRaw
  rcases hLayer4StepSeedLoadXmssBaseObligations pkSeed pkRoot message sig sigParsed hParse
      s a idx hData hRaw with
    ⟨vsib, hIdxLt, hSeed, hLoad, h1, hXmssBase, hIdxLtFour⟩
  exact ⟨vsib, hIdxLt, hSeed, hLoad, h1, hXmssBase,
    c12Layer4ParsedBase_lt pkSeed pkRoot message sigParsed, hIdxLtFour⟩

/-- The layer-4 generic XMSS executable residual reduces to the raw model theorem
with the concrete layer-4 auth calldata reader.  The remaining facts are exactly
the per-step raw-relation advance, sibling-data correspondence for the four C12
climb heights, and the initial raw relation at the generic fold entry. -/
theorem c12_layer4_generic_xmss_of_raw_merkle_fold_obligations
    (hLayer4RawFoldObligations :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
          (∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat),
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
              (c12Layer4ParsedAuth sigParsed)
              (c12Layer4ParsedAuthCdAt pkSeed pkRoot message sig) idx →
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
              "merkleNode" "mIdx" s a →
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
              "merkleNode" "mIdx"
                (SphincsMinusVerifiers.ClimbKit.stepMerkle
                  "merkleNode" "mIdx" "xmssBase" "authPtr"
                  { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
                (SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleSpecStep
                  (c12Layer4ParsedSeed pkSeed)
                  (c12Layer4ParsedBase pkSeed pkRoot message sigParsed)
                  (c12Layer4ParsedAuth sigParsed) idx a))
          ∧ (∀ i, i < wordNormalize 4 →
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
              (c12Layer4ParsedAuth sigParsed)
              (c12Layer4ParsedAuthCdAt pkSeed pkRoot message sig) i)
          ∧ SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
              "merkleNode" "mIdx"
              { (c12Layer4XmssEntryState pkSeed pkRoot message sig) with
                bindings :=
                  bindValue
                    (c12Layer4XmssEntryState pkSeed pkRoot message sig).bindings
                    "h" (wordNormalize 0) }
              (c12Layer4Leaf
                (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex,
                c12Layer4ParsedStartNode pkSeed pkRoot message sigParsed)) :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (SphincsMinusVerifiers.ClimbLoop.foldLoop "h"
            (SphincsMinusVerifiers.ClimbKit.stepMerkle
              "merkleNode" "mIdx" "xmssBase" "authPtr")
            { (C12SegmentWotsSetup.c12LayerStateBeforeXmssLoop
                (c12LayerBodyInput4
                  (C12SegmentForsCompress.c12StepForsCompress
                    (C12SegmentFors.c12StepFors
                      (C12SegmentSeed.c12StepSeed
                        (MkC13State.mkC13State pkSeed pkRoot message sig)))))) with
              bindings :=
                bindValue
                  (C12SegmentWotsSetup.c12LayerStateBeforeXmssLoop
                    (c12LayerBodyInput4
                      (C12SegmentForsCompress.c12StepForsCompress
                        (C12SegmentFors.c12StepFors
                          (C12SegmentSeed.c12StepSeed
                            (MkC13State.mkC13State pkSeed pkRoot message sig)))))).bindings
                  "h" (wordNormalize 0) }
            0 (wordNormalize 4)).bindings
          "merkleNode" =
        SphincsMinusVerifierSpec.C13Concrete.xmssClimb
          (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed)
          (C12Concrete.xmssBaseC12 4
            (c12Layer4NextTree
              (C12Concrete.hMsgC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex))
          4 0
          (c12Layer4Leaf
            (C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex)
          (C12Concrete.wotsPkWordC12
            (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed)
            4
            (c12Layer4NextTree
              (C12Concrete.hMsgC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex)
            (c12Layer4Leaf
              (C12Concrete.hMsgC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex)
            (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
              (c12UnrolledLayerRoot3 pkSeed
                (C12Concrete.hMsgC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex
                ((C12Concrete.forsPkFromSigC12 c12
                    { pkSeed := pkSeed, pkRoot := pkRoot }
                    (C12Concrete.hMsgC12 c12
                      { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
                    sigParsed.fors).getD ⟨#[]⟩)
                sigParsed.layers))
            ((sigParsed.layers[4]?).getD c12EmptyXmssLayerSig).wots)
          ((sigParsed.layers[4]?).getD c12EmptyXmssLayerSig).authPath := by
  intro pkSeed pkRoot message sig sigParsed hParse
  rcases hLayer4RawFoldObligations pkSeed pkRoot message sig sigParsed hParse with
    ⟨hstep, hDdata, hR⟩
  let cdAt := c12Layer4ParsedAuthCdAt pkSeed pkRoot message sig
  have hD :
      ∀ i, 0 ≤ i → i < 0 + wordNormalize 4 →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
          (c12Layer4ParsedAuth sigParsed) cdAt i := by
    intro i _ hi
    exact hDdata i (by simpa using hi)
  simpa [c12Layer4XmssEntryState, c12Layer4ParsedSeed, c12Layer4ParsedBase,
    c12Layer4ParsedAuth, c12Layer4ParsedAuthCdAt, c12Layer4ParsedStartNode,
    c12Layer4ParsedMessage, cdAt]
    using
      SphincsMinusVerifiers.ClimbMemFrameMerkle.xmssClimbRaw_model_node
        "merkleNode" "mIdx" "xmssBase" "authPtr"
        (c12Layer4ParsedSeed pkSeed)
        (c12Layer4ParsedBase pkSeed pkRoot message sigParsed)
        (c12Layer4ParsedAuth sigParsed) cdAt hstep
        { (c12Layer4XmssEntryState pkSeed pkRoot message sig) with
          bindings :=
            bindValue (c12Layer4XmssEntryState pkSeed pkRoot message sig).bindings
              "h" (wordNormalize 0) }
        (c12Layer4Leaf
          (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
        (c12Layer4ParsedStartNode pkSeed pkRoot message sigParsed)
        0 (wordNormalize 4) hD hR

/-- Parser-backed layer-4 XMSS wrapper with the calldata range and initial raw
relation discharged.  Compared with
`c12_layer4_generic_xmss_of_raw_merkle_fold_obligations`, the remaining facts are
only the raw step advance plus the two entry bindings: input `"curLeaf"` and
pre-XMSS-node `"wotsPk"`. -/
theorem c12_layer4_generic_xmss_of_step_and_input_bindings
    (hLayer4StepRawAdvance :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
          ∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat),
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
              (c12Layer4ParsedAuth sigParsed)
              (c12Layer4ParsedAuthCdAt pkSeed pkRoot message sig) idx →
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
              "merkleNode" "mIdx" s a →
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
              "merkleNode" "mIdx"
                (SphincsMinusVerifiers.ClimbKit.stepMerkle
                  "merkleNode" "mIdx" "xmssBase" "authPtr"
                  { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
                (SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleSpecStep
                  (c12Layer4ParsedSeed pkSeed)
                  (c12Layer4ParsedBase pkSeed pkRoot message sigParsed)
                  (c12Layer4ParsedAuth sigParsed) idx a))
    (hLayer4CurLeafInput :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (c12LayerBodyInput4
            (C12SegmentForsCompress.c12StepForsCompress
              (C12SegmentFors.c12StepFors
                (C12SegmentSeed.c12StepSeed
                  (MkC13State.mkC13State pkSeed pkRoot message sig))))).bindings
          "curLeaf" =
        c12Layer4Leaf
          (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
    (hLayer4WotsPkBeforeNode :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (C12SegmentWotsSetup.c12LayerStateBeforeXmssNode
            (c12LayerBodyInput4
              (C12SegmentForsCompress.c12StepForsCompress
                (C12SegmentFors.c12StepFors
                  (C12SegmentSeed.c12StepSeed
                    (MkC13State.mkC13State pkSeed pkRoot message sig)))))).bindings
          "wotsPk" =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          (c12Layer4WotsPkBytes pkSeed
            (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex
            (c12UnrolledLayerRoot3 pkSeed
              (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex
              ((C12Concrete.forsPkFromSigC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot }
                  (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed)
                  sigParsed.fors).getD ⟨#[]⟩)
              sigParsed.layers)
            ((sigParsed.layers[4]?).getD c12EmptyXmssLayerSig))) :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (SphincsMinusVerifiers.ClimbLoop.foldLoop "h"
            (SphincsMinusVerifiers.ClimbKit.stepMerkle
              "merkleNode" "mIdx" "xmssBase" "authPtr")
            { (C12SegmentWotsSetup.c12LayerStateBeforeXmssLoop
                (c12LayerBodyInput4
                  (C12SegmentForsCompress.c12StepForsCompress
                    (C12SegmentFors.c12StepFors
                      (C12SegmentSeed.c12StepSeed
                        (MkC13State.mkC13State pkSeed pkRoot message sig)))))) with
              bindings :=
                bindValue
                  (C12SegmentWotsSetup.c12LayerStateBeforeXmssLoop
                    (c12LayerBodyInput4
                      (C12SegmentForsCompress.c12StepForsCompress
                        (C12SegmentFors.c12StepFors
                          (C12SegmentSeed.c12StepSeed
                            (MkC13State.mkC13State pkSeed pkRoot message sig)))))).bindings
                  "h" (wordNormalize 0) }
            0 (wordNormalize 4)).bindings
          "merkleNode" =
        SphincsMinusVerifierSpec.C13Concrete.xmssClimb
          (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed)
          (C12Concrete.xmssBaseC12 4
            (c12Layer4NextTree
              (C12Concrete.hMsgC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex))
          4 0
          (c12Layer4Leaf
            (C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex)
          (C12Concrete.wotsPkWordC12
            (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed)
            4
            (c12Layer4NextTree
              (C12Concrete.hMsgC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex)
            (c12Layer4Leaf
              (C12Concrete.hMsgC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex)
            (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
              (c12UnrolledLayerRoot3 pkSeed
                (C12Concrete.hMsgC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex
                ((C12Concrete.forsPkFromSigC12 c12
                    { pkSeed := pkSeed, pkRoot := pkRoot }
                    (C12Concrete.hMsgC12 c12
                      { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
                    sigParsed.fors).getD ⟨#[]⟩)
                sigParsed.layers))
            ((sigParsed.layers[4]?).getD c12EmptyXmssLayerSig).wots)
          ((sigParsed.layers[4]?).getD c12EmptyXmssLayerSig).authPath := by
  refine c12_layer4_generic_xmss_of_raw_merkle_fold_obligations ?_
  intro pkSeed pkRoot message sig sigParsed hParse
  exact ⟨
    hLayer4StepRawAdvance pkSeed pkRoot message sig sigParsed hParse,
    c12_layer4_hDdata_of_parse pkSeed pkRoot message sig sigParsed hParse,
    c12_layer4_initial_raw_rel_of_input_curLeaf_and_wotsPk
      hLayer4CurLeafInput hLayer4WotsPkBeforeNode
      pkSeed pkRoot message sig sigParsed hParse⟩

/-- Entry variant reducing the layer-4 `"curLeaf"` residual to the concrete
handoff binding in `c12LayerStateAfter3`.  The only executable work here is the
`"layer"` injection for the next body, which leaves `"curLeaf"` untouched. -/
theorem c12_layer4_generic_xmss_of_step_after3_curLeaf_and_wotsPk
    (hLayer4StepRawAdvance :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
          ∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat),
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
              (c12Layer4ParsedAuth sigParsed)
              (c12Layer4ParsedAuthCdAt pkSeed pkRoot message sig) idx →
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
              "merkleNode" "mIdx" s a →
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
              "merkleNode" "mIdx"
                (SphincsMinusVerifiers.ClimbKit.stepMerkle
                  "merkleNode" "mIdx" "xmssBase" "authPtr"
                  { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
                (SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleSpecStep
                  (c12Layer4ParsedSeed pkSeed)
                  (c12Layer4ParsedBase pkSeed pkRoot message sigParsed)
                  (c12Layer4ParsedAuth sigParsed) idx a))
    (hLayer4CurLeafAfter3 :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (c12LayerStateAfter3
            (C12SegmentForsCompress.c12StepForsCompress
              (C12SegmentFors.c12StepFors
                (C12SegmentSeed.c12StepSeed
                  (MkC13State.mkC13State pkSeed pkRoot message sig))))).bindings
          "curLeaf" =
        c12Layer4Leaf
          (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
    (hLayer4WotsPkBeforeNode :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (C12SegmentWotsSetup.c12LayerStateBeforeXmssNode
            (c12LayerBodyInput4
              (C12SegmentForsCompress.c12StepForsCompress
                (C12SegmentFors.c12StepFors
                  (C12SegmentSeed.c12StepSeed
                    (MkC13State.mkC13State pkSeed pkRoot message sig)))))).bindings
          "wotsPk" =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          (c12Layer4WotsPkBytes pkSeed
            (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex
            (c12UnrolledLayerRoot3 pkSeed
              (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex
              ((C12Concrete.forsPkFromSigC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot }
                  (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed)
                  sigParsed.fors).getD ⟨#[]⟩)
              sigParsed.layers)
            ((sigParsed.layers[4]?).getD c12EmptyXmssLayerSig))) :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (SphincsMinusVerifiers.ClimbLoop.foldLoop "h"
            (SphincsMinusVerifiers.ClimbKit.stepMerkle
              "merkleNode" "mIdx" "xmssBase" "authPtr")
            { (C12SegmentWotsSetup.c12LayerStateBeforeXmssLoop
                (c12LayerBodyInput4
                  (C12SegmentForsCompress.c12StepForsCompress
                    (C12SegmentFors.c12StepFors
                      (C12SegmentSeed.c12StepSeed
                        (MkC13State.mkC13State pkSeed pkRoot message sig)))))) with
              bindings :=
                bindValue
                  (C12SegmentWotsSetup.c12LayerStateBeforeXmssLoop
                    (c12LayerBodyInput4
                      (C12SegmentForsCompress.c12StepForsCompress
                        (C12SegmentFors.c12StepFors
                          (C12SegmentSeed.c12StepSeed
                            (MkC13State.mkC13State pkSeed pkRoot message sig)))))).bindings
                  "h" (wordNormalize 0) }
            0 (wordNormalize 4)).bindings
          "merkleNode" =
        SphincsMinusVerifierSpec.C13Concrete.xmssClimb
          (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed)
          (C12Concrete.xmssBaseC12 4
            (c12Layer4NextTree
              (C12Concrete.hMsgC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex))
          4 0
          (c12Layer4Leaf
            (C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex)
          (C12Concrete.wotsPkWordC12
            (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed)
            4
            (c12Layer4NextTree
              (C12Concrete.hMsgC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex)
            (c12Layer4Leaf
              (C12Concrete.hMsgC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex)
            (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
              (c12UnrolledLayerRoot3 pkSeed
                (C12Concrete.hMsgC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex
                ((C12Concrete.forsPkFromSigC12 c12
                    { pkSeed := pkSeed, pkRoot := pkRoot }
                    (C12Concrete.hMsgC12 c12
                      { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
                    sigParsed.fors).getD ⟨#[]⟩)
                sigParsed.layers))
            ((sigParsed.layers[4]?).getD c12EmptyXmssLayerSig).wots)
          ((sigParsed.layers[4]?).getD c12EmptyXmssLayerSig).authPath := by
  refine c12_layer4_generic_xmss_of_step_and_input_bindings
    hLayer4StepRawAdvance ?_ hLayer4WotsPkBeforeNode
  intro pkSeed pkRoot message sig sigParsed hParse
  rw [c12LayerBodyInput4_curLeaf_eq]
  exact hLayer4CurLeafAfter3 pkSeed pkRoot message sig sigParsed hParse

/-- `c12Layer4Leaf x = c12Layer4IdxTree x % 16` is bounded by `16`. -/
theorem c12Layer4Leaf_lt_16 (idxTree : Nat) :
    c12Layer4Leaf idxTree < 16 := by
  unfold c12Layer4Leaf
  exact Nat.mod_lt _ (by decide)

/-- The parsed layer-4 leaf index is naturally bounded below `2 ^ 256`: it is
the spec's `% 16` digit, hence `< 16 ≤ 2 ^ 256`. -/
theorem c12Layer4Leaf_lt_two_pow_256 (idxTree : Nat) :
    c12Layer4Leaf idxTree < 2 ^ 256 :=
  lt_of_lt_of_le (c12Layer4Leaf_lt_16 idxTree) (by decide)

/-- A parsed C12 WOTS-base address word for layer 4 is EVM-word bounded. -/
theorem c12_wotsBaseC12_layer4_lt_two_pow_256
    (treeIdx leafIdx : Nat)
    (hTree : treeIdx < 2 ^ 64) (hLeaf : leafIdx < 2 ^ 64) :
    C12Concrete.wotsBaseC12 4 treeIdx leafIdx < 2 ^ 256 := by
  unfold C12Concrete.wotsBaseC12
  have hLayerShift : (4 : Nat) <<< 224 < 2 ^ 256 := by
    rw [Nat.shiftLeft_eq]
    norm_num [pow_add]
  have hTreeShift : treeIdx <<< 160 < 2 ^ 256 := by
    rw [Nat.shiftLeft_eq]
    calc
      treeIdx * 2 ^ 160 < 2 ^ 64 * 2 ^ 160 := by
        exact Nat.mul_lt_mul_of_pos_right hTree (by positivity)
      _ = 2 ^ 224 := by rw [← pow_add]
      _ < 2 ^ 256 := by norm_num
  have hLeafShift : leafIdx <<< 96 < 2 ^ 256 := by
    rw [Nat.shiftLeft_eq]
    calc
      leafIdx * 2 ^ 96 < 2 ^ 64 * 2 ^ 96 := by
        exact Nat.mul_lt_mul_of_pos_right hLeaf (by positivity)
      _ = 2 ^ 160 := by rw [← pow_add]
      _ < 2 ^ 256 := by norm_num
  exact Nat.bitwise_lt_two_pow
    (Nat.bitwise_lt_two_pow hLayerShift hTreeShift)
    hLeafShift

/-- At the layer-4 WOTS setup entry, evaluating the WOTS-base ADRS expression
matches the parsed C12 layer-4 WOTS base. -/
theorem c12Layer4PreBodyState_wotsBase_eval
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature)
    (hParse : C12Concrete.parseSignatureC12 c12 sig = some sigParsed) :
    evalExpr [] (c12Layer4PreBodyState pkSeed pkRoot message sig)
        (.bitOr
          (.bitOr
            (.shl (.literal 224) (.localVar "layer"))
            (.shl (.literal 160) (.localVar "curTree")))
          (.shl (.literal 96) (.localVar "curLeaf"))) =
      some
        (C12Concrete.wotsBaseC12 4
          (c12Layer4NextTree
            (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
          (c12Layer4Leaf
            (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)) := by
  let idx := (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex
  let leaf := c12Layer4Leaf idx
  have h224Lit : evalExpr [] (c12Layer4PreBodyState pkSeed pkRoot message sig)
      (.literal 224) = some 224 := by
    show some (wordNormalize 224) = some 224
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide)]
  have h160Lit : evalExpr [] (c12Layer4PreBodyState pkSeed pkRoot message sig)
      (.literal 160) = some 160 := by
    show some (wordNormalize 160) = some 160
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide)]
  have h96Lit : evalExpr [] (c12Layer4PreBodyState pkSeed pkRoot message sig)
      (.literal 96) = some 96 := by
    show some (wordNormalize 96) = some 96
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide)]
  have hLayerEval : evalExpr [] (c12Layer4PreBodyState pkSeed pkRoot message sig)
      (.localVar "layer") = some 4 := by
    show some (lookupValue
      (c12Layer4PreBodyState pkSeed pkRoot message sig).bindings "layer") = some 4
    unfold c12Layer4PreBodyState
    rw [c12LayerBodyInput4_layer_eq]
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide)]
  have hCurTreeEval : evalExpr [] (c12Layer4PreBodyState pkSeed pkRoot message sig)
      (.localVar "curTree") = some 0 := by
    show some (lookupValue
      (c12Layer4PreBodyState pkSeed pkRoot message sig).bindings "curTree") = some 0
    unfold c12Layer4PreBodyState
    rw [c12LayerBodyInput4_curTree_eq]
    exact congrArg some
      (c12Layer4CurTreeAfter3 pkSeed pkRoot message sig sigParsed hParse)
  have hCurLeafEval : evalExpr [] (c12Layer4PreBodyState pkSeed pkRoot message sig)
      (.localVar "curLeaf") = some leaf := by
    show some (lookupValue
      (c12Layer4PreBodyState pkSeed pkRoot message sig).bindings "curLeaf") = some leaf
    unfold c12Layer4PreBodyState
    rw [c12LayerBodyInput4_curLeaf_eq]
    exact congrArg some
      (c12Layer4CurLeafAfter3 pkSeed pkRoot message sig sigParsed hParse)
  have h4ShiftLt : 4 <<< 224 < 2 ^ 256 := by decide
  have h0ShiftLt : 0 <<< 160 < 2 ^ 256 := by decide
  have hLeafShiftLt : leaf <<< 96 < 2 ^ 256 := by
    have hLeafLt16 : leaf < 16 := c12Layer4Leaf_lt_16 idx
    rw [Nat.shiftLeft_eq]
    calc
      leaf * 2 ^ 96 < 16 * 2 ^ 96 :=
        Nat.mul_lt_mul_of_pos_right hLeafLt16 (by decide)
      _ < 2 ^ 256 := by decide
  have h224 : evalExpr [] (c12Layer4PreBodyState pkSeed pkRoot message sig)
      (.shl (.literal 224) (.localVar "layer")) = some (4 <<< 224) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded
      (c12Layer4PreBodyState pkSeed pkRoot message sig)
      (.literal 224) (.localVar "layer") 224 4 h224Lit hLayerEval
      (by decide) (by decide) h4ShiftLt
  have h160 : evalExpr [] (c12Layer4PreBodyState pkSeed pkRoot message sig)
      (.shl (.literal 160) (.localVar "curTree")) = some (0 <<< 160) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded
      (c12Layer4PreBodyState pkSeed pkRoot message sig)
      (.literal 160) (.localVar "curTree") 160 0 h160Lit hCurTreeEval
      (by decide) (by decide) h0ShiftLt
  have h96 : evalExpr [] (c12Layer4PreBodyState pkSeed pkRoot message sig)
      (.shl (.literal 96) (.localVar "curLeaf")) = some (leaf <<< 96) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded
      (c12Layer4PreBodyState pkSeed pkRoot message sig)
      (.literal 96) (.localVar "curLeaf") 96 leaf h96Lit hCurLeafEval
      (by decide) (c12Layer4Leaf_lt_two_pow_256 idx) hLeafShiftLt
  have hInner : evalExpr [] (c12Layer4PreBodyState pkSeed pkRoot message sig)
      (.bitOr
        (.shl (.literal 224) (.localVar "layer"))
        (.shl (.literal 160) (.localVar "curTree"))) =
        some (Nat.lor (4 <<< 224) (0 <<< 160)) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_bitOr_bounded
      (c12Layer4PreBodyState pkSeed pkRoot message sig)
      (.shl (.literal 224) (.localVar "layer"))
      (.shl (.literal 160) (.localVar "curTree"))
      (4 <<< 224) (0 <<< 160) h224 h160 h4ShiftLt h0ShiftLt
  have hInnerLt : Nat.lor (4 <<< 224) (0 <<< 160) < 2 ^ 256 :=
    by decide
  have hFull : evalExpr [] (c12Layer4PreBodyState pkSeed pkRoot message sig)
      (.bitOr
        (.bitOr
          (.shl (.literal 224) (.localVar "layer"))
          (.shl (.literal 160) (.localVar "curTree")))
        (.shl (.literal 96) (.localVar "curLeaf"))) =
        some (Nat.lor (Nat.lor (4 <<< 224) (0 <<< 160)) (leaf <<< 96)) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_bitOr_bounded
      (c12Layer4PreBodyState pkSeed pkRoot message sig)
      (.bitOr
        (.shl (.literal 224) (.localVar "layer"))
        (.shl (.literal 160) (.localVar "curTree")))
      (.shl (.literal 96) (.localVar "curLeaf"))
      (Nat.lor (4 <<< 224) (0 <<< 160)) (leaf <<< 96)
      hInner h96 hInnerLt hLeafShiftLt
  rw [hFull]
  unfold C12Concrete.wotsBaseC12
  rw [c12Layer4NextTree_of_parsed_eq_zero]
  change some (Nat.lor (Nat.lor (4 <<< 224) (0 <<< 160)) (leaf <<< 96)) =
    some ((4 <<< 224) ||| (0 <<< 160) ||| (leaf <<< 96))
  rfl

private theorem c12_nat_lor_lt_two_pow {x y n : Nat}
    (hx : x < 2 ^ n) (hy : y < 2 ^ n) :
    Nat.lor x y < 2 ^ n := by
  show Nat.bitwise or x y < 2 ^ n
  exact Nat.bitwise_lt_two_pow hx hy

/-- At the layer-4 WOTS setup prefix just before binding `"pkAdrs"`, evaluating
the WOTS-PK ADRS expression matches the parsed C12 layer-4 WOTS-PK address. -/
theorem c12Layer4BeforePkAdrs_wotsPkAdrs_eval
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature)
    (hParse : C12Concrete.parseSignatureC12 c12 sig = some sigParsed) :
    evalExpr []
        (C12SegmentWotsSetup.c12LayerStateBeforePkAdrs
          (c12Layer4PreBodyState pkSeed pkRoot message sig))
        C12SegmentWotsSetup.c12LayerPkAdrsExpr =
      some
        (C12Concrete.wotsPkAdrsC12 4
          (c12Layer4NextTree
            (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
          (c12Layer4Leaf
            (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)) := by
  let idx := (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex
  let leaf := c12Layer4Leaf idx
  let st :=
    C12SegmentWotsSetup.c12LayerStateBeforePkAdrs
      (c12Layer4PreBodyState pkSeed pkRoot message sig)
  have h224Lit : evalExpr [] st (.literal 224) = some 224 := by
    show some (wordNormalize 224) = some 224
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide)]
  have h160Lit : evalExpr [] st (.literal 160) = some 160 := by
    show some (wordNormalize 160) = some 160
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide)]
  have h128Lit : evalExpr [] st (.literal 128) = some 128 := by
    show some (wordNormalize 128) = some 128
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide)]
  have h96Lit : evalExpr [] st (.literal 96) = some 96 := by
    show some (wordNormalize 96) = some 96
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide)]
  have h1Lit : evalExpr [] st (.literal 1) = some 1 := by
    show some (wordNormalize 1) = some 1
    rfl
  have hLayerEval : evalExpr [] st (.localVar "layer") = some 4 := by
    show some (lookupValue st.bindings "layer") = some 4
    dsimp [st]
    rw [C12SegmentWotsSetup.c12LayerStateBeforePkAdrs_layer_eq]
    unfold c12Layer4PreBodyState
    rw [c12LayerBodyInput4_layer_eq]
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide)]
  have hCurTreeEval : evalExpr [] st (.localVar "curTree") = some 0 := by
    show some (lookupValue st.bindings "curTree") = some 0
    dsimp [st]
    rw [C12SegmentWotsSetup.c12LayerStateBeforePkAdrs_curTree_eq]
    unfold c12Layer4PreBodyState
    rw [c12LayerBodyInput4_curTree_eq]
    exact congrArg some
      (c12Layer4CurTreeAfter3 pkSeed pkRoot message sig sigParsed hParse)
  have hCurLeafEval : evalExpr [] st (.localVar "curLeaf") = some leaf := by
    show some (lookupValue st.bindings "curLeaf") = some leaf
    dsimp [st]
    rw [C12SegmentWotsSetup.c12LayerStateBeforePkAdrs_curLeaf_eq]
    unfold c12Layer4PreBodyState
    rw [c12LayerBodyInput4_curLeaf_eq]
    exact congrArg some
      (c12Layer4CurLeafAfter3 pkSeed pkRoot message sig sigParsed hParse)
  have h4ShiftLt : 4 <<< 224 < 2 ^ 256 := by decide
  have h0ShiftLt : 0 <<< 160 < 2 ^ 256 := by decide
  have h1ShiftLt : 1 <<< 128 < 2 ^ 256 := by decide
  have hLeafShiftLt : leaf <<< 96 < 2 ^ 256 := by
    have hLeafLt16 : leaf < 16 := c12Layer4Leaf_lt_16 idx
    rw [Nat.shiftLeft_eq]
    calc
      leaf * 2 ^ 96 < 16 * 2 ^ 96 :=
        Nat.mul_lt_mul_of_pos_right hLeafLt16 (by decide)
      _ < 2 ^ 256 := by decide
  have h224 : evalExpr [] st
      (.shl (.literal 224) (.localVar "layer")) = some (4 <<< 224) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded
      st (.literal 224) (.localVar "layer") 224 4 h224Lit hLayerEval
      (by decide) (by decide) h4ShiftLt
  have h160 : evalExpr [] st
      (.shl (.literal 160) (.localVar "curTree")) = some (0 <<< 160) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded
      st (.literal 160) (.localVar "curTree") 160 0 h160Lit hCurTreeEval
      (by decide) (by decide) h0ShiftLt
  have h128 : evalExpr [] st
      (.shl (.literal 128) (.literal 1)) = some (1 <<< 128) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded
      st (.literal 128) (.literal 1) 128 1 h128Lit h1Lit
      (by decide) (by decide) h1ShiftLt
  have h96 : evalExpr [] st
      (.shl (.literal 96) (.localVar "curLeaf")) = some (leaf <<< 96) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded
      st (.literal 96) (.localVar "curLeaf") 96 leaf h96Lit hCurLeafEval
      (by decide) (c12Layer4Leaf_lt_two_pow_256 idx) hLeafShiftLt
  have hLayerTree : evalExpr [] st
      (.bitOr
        (.shl (.literal 224) (.localVar "layer"))
        (.shl (.literal 160) (.localVar "curTree"))) =
        some (Nat.lor (4 <<< 224) (0 <<< 160)) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_bitOr_bounded
      st
      (.shl (.literal 224) (.localVar "layer"))
      (.shl (.literal 160) (.localVar "curTree"))
      (4 <<< 224) (0 <<< 160) h224 h160 h4ShiftLt h0ShiftLt
  have hTypeLeaf : evalExpr [] st
      (.bitOr
        (.shl (.literal 128) (.literal 1))
        (.shl (.literal 96) (.localVar "curLeaf"))) =
        some (Nat.lor (1 <<< 128) (leaf <<< 96)) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_bitOr_bounded
      st
      (.shl (.literal 128) (.literal 1))
      (.shl (.literal 96) (.localVar "curLeaf"))
      (1 <<< 128) (leaf <<< 96) h128 h96 h1ShiftLt hLeafShiftLt
  have hLayerTreeLt : Nat.lor (4 <<< 224) (0 <<< 160) < 2 ^ 256 :=
    c12_nat_lor_lt_two_pow h4ShiftLt h0ShiftLt
  have hTypeLeafLt : Nat.lor (1 <<< 128) (leaf <<< 96) < 2 ^ 256 :=
    c12_nat_lor_lt_two_pow h1ShiftLt hLeafShiftLt
  have hFull : evalExpr [] st C12SegmentWotsSetup.c12LayerPkAdrsExpr =
      some (Nat.lor (Nat.lor (4 <<< 224) (0 <<< 160))
        (Nat.lor (1 <<< 128) (leaf <<< 96))) := by
    unfold C12SegmentWotsSetup.c12LayerPkAdrsExpr
    exact SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_bitOr_bounded
      st
      (.bitOr
        (.shl (.literal 224) (.localVar "layer"))
        (.shl (.literal 160) (.localVar "curTree")))
      (.bitOr
        (.shl (.literal 128) (.literal 1))
        (.shl (.literal 96) (.localVar "curLeaf")))
      (Nat.lor (4 <<< 224) (0 <<< 160))
      (Nat.lor (1 <<< 128) (leaf <<< 96))
      hLayerTree hTypeLeaf hLayerTreeLt hTypeLeafLt
  rw [hFull]
  unfold C12Concrete.wotsPkAdrsC12
  rw [c12Layer4NextTree_of_parsed_eq_zero]
  change some (Nat.lor (Nat.lor (4 <<< 224) (0 <<< 160))
      (Nat.lor (1 <<< 128) (leaf <<< 96))) =
    some (Nat.lor (Nat.lor (Nat.lor (4 <<< 224) (0 <<< 160)) (1 <<< 128))
      (leaf <<< 96))
  exact congrArg some
    (Nat.lor_assoc (Nat.lor (4 <<< 224) (0 <<< 160)) (1 <<< 128) (leaf <<< 96)).symm

/-- **Top-level C12 layer-4 generic xmssClimb under the frozen site.**  Mirrors
`c12_layer4_generic_xmss_of_step_after3_curLeaf_and_wotsPk`, but the bare
universal per-step `hLayer4StepRawAdvance` is replaced by a site-restricted
step `hLayer4StepRawAdvanceUnderSite` *and* an entry-site fact
`hLayer4EntrySite`.  All other previously-implicit fold-level residuals —
the initial `MerkleClimbRawRel` (from `c12_layer4_initial_raw_rel_of_input_curLeaf_and_wotsPk`),
the per-iteration data range (from `c12_layer4_hDdata_of_parse`), and the
entry `mIdx` EVM bound (from `c12Layer4Leaf_lt_two_pow_256`) — are dischared
internally.  Composes
`c12Layer4_foldLoop_merkleNode_eq_xmssClimb_of_entry_site_and_step` with the
frozen-site `h_inject` lift, the existing input-binding initial-raw-rel
helper, and the parser-derived data range.  Returns the same fold conclusion
as the bare-step top-level. -/
theorem c12_layer4_generic_xmss_of_site_step_after3_curLeaf_and_wotsPk
    (hLayer4StepRawAdvanceUnderSite :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
          ∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat),
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
              (c12Layer4ParsedAuth sigParsed)
              (c12Layer4ParsedAuthCdAt pkSeed pkRoot message sig) idx →
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
              "merkleNode" "mIdx" s a →
            C12Layer4FrozenSite pkSeed pkRoot message sig sigParsed s →
            a.1 < 2 ^ 256 →
            idx < 4 →
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
              "merkleNode" "mIdx"
                (SphincsMinusVerifiers.ClimbKit.stepMerkle
                  "merkleNode" "mIdx" "xmssBase" "authPtr"
                  { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
                (SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleSpecStep
                  (c12Layer4ParsedSeed pkSeed)
                  (c12Layer4ParsedBase pkSeed pkRoot message sigParsed)
                  (c12Layer4ParsedAuth sigParsed) idx a))
    (hLayer4EntrySite :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        C12Layer4FrozenSite pkSeed pkRoot message sig sigParsed
          (c12Layer4XmssEntryState pkSeed pkRoot message sig))
    (hLayer4CurLeafAfter3 :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (c12LayerStateAfter3
            (C12SegmentForsCompress.c12StepForsCompress
              (C12SegmentFors.c12StepFors
                (C12SegmentSeed.c12StepSeed
                  (MkC13State.mkC13State pkSeed pkRoot message sig))))).bindings
          "curLeaf" =
        c12Layer4Leaf
          (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
    (hLayer4WotsPkBeforeNode :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (C12SegmentWotsSetup.c12LayerStateBeforeXmssNode
            (c12LayerBodyInput4
              (C12SegmentForsCompress.c12StepForsCompress
                (C12SegmentFors.c12StepFors
                  (C12SegmentSeed.c12StepSeed
                    (MkC13State.mkC13State pkSeed pkRoot message sig)))))).bindings
          "wotsPk" =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          (c12Layer4WotsPkBytes pkSeed
            (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex
            (c12UnrolledLayerRoot3 pkSeed
              (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex
              ((C12Concrete.forsPkFromSigC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot }
                  (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed)
                  sigParsed.fors).getD ⟨#[]⟩)
              sigParsed.layers)
            ((sigParsed.layers[4]?).getD c12EmptyXmssLayerSig))) :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (SphincsMinusVerifiers.ClimbLoop.foldLoop "h"
            (SphincsMinusVerifiers.ClimbKit.stepMerkle
              "merkleNode" "mIdx" "xmssBase" "authPtr")
            { (C12SegmentWotsSetup.c12LayerStateBeforeXmssLoop
                (c12LayerBodyInput4
                  (C12SegmentForsCompress.c12StepForsCompress
                    (C12SegmentFors.c12StepFors
                      (C12SegmentSeed.c12StepSeed
                        (MkC13State.mkC13State pkSeed pkRoot message sig)))))) with
              bindings :=
                bindValue
                  (C12SegmentWotsSetup.c12LayerStateBeforeXmssLoop
                    (c12LayerBodyInput4
                      (C12SegmentForsCompress.c12StepForsCompress
                        (C12SegmentFors.c12StepFors
                          (C12SegmentSeed.c12StepSeed
                            (MkC13State.mkC13State pkSeed pkRoot message sig)))))).bindings
                  "h" (wordNormalize 0) }
            0 (wordNormalize 4)).bindings
          "merkleNode" =
        SphincsMinusVerifierSpec.C13Concrete.xmssClimb
          (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed)
          (C12Concrete.xmssBaseC12 4
            (c12Layer4NextTree
              (C12Concrete.hMsgC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex))
          4 0
          (c12Layer4Leaf
            (C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex)
          (C12Concrete.wotsPkWordC12
            (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed)
            4
            (c12Layer4NextTree
              (C12Concrete.hMsgC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex)
            (c12Layer4Leaf
              (C12Concrete.hMsgC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex)
            (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
              (c12UnrolledLayerRoot3 pkSeed
                (C12Concrete.hMsgC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex
                ((C12Concrete.forsPkFromSigC12 c12
                    { pkSeed := pkSeed, pkRoot := pkRoot }
                    (C12Concrete.hMsgC12 c12
                      { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
                    sigParsed.fors).getD ⟨#[]⟩)
                sigParsed.layers))
            ((sigParsed.layers[4]?).getD c12EmptyXmssLayerSig).wots)
          ((sigParsed.layers[4]?).getD c12EmptyXmssLayerSig).authPath := by
  intro pkSeed pkRoot message sig sigParsed hParse
  let entry : RuntimeState := c12Layer4XmssEntryState pkSeed pkRoot message sig
  let state : RuntimeState :=
    { entry with bindings := bindValue entry.bindings "h" (wordNormalize 0) }
  let initial_mIdx : Nat :=
    c12Layer4Leaf
      (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex
  let initial_node : Nat :=
    c12Layer4ParsedStartNode pkSeed pkRoot message sigParsed
  -- Entry-site at `state` (h-injected) follows from the entry-site at `entry`
  -- via `C12Layer4FrozenSite.h_inject`.
  have hSiteState : C12Layer4FrozenSite pkSeed pkRoot message sig sigParsed state :=
    C12Layer4FrozenSite.h_inject pkSeed pkRoot message sig sigParsed entry 0
      (hLayer4EntrySite pkSeed pkRoot message sig sigParsed hParse)
  -- Initial `MerkleClimbRawRel` at `state` follows from the curLeaf-input and
  -- wotsPk-before-node handoffs via `c12_layer4_initial_raw_rel_of_input_curLeaf_and_wotsPk`.
  have hLayer4CurLeafInput :
      ∀ pkSeed' pkRoot' message' sig' sigParsed',
        C12Concrete.parseSignatureC12 c12 sig' = some sigParsed' →
        lookupValue
          (c12LayerBodyInput4
            (C12SegmentForsCompress.c12StepForsCompress
              (C12SegmentFors.c12StepFors
                (C12SegmentSeed.c12StepSeed
                  (MkC13State.mkC13State pkSeed' pkRoot' message' sig'))))).bindings
          "curLeaf" =
        c12Layer4Leaf
          (c12Layer4ParsedMessage pkSeed' pkRoot' message' sigParsed').hyperIndex := by
    intro pkSeed' pkRoot' message' sig' sigParsed' hParse'
    rw [c12LayerBodyInput4_curLeaf_eq]
    exact hLayer4CurLeafAfter3 pkSeed' pkRoot' message' sig' sigParsed' hParse'
  have hRawEntry :
      SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
        "merkleNode" "mIdx" state (initial_mIdx, initial_node) :=
    c12_layer4_initial_raw_rel_of_input_curLeaf_and_wotsPk
      hLayer4CurLeafInput hLayer4WotsPkBeforeNode
      pkSeed pkRoot message sig sigParsed hParse
  have hBoundEntry : initial_mIdx < 2 ^ 256 :=
    c12Layer4Leaf_lt_two_pow_256 _
  have hData :=
    c12_layer4_hDdata_of_parse pkSeed pkRoot message sig sigParsed hParse
  -- Pack the step under-site for the foldLoop lift.
  have hStep :
      ∀ (s : RuntimeState) (b : Nat × Nat) (idx : Nat),
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
          (c12Layer4ParsedAuth sigParsed)
          (c12Layer4ParsedAuthCdAt pkSeed pkRoot message sig) idx →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
          "merkleNode" "mIdx" s b →
        C12Layer4FrozenSite pkSeed pkRoot message sig sigParsed s →
        b.1 < 2 ^ 256 →
        idx < 4 →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
          "merkleNode" "mIdx"
          (SphincsMinusVerifiers.ClimbKit.stepMerkle
            "merkleNode" "mIdx" "xmssBase" "authPtr"
            { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
          (SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleSpecStep
            (c12Layer4ParsedSeed pkSeed)
            (c12Layer4ParsedBase pkSeed pkRoot message sigParsed)
            (c12Layer4ParsedAuth sigParsed) idx b) :=
    fun s b idx hData' hRaw hSite hBnd hIdx =>
      hLayer4StepRawAdvanceUnderSite pkSeed pkRoot message sig sigParsed hParse
        s b idx hData' hRaw hSite hBnd hIdx
  have hRange :
      ∀ i, i < (4 : Nat) →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
          (c12Layer4ParsedAuth sigParsed)
          (c12Layer4ParsedAuthCdAt pkSeed pkRoot message sig) i := by
    intro i hi
    exact hData i (by simpa using hi)
  exact c12Layer4_foldLoop_merkleNode_eq_xmssClimb_of_entry_site_and_step
    pkSeed pkRoot message sig sigParsed state initial_mIdx initial_node
    hSiteState hRawEntry hBoundEntry hRange hStep

/-- **Site-restricted layer-4 Merkle step closure** — the per-step Raw-rel
advance follows directly from the bundled frozen site, the EVM bound on
`a.1`, and the per-iteration height bound `idx < 4`, with no further consumer
input.  Composes the closed-form helpers
`c12Layer4StepLoad_h1_of_state_shape` (h1 from selector+calldata+authPtr),
`c12Layer4StepAdr_h3_and_frame_of_xmssBase` (h3 + ADRS frame from xmssBase),
`c12Layer4StepLocalEvalObligations_of_raw_load_adr` (the 8-conjunct local
eval bundle), `c12Layer4StepDataObligations_of_frame_load` (seed/ADRS/sib data
bundle), and `c12Layer4StepArithmeticObligations_of_raw_local` (the
parity/offset/node-norm triple), then welds them via the shared
`c12_layer4_MerkleClimbRawRel_step` weld.  The parsed-base bound is
discharged internally from `c12Layer4ParsedBase_lt`. -/
theorem c12Layer4_stepRawAdvance_under_frozenSite
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature)
    (s : RuntimeState) (a : Nat × Nat) (idx : Nat)
    (hData :
      SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
        (c12Layer4ParsedAuth sigParsed)
        (c12Layer4ParsedAuthCdAt pkSeed pkRoot message sig) idx)
    (hRaw :
      SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
        "merkleNode" "mIdx" s a)
    (hSite : C12Layer4FrozenSite pkSeed pkRoot message sig sigParsed s)
    (hBound : a.1 < 2 ^ 256)
    (hIdxLt : idx < 4) :
    SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
      "merkleNode" "mIdx"
      (SphincsMinusVerifiers.ClimbKit.stepMerkle
        "merkleNode" "mIdx" "xmssBase" "authPtr"
        { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
      (SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleSpecStep
        (c12Layer4ParsedSeed pkSeed)
        (c12Layer4ParsedBase pkSeed pkRoot message sigParsed)
        (c12Layer4ParsedAuth sigParsed) idx a) := by
  obtain ⟨hSel, hCD, hAuthPtr, hXmssBase, hSeed⟩ := hSite
  let vsib : Nat :=
    SphincsMinusVerifierSpec.C13Concrete.maskN
      (c12Layer4ParsedAuthCdAt pkSeed pkRoot message sig idx)
  have h1 := c12Layer4StepLoad_h1_of_state_shape
    pkSeed pkRoot message sig s idx hSel hCD hAuthPtr hIdxLt
  obtain ⟨vadr, h3, hAdr⟩ :=
    c12Layer4StepAdr_h3_and_frame_of_xmssBase
      pkSeed pkRoot message sigParsed s a idx vsib
      hXmssBase
      (c12Layer4ParsedBase_lt pkSeed pkRoot message sigParsed)
      hIdxLt hBound
  have hEval :=
    c12Layer4StepLocalEvalObligations_of_raw_load_adr
      s a idx vsib vadr hRaw hBound h1 h3
  have hLoad :
      vsib =
        SphincsMinusVerifierSpec.C13Concrete.maskN
          (c12Layer4ParsedAuthCdAt pkSeed pkRoot message sig idx) := rfl
  let vpar : Nat := a.1 >>> 1
  let sval : Nat := (Nat.land a.1 1) <<< 5
  let o5 : Nat := Nat.xor 0x40 sval
  let o6 : Nat := Nat.xor 0x60 sval
  have hStepData :=
    c12Layer4StepDataObligations_of_frame_load
      pkSeed pkRoot message sig sigParsed s a idx
      vsib vpar vadr sval o5 a.2 o6 vsib
      hData hSeed hAdr hLoad hEval
  have hArith :=
    c12Layer4StepArithmeticObligations_of_raw_local
      s a idx vsib vpar vadr sval o5 a.2 o6 vsib
      hBound hRaw hEval
  obtain ⟨hparOff, hvpar, hnode⟩ := hArith
  obtain ⟨e1, e2, e3, e4, e5off, e5val, e6off, e6val⟩ := hEval
  dsimp [c12Layer4StepDataObligations] at hStepData
  exact c12_layer4_MerkleClimbRawRel_step
    "merkleNode" "mIdx" "xmssBase" "authPtr"
    { s with bindings := bindValue s.bindings "h" (wordNormalize idx) }
    vsib vpar vadr sval o5 a.2 o6 vsib
    (c12Layer4ParsedSeed pkSeed)
    (c12Layer4ParsedBase pkSeed pkRoot message sigParsed)
    idx a.1 a.2 (c12Layer4ParsedAuth sigParsed)
    (by decide) (by decide) hparOff hvpar hnode hStepData
    e1 e2 e3 e4 e5off e5val e6off e6val

/-- **Top-level C12 layer-4 generic xmssClimb with the site step internalized.**
Strictly reduces the residual of
`c12_layer4_generic_xmss_of_site_step_after3_curLeaf_and_wotsPk` by closing
its `hLayer4StepRawAdvanceUnderSite` argument internally via
`c12Layer4_stepRawAdvance_under_frozenSite`.  Consumer now supplies only the
three entry-time facts (`hLayer4EntrySite`, `hLayer4CurLeafAfter3`,
`hLayer4WotsPkBeforeNode`); the per-step advance is no longer a residual. -/
theorem c12_layer4_generic_xmss_of_entry_site_and_handoffs
    (hLayer4EntrySite :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        C12Layer4FrozenSite pkSeed pkRoot message sig sigParsed
          (c12Layer4XmssEntryState pkSeed pkRoot message sig))
    (hLayer4CurLeafAfter3 :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (c12LayerStateAfter3
            (C12SegmentForsCompress.c12StepForsCompress
              (C12SegmentFors.c12StepFors
                (C12SegmentSeed.c12StepSeed
                  (MkC13State.mkC13State pkSeed pkRoot message sig))))).bindings
          "curLeaf" =
        c12Layer4Leaf
          (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
    (hLayer4WotsPkBeforeNode :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (C12SegmentWotsSetup.c12LayerStateBeforeXmssNode
            (c12LayerBodyInput4
              (C12SegmentForsCompress.c12StepForsCompress
                (C12SegmentFors.c12StepFors
                  (C12SegmentSeed.c12StepSeed
                    (MkC13State.mkC13State pkSeed pkRoot message sig)))))).bindings
          "wotsPk" =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          (c12Layer4WotsPkBytes pkSeed
            (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex
            (c12UnrolledLayerRoot3 pkSeed
              (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex
              ((C12Concrete.forsPkFromSigC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot }
                  (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed)
                  sigParsed.fors).getD ⟨#[]⟩)
              sigParsed.layers)
            ((sigParsed.layers[4]?).getD c12EmptyXmssLayerSig))) :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (SphincsMinusVerifiers.ClimbLoop.foldLoop "h"
            (SphincsMinusVerifiers.ClimbKit.stepMerkle
              "merkleNode" "mIdx" "xmssBase" "authPtr")
            { (C12SegmentWotsSetup.c12LayerStateBeforeXmssLoop
                (c12LayerBodyInput4
                  (C12SegmentForsCompress.c12StepForsCompress
                    (C12SegmentFors.c12StepFors
                      (C12SegmentSeed.c12StepSeed
                        (MkC13State.mkC13State pkSeed pkRoot message sig)))))) with
              bindings :=
                bindValue
                  (C12SegmentWotsSetup.c12LayerStateBeforeXmssLoop
                    (c12LayerBodyInput4
                      (C12SegmentForsCompress.c12StepForsCompress
                        (C12SegmentFors.c12StepFors
                          (C12SegmentSeed.c12StepSeed
                            (MkC13State.mkC13State pkSeed pkRoot message sig)))))).bindings
                  "h" (wordNormalize 0) }
            0 (wordNormalize 4)).bindings
          "merkleNode" =
        SphincsMinusVerifierSpec.C13Concrete.xmssClimb
          (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed)
          (C12Concrete.xmssBaseC12 4
            (c12Layer4NextTree
              (C12Concrete.hMsgC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex))
          4 0
          (c12Layer4Leaf
            (C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex)
          (C12Concrete.wotsPkWordC12
            (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed)
            4
            (c12Layer4NextTree
              (C12Concrete.hMsgC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex)
            (c12Layer4Leaf
              (C12Concrete.hMsgC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex)
            (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
              (c12UnrolledLayerRoot3 pkSeed
                (C12Concrete.hMsgC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex
                ((C12Concrete.forsPkFromSigC12 c12
                    { pkSeed := pkSeed, pkRoot := pkRoot }
                    (C12Concrete.hMsgC12 c12
                      { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
                    sigParsed.fors).getD ⟨#[]⟩)
                sigParsed.layers))
            ((sigParsed.layers[4]?).getD c12EmptyXmssLayerSig).wots)
          ((sigParsed.layers[4]?).getD c12EmptyXmssLayerSig).authPath := by
  refine c12_layer4_generic_xmss_of_site_step_after3_curLeaf_and_wotsPk
    ?_ hLayer4EntrySite hLayer4CurLeafAfter3 hLayer4WotsPkBeforeNode
  intro pkSeed pkRoot message sig sigParsed hParse s b idx hData hRaw hSite hBound hIdxLt
  exact c12Layer4_stepRawAdvance_under_frozenSite
    pkSeed pkRoot message sig sigParsed s b idx hData hRaw hSite hBound hIdxLt

/-! ### Selector/calldata frame chain for the C12 layer-4 entry state.

Each c12 segment between `mkC13State` and `c12Layer4XmssEntryState` is a pure
composition of `letVar`/`assignVar`/`mstore`/`forEach` — none of which touch
the EVM `selector` or the `world.calldata` image.  The lemmas below thread
that structural fact through every layer-side body
(`c12WotsChainBody`/`c12WotsMessageBody`/`c12WotsChecksumBody`/
`c12WotsPkCopyBody`/`c12LayerBodyBeforeXmssLoop`), then through the segment-
level step (`c12LayerStateBeforeXmssLoop`).  The result is `(c12Layer4XmssEntryState
…).selector = (precursor).selector ∧ …calldata = …calldata` where
`precursor = c12StepForsCompress (c12StepFors (c12StepSeed (mkC13State …)))`. -/

private theorem c12WotsChainBody_preserves_sc :
    ∀ (s s'' : RuntimeState) (stmt : Compiler.CompilationModel.Stmt),
      stmt ∈ C12SegmentWotsSetup.c12WotsChainBody →
      execStmt [] s stmt = .continue s'' →
      StateFrame.PreservesSelectorCalldata s s'' := by
  intro s s'' stmt hmem hexec
  simp only [C12SegmentWotsSetup.c12WotsChainBody, List.mem_cons,
    List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl
  · exact StateFrame.execStmt_mstore_preserves_selector_calldata _ _ _ _ hexec
  · exact StateFrame.execStmt_mstore_preserves_selector_calldata _ _ _ _ hexec
  · exact StateFrame.execStmt_assignVar_preserves_selector_calldata _ _ "val" _ hexec

private theorem c12WotsMessageBody_preserves_sc :
    ∀ (s s'' : RuntimeState) (stmt : Compiler.CompilationModel.Stmt),
      stmt ∈ C12SegmentWotsSetup.c12WotsMessageBody →
      execStmt [] s stmt = .continue s'' →
      StateFrame.PreservesSelectorCalldata s s'' := by
  intro s s'' stmt hmem hexec
  simp only [C12SegmentWotsSetup.c12WotsMessageBody, List.mem_cons,
    List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact StateFrame.execStmt_letVar_preserves_selector_calldata _ _ "digit" _ hexec
  · exact StateFrame.execStmt_assignVar_preserves_selector_calldata _ _ "csum" _ hexec
  · exact StateFrame.execStmt_letVar_preserves_selector_calldata _ _ "val" _ hexec
  · exact StateFrame.execStmt_letVar_preserves_selector_calldata _ _ "chainBase" _ hexec
  · exact StateFrame.execStmt_letVar_preserves_selector_calldata _ _ "steps" _ hexec
  · exact StateFrame.execStmt_forEach_preserves_selector_calldata "s" _
      C12SegmentWotsSetup.c12WotsChainBody _ _ c12WotsChainBody_preserves_sc hexec
  · exact StateFrame.execStmt_mstore_preserves_selector_calldata _ _ _ _ hexec

private theorem c12WotsMessageStep_preserves_sc (st : RuntimeState) :
    StateFrame.PreservesSelectorCalldata st
      (C12SegmentWotsSetup.c12WotsMessageStep st) :=
  StateFrame.execStmtList_preserves_selector_calldata
    C12SegmentWotsSetup.c12WotsMessageBody st
    (C12SegmentWotsSetup.c12WotsMessageStep st)
    c12WotsMessageBody_preserves_sc
    (C12SegmentWotsSetup.execC12WotsMessageBody st)

private theorem c12WotsChecksumBody_preserves_sc :
    ∀ (s s'' : RuntimeState) (stmt : Compiler.CompilationModel.Stmt),
      stmt ∈ C12SegmentWotsSetup.c12WotsChecksumBody →
      execStmt [] s stmt = .continue s'' →
      StateFrame.PreservesSelectorCalldata s s'' := by
  intro s s'' stmt hmem hexec
  simp only [C12SegmentWotsSetup.c12WotsChecksumBody, List.mem_cons,
    List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact StateFrame.execStmt_letVar_preserves_selector_calldata _ _ "digit" _ hexec
  · exact StateFrame.execStmt_letVar_preserves_selector_calldata _ _ "i" _ hexec
  · exact StateFrame.execStmt_letVar_preserves_selector_calldata _ _ "val" _ hexec
  · exact StateFrame.execStmt_letVar_preserves_selector_calldata _ _ "chainBase" _ hexec
  · exact StateFrame.execStmt_letVar_preserves_selector_calldata _ _ "steps" _ hexec
  · exact StateFrame.execStmt_forEach_preserves_selector_calldata "s" _
      C12SegmentWotsSetup.c12WotsChainBody _ _ c12WotsChainBody_preserves_sc hexec
  · exact StateFrame.execStmt_mstore_preserves_selector_calldata _ _ _ _ hexec

private theorem c12WotsChecksumStep_preserves_sc (st : RuntimeState) :
    StateFrame.PreservesSelectorCalldata st
      (C12SegmentWotsSetup.c12WotsChecksumStep st) :=
  StateFrame.execStmtList_preserves_selector_calldata
    C12SegmentWotsSetup.c12WotsChecksumBody
    st
    (C12SegmentWotsSetup.c12WotsChecksumStep st)
    c12WotsChecksumBody_preserves_sc
    (C12SegmentWotsSetup.execC12WotsChecksumBody st)

private theorem c12WotsPkCopyBody_preserves_sc :
    ∀ (s s'' : RuntimeState) (stmt : Compiler.CompilationModel.Stmt),
      stmt ∈ C12SegmentWotsSetup.c12WotsPkCopyBody →
      execStmt [] s stmt = .continue s'' →
      StateFrame.PreservesSelectorCalldata s s'' := by
  intro s s'' stmt hmem hexec
  simp only [C12SegmentWotsSetup.c12WotsPkCopyBody, List.mem_cons,
    List.not_mem_nil, or_false] at hmem
  subst hmem
  exact StateFrame.execStmt_mstore_preserves_selector_calldata _ _ _ _ hexec

private theorem c12LayerBodyBeforeXmssLoop_preserves_sc :
    ∀ (s s'' : RuntimeState) (stmt : Compiler.CompilationModel.Stmt),
      stmt ∈ C12SegmentWotsSetup.c12LayerBodyBeforeXmssLoop →
      execStmt [] s stmt = .continue s'' →
      StateFrame.PreservesSelectorCalldata s s'' := by
  intro s s'' stmt hmem hexec
  simp only [C12SegmentWotsSetup.c12LayerBodyBeforeXmssLoop, List.mem_cons,
    List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  · exact StateFrame.execStmt_letVar_preserves_selector_calldata _ _ "wotsBase" _ hexec
  · exact StateFrame.execStmt_letVar_preserves_selector_calldata _ _ "wotsPtr" _ hexec
  · exact StateFrame.execStmt_letVar_preserves_selector_calldata _ _ "csum" _ hexec
  · exact StateFrame.execStmt_forEach_preserves_selector_calldata "i" _
      C12SegmentWotsSetup.c12WotsMessageBody _ _ c12WotsMessageBody_preserves_sc hexec
  · exact StateFrame.execStmt_letVar_preserves_selector_calldata _ _ "csumShifted" _ hexec
  · exact StateFrame.execStmt_forEach_preserves_selector_calldata "j" _
      C12SegmentWotsSetup.c12WotsChecksumBody _ _ c12WotsChecksumBody_preserves_sc hexec
  · exact StateFrame.execStmt_letVar_preserves_selector_calldata _ _ "pkAdrs" _ hexec
  · exact StateFrame.execStmt_mstore_preserves_selector_calldata _ _ _ _ hexec
  · exact StateFrame.execStmt_forEach_preserves_selector_calldata "i" _
      C12SegmentWotsSetup.c12WotsPkCopyBody _ _ c12WotsPkCopyBody_preserves_sc hexec
  · exact StateFrame.execStmt_letVar_preserves_selector_calldata _ _ "wotsPk" _ hexec
  · exact StateFrame.execStmt_letVar_preserves_selector_calldata _ _ "authOff" _ hexec
  · exact StateFrame.execStmt_letVar_preserves_selector_calldata _ _ "authPtr" _ hexec
  · exact StateFrame.execStmt_letVar_preserves_selector_calldata _ _ "xmssBase" _ hexec
  · exact StateFrame.execStmt_letVar_preserves_selector_calldata _ _ "merkleNode" _ hexec
  · exact StateFrame.execStmt_letVar_preserves_selector_calldata _ _ "mIdx" _ hexec

/-- The C12 layer-4 body prefix (everything before the XMSS-loop iteration)
preserves the EVM selector and the calldata image.  Closes the last step of the
selector/calldata chain to `c12Layer4XmssEntryState`. -/
theorem c12LayerStateBeforeXmssLoop_preserves_selector_calldata (st : RuntimeState) :
    StateFrame.PreservesSelectorCalldata st
      (C12SegmentWotsSetup.c12LayerStateBeforeXmssLoop st) :=
  StateFrame.execStmtList_preserves_selector_calldata
    C12SegmentWotsSetup.c12LayerBodyBeforeXmssLoop st
    (C12SegmentWotsSetup.c12LayerStateBeforeXmssLoop st)
    c12LayerBodyBeforeXmssLoop_preserves_sc
    (C12SegmentWotsSetup.execC12LayerBodyBeforeXmssLoop st)

private theorem c12XmssBody_preserves_sc :
    ∀ (s s'' : RuntimeState) (stmt : Compiler.CompilationModel.Stmt),
      stmt ∈ C12SegmentWotsSetup.c12XmssBody →
      execStmt [] s stmt = .continue s'' →
      StateFrame.PreservesSelectorCalldata s s'' := by
  intro s s'' stmt hmem hexec
  simp only [C12SegmentWotsSetup.c12XmssBody, List.mem_cons,
    List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact StateFrame.execStmt_letVar_preserves_selector_calldata _ _ "sibling" _ hexec
  · exact StateFrame.execStmt_letVar_preserves_selector_calldata _ _ "parentIdx" _ hexec
  · exact StateFrame.execStmt_mstore_preserves_selector_calldata _ _ _ _ hexec
  · exact StateFrame.execStmt_letVar_preserves_selector_calldata _ _ "s" _ hexec
  · exact StateFrame.execStmt_mstore_preserves_selector_calldata _ _ _ _ hexec
  · exact StateFrame.execStmt_mstore_preserves_selector_calldata _ _ _ _ hexec
  · exact StateFrame.execStmt_assignVar_preserves_selector_calldata _ _ "merkleNode" _ hexec
  · exact StateFrame.execStmt_assignVar_preserves_selector_calldata _ _ "mIdx" _ hexec

private theorem c12LayerBody_preserves_sc :
    ∀ (s s'' : RuntimeState) (stmt : Compiler.CompilationModel.Stmt),
      stmt ∈ C12SegmentWotsSetup.c12LayerBody →
      execStmt [] s stmt = .continue s'' →
      StateFrame.PreservesSelectorCalldata s s'' := by
  intro s s'' stmt hmem hexec
  simp only [C12SegmentWotsSetup.c12LayerBody, List.mem_cons,
    List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact StateFrame.execStmt_letVar_preserves_selector_calldata _ _ "wotsBase" _ hexec
  · exact StateFrame.execStmt_letVar_preserves_selector_calldata _ _ "wotsPtr" _ hexec
  · exact StateFrame.execStmt_letVar_preserves_selector_calldata _ _ "csum" _ hexec
  · exact StateFrame.execStmt_forEach_preserves_selector_calldata "i" _
      C12SegmentWotsSetup.c12WotsMessageBody _ _ c12WotsMessageBody_preserves_sc hexec
  · exact StateFrame.execStmt_letVar_preserves_selector_calldata _ _ "csumShifted" _ hexec
  · exact StateFrame.execStmt_forEach_preserves_selector_calldata "j" _
      C12SegmentWotsSetup.c12WotsChecksumBody _ _ c12WotsChecksumBody_preserves_sc hexec
  · exact StateFrame.execStmt_letVar_preserves_selector_calldata _ _ "pkAdrs" _ hexec
  · exact StateFrame.execStmt_mstore_preserves_selector_calldata _ _ _ _ hexec
  · exact StateFrame.execStmt_forEach_preserves_selector_calldata "i" _
      C12SegmentWotsSetup.c12WotsPkCopyBody _ _ c12WotsPkCopyBody_preserves_sc hexec
  · exact StateFrame.execStmt_letVar_preserves_selector_calldata _ _ "wotsPk" _ hexec
  · exact StateFrame.execStmt_letVar_preserves_selector_calldata _ _ "authOff" _ hexec
  · exact StateFrame.execStmt_letVar_preserves_selector_calldata _ _ "authPtr" _ hexec
  · exact StateFrame.execStmt_letVar_preserves_selector_calldata _ _ "xmssBase" _ hexec
  · exact StateFrame.execStmt_letVar_preserves_selector_calldata _ _ "merkleNode" _ hexec
  · exact StateFrame.execStmt_letVar_preserves_selector_calldata _ _ "mIdx" _ hexec
  · exact StateFrame.execStmt_forEach_preserves_selector_calldata "h" _
      C12SegmentWotsSetup.c12XmssBody _ _ c12XmssBody_preserves_sc hexec
  · exact StateFrame.execStmt_assignVar_preserves_selector_calldata _ _ "currentNode" _ hexec
  · exact StateFrame.execStmt_assignVar_preserves_selector_calldata _ _ "sigOff" _ hexec
  · exact StateFrame.execStmt_assignVar_preserves_selector_calldata _ _ "curLeaf" _ hexec
  · exact StateFrame.execStmt_assignVar_preserves_selector_calldata _ _ "curTree" _ hexec

/-- One C12 hypertree layer iteration preserves selector and calldata. -/
theorem c12LayerStep_preserves_selector_calldata (st : RuntimeState) :
    StateFrame.PreservesSelectorCalldata st (C12SegmentWotsSetup.c12LayerStep st) :=
  StateFrame.execStmtList_preserves_selector_calldata
    C12SegmentWotsSetup.c12LayerBody st (C12SegmentWotsSetup.c12LayerStep st)
    c12LayerBody_preserves_sc
    (C12SegmentWotsSetup.execC12LayerBody st)

/-- The `"layer"` fold loop preserves selector and calldata (any number of
iterations).  The body-side preservation is supplied by
`c12LayerStep_preserves_selector_calldata`; the structural inequality
`({st with bindings := …}).selector = st.selector` and the analogous calldata
projection close the gap between the foldLoop's `{st with …}` input and the
caller's raw `st`. -/
theorem c12LayerLoopFold_preserves_selector_calldata
    (st : RuntimeState) (layers : Nat) :
    StateFrame.PreservesSelectorCalldata st (c12LayerLoopFold st layers) := by
  unfold c12LayerLoopFold
  have hfold := StateFrame.foldLoop_preserves_selector_calldata "layer"
    C12SegmentWotsSetup.c12LayerStep c12LayerStep_preserves_selector_calldata
    { st with bindings := bindValue st.bindings "layer" (wordNormalize 0) }
    0 (wordNormalize layers)
  exact ⟨by rw [hfold.1], by rw [hfold.2]⟩

/-- `c12LayerStateAfter3` preserves selector and calldata (it is just
`c12LayerLoopFold st 4`). -/
theorem c12LayerStateAfter3_preserves_selector_calldata (st : RuntimeState) :
    StateFrame.PreservesSelectorCalldata st (c12LayerStateAfter3 st) := by
  unfold c12LayerStateAfter3
  exact c12LayerLoopFold_preserves_selector_calldata st 4

/-- The layer-4 pre-body state preserves the byte-facing frame from the initial
C12 runtime state.  This is intentionally specialized to the layer-4 entry path:
it chains the three proved pre-layer segment frame lemmas, then the first four
hypertree layer iterations, and finally the `"layer"` rebinding. -/
theorem c12Layer4PreBodyState_preserves_selector_calldata
    (pkSeed pkRoot message sig : ByteArray) :
    StateFrame.PreservesSelectorCalldata
      (MkC13State.mkC13State pkSeed pkRoot message sig)
      (c12Layer4PreBodyState pkSeed pkRoot message sig) := by
  let st0 := MkC13State.mkC13State pkSeed pkRoot message sig
  let st1 := C12SegmentSeed.c12StepSeed st0
  let st2 := C12SegmentFors.c12StepFors st1
  let st3 := C12SegmentForsCompress.c12StepForsCompress st2
  have hSeed := C12SegmentSeed.c12StepSeed_preserves_selector_calldata st0
  have hFors := C12SegmentFors.c12StepFors_preserves_selector_calldata st1
  have hCompress := C12SegmentForsCompress.c12StepForsCompress_preserves_selector_calldata st2
  have hAfter3 := c12LayerStateAfter3_preserves_selector_calldata st3
  exact ⟨
    by
      simp only [c12Layer4PreBodyState, c12LayerBodyInput4]
      rw [hAfter3.1, hCompress.1, hFors.1, hSeed.1],
    by
      simp only [c12Layer4PreBodyState, c12LayerBodyInput4]
      rw [hAfter3.2, hCompress.2, hFors.2, hSeed.2]⟩

theorem c12Layer4PreBodyState_selector_eq
    (pkSeed pkRoot message sig : ByteArray) :
    (c12Layer4PreBodyState pkSeed pkRoot message sig).selector = 0 := by
  have h :=
    c12Layer4PreBodyState_preserves_selector_calldata
      pkSeed pkRoot message sig
  simpa [MkC13State.mkC13State] using h.1

theorem c12Layer4PreBodyState_calldata_eq
    (pkSeed pkRoot message sig : ByteArray) :
    (c12Layer4PreBodyState pkSeed pkRoot message sig).world.calldata =
      MkC13State.headWords pkSeed pkRoot message sig.size
        ++ MkC13State.bytesToWords sig := by
  have h :=
    c12Layer4PreBodyState_preserves_selector_calldata
      pkSeed pkRoot message sig
  simpa [MkC13State.mkC13State] using h.2

/-- **Strict reduction of `hLayer4EntrySite`.**  The consumer no longer
supplies the bundled `C12Layer4FrozenSite` predicate.  Instead they supply
five atomic facts about a state `s` whose layer-4 body-prefix push yields the
entry state — its selector, calldata image, parsed-base `"authPtr"`/
`"xmssBase"` bindings, and seed cell — and the predicate is assembled
internally.  Substantive content: the layer-4 body-prefix preservation
`c12LayerStateBeforeXmssLoop_preserves_selector_calldata` (and the nested
WOTS body preservations it depends on), proven above. -/
theorem C12Layer4FrozenSite_of_pre_body_sc_and_components
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature)
    (hSel :
      (c12Layer4PreBodyState pkSeed pkRoot message sig).selector = 0)
    (hCD :
      (c12Layer4PreBodyState pkSeed pkRoot message sig).world.calldata =
        MkC13State.headWords pkSeed pkRoot message sig.size
          ++ MkC13State.bytesToWords sig)
    (hAuthPtr :
      lookupValue
        (c12Layer4XmssEntryState pkSeed pkRoot message sig).bindings "authPtr" =
        MkC13State.sigDataOffset + (2592 + 784 * 4 + 720))
    (hXmssBase :
      lookupValue
        (c12Layer4XmssEntryState pkSeed pkRoot message sig).bindings "xmssBase" =
        c12Layer4ParsedBase pkSeed pkRoot message sigParsed)
    (hSeed :
      ((c12Layer4XmssEntryState pkSeed pkRoot message sig).world.memory 0x00).val =
        c12Layer4ParsedSeed pkSeed) :
    C12Layer4FrozenSite pkSeed pkRoot message sig sigParsed
      (c12Layer4XmssEntryState pkSeed pkRoot message sig) := by
  let st :=
    c12Layer4PreBodyState pkSeed pkRoot message sig
  have hChain : StateFrame.PreservesSelectorCalldata st
      (C12SegmentWotsSetup.c12LayerStateBeforeXmssLoop st) :=
    c12LayerStateBeforeXmssLoop_preserves_selector_calldata st
  refine ⟨?_, ?_, hAuthPtr, hXmssBase, hSeed⟩
  · simpa [c12Layer4XmssEntryState, st] using Eq.trans hChain.1 hSel
  · simpa [c12Layer4XmssEntryState, st] using Eq.trans hChain.2 hCD

/-- **Top-level layer-4 generic xmssClimb with the entry-site split into five
atomic facts.**  Consumes
`C12Layer4FrozenSite_of_pre_body_sc_and_components` (the substantive entry-
site builder using the layer-4 body-prefix preservation chain) inside
`c12_layer4_generic_xmss_of_entry_site_and_handoffs`.  Replaces the bundled
`hLayer4EntrySite` with the five separately-dischargeable site components,
each about a much simpler segment-level state instead of the deep entry
state. -/
theorem c12_layer4_generic_xmss_of_pre_body_components_and_handoffs
    (hLayer4PreBodySel :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        (c12Layer4PreBodyState pkSeed pkRoot message sig).selector = 0)
    (hLayer4PreBodyCD :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        (c12Layer4PreBodyState pkSeed pkRoot message sig).world.calldata =
          MkC13State.headWords pkSeed pkRoot message sig.size
            ++ MkC13State.bytesToWords sig)
    (hLayer4EntryAuthPtr :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (c12Layer4XmssEntryState pkSeed pkRoot message sig).bindings "authPtr" =
          MkC13State.sigDataOffset + (2592 + 784 * 4 + 720))
    (hLayer4EntryXmssBase :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (c12Layer4XmssEntryState pkSeed pkRoot message sig).bindings "xmssBase" =
          c12Layer4ParsedBase pkSeed pkRoot message sigParsed)
    (hLayer4EntrySeed :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        ((c12Layer4XmssEntryState pkSeed pkRoot message sig).world.memory 0x00).val =
          c12Layer4ParsedSeed pkSeed)
    (hLayer4CurLeafAfter3 :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (c12LayerStateAfter3
            (C12SegmentForsCompress.c12StepForsCompress
              (C12SegmentFors.c12StepFors
                (C12SegmentSeed.c12StepSeed
                  (MkC13State.mkC13State pkSeed pkRoot message sig))))).bindings
          "curLeaf" =
        c12Layer4Leaf
          (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
    (hLayer4WotsPkBeforeNode :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (C12SegmentWotsSetup.c12LayerStateBeforeXmssNode
            (c12LayerBodyInput4
              (C12SegmentForsCompress.c12StepForsCompress
                (C12SegmentFors.c12StepFors
                  (C12SegmentSeed.c12StepSeed
                    (MkC13State.mkC13State pkSeed pkRoot message sig)))))).bindings
          "wotsPk" =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          (c12Layer4WotsPkBytes pkSeed
            (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex
            (c12UnrolledLayerRoot3 pkSeed
              (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex
              ((C12Concrete.forsPkFromSigC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot }
                  (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed)
                  sigParsed.fors).getD ⟨#[]⟩)
              sigParsed.layers)
            ((sigParsed.layers[4]?).getD c12EmptyXmssLayerSig))) :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (SphincsMinusVerifiers.ClimbLoop.foldLoop "h"
            (SphincsMinusVerifiers.ClimbKit.stepMerkle
              "merkleNode" "mIdx" "xmssBase" "authPtr")
            { (C12SegmentWotsSetup.c12LayerStateBeforeXmssLoop
                (c12LayerBodyInput4
                  (C12SegmentForsCompress.c12StepForsCompress
                    (C12SegmentFors.c12StepFors
                      (C12SegmentSeed.c12StepSeed
                        (MkC13State.mkC13State pkSeed pkRoot message sig)))))) with
              bindings :=
                bindValue
                  (C12SegmentWotsSetup.c12LayerStateBeforeXmssLoop
                    (c12LayerBodyInput4
                      (C12SegmentForsCompress.c12StepForsCompress
                        (C12SegmentFors.c12StepFors
                          (C12SegmentSeed.c12StepSeed
                            (MkC13State.mkC13State pkSeed pkRoot message sig)))))).bindings
                  "h" (wordNormalize 0) }
            0 (wordNormalize 4)).bindings
          "merkleNode" =
        SphincsMinusVerifierSpec.C13Concrete.xmssClimb
          (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed)
          (C12Concrete.xmssBaseC12 4
            (c12Layer4NextTree
              (C12Concrete.hMsgC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex))
          4 0
          (c12Layer4Leaf
            (C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex)
          (C12Concrete.wotsPkWordC12
            (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed)
            4
            (c12Layer4NextTree
              (C12Concrete.hMsgC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex)
            (c12Layer4Leaf
              (C12Concrete.hMsgC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex)
            (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
              (c12UnrolledLayerRoot3 pkSeed
                (C12Concrete.hMsgC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex
                ((C12Concrete.forsPkFromSigC12 c12
                    { pkSeed := pkSeed, pkRoot := pkRoot }
                    (C12Concrete.hMsgC12 c12
                      { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
                    sigParsed.fors).getD ⟨#[]⟩)
                sigParsed.layers))
            ((sigParsed.layers[4]?).getD c12EmptyXmssLayerSig).wots)
          ((sigParsed.layers[4]?).getD c12EmptyXmssLayerSig).authPath := by
  refine c12_layer4_generic_xmss_of_entry_site_and_handoffs
    ?_ hLayer4CurLeafAfter3 hLayer4WotsPkBeforeNode
  intro pkSeed pkRoot message sig sigParsed hParse
  exact
    C12Layer4FrozenSite_of_pre_body_sc_and_components
      pkSeed pkRoot message sig sigParsed
      (hLayer4PreBodySel pkSeed pkRoot message sig sigParsed hParse)
      (hLayer4PreBodyCD pkSeed pkRoot message sig sigParsed hParse)
      (hLayer4EntryAuthPtr pkSeed pkRoot message sig sigParsed hParse)
      (hLayer4EntryXmssBase pkSeed pkRoot message sig sigParsed hParse)
      (hLayer4EntrySeed pkSeed pkRoot message sig sigParsed hParse)

/-- Same layer-4 generic XMSS reducer with the pre-body selector/calldata
components discharged by the segment-level frame preservation chain. -/
theorem c12_layer4_generic_xmss_of_entry_components_and_handoffs
    (hLayer4EntryAuthPtr :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (c12Layer4XmssEntryState pkSeed pkRoot message sig).bindings "authPtr" =
          MkC13State.sigDataOffset + (2592 + 784 * 4 + 720))
    (hLayer4EntryXmssBase :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (c12Layer4XmssEntryState pkSeed pkRoot message sig).bindings "xmssBase" =
          c12Layer4ParsedBase pkSeed pkRoot message sigParsed)
    (hLayer4EntrySeed :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        ((c12Layer4XmssEntryState pkSeed pkRoot message sig).world.memory 0x00).val =
          c12Layer4ParsedSeed pkSeed)
    (hLayer4CurLeafAfter3 :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (c12LayerStateAfter3
            (C12SegmentForsCompress.c12StepForsCompress
              (C12SegmentFors.c12StepFors
                (C12SegmentSeed.c12StepSeed
                  (MkC13State.mkC13State pkSeed pkRoot message sig))))).bindings
          "curLeaf" =
        c12Layer4Leaf
          (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
    (hLayer4WotsPkBeforeNode :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (C12SegmentWotsSetup.c12LayerStateBeforeXmssNode
            (c12LayerBodyInput4
              (C12SegmentForsCompress.c12StepForsCompress
                (C12SegmentFors.c12StepFors
                  (C12SegmentSeed.c12StepSeed
                    (MkC13State.mkC13State pkSeed pkRoot message sig)))))).bindings
          "wotsPk" =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          (c12Layer4WotsPkBytes pkSeed
            (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex
            (c12UnrolledLayerRoot3 pkSeed
              (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex
              ((C12Concrete.forsPkFromSigC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot }
                  (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed)
                  sigParsed.fors).getD ⟨#[]⟩)
              sigParsed.layers)
            ((sigParsed.layers[4]?).getD c12EmptyXmssLayerSig))) :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (SphincsMinusVerifiers.ClimbLoop.foldLoop "h"
            (SphincsMinusVerifiers.ClimbKit.stepMerkle
              "merkleNode" "mIdx" "xmssBase" "authPtr")
            { (C12SegmentWotsSetup.c12LayerStateBeforeXmssLoop
                (c12LayerBodyInput4
                  (C12SegmentForsCompress.c12StepForsCompress
                    (C12SegmentFors.c12StepFors
                      (C12SegmentSeed.c12StepSeed
                        (MkC13State.mkC13State pkSeed pkRoot message sig)))))) with
              bindings :=
                bindValue
                  (C12SegmentWotsSetup.c12LayerStateBeforeXmssLoop
                    (c12LayerBodyInput4
                      (C12SegmentForsCompress.c12StepForsCompress
                        (C12SegmentFors.c12StepFors
                          (C12SegmentSeed.c12StepSeed
                            (MkC13State.mkC13State pkSeed pkRoot message sig)))))).bindings
                  "h" (wordNormalize 0) }
            0 (wordNormalize 4)).bindings
          "merkleNode" =
        SphincsMinusVerifierSpec.C13Concrete.xmssClimb
          (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed)
          (C12Concrete.xmssBaseC12 4
            (c12Layer4NextTree
              (C12Concrete.hMsgC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex))
          4 0
          (c12Layer4Leaf
            (C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex)
          (C12Concrete.wotsPkWordC12
            (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed)
            4
            (c12Layer4NextTree
              (C12Concrete.hMsgC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex)
            (c12Layer4Leaf
              (C12Concrete.hMsgC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex)
            (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
              (c12UnrolledLayerRoot3 pkSeed
                (C12Concrete.hMsgC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex
                ((C12Concrete.forsPkFromSigC12 c12
                    { pkSeed := pkSeed, pkRoot := pkRoot }
                    (C12Concrete.hMsgC12 c12
                      { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
                    sigParsed.fors).getD ⟨#[]⟩)
                sigParsed.layers))
            ((sigParsed.layers[4]?).getD c12EmptyXmssLayerSig).wots)
          ((sigParsed.layers[4]?).getD c12EmptyXmssLayerSig).authPath := by
  exact
    c12_layer4_generic_xmss_of_pre_body_components_and_handoffs
      (fun pkSeed pkRoot message sig _ _ =>
        c12Layer4PreBodyState_selector_eq pkSeed pkRoot message sig)
      (fun pkSeed pkRoot message sig _ _ =>
        c12Layer4PreBodyState_calldata_eq pkSeed pkRoot message sig)
      hLayer4EntryAuthPtr
      hLayer4EntryXmssBase
      hLayer4EntrySeed
      hLayer4CurLeafAfter3
      hLayer4WotsPkBeforeNode

/-- The raw layer-4 XMSS residual can be discharged at the standard generic
Merkle-climb fold: C12's local `c12XmssStep` is definitionally the generic
`stepMerkle` over `"merkleNode"`, `"mIdx"`, `"xmssBase"`, and `"authPtr"`. -/
theorem c12_layer4_raw_xmss_of_generic_merkle_fold
    (hLayer4GenericXmss :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (SphincsMinusVerifiers.ClimbLoop.foldLoop "h"
            (SphincsMinusVerifiers.ClimbKit.stepMerkle
              "merkleNode" "mIdx" "xmssBase" "authPtr")
            { (C12SegmentWotsSetup.c12LayerStateBeforeXmssLoop
                (c12LayerBodyInput4
                  (C12SegmentForsCompress.c12StepForsCompress
                    (C12SegmentFors.c12StepFors
                      (C12SegmentSeed.c12StepSeed
                        (MkC13State.mkC13State pkSeed pkRoot message sig)))))) with
              bindings :=
                bindValue
                  (C12SegmentWotsSetup.c12LayerStateBeforeXmssLoop
                    (c12LayerBodyInput4
                      (C12SegmentForsCompress.c12StepForsCompress
                        (C12SegmentFors.c12StepFors
                          (C12SegmentSeed.c12StepSeed
                            (MkC13State.mkC13State pkSeed pkRoot message sig)))))).bindings
                  "h" (wordNormalize 0) }
            0 (wordNormalize 4)).bindings
          "merkleNode" =
        SphincsMinusVerifierSpec.C13Concrete.xmssClimb
          (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed)
          (C12Concrete.xmssBaseC12 4
            (c12Layer4NextTree
              (C12Concrete.hMsgC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex))
          4 0
          (c12Layer4Leaf
            (C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex)
          (C12Concrete.wotsPkWordC12
            (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed)
            4
            (c12Layer4NextTree
              (C12Concrete.hMsgC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex)
            (c12Layer4Leaf
              (C12Concrete.hMsgC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex)
            (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
              (c12UnrolledLayerRoot3 pkSeed
                (C12Concrete.hMsgC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex
                ((C12Concrete.forsPkFromSigC12 c12
                    { pkSeed := pkSeed, pkRoot := pkRoot }
                    (C12Concrete.hMsgC12 c12
                      { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
                    sigParsed.fors).getD ⟨#[]⟩)
                sigParsed.layers))
            ((sigParsed.layers[4]?).getD c12EmptyXmssLayerSig).wots)
          ((sigParsed.layers[4]?).getD c12EmptyXmssLayerSig).authPath) :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (C12SegmentWotsSetup.c12LayerStateAfterXmssLoop
            (C12SegmentWotsSetup.c12LayerStateBeforeXmssLoop
              (c12LayerBodyInput4
                (C12SegmentForsCompress.c12StepForsCompress
                  (C12SegmentFors.c12StepFors
                    (C12SegmentSeed.c12StepSeed
                      (MkC13State.mkC13State pkSeed pkRoot message sig))))))).bindings
          "merkleNode" =
        SphincsMinusVerifierSpec.C13Concrete.xmssClimb
          (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed)
          (C12Concrete.xmssBaseC12 4
            (c12Layer4NextTree
              (C12Concrete.hMsgC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex))
          4 0
          (c12Layer4Leaf
            (C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex)
          (C12Concrete.wotsPkWordC12
            (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed)
            4
            (c12Layer4NextTree
              (C12Concrete.hMsgC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex)
            (c12Layer4Leaf
              (C12Concrete.hMsgC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex)
            (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
              (c12UnrolledLayerRoot3 pkSeed
                (C12Concrete.hMsgC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex
                ((C12Concrete.forsPkFromSigC12 c12
                    { pkSeed := pkSeed, pkRoot := pkRoot }
                    (C12Concrete.hMsgC12 c12
                      { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
                    sigParsed.fors).getD ⟨#[]⟩)
                sigParsed.layers))
            ((sigParsed.layers[4]?).getD c12EmptyXmssLayerSig).wots)
          ((sigParsed.layers[4]?).getD c12EmptyXmssLayerSig).authPath := by
  intro pkSeed pkRoot message sig sigParsed hParse
  rw [c12LayerStateAfterXmssLoop_eq_merkleFold]
  exact hLayer4GenericXmss pkSeed pkRoot message sig sigParsed hParse

/-- The layer-4 XMSS byte-root residual follows from the smaller raw executable
`xmssClimb` word correspondence.  This removes the `hash16OfWord`/`wordOfHash16`
roundtrip wrapper from the remaining semantic work; the start WOTS word is
canonical because `wotsPkWordC12` is a masked keccak word. -/
theorem c12_layer4_wots_xmss_roundtrip_of_raw_xmssClimb
    (hLayer4RawXmss :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (C12SegmentWotsSetup.c12LayerStateAfterXmssLoop
            (C12SegmentWotsSetup.c12LayerStateBeforeXmssLoop
              (c12LayerBodyInput4
                (C12SegmentForsCompress.c12StepForsCompress
                  (C12SegmentFors.c12StepFors
                    (C12SegmentSeed.c12StepSeed
                      (MkC13State.mkC13State pkSeed pkRoot message sig))))))).bindings
          "merkleNode" =
        SphincsMinusVerifierSpec.C13Concrete.xmssClimb
          (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed)
          (C12Concrete.xmssBaseC12 4
            (c12Layer4NextTree
              (C12Concrete.hMsgC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex))
          4 0
          (c12Layer4Leaf
            (C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex)
          (C12Concrete.wotsPkWordC12
            (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed)
            4
            (c12Layer4NextTree
              (C12Concrete.hMsgC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex)
            (c12Layer4Leaf
              (C12Concrete.hMsgC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex)
            (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
              (c12UnrolledLayerRoot3 pkSeed
                (C12Concrete.hMsgC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex
                ((C12Concrete.forsPkFromSigC12 c12
                    { pkSeed := pkSeed, pkRoot := pkRoot }
                    (C12Concrete.hMsgC12 c12
                      { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
                    sigParsed.fors).getD ⟨#[]⟩)
                sigParsed.layers))
            ((sigParsed.layers[4]?).getD c12EmptyXmssLayerSig).wots)
          ((sigParsed.layers[4]?).getD c12EmptyXmssLayerSig).authPath) :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (C12SegmentWotsSetup.c12LayerStateAfterXmssLoop
            (C12SegmentWotsSetup.c12LayerStateBeforeXmssLoop
              (c12LayerBodyInput4
                (C12SegmentForsCompress.c12StepForsCompress
                  (C12SegmentFors.c12StepFors
                    (C12SegmentSeed.c12StepSeed
                      (MkC13State.mkC13State pkSeed pkRoot message sig))))))).bindings
          "merkleNode" =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          (c12FoldLayerRoot pkSeed 4
            (((C12Concrete.hMsgC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 16) / 16 / 16 / 16)
            (c12UnrolledLayerRoot3 pkSeed
              (C12Concrete.hMsgC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex
              ((C12Concrete.forsPkFromSigC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot }
                  (C12Concrete.hMsgC12 c12
                    { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
                  sigParsed.fors).getD ⟨#[]⟩)
              sigParsed.layers)
            ((sigParsed.layers[4]?).getD c12EmptyXmssLayerSig)) := by
  intro pkSeed pkRoot message sig sigParsed hParse
  let digest :=
    C12Concrete.hMsgC12 c12
      { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message
  let idxTree := c12Layer4IdxTree digest.hyperIndex
  let node :=
    c12UnrolledLayerRoot3 pkSeed digest.hyperIndex
      ((C12Concrete.forsPkFromSigC12 c12
          { pkSeed := pkSeed, pkRoot := pkRoot } digest sigParsed.fors).getD ⟨#[]⟩)
      sigParsed.layers
  let layer4Sig := (sigParsed.layers[4]?).getD c12EmptyXmssLayerSig
  have hRaw := hLayer4RawXmss pkSeed pkRoot message sig sigParsed hParse
  change lookupValue
      (C12SegmentWotsSetup.c12LayerStateAfterXmssLoop
        (C12SegmentWotsSetup.c12LayerStateBeforeXmssLoop
          (c12LayerBodyInput4
            (C12SegmentForsCompress.c12StepForsCompress
              (C12SegmentFors.c12StepFors
                (C12SegmentSeed.c12StepSeed
                  (MkC13State.mkC13State pkSeed pkRoot message sig))))))).bindings
      "merkleNode" =
    SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
      (c12FoldLayerRoot pkSeed 4 idxTree node layer4Sig)
  exact c12_wots_xmss_roundtrip_of_raw_xmssClimb_at_layer
    pkSeed 4 idxTree node layer4Sig _ (by
      simpa [idxTree, node, layer4Sig, c12Layer4NextTree, c12Layer4Leaf] using hRaw)

/-- Layer 4's prefix `"merkleNode"` fact follows from the smaller WOTS/XMSS
roundtrip for that single layer.  The premise is phrased at the exact executable
XMSS-loop boundary after the WOTS digest/checksum/public-key-copy setup; this
theorem only connects that boundary back to the layer prefix and re-expands the
already named unrolled layer-root expression. -/
theorem c12_layer4_before_current_node_merkleNode_of_wots_xmss_roundtrip
    (hLayer4WotsXmss :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (C12SegmentWotsSetup.c12LayerStateAfterXmssLoop
            (C12SegmentWotsSetup.c12LayerStateBeforeXmssLoop
              (c12LayerBodyInput4
                (C12SegmentForsCompress.c12StepForsCompress
                  (C12SegmentFors.c12StepFors
                    (C12SegmentSeed.c12StepSeed
                      (MkC13State.mkC13State pkSeed pkRoot message sig))))))).bindings
          "merkleNode" =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          (c12FoldLayerRoot pkSeed 4
            (((C12Concrete.hMsgC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 16) / 16 / 16 / 16)
            (c12UnrolledLayerRoot3 pkSeed
              (C12Concrete.hMsgC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex
              ((C12Concrete.forsPkFromSigC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot }
                  (C12Concrete.hMsgC12 c12
                    { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
                  sigParsed.fors).getD ⟨#[]⟩)
              sigParsed.layers)
            ((sigParsed.layers[4]?).getD c12EmptyXmssLayerSig))) :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (C12SegmentWotsSetup.c12LayerStateBeforeCurrentNode
            (c12LayerBodyInput4
              (C12SegmentForsCompress.c12StepForsCompress
                (C12SegmentFors.c12StepFors
                  (C12SegmentSeed.c12StepSeed
                    (MkC13State.mkC13State pkSeed pkRoot message sig)))))).bindings
          "merkleNode" =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          (c12UnrolledLayerRoot4 pkSeed
            (C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex
            ((C12Concrete.forsPkFromSigC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot }
                (C12Concrete.hMsgC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
                sigParsed.fors).getD ⟨#[]⟩)
            sigParsed.layers) := by
  intro pkSeed pkRoot message sig sigParsed hParse
  rw [C12SegmentWotsSetup.c12LayerStateBeforeCurrentNode_merkleNode_eq_afterXmssLoop]
  exact hLayer4WotsXmss pkSeed pkRoot message sig sigParsed hParse

/-- The final C12 layer-loop `currentNode` fact is reduced one statement past
the hard XMSS correspondence: it is enough to prove the single layer-4 WOTS/XMSS
roundtrip that computes `"merkleNode"` from the named post-WOTS XMSS loop. -/
theorem c12_layer_root4_current_node_of_layer4_wots_xmss_roundtrip
    (hLayer4WotsXmss :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (C12SegmentWotsSetup.c12LayerStateAfterXmssLoop
            (C12SegmentWotsSetup.c12LayerStateBeforeXmssLoop
              (c12LayerBodyInput4
                (C12SegmentForsCompress.c12StepForsCompress
                  (C12SegmentFors.c12StepFors
                    (C12SegmentSeed.c12StepSeed
                      (MkC13State.mkC13State pkSeed pkRoot message sig))))))).bindings
          "merkleNode" =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          (c12FoldLayerRoot pkSeed 4
            (((C12Concrete.hMsgC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 16) / 16 / 16 / 16)
            (c12UnrolledLayerRoot3 pkSeed
              (C12Concrete.hMsgC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex
              ((C12Concrete.forsPkFromSigC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot }
                  (C12Concrete.hMsgC12 c12
                    { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
                  sigParsed.fors).getD ⟨#[]⟩)
              sigParsed.layers)
            ((sigParsed.layers[4]?).getD c12EmptyXmssLayerSig))) :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (C12SegmentWotsSetup.c12StepLayerLoop
            (C12SegmentForsCompress.c12StepForsCompress
              (C12SegmentFors.c12StepFors
                (C12SegmentSeed.c12StepSeed
                  (MkC13State.mkC13State pkSeed pkRoot message sig))))).bindings
          "currentNode" =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          (c12UnrolledLayerRoot4 pkSeed
            (C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex
            ((C12Concrete.forsPkFromSigC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot }
                (C12Concrete.hMsgC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
                sigParsed.fors).getD ⟨#[]⟩)
            sigParsed.layers) := by
  intro pkSeed pkRoot message sig sigParsed hParse
  rw [c12StepLayerLoop_eq_layerStateAfter4]
  rw [c12LayerStateAfter4_currentNode_eq_layer4_beforeCurrentNode_merkleNode]
  exact c12_layer4_before_current_node_merkleNode_of_wots_xmss_roundtrip
    hLayer4WotsXmss pkSeed pkRoot message sig sigParsed hParse

def c12Layer0PreBodyState
    (pkSeed pkRoot message sig : ByteArray) : RuntimeState :=
  c12LayerBodyInput0
    (C12SegmentForsCompress.c12StepForsCompress
      (C12SegmentFors.c12StepFors
        (C12SegmentSeed.c12StepSeed
          (MkC13State.mkC13State pkSeed pkRoot message sig))))

def c12Layer0XmssEntryState
    (pkSeed pkRoot message sig : ByteArray) : RuntimeState :=
  C12SegmentWotsSetup.c12LayerStateBeforeXmssLoop
    (c12Layer0PreBodyState pkSeed pkRoot message sig)

def c12Layer0ParsedSeed (pkSeed : ByteArray) : Nat :=
  SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed

def c12Layer0ParsedMessage
    (pkSeed pkRoot message : ByteArray) (sigParsed : Signature) :=
  C12Concrete.hMsgC12 c12
    { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message

def c12Layer0ParsedBase
    (pkSeed pkRoot message : ByteArray) (sigParsed : Signature) : Nat :=
  C12Concrete.xmssBaseC12 0
    ((c12Layer0ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex / 16)

def c12Layer0ParsedLeaf
    (pkSeed pkRoot message : ByteArray) (sigParsed : Signature) : Nat :=
  (c12Layer0ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex % 16

def c12Layer0ParsedStartNode
    (pkSeed pkRoot message : ByteArray) (sigParsed : Signature) : Nat :=
  C12Concrete.wotsPkWordC12
    (c12Layer0ParsedSeed pkSeed)
    0
    ((c12Layer0ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex / 16)
    (c12Layer0ParsedLeaf pkSeed pkRoot message sigParsed)
    (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
      ((C12Concrete.forsPkFromSigC12 c12
          { pkSeed := pkSeed, pkRoot := pkRoot }
          (c12Layer0ParsedMessage pkSeed pkRoot message sigParsed)
          sigParsed.fors).getD ⟨#[]⟩))
    ((sigParsed.layers[0]?).getD c12EmptyXmssLayerSig).wots

def c12Layer0ParsedAuth (sigParsed : Signature) :
    List SphincsMinusVerifierSpec.Bytes :=
  ((sigParsed.layers[0]?).getD c12EmptyXmssLayerSig).authPath

def c12Layer0ParsedAuthCdAt
    (pkSeed pkRoot message sig : ByteArray) (i : Nat) : Nat :=
  Compiler.Proofs.YulGeneration.calldataloadWord 0
    (MkC13State.headWords pkSeed pkRoot message sig.size ++
      MkC13State.bytesToWords sig)
    (MkC13State.sigDataOffset + (2592 + 720 + 16 * i))

/-- Layer 0's concrete auth calldata reader discharges the generic
`MerkleClimbData` obligation once the parsed auth entry is known to be the
16-byte signature slice at the same byte offset. -/
theorem c12_layer0_MerkleClimbData_of_authPath_read16
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature) (i : Nat)
    (hauth :
      ((c12Layer0ParsedAuth sigParsed)[i]?).getD ⟨#[]⟩ =
        SphincsMinusVerifierSpec.C13Concrete.read16 sig
          (2592 + 720 + 16 * i)) :
    SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
      (c12Layer0ParsedAuth sigParsed)
      (c12Layer0ParsedAuthCdAt pkSeed pkRoot message sig) i := by
  refine
    SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleClimbData_of_frozenCalldata
      pkSeed pkRoot message sig
      (c12Layer0ParsedAuth sigParsed)
      (c12Layer0ParsedAuthCdAt pkSeed pkRoot message sig)
      i (2592 + 720 + 16 * i) ?_ hauth
  rfl

/-- Successful C12 parsing identifies each layer-0 auth node with the matching
16-byte signature slice from C12's first XMSS layout. -/
theorem c12_layer0_authPath_read16_range_of_parse
    (sig : ByteArray) (sigParsed : Signature)
    (hParse : C12Concrete.parseSignatureC12 c12 sig = some sigParsed) :
    ∀ i, i < wordNormalize 4 →
      ((c12Layer0ParsedAuth sigParsed)[i]?).getD ⟨#[]⟩ =
        SphincsMinusVerifierSpec.C13Concrete.read16 sig
          (2592 + 720 + 16 * i) := by
  intro i hi
  have hi4 : i < 4 := by
    simpa using hi
  have hSize : sig.size = c12.sigBytes :=
    parseSignatureC12_size_of_some hParse
  unfold C12Concrete.parseSignatureC12 at hParse
  simp only [hSize, ne_eq, not_true_eq_false, if_false, Option.some.injEq] at hParse
  subst hParse
  unfold c12Layer0ParsedAuth
  rw [SphincsMinusVerifierSpec.C13Concrete.getElem?_map_range _ (by decide : 0 < 5)]
  simp only [Option.getD_some]
  rw [SphincsMinusVerifierSpec.C13Concrete.getElem?_map_range _ hi4]
  rfl

/-- Parser-backed layer-0 `hDdata`: the parsed auth extraction premise is
discharged by the concrete C12 parser's layer indexing. -/
theorem c12_layer0_hDdata_of_parse
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature)
    (hParse : C12Concrete.parseSignatureC12 c12 sig = some sigParsed) :
    ∀ i, i < wordNormalize 4 →
      SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
        (c12Layer0ParsedAuth sigParsed)
        (c12Layer0ParsedAuthCdAt pkSeed pkRoot message sig) i := by
  intro i hi
  exact c12_layer0_MerkleClimbData_of_authPath_read16
    pkSeed pkRoot message sig sigParsed i
    (c12_layer0_authPath_read16_range_of_parse sig sigParsed hParse i hi)

/-- The parsed layer-0 WOTS start node is already an EVM-normalized word. -/
theorem c12Layer0ParsedStartNode_normalized
    (pkSeed pkRoot message : ByteArray) (sigParsed : Signature) :
    wordNormalize (c12Layer0ParsedStartNode pkSeed pkRoot message sigParsed) =
      c12Layer0ParsedStartNode pkSeed pkRoot message sigParsed := by
  unfold c12Layer0ParsedStartNode C12Concrete.wotsPkWordC12
  exact SphincsMinusVerifiers.ClimbMemFrameMerkle.wordNormalize_maskN _

/-- C12 FORS inner-step body does not rebind `"leafIdx"`.  Kept bridge-local so
layer-0 entry facts can thread the seed segment's leaf nibble through FORS. -/
private theorem c12ForsInnerBody_preserves_leafIdx :
    ∀ (s s'' : RuntimeState) (stmt : Compiler.CompilationModel.Stmt),
      stmt ∈ C12SegmentFors.c12ForsInnerBody →
      execStmt [] s stmt = .continue s'' →
      lookupValue s''.bindings "leafIdx" = lookupValue s.bindings "leafIdx" := by
  intro s s'' stmt hmem hexec
  simp only [C12SegmentFors.c12ForsInnerBody, List.mem_cons,
    List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "sibling" "leafIdx" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "parentIdx" "leafIdx" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "globalY" "leafIdx" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      _ _ "leafIdx" _ _ hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "s" "leafIdx" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      _ _ "leafIdx" _ _ hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      _ _ "leafIdx" _ _ hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
      _ _ "node" "leafIdx" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
      _ _ "pathIdx" "leafIdx" _ (by decide) hexec

/-- C12 FORS outer-step body does not rebind `"leafIdx"`. -/
private theorem c12ForsOuterBody_preserves_leafIdx :
    ∀ (s s'' : RuntimeState) (stmt : Compiler.CompilationModel.Stmt),
      stmt ∈ C12SegmentFors.c12ForsOuterBody →
      execStmt [] s stmt = .continue s'' →
      lookupValue s''.bindings "leafIdx" = lookupValue s.bindings "leafIdx" := by
  intro s s'' stmt hmem hexec
  simp only [C12SegmentFors.c12ForsOuterBody, List.mem_cons,
    List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "mdT" "leafIdx" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "treeOff" "leafIdx" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "sk" "leafIdx" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      _ _ "leafIdx" _ _ hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      _ _ "leafIdx" _ _ hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "node" "leafIdx" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "authPtr" "leafIdx" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "pathIdx" "leafIdx" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
      "j" "leafIdx" _ _ _ _ (by decide)
      c12ForsInnerBody_preserves_leafIdx hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      _ _ "leafIdx" _ _ hexec

/-- The C12 FORS reconstruction loop preserves `"leafIdx"`. -/
theorem c12StepFors_preserves_leafIdx (st : RuntimeState) :
    lookupValue (C12SegmentFors.c12StepFors st).bindings "leafIdx" =
      lookupValue st.bindings "leafIdx" :=
  SphincsMinusVerifiers.BindingFrame.execStmtList_preserves_lookup
    "leafIdx" [C12SegmentFors.c12ForsOuterStmt] st
    (C12SegmentFors.c12StepFors st)
    (by
      intro s s'' stmt hmem hexec
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      subst hmem
      exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
        "t" "leafIdx" _ _ _ _ (by decide)
        c12ForsOuterBody_preserves_leafIdx hexec)
    (C12SegmentFors.execC12ForsOuter st)

private theorem c12_packed_hyperIndex_mod16 (treeIdx leafIdx : Nat)
    (hLeaf : leafIdx < 2 ^ 4) :
    ((treeIdx <<< 4) ||| leafIdx) % 16 = leafIdx := by
  change ((treeIdx <<< 4) ||| leafIdx) % 2 ^ 4 = leafIdx
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_lor]
  by_cases hi : i < 4
  · have hshift : (treeIdx <<< 4).testBit i = false := by
      simp [Nat.testBit_shiftLeft, hi]
    rw [hshift, Bool.false_or]
    simp [hi]
  · have hleaf : leafIdx.testBit i = false :=
      Nat.testBit_eq_false_of_lt
        (lt_of_lt_of_le hLeaf
          (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_not_gt hi)))
    rw [hleaf, Bool.or_false]
    rw [Nat.testBit_shiftLeft]
    simp [hi]

/-- The layer-0 parsed leaf is exactly the executable leaf nibble selected by
`c12StepSeed`. -/
theorem c12Layer0ParsedLeaf_eq_hMsgC12_leaf
    (pkSeed pkRoot message : ByteArray) (sigParsed : Signature) :
    c12Layer0ParsedLeaf pkSeed pkRoot message sigParsed =
      (SphincsMinusVerifierSpec.C13Concrete.keccakWords
        [ SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed
        , SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkRoot
        , SphincsMinusVerifierSpec.C13Concrete.baToNatBE sigParsed.R %
            SphincsMinusVerifierSpec.C13Concrete.wordMod
        , SphincsMinusVerifierSpec.C13Concrete.baToNatBE message %
            SphincsMinusVerifierSpec.C13Concrete.wordMod
        , C12Concrete.hMsgPad ] >>> 156) % (2 ^ 4) := by
  unfold c12Layer0ParsedLeaf c12Layer0ParsedMessage C12Concrete.hMsgC12
  exact c12_packed_hyperIndex_mod16 _ _
    (Nat.mod_lt _ (by decide : 0 < 2 ^ 4))

/-- The layer-0 pre-XMSS-node WOTS prefix preserves and exposes the parsed
`"curLeaf"` handoff. -/
theorem c12_layer0_before_xmss_node_curLeaf
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature)
    (hParse : C12Concrete.parseSignatureC12 c12 sig = some sigParsed) :
    lookupValue
      (C12SegmentWotsSetup.c12LayerStateBeforeXmssNode
        (c12Layer0PreBodyState pkSeed pkRoot message sig)).bindings
      "curLeaf" =
    c12Layer0ParsedLeaf pkSeed pkRoot message sigParsed := by
  rw [C12SegmentWotsSetup.c12LayerStateBeforeXmssNode_curLeaf_eq]
  unfold c12Layer0PreBodyState c12LayerBodyInput0
  rw [MemoryKit.lookupValue_bindValue_ne _ "layer" "curLeaf" _ (by decide)]
  rw [C12SegmentForsCompress.c12StepForsCompress_curLeaf_eq]
  rw [c12StepFors_preserves_leafIdx]
  rw [C12SegmentSeed.c12StepSeed_leafIdx_hMsgC12_words
    pkSeed pkRoot message sig sigParsed hParse]
  exact (c12Layer0ParsedLeaf_eq_hMsgC12_leaf
    pkSeed pkRoot message sigParsed).symm

/-- The layer-0 pre-XMSS-node address setup runs after `"wotsPk"` has been
computed, so the exact WOTS-public-key boundary can be handed from
`BeforeAuthOff` to the XMSS-node entry state. -/
theorem c12_layer0_before_xmss_node_wotsPk_of_before_authOff
    (hLayer0WotsPkBeforeAuthOff :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (C12SegmentWotsSetup.c12LayerStateBeforeAuthOff
            (c12Layer0PreBodyState pkSeed pkRoot message sig)).bindings
          "wotsPk" =
        c12Layer0ParsedStartNode pkSeed pkRoot message sigParsed) :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (C12SegmentWotsSetup.c12LayerStateBeforeXmssNode
            (c12Layer0PreBodyState pkSeed pkRoot message sig)).bindings
          "wotsPk" =
        c12Layer0ParsedStartNode pkSeed pkRoot message sigParsed := by
  intro pkSeed pkRoot message sig sigParsed hParse
  rw [C12SegmentWotsSetup.c12LayerStateBeforeXmssNode_wotsPk_eq_beforeAuthOff]
  exact hLayer0WotsPkBeforeAuthOff pkSeed pkRoot message sig sigParsed hParse

/-- The layer-0 XMSS initial raw relation reduces to the exact entry-state
`"curLeaf"` and pre-node `"wotsPk"` boundary facts. -/
theorem c12_layer0_initial_raw_rel_of_entry_bindings
    (hLayer0CurLeafBeforeNode :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (C12SegmentWotsSetup.c12LayerStateBeforeXmssNode
            (c12Layer0PreBodyState pkSeed pkRoot message sig)).bindings
          "curLeaf" =
        c12Layer0ParsedLeaf pkSeed pkRoot message sigParsed)
    (hLayer0WotsPkBeforeNode :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (C12SegmentWotsSetup.c12LayerStateBeforeXmssNode
            (c12Layer0PreBodyState pkSeed pkRoot message sig)).bindings
          "wotsPk" =
        c12Layer0ParsedStartNode pkSeed pkRoot message sigParsed) :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
          "merkleNode" "mIdx"
          { (c12Layer0XmssEntryState pkSeed pkRoot message sig) with
            bindings :=
              bindValue
                (c12Layer0XmssEntryState pkSeed pkRoot message sig).bindings
                "h" (wordNormalize 0) }
          (c12Layer0ParsedLeaf pkSeed pkRoot message sigParsed,
            c12Layer0ParsedStartNode pkSeed pkRoot message sigParsed) := by
  intro pkSeed pkRoot message sig sigParsed hParse
  let st0 :=
    C12SegmentWotsSetup.c12LayerStateBeforeXmssNode
      (c12Layer0PreBodyState pkSeed pkRoot message sig)
  have hIdx :
      lookupValue
          (bindValue (c12Layer0XmssEntryState pkSeed pkRoot message sig).bindings
            "h" (wordNormalize 0))
          "mIdx" =
        c12Layer0ParsedLeaf pkSeed pkRoot message sigParsed := by
    unfold c12Layer0XmssEntryState C12SegmentWotsSetup.c12LayerStateBeforeXmssLoop
    rw [C12SegmentWotsSetup.c12LayerBodyBeforeXmssLoop_eq_beforeNode_append]
    rw [MemoryKit.execStmtList_append_continue _ _ _ _
      (C12SegmentWotsSetup.execC12LayerBodyBeforeXmssNode _)]
    rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ _
      (MemoryKit.execStmt_letVar_continue st0 "merkleNode" _ _ rfl)]
    rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ _
      (MemoryKit.execStmt_letVar_continue _ "mIdx" _ _ rfl)]
    change
      lookupValue
          (bindValue
            (bindValue
              (bindValue st0.bindings "merkleNode" (lookupValue st0.bindings "wotsPk"))
              "mIdx"
              (lookupValue
                (bindValue st0.bindings "merkleNode" (lookupValue st0.bindings "wotsPk"))
                "curLeaf"))
            "h" (wordNormalize 0))
          "mIdx" =
        c12Layer0ParsedLeaf pkSeed pkRoot message sigParsed
    rw [MemoryKit.lookupValue_bindValue_ne _ "h" "mIdx" _ (by decide)]
    rw [MemoryKit.lookupValue_bindValue_self]
    rw [MemoryKit.lookupValue_bindValue_ne _ "merkleNode" "curLeaf" _ (by decide)]
    exact hLayer0CurLeafBeforeNode pkSeed pkRoot message sig sigParsed hParse
  have hNode :
      lookupValue
          (bindValue (c12Layer0XmssEntryState pkSeed pkRoot message sig).bindings
            "h" (wordNormalize 0))
          "merkleNode" =
        c12Layer0ParsedStartNode pkSeed pkRoot message sigParsed := by
    unfold c12Layer0XmssEntryState C12SegmentWotsSetup.c12LayerStateBeforeXmssLoop
    rw [C12SegmentWotsSetup.c12LayerBodyBeforeXmssLoop_eq_beforeNode_append]
    rw [MemoryKit.execStmtList_append_continue _ _ _ _
      (C12SegmentWotsSetup.execC12LayerBodyBeforeXmssNode _)]
    rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ _
      (MemoryKit.execStmt_letVar_continue st0 "merkleNode" _ _ rfl)]
    rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ _
      (MemoryKit.execStmt_letVar_continue _ "mIdx" _ _ rfl)]
    change
      lookupValue
          (bindValue
            (bindValue
              (bindValue st0.bindings "merkleNode" (lookupValue st0.bindings "wotsPk"))
              "mIdx"
              (lookupValue
                (bindValue st0.bindings "merkleNode" (lookupValue st0.bindings "wotsPk"))
                "curLeaf"))
            "h" (wordNormalize 0))
          "merkleNode" =
        c12Layer0ParsedStartNode pkSeed pkRoot message sigParsed
    rw [MemoryKit.lookupValue_bindValue_ne _ "h" "merkleNode" _ (by decide)]
    rw [MemoryKit.lookupValue_bindValue_ne _ "mIdx" "merkleNode" _ (by decide)]
    rw [MemoryKit.lookupValue_bindValue_self]
    exact hLayer0WotsPkBeforeNode pkSeed pkRoot message sig sigParsed hParse
  exact SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel.intro
    hIdx hNode (c12Layer0ParsedStartNode_normalized pkSeed pkRoot message sigParsed)

/-- Layer-0 raw executable XMSS correspondence reduced to the generic Merkle
fold obligations.  This is the layer-0 analogue of the layer-4 raw fold
pipeline, specialized to `c12LayerBodyInput0` and the first C12 XMSS slice. -/
theorem c12_layer0_raw_xmss_of_raw_merkle_fold_obligations
    (hLayer0RawFoldObligations :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
          (∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat),
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
              (c12Layer0ParsedAuth sigParsed)
              (c12Layer0ParsedAuthCdAt pkSeed pkRoot message sig) idx →
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
              "merkleNode" "mIdx" s a →
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
              "merkleNode" "mIdx"
                (SphincsMinusVerifiers.ClimbKit.stepMerkle
                  "merkleNode" "mIdx" "xmssBase" "authPtr"
                  { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
                (SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleSpecStep
                  (c12Layer0ParsedSeed pkSeed)
                  (c12Layer0ParsedBase pkSeed pkRoot message sigParsed)
                  (c12Layer0ParsedAuth sigParsed) idx a))
          ∧ (∀ i, i < wordNormalize 4 →
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
              (c12Layer0ParsedAuth sigParsed)
              (c12Layer0ParsedAuthCdAt pkSeed pkRoot message sig) i)
          ∧ SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
              "merkleNode" "mIdx"
              { (c12Layer0XmssEntryState pkSeed pkRoot message sig) with
                bindings :=
                  bindValue
                    (c12Layer0XmssEntryState pkSeed pkRoot message sig).bindings
                    "h" (wordNormalize 0) }
              (c12Layer0ParsedLeaf pkSeed pkRoot message sigParsed,
                c12Layer0ParsedStartNode pkSeed pkRoot message sigParsed)) :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (C12SegmentWotsSetup.c12LayerStateAfterXmssLoop
            (C12SegmentWotsSetup.c12LayerStateBeforeXmssLoop
              (c12LayerBodyInput0
                (C12SegmentForsCompress.c12StepForsCompress
                  (C12SegmentFors.c12StepFors
                    (C12SegmentSeed.c12StepSeed
                      (MkC13State.mkC13State pkSeed pkRoot message sig))))))).bindings
          "merkleNode" =
        SphincsMinusVerifierSpec.C13Concrete.xmssClimb
          (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed)
          (C12Concrete.xmssBaseC12 0
            ((C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 16))
          4 0
          ((C12Concrete.hMsgC12 c12
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex % 16)
          (C12Concrete.wotsPkWordC12
            (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed)
            0
            ((C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 16)
            ((C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex % 16)
            (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
              ((C12Concrete.forsPkFromSigC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot }
                  (C12Concrete.hMsgC12 c12
                    { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
                  sigParsed.fors).getD ⟨#[]⟩))
            ((sigParsed.layers[0]?).getD c12EmptyXmssLayerSig).wots)
          ((sigParsed.layers[0]?).getD c12EmptyXmssLayerSig).authPath := by
  intro pkSeed pkRoot message sig sigParsed hParse
  rcases hLayer0RawFoldObligations pkSeed pkRoot message sig sigParsed hParse with
    ⟨hstep, hDdata, hR⟩
  rw [C12SegmentWotsSetup.c12LayerStateAfterXmssLoop_eq_merkleFold]
  let cdAt := c12Layer0ParsedAuthCdAt pkSeed pkRoot message sig
  have hD :
      ∀ i, 0 ≤ i → i < 0 + wordNormalize 4 →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
          (c12Layer0ParsedAuth sigParsed) cdAt i := by
    intro i _ hi
    exact hDdata i (by simpa using hi)
  simpa [c12Layer0XmssEntryState, c12Layer0PreBodyState, c12Layer0ParsedSeed,
    c12Layer0ParsedBase, c12Layer0ParsedAuth, c12Layer0ParsedAuthCdAt,
    c12Layer0ParsedStartNode, c12Layer0ParsedLeaf, c12Layer0ParsedMessage, cdAt]
    using
      SphincsMinusVerifiers.ClimbMemFrameMerkle.xmssClimbRaw_model_node
        "merkleNode" "mIdx" "xmssBase" "authPtr"
        (c12Layer0ParsedSeed pkSeed)
        (c12Layer0ParsedBase pkSeed pkRoot message sigParsed)
        (c12Layer0ParsedAuth sigParsed) cdAt hstep
        { (c12Layer0XmssEntryState pkSeed pkRoot message sig) with
          bindings :=
            bindValue (c12Layer0XmssEntryState pkSeed pkRoot message sig).bindings
              "h" (wordNormalize 0) }
        (c12Layer0ParsedLeaf pkSeed pkRoot message sigParsed)
        (c12Layer0ParsedStartNode pkSeed pkRoot message sigParsed)
        0 (wordNormalize 4) hD hR

/-- Parser-data variant of the layer-0 raw executable XMSS correspondence.
The calldata/auth-path range is discharged, leaving only the per-step raw
advance and initial raw entry relation. -/
theorem c12_layer0_raw_xmss_of_step_and_initial_raw
    (hLayer0StepRawAdvance :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
          ∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat),
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
              (c12Layer0ParsedAuth sigParsed)
              (c12Layer0ParsedAuthCdAt pkSeed pkRoot message sig) idx →
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
              "merkleNode" "mIdx" s a →
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
              "merkleNode" "mIdx"
                (SphincsMinusVerifiers.ClimbKit.stepMerkle
                  "merkleNode" "mIdx" "xmssBase" "authPtr"
                  { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
                (SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleSpecStep
                  (c12Layer0ParsedSeed pkSeed)
                  (c12Layer0ParsedBase pkSeed pkRoot message sigParsed)
                  (c12Layer0ParsedAuth sigParsed) idx a))
    (hLayer0InitialRaw :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
          "merkleNode" "mIdx"
          { (c12Layer0XmssEntryState pkSeed pkRoot message sig) with
            bindings :=
              bindValue
                (c12Layer0XmssEntryState pkSeed pkRoot message sig).bindings
                "h" (wordNormalize 0) }
          (c12Layer0ParsedLeaf pkSeed pkRoot message sigParsed,
            c12Layer0ParsedStartNode pkSeed pkRoot message sigParsed)) :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (C12SegmentWotsSetup.c12LayerStateAfterXmssLoop
            (C12SegmentWotsSetup.c12LayerStateBeforeXmssLoop
              (c12LayerBodyInput0
                (C12SegmentForsCompress.c12StepForsCompress
                  (C12SegmentFors.c12StepFors
                    (C12SegmentSeed.c12StepSeed
                      (MkC13State.mkC13State pkSeed pkRoot message sig))))))).bindings
          "merkleNode" =
        SphincsMinusVerifierSpec.C13Concrete.xmssClimb
          (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed)
          (C12Concrete.xmssBaseC12 0
            ((C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 16))
          4 0
          ((C12Concrete.hMsgC12 c12
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex % 16)
          (C12Concrete.wotsPkWordC12
            (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed)
            0
            ((C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 16)
            ((C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex % 16)
            (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
              ((C12Concrete.forsPkFromSigC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot }
                  (C12Concrete.hMsgC12 c12
                    { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
                  sigParsed.fors).getD ⟨#[]⟩))
            ((sigParsed.layers[0]?).getD c12EmptyXmssLayerSig).wots)
          ((sigParsed.layers[0]?).getD c12EmptyXmssLayerSig).authPath := by
  refine c12_layer0_raw_xmss_of_raw_merkle_fold_obligations ?_
  intro pkSeed pkRoot message sig sigParsed hParse
  exact ⟨
    hLayer0StepRawAdvance pkSeed pkRoot message sig sigParsed hParse,
    c12_layer0_hDdata_of_parse pkSeed pkRoot message sig sigParsed hParse,
    hLayer0InitialRaw pkSeed pkRoot message sig sigParsed hParse⟩

/-- Entry-binding variant of the layer-0 raw executable XMSS correspondence.
Parser auth-data and the initial raw adapter are discharged; the residuals are
the per-step raw advance plus the two pre-XMSS-node handoff bindings. -/
theorem c12_layer0_raw_xmss_of_step_and_entry_bindings
    (hLayer0StepRawAdvance :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
          ∀ (s : RuntimeState) (a : Nat × Nat) (idx : Nat),
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbData
              (c12Layer0ParsedAuth sigParsed)
              (c12Layer0ParsedAuthCdAt pkSeed pkRoot message sig) idx →
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
              "merkleNode" "mIdx" s a →
            SphincsMinusVerifiers.ClimbMemFrameMerkle.MerkleClimbRawRel
              "merkleNode" "mIdx"
                (SphincsMinusVerifiers.ClimbKit.stepMerkle
                  "merkleNode" "mIdx" "xmssBase" "authPtr"
                  { s with bindings := bindValue s.bindings "h" (wordNormalize idx) })
                (SphincsMinusVerifiers.ClimbMemFrameMerkle.merkleSpecStep
                  (c12Layer0ParsedSeed pkSeed)
                  (c12Layer0ParsedBase pkSeed pkRoot message sigParsed)
                  (c12Layer0ParsedAuth sigParsed) idx a))
    (hLayer0CurLeafBeforeNode :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (C12SegmentWotsSetup.c12LayerStateBeforeXmssNode
            (c12Layer0PreBodyState pkSeed pkRoot message sig)).bindings
          "curLeaf" =
        c12Layer0ParsedLeaf pkSeed pkRoot message sigParsed)
    (hLayer0WotsPkBeforeNode :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (C12SegmentWotsSetup.c12LayerStateBeforeXmssNode
            (c12Layer0PreBodyState pkSeed pkRoot message sig)).bindings
          "wotsPk" =
        c12Layer0ParsedStartNode pkSeed pkRoot message sigParsed) :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (C12SegmentWotsSetup.c12LayerStateAfterXmssLoop
            (C12SegmentWotsSetup.c12LayerStateBeforeXmssLoop
              (c12LayerBodyInput0
                (C12SegmentForsCompress.c12StepForsCompress
                  (C12SegmentFors.c12StepFors
                    (C12SegmentSeed.c12StepSeed
                      (MkC13State.mkC13State pkSeed pkRoot message sig))))))).bindings
          "merkleNode" =
        SphincsMinusVerifierSpec.C13Concrete.xmssClimb
          (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed)
          (C12Concrete.xmssBaseC12 0
            ((C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 16))
          4 0
          ((C12Concrete.hMsgC12 c12
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex % 16)
          (C12Concrete.wotsPkWordC12
            (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed)
            0
            ((C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 16)
            ((C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex % 16)
            (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
              ((C12Concrete.forsPkFromSigC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot }
                  (C12Concrete.hMsgC12 c12
                    { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
                  sigParsed.fors).getD ⟨#[]⟩))
            ((sigParsed.layers[0]?).getD c12EmptyXmssLayerSig).wots)
          ((sigParsed.layers[0]?).getD c12EmptyXmssLayerSig).authPath := by
  refine c12_layer0_raw_xmss_of_step_and_initial_raw hLayer0StepRawAdvance ?_
  exact c12_layer0_initial_raw_rel_of_entry_bindings
    hLayer0CurLeafBeforeNode hLayer0WotsPkBeforeNode

/-- The layer-0 XMSS byte-root residual follows from the raw executable
`xmssClimb` word correspondence.  This is the layer-0 analogue of
`c12_layer4_wots_xmss_roundtrip_of_raw_xmssClimb`, with the first layer's
start node supplied directly by the FORS-compress root. -/
theorem c12_layer0_wots_xmss_roundtrip_of_raw_xmssClimb
    (hLayer0RawXmss :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (C12SegmentWotsSetup.c12LayerStateAfterXmssLoop
            (C12SegmentWotsSetup.c12LayerStateBeforeXmssLoop
              (c12LayerBodyInput0
                (C12SegmentForsCompress.c12StepForsCompress
                  (C12SegmentFors.c12StepFors
                    (C12SegmentSeed.c12StepSeed
                      (MkC13State.mkC13State pkSeed pkRoot message sig))))))).bindings
          "merkleNode" =
        SphincsMinusVerifierSpec.C13Concrete.xmssClimb
          (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed)
          (C12Concrete.xmssBaseC12 0
            ((C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 16))
          4 0
          ((C12Concrete.hMsgC12 c12
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex % 16)
          (C12Concrete.wotsPkWordC12
            (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed)
            0
            ((C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 16)
            ((C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex % 16)
            (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
              ((C12Concrete.forsPkFromSigC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot }
                  (C12Concrete.hMsgC12 c12
                    { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
                  sigParsed.fors).getD ⟨#[]⟩))
            ((sigParsed.layers[0]?).getD c12EmptyXmssLayerSig).wots)
          ((sigParsed.layers[0]?).getD c12EmptyXmssLayerSig).authPath) :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (C12SegmentWotsSetup.c12LayerStateAfterXmssLoop
            (C12SegmentWotsSetup.c12LayerStateBeforeXmssLoop
              (c12LayerBodyInput0
                (C12SegmentForsCompress.c12StepForsCompress
                  (C12SegmentFors.c12StepFors
                    (C12SegmentSeed.c12StepSeed
                      (MkC13State.mkC13State pkSeed pkRoot message sig))))))).bindings
          "merkleNode" =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          (c12FoldLayerRoot pkSeed 0
            (C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex
            ((C12Concrete.forsPkFromSigC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot }
                (C12Concrete.hMsgC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
                sigParsed.fors).getD ⟨#[]⟩)
            ((sigParsed.layers[0]?).getD c12EmptyXmssLayerSig)) := by
  intro pkSeed pkRoot message sig sigParsed hParse
  let digest :=
    C12Concrete.hMsgC12 c12
      { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message
  let idxTree := digest.hyperIndex
  let nextTree := idxTree / 16
  let idxLeaf := idxTree % 16
  let node :=
    (C12Concrete.forsPkFromSigC12 c12
      { pkSeed := pkSeed, pkRoot := pkRoot } digest sigParsed.fors).getD ⟨#[]⟩
  let layer0Sig := (sigParsed.layers[0]?).getD c12EmptyXmssLayerSig
  let wotsWord :=
    C12Concrete.wotsPkWordC12
      (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed)
      0 nextTree idxLeaf
      (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 node)
      layer0Sig.wots
  have hRaw := hLayer0RawXmss pkSeed pkRoot message sig sigParsed hParse
  change lookupValue
      (C12SegmentWotsSetup.c12LayerStateAfterXmssLoop
        (C12SegmentWotsSetup.c12LayerStateBeforeXmssLoop
          (c12LayerBodyInput0
            (C12SegmentForsCompress.c12StepForsCompress
              (C12SegmentFors.c12StepFors
                (C12SegmentSeed.c12StepSeed
                  (MkC13State.mkC13State pkSeed pkRoot message sig))))))).bindings
      "merkleNode" =
    SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
      (c12FoldLayerRoot pkSeed 0 idxTree node layer0Sig)
  rw [hRaw]
  have hWotsRoundtrip :
      SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          (SphincsMinusVerifierSpec.C13Concrete.hash16OfWord wotsWord) =
        wotsWord := by
    unfold wotsWord C12Concrete.wotsPkWordC12
    exact SegmentAcceptSpec.wordOfHash16_hash16OfWord_maskN_of_lt _ (by
      simpa [Compiler.Constants.evmModulus] using
        SphincsMinusVerifiers.KeccakBridge.keccakWords_lt
          ((SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed) ::
            C12Concrete.wotsPkAdrsC12 0 nextTree idxLeaf ::
            (List.range 45).map (fun i =>
              let digit :=
                if i < 42 then
                  C12Concrete.wotsDigitC12
                    (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 node) i
                else
                  ((C12Concrete.wotsCsumC12
                        (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 node) <<< 7) >>>
                      (13 - 3 * (i - 42))) %
                    8
              let steps := 7 - digit
              let val :=
                SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
                  ((layer0Sig.wots.chains[i]?).getD ⟨#[]⟩)
              let chainBase := C12Concrete.wotsBaseC12 0 nextTree idxLeaf ||| (i <<< 64)
              C12Concrete.chainHashC12
                (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed)
                chainBase digit steps 0 val)))
  have hXmssRoundtrip :=
    SegmentAcceptSpec.xmssClimb_roundtrip_of_node_roundtrip
      (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed)
      (C12Concrete.xmssBaseC12 0 nextTree)
      4 0 idxLeaf wotsWord layer0Sig.authPath hWotsRoundtrip
  unfold c12FoldLayerRoot at *
  change
    SphincsMinusVerifierSpec.C13Concrete.xmssClimb
      (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed)
      (C12Concrete.xmssBaseC12 0 (idxTree / 16)) 4 0 (idxTree % 16)
      wotsWord layer0Sig.authPath =
    SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
      (SphincsMinusVerifierSpec.C13Concrete.hash16OfWord
        (SphincsMinusVerifierSpec.C13Concrete.xmssClimb
          (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed)
          (C12Concrete.xmssBaseC12 0 (idxTree / 16)) 4 0 (idxTree % 16)
          (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
            (SphincsMinusVerifierSpec.C13Concrete.hash16OfWord wotsWord))
          layer0Sig.authPath))
  rw [hWotsRoundtrip]
  exact hXmssRoundtrip.symm

/-- Layer 0's pre-current-node `"merkleNode"` fact follows from the smaller
WOTS/XMSS roundtrip at the exact post-XMSS-loop boundary. -/
theorem c12_layer0_before_current_node_merkleNode_of_wots_xmss_roundtrip
    (hLayer0WotsXmss :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (C12SegmentWotsSetup.c12LayerStateAfterXmssLoop
            (C12SegmentWotsSetup.c12LayerStateBeforeXmssLoop
              (c12LayerBodyInput0
                (C12SegmentForsCompress.c12StepForsCompress
                  (C12SegmentFors.c12StepFors
                    (C12SegmentSeed.c12StepSeed
                      (MkC13State.mkC13State pkSeed pkRoot message sig))))))).bindings
          "merkleNode" =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          (c12FoldLayerRoot pkSeed 0
            (C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex
            ((C12Concrete.forsPkFromSigC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot }
                (C12Concrete.hMsgC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
                sigParsed.fors).getD ⟨#[]⟩)
            ((sigParsed.layers[0]?).getD c12EmptyXmssLayerSig))) :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (C12SegmentWotsSetup.c12LayerStateBeforeCurrentNode
            (c12LayerBodyInput0
              (C12SegmentForsCompress.c12StepForsCompress
                (C12SegmentFors.c12StepFors
                  (C12SegmentSeed.c12StepSeed
                    (MkC13State.mkC13State pkSeed pkRoot message sig)))))).bindings
          "merkleNode" =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          (c12UnrolledLayerRoot0 pkSeed
            (C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex
            ((C12Concrete.forsPkFromSigC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot }
                (C12Concrete.hMsgC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
                sigParsed.fors).getD ⟨#[]⟩)
            sigParsed.layers) := by
  intro pkSeed pkRoot message sig sigParsed hParse
  rw [C12SegmentWotsSetup.c12LayerStateBeforeCurrentNode_merkleNode_eq_afterXmssLoop]
  exact hLayer0WotsXmss pkSeed pkRoot message sig sigParsed hParse

/-- The layer-0 `currentNode` obligation reduces to the post-XMSS WOTS/XMSS
roundtrip for that single layer. -/
theorem c12_layer0_current_node_of_layer0_wots_xmss_roundtrip
    (hLayer0WotsXmss :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (C12SegmentWotsSetup.c12LayerStateAfterXmssLoop
            (C12SegmentWotsSetup.c12LayerStateBeforeXmssLoop
              (c12LayerBodyInput0
                (C12SegmentForsCompress.c12StepForsCompress
                  (C12SegmentFors.c12StepFors
                    (C12SegmentSeed.c12StepSeed
                      (MkC13State.mkC13State pkSeed pkRoot message sig))))))).bindings
          "merkleNode" =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          (c12FoldLayerRoot pkSeed 0
            (C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex
            ((C12Concrete.forsPkFromSigC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot }
                (C12Concrete.hMsgC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
                sigParsed.fors).getD ⟨#[]⟩)
            ((sigParsed.layers[0]?).getD c12EmptyXmssLayerSig))) :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (c12LayerStateAfter0
            (C12SegmentForsCompress.c12StepForsCompress
              (C12SegmentFors.c12StepFors
                (C12SegmentSeed.c12StepSeed
                  (MkC13State.mkC13State pkSeed pkRoot message sig))))).bindings
          "currentNode" =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          (c12UnrolledLayerRoot0 pkSeed
            (C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex
            ((C12Concrete.forsPkFromSigC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot }
                (C12Concrete.hMsgC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
                sigParsed.fors).getD ⟨#[]⟩)
            sigParsed.layers) := by
  intro pkSeed pkRoot message sig sigParsed hParse
  rw [c12LayerStateAfter0_currentNode_eq_layer0_beforeCurrentNode_merkleNode]
  exact c12_layer0_before_current_node_merkleNode_of_wots_xmss_roundtrip
    hLayer0WotsXmss pkSeed pkRoot message sig sigParsed hParse

/-- Strongest currently exposed layer-0 reducer: the requested post-layer-0
`"currentNode"` fact follows once the raw executable XMSS loop is identified
with the layer-0 spec `xmssClimb` word. -/
theorem c12_layer0_current_node_of_raw_xmssClimb
    (hLayer0RawXmss :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (C12SegmentWotsSetup.c12LayerStateAfterXmssLoop
            (C12SegmentWotsSetup.c12LayerStateBeforeXmssLoop
              (c12LayerBodyInput0
                (C12SegmentForsCompress.c12StepForsCompress
                  (C12SegmentFors.c12StepFors
                    (C12SegmentSeed.c12StepSeed
                      (MkC13State.mkC13State pkSeed pkRoot message sig))))))).bindings
          "merkleNode" =
        SphincsMinusVerifierSpec.C13Concrete.xmssClimb
          (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed)
          (C12Concrete.xmssBaseC12 0
            ((C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 16))
          4 0
          ((C12Concrete.hMsgC12 c12
            { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex % 16)
          (C12Concrete.wotsPkWordC12
            (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkSeed)
            0
            ((C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 16)
            ((C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex % 16)
            (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
              ((C12Concrete.forsPkFromSigC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot }
                  (C12Concrete.hMsgC12 c12
                    { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
                  sigParsed.fors).getD ⟨#[]⟩))
            ((sigParsed.layers[0]?).getD c12EmptyXmssLayerSig).wots)
          ((sigParsed.layers[0]?).getD c12EmptyXmssLayerSig).authPath) :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (c12LayerStateAfter0
            (C12SegmentForsCompress.c12StepForsCompress
              (C12SegmentFors.c12StepFors
                (C12SegmentSeed.c12StepSeed
                  (MkC13State.mkC13State pkSeed pkRoot message sig))))).bindings
          "currentNode" =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          (c12UnrolledLayerRoot0 pkSeed
            (C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex
            ((C12Concrete.forsPkFromSigC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot }
                (C12Concrete.hMsgC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
                sigParsed.fors).getD ⟨#[]⟩)
            sigParsed.layers) := by
  exact c12_layer0_current_node_of_layer0_wots_xmss_roundtrip
    (c12_layer0_wots_xmss_roundtrip_of_raw_xmssClimb hLayer0RawXmss)

/-- Per-layer currentNode obligations that imply the bridge's final layer-4
premise.  The first four facts document the intended iteration-by-iteration
handoff; the last fact is the exact final fact consumed by the bridge. -/
theorem c12_layer_root4_current_node_of_layer_step_current_nodes
    (hLayer0 :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (c12LayerStateAfter0
            (C12SegmentForsCompress.c12StepForsCompress
              (C12SegmentFors.c12StepFors
                (C12SegmentSeed.c12StepSeed
                  (MkC13State.mkC13State pkSeed pkRoot message sig))))).bindings
          "currentNode" =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          (c12UnrolledLayerRoot0 pkSeed
            (C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex
            ((C12Concrete.forsPkFromSigC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot }
                (C12Concrete.hMsgC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
                sigParsed.fors).getD ⟨#[]⟩)
            sigParsed.layers))
    (hLayer1 :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (c12LayerStateAfter1
            (C12SegmentForsCompress.c12StepForsCompress
              (C12SegmentFors.c12StepFors
                (C12SegmentSeed.c12StepSeed
                  (MkC13State.mkC13State pkSeed pkRoot message sig))))).bindings
          "currentNode" =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          (c12UnrolledLayerRoot1 pkSeed
            (C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex
            ((C12Concrete.forsPkFromSigC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot }
                (C12Concrete.hMsgC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
                sigParsed.fors).getD ⟨#[]⟩)
            sigParsed.layers))
    (hLayer2 :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (c12LayerStateAfter2
            (C12SegmentForsCompress.c12StepForsCompress
              (C12SegmentFors.c12StepFors
                (C12SegmentSeed.c12StepSeed
                  (MkC13State.mkC13State pkSeed pkRoot message sig))))).bindings
          "currentNode" =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          (c12UnrolledLayerRoot2 pkSeed
            (C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex
            ((C12Concrete.forsPkFromSigC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot }
                (C12Concrete.hMsgC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
                sigParsed.fors).getD ⟨#[]⟩)
            sigParsed.layers))
    (hLayer3 :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (c12LayerStateAfter3
            (C12SegmentForsCompress.c12StepForsCompress
              (C12SegmentFors.c12StepFors
                (C12SegmentSeed.c12StepSeed
                  (MkC13State.mkC13State pkSeed pkRoot message sig))))).bindings
          "currentNode" =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          (c12UnrolledLayerRoot3 pkSeed
            (C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex
            ((C12Concrete.forsPkFromSigC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot }
                (C12Concrete.hMsgC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
                sigParsed.fors).getD ⟨#[]⟩)
            sigParsed.layers))
    (hLayer4 :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (c12LayerStateAfter4
            (C12SegmentForsCompress.c12StepForsCompress
              (C12SegmentFors.c12StepFors
                (C12SegmentSeed.c12StepSeed
                  (MkC13State.mkC13State pkSeed pkRoot message sig))))).bindings
          "currentNode" =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          (c12UnrolledLayerRoot4 pkSeed
            (C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex
            ((C12Concrete.forsPkFromSigC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot }
                (C12Concrete.hMsgC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
                sigParsed.fors).getD ⟨#[]⟩)
            sigParsed.layers)) :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (C12SegmentWotsSetup.c12StepLayerLoop
            (C12SegmentForsCompress.c12StepForsCompress
              (C12SegmentFors.c12StepFors
                (C12SegmentSeed.c12StepSeed
                  (MkC13State.mkC13State pkSeed pkRoot message sig))))).bindings
          "currentNode" =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          (c12UnrolledLayerRoot4 pkSeed
            (C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex
            ((C12Concrete.forsPkFromSigC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot }
                (C12Concrete.hMsgC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
                sigParsed.fors).getD ⟨#[]⟩)
            sigParsed.layers) := by
  have _ := hLayer0
  have _ := hLayer1
  have _ := hLayer2
  have _ := hLayer3
  exact c12_layer_root4_current_node_of_layer_state_after4_current_node hLayer4

/-- A successful parsed C12 `foldHypertree` result is definitionally the named
five-layer unrolling above.  This removes `foldHypertree` from the remaining
executable-currentNode obligation. -/
theorem c12_foldHypertree_ok_specRoot_eq_unrolled5_of_parse
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature)
    (hParse : C12Concrete.parseSignatureC12 c12 sig = some sigParsed)
    (specRoot : ByteArray)
    (hFold :
      foldHypertree C12Concrete.c12PrimitivesConcrete c12
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (C12Concrete.hMsgC12 c12
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
        ((C12Concrete.forsPkFromSigC12 c12
            { pkSeed := pkSeed, pkRoot := pkRoot }
            (C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
            sigParsed.fors).getD ⟨#[]⟩)
        sigParsed.layers = .ok specRoot) :
    specRoot =
      c12FoldRootUnrolled5 pkSeed
        (C12Concrete.hMsgC12 c12
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex
        ((C12Concrete.forsPkFromSigC12 c12
            { pkSeed := pkSeed, pkRoot := pkRoot }
            (C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
            sigParsed.fors).getD ⟨#[]⟩)
        sigParsed.layers := by
  unfold C12Concrete.parseSignatureC12 at hParse
  by_cases hLen : sig.size = c12.sigBytes
  · simp [hLen] at hParse
    rw [← hParse] at hFold ⊢
    simp [c12FoldRootUnrolled5, c12FoldLayerRoot, c12,
      C12Concrete.c12PrimitivesConcrete, foldHypertree, foldHypertreeAux,
      C12Concrete.wotsPkFromSigC12AtLayer,
      C12Concrete.xmssRootFromSigC12AtLayer, wotsGrindingFailsAtLayer] at hFold ⊢
    exact hFold.symm
  · simp [hLen] at hParse

/-- The exact C12 fold-currentNode bridge follows from the smaller named
executable obligation: match the layer-loop output against
`c12FoldRootUnrolled5`. -/
theorem c12_layer_loop_fold_current_node_of_unrolled5_current_node
    (hUnrolledCurrent :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (C12SegmentWotsSetup.c12StepLayerLoop
            (C12SegmentForsCompress.c12StepForsCompress
              (C12SegmentFors.c12StepFors
                (C12SegmentSeed.c12StepSeed
                  (MkC13State.mkC13State pkSeed pkRoot message sig))))).bindings
          "currentNode" =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          (c12FoldRootUnrolled5 pkSeed
            (C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex
            ((C12Concrete.forsPkFromSigC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot }
                (C12Concrete.hMsgC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
                sigParsed.fors).getD ⟨#[]⟩)
            sigParsed.layers)) :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        ∀ specRoot,
          foldHypertree C12Concrete.c12PrimitivesConcrete c12
            { pkSeed := pkSeed, pkRoot := pkRoot }
            (C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
            ((C12Concrete.forsPkFromSigC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot }
                (C12Concrete.hMsgC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
                sigParsed.fors).getD ⟨#[]⟩)
            sigParsed.layers = .ok specRoot →
          lookupValue
            (C12SegmentWotsSetup.c12StepLayerLoop
              (C12SegmentForsCompress.c12StepForsCompress
                (C12SegmentFors.c12StepFors
                  (C12SegmentSeed.c12StepSeed
                    (MkC13State.mkC13State pkSeed pkRoot message sig))))).bindings
            "currentNode" =
            SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 specRoot := by
  intro pkSeed pkRoot message sig sigParsed hParse specRoot hFold
  rw [hUnrolledCurrent pkSeed pkRoot message sig sigParsed hParse]
  rw [c12_foldHypertree_ok_specRoot_eq_unrolled5_of_parse
    pkSeed pkRoot message sig sigParsed hParse specRoot hFold]

/-- Build the final semantic package expected by
`c12_refines_byte_spec_of_parsed_final_semantic_cover` from the parsed verifier
root extracted above plus the remaining executable binding correspondence. -/
theorem c12_parsed_final_facts_of_executable_bindings
    (hExecBindings :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        ∀ specRoot,
          verifyParsed C12Concrete.c12PrimitivesConcrete c12
            { pkSeed := pkSeed, pkRoot := pkRoot } message sigParsed =
              some (rootMatchesPk c12 specRoot pkRoot) →
          lookupValue
            (C12SegmentWotsSetup.c12StepLayerLoop
              (C12SegmentForsCompress.c12StepForsCompress
                (C12SegmentFors.c12StepFors
                  (C12SegmentSeed.c12StepSeed
                    (MkC13State.mkC13State pkSeed pkRoot message sig))))).bindings
              "currentNode" =
            SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 specRoot ∧
          lookupValue
            (C12SegmentWotsSetup.c12StepLayerLoop
              (C12SegmentForsCompress.c12StepForsCompress
                (C12SegmentFors.c12StepFors
                  (C12SegmentSeed.c12StepSeed
                    (MkC13State.mkC13State pkSeed pkRoot message sig))))).bindings
              "root" =
            SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkRoot) :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        ∃ specRoot,
          verifyParsed C12Concrete.c12PrimitivesConcrete c12
            { pkSeed := pkSeed, pkRoot := pkRoot } message sigParsed =
              some (rootMatchesPk c12 specRoot pkRoot) ∧
          lookupValue
            (C12SegmentWotsSetup.c12StepLayerLoop
              (C12SegmentForsCompress.c12StepForsCompress
                (C12SegmentFors.c12StepFors
                  (C12SegmentSeed.c12StepSeed
                    (MkC13State.mkC13State pkSeed pkRoot message sig))))).bindings
              "currentNode" =
            SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 specRoot ∧
          lookupValue
            (C12SegmentWotsSetup.c12StepLayerLoop
              (C12SegmentForsCompress.c12StepForsCompress
                (C12SegmentFors.c12StepFors
                  (C12SegmentSeed.c12StepSeed
                    (MkC13State.mkC13State pkSeed pkRoot message sig))))).bindings
              "root" =
            SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkRoot ∧
          decide
              (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 specRoot =
                SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkRoot) =
            rootMatchesPk c12 specRoot pkRoot := by
  intro pkSeed pkRoot message sig sigParsed hParse
  rcases c12_verifyParsed_root_roundtrip_of_parse
      pkSeed pkRoot message sig sigParsed hParse with
    ⟨specRoot, hSpec, hSpecRootRoundtrip⟩
  rcases hExecBindings pkSeed pkRoot message sig sigParsed hParse specRoot hSpec with
    ⟨hCurrent, hRoot⟩
  refine ⟨specRoot, hSpec, hCurrent, hRoot, ?_⟩
  exact wordCmp_of_wordOfHash16_rootMatchesPk_c12 specRoot pkRoot hSpecRootRoundtrip

/-- Build the final semantic package expected by
`c12_refines_byte_spec_of_parsed_final_semantic_cover` from parsed-verifier root
extraction plus the remaining hard executable fact: the final C12 layer-loop
`currentNode` binding.  The easy `"root"` binding is discharged by
`C12SegmentWotsSetup.c12FinalLayerLoop_root_mkC13State`. -/
theorem c12_parsed_final_facts_of_current_node_binding
    (hCurrentBinding :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        ∀ specRoot,
          verifyParsed C12Concrete.c12PrimitivesConcrete c12
            { pkSeed := pkSeed, pkRoot := pkRoot } message sigParsed =
              some (rootMatchesPk c12 specRoot pkRoot) →
          lookupValue
            (C12SegmentWotsSetup.c12StepLayerLoop
              (C12SegmentForsCompress.c12StepForsCompress
                (C12SegmentFors.c12StepFors
                  (C12SegmentSeed.c12StepSeed
                    (MkC13State.mkC13State pkSeed pkRoot message sig))))).bindings
              "currentNode" =
            SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 specRoot) :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        ∃ specRoot,
          verifyParsed C12Concrete.c12PrimitivesConcrete c12
            { pkSeed := pkSeed, pkRoot := pkRoot } message sigParsed =
              some (rootMatchesPk c12 specRoot pkRoot) ∧
          lookupValue
            (C12SegmentWotsSetup.c12StepLayerLoop
              (C12SegmentForsCompress.c12StepForsCompress
                (C12SegmentFors.c12StepFors
                  (C12SegmentSeed.c12StepSeed
                    (MkC13State.mkC13State pkSeed pkRoot message sig))))).bindings
              "currentNode" =
            SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 specRoot ∧
          lookupValue
            (C12SegmentWotsSetup.c12StepLayerLoop
              (C12SegmentForsCompress.c12StepForsCompress
                (C12SegmentFors.c12StepFors
                  (C12SegmentSeed.c12StepSeed
                    (MkC13State.mkC13State pkSeed pkRoot message sig))))).bindings
              "root" =
            SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkRoot ∧
          decide
              (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 specRoot =
                SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkRoot) =
            rootMatchesPk c12 specRoot pkRoot := by
  intro pkSeed pkRoot message sig sigParsed hParse
  rcases c12_verifyParsed_root_roundtrip_of_parse
      pkSeed pkRoot message sig sigParsed hParse with
    ⟨specRoot, hSpec, hSpecRootRoundtrip⟩
  refine ⟨specRoot, hSpec, ?_, ?_, ?_⟩
  · exact hCurrentBinding pkSeed pkRoot message sig sigParsed hParse specRoot hSpec
  · exact C12SegmentWotsSetup.c12FinalLayerLoop_root_mkC13State
      pkSeed pkRoot message sig
  · exact wordCmp_of_wordOfHash16_rootMatchesPk_c12 specRoot pkRoot hSpecRootRoundtrip

/-- Build the final semantic package from the exact remaining C12 layer-loop
model fact: whenever the parsed C12 hypertree fold returns `.ok specRoot`, the
final executable layer-loop state stores `wordOfHash16 specRoot` in
`"currentNode"`. -/
theorem c12_parsed_final_facts_of_layer_loop_fold_current_node
    (hLayerLoopFoldCurrent :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        ∀ specRoot,
          foldHypertree C12Concrete.c12PrimitivesConcrete c12
            { pkSeed := pkSeed, pkRoot := pkRoot }
            (C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
            ((C12Concrete.forsPkFromSigC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot }
                (C12Concrete.hMsgC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
                sigParsed.fors).getD ⟨#[]⟩)
            sigParsed.layers = .ok specRoot →
          lookupValue
            (C12SegmentWotsSetup.c12StepLayerLoop
              (C12SegmentForsCompress.c12StepForsCompress
                (C12SegmentFors.c12StepFors
                  (C12SegmentSeed.c12StepSeed
                    (MkC13State.mkC13State pkSeed pkRoot message sig))))).bindings
              "currentNode" =
            SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 specRoot) :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        ∃ specRoot,
          verifyParsed C12Concrete.c12PrimitivesConcrete c12
            { pkSeed := pkSeed, pkRoot := pkRoot } message sigParsed =
              some (rootMatchesPk c12 specRoot pkRoot) ∧
          lookupValue
            (C12SegmentWotsSetup.c12StepLayerLoop
              (C12SegmentForsCompress.c12StepForsCompress
                (C12SegmentFors.c12StepFors
                  (C12SegmentSeed.c12StepSeed
                    (MkC13State.mkC13State pkSeed pkRoot message sig))))).bindings
              "currentNode" =
            SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 specRoot ∧
          lookupValue
            (C12SegmentWotsSetup.c12StepLayerLoop
              (C12SegmentForsCompress.c12StepForsCompress
                (C12SegmentFors.c12StepFors
                  (C12SegmentSeed.c12StepSeed
                    (MkC13State.mkC13State pkSeed pkRoot message sig))))).bindings
              "root" =
            SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkRoot ∧
          decide
              (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 specRoot =
                SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkRoot) =
            rootMatchesPk c12 specRoot pkRoot := by
  intro pkSeed pkRoot message sig sigParsed hParse
  rcases c12_verifyParsed_root_roundtrip_and_fold_ok_of_parse
      pkSeed pkRoot message sig sigParsed hParse with
    ⟨specRoot, hSpec, hFold, hSpecRootRoundtrip⟩
  refine ⟨specRoot, hSpec, ?_, ?_, ?_⟩
  · exact hLayerLoopFoldCurrent pkSeed pkRoot message sig sigParsed hParse specRoot hFold
  · exact C12SegmentWotsSetup.c12FinalLayerLoop_root_mkC13State
      pkSeed pkRoot message sig
  · exact wordCmp_of_wordOfHash16_rootMatchesPk_c12 specRoot pkRoot hSpecRootRoundtrip

/-- Build the final semantic package expected by
`c12_refines_byte_spec_of_parsed_final_semantic_cover` from the smaller residual
facts: parsed verifier root, final concrete `currentNode`/`root` bindings, and
canonicality of the produced spec root. -/
theorem c12_parsed_final_facts_of_root_roundtrip
    (hParsedRoot :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        ∃ specRoot,
          verifyParsed C12Concrete.c12PrimitivesConcrete c12
            { pkSeed := pkSeed, pkRoot := pkRoot } message sigParsed =
              some (rootMatchesPk c12 specRoot pkRoot) ∧
          lookupValue
            (C12SegmentWotsSetup.c12StepLayerLoop
              (C12SegmentForsCompress.c12StepForsCompress
                (C12SegmentFors.c12StepFors
                  (C12SegmentSeed.c12StepSeed
                    (MkC13State.mkC13State pkSeed pkRoot message sig))))).bindings
              "currentNode" =
            SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 specRoot ∧
          lookupValue
            (C12SegmentWotsSetup.c12StepLayerLoop
              (C12SegmentForsCompress.c12StepForsCompress
                (C12SegmentFors.c12StepFors
                  (C12SegmentSeed.c12StepSeed
                    (MkC13State.mkC13State pkSeed pkRoot message sig))))).bindings
              "root" =
            SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkRoot ∧
          SphincsMinusVerifierSpec.C13Concrete.hash16OfWord
            (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 specRoot) =
            specRoot) :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        ∃ specRoot,
          verifyParsed C12Concrete.c12PrimitivesConcrete c12
            { pkSeed := pkSeed, pkRoot := pkRoot } message sigParsed =
              some (rootMatchesPk c12 specRoot pkRoot) ∧
          lookupValue
            (C12SegmentWotsSetup.c12StepLayerLoop
              (C12SegmentForsCompress.c12StepForsCompress
                (C12SegmentFors.c12StepFors
                  (C12SegmentSeed.c12StepSeed
                    (MkC13State.mkC13State pkSeed pkRoot message sig))))).bindings
              "currentNode" =
            SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 specRoot ∧
          lookupValue
            (C12SegmentWotsSetup.c12StepLayerLoop
              (C12SegmentForsCompress.c12StepForsCompress
                (C12SegmentFors.c12StepFors
                  (C12SegmentSeed.c12StepSeed
                    (MkC13State.mkC13State pkSeed pkRoot message sig))))).bindings
              "root" =
            SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkRoot ∧
          decide
              (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 specRoot =
                SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkRoot) =
            rootMatchesPk c12 specRoot pkRoot := by
  intro pkSeed pkRoot message sig sigParsed hParse
  rcases hParsedRoot pkSeed pkRoot message sig sigParsed hParse with
    ⟨specRoot, hSpec, hCurrent, hRoot, hSpecRootRoundtrip⟩
  refine ⟨specRoot, hSpec, hCurrent, hRoot, ?_⟩
  exact wordCmp_of_wordOfHash16_rootMatchesPk_c12 specRoot pkRoot hSpecRootRoundtrip

/-- C12 bridge reducer after byte-length parsing.  The only caller obligation is
the parsed executable correspondence above; all malformed lengths are discharged
by the existing C12 reject-side theorem. -/
theorem c12_refines_byte_spec_of_parsed_executable_cover
    (hParsedExec :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        runC12BodyObserved pkSeed pkRoot message sig =
          verifyParsed C12Concrete.c12PrimitivesConcrete c12
            { pkSeed := pkSeed, pkRoot := pkRoot } message sigParsed) :
    ByteLevel.ImplementsByteVerifier c12Primitives c12 runC12BodyObserved := by
  intro pkSeed pkRoot message sig
  by_cases hLen : sig.size = c12.sigBytes
  · obtain ⟨sigParsed, hParse⟩ :=
      C12Concrete.parseSignatureC12_some_of_size (v := c12) (sig := sig) hLen
    exact
      runC12BodyObserved_eq_verifyBytes_of_parse_and_verifyParsed
        pkSeed pkRoot message sig sigParsed hParse
        (hParsedExec pkSeed pkRoot message sig sigParsed hParse)
  · unfold runC12BodyObserved
    exact runC12BodyObserved_revert_on_bad_length pkSeed pkRoot message sig hLen

/-- C12 byte-spec cover with the final executable/spec equality eliminated from
the caller interface.  The good-length branch now asks for named final semantic
facts only. -/
theorem c12_refines_byte_spec_of_parsed_final_semantic_cover
    (hParsedFinal :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        ∃ specRoot,
          verifyParsed C12Concrete.c12PrimitivesConcrete c12
            { pkSeed := pkSeed, pkRoot := pkRoot } message sigParsed =
              some (rootMatchesPk c12 specRoot pkRoot) ∧
          lookupValue
            (C12SegmentWotsSetup.c12StepLayerLoop
              (C12SegmentForsCompress.c12StepForsCompress
                (C12SegmentFors.c12StepFors
                  (C12SegmentSeed.c12StepSeed
                    (MkC13State.mkC13State pkSeed pkRoot message sig))))).bindings
              "currentNode" =
            SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 specRoot ∧
          lookupValue
            (C12SegmentWotsSetup.c12StepLayerLoop
              (C12SegmentForsCompress.c12StepForsCompress
                (C12SegmentFors.c12StepFors
                  (C12SegmentSeed.c12StepSeed
                    (MkC13State.mkC13State pkSeed pkRoot message sig))))).bindings
              "root" =
            SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkRoot ∧
          decide
              (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 specRoot =
                SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 pkRoot) =
            rootMatchesPk c12 specRoot pkRoot) :
    ByteLevel.ImplementsByteVerifier c12Primitives c12 runC12BodyObserved := by
  refine c12_refines_byte_spec_of_parsed_executable_cover ?_
  intro pkSeed pkRoot message sig sigParsed hParse
  rcases hParsedFinal pkSeed pkRoot message sig sigParsed hParse with
    ⟨specRoot, hSpec, hCurrent, hRoot, hWordCmp⟩
  exact
    runC12BodyObserved_eq_verifyParsed_of_parse_and_final_result
      pkSeed pkRoot message sig sigParsed hParse specRoot
      hSpec hCurrent hRoot hWordCmp

/-- C12 byte-spec cover with parsed-verifier root extraction, root canonicality,
and `hWordCmp` discharged internally.  The remaining good-length facts are only
the final executable C12 segment state binding for `currentNode`, indexed by the
parsed verifier's produced root.  The corresponding `"root"` binding is proved
by `C12SegmentWotsSetup.c12FinalLayerLoop_root_mkC13State`. -/
theorem c12_refines_byte_spec_of_parsed_final_root_roundtrip_cover
    (hCurrentBinding :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        ∀ specRoot,
          verifyParsed C12Concrete.c12PrimitivesConcrete c12
            { pkSeed := pkSeed, pkRoot := pkRoot } message sigParsed =
              some (rootMatchesPk c12 specRoot pkRoot) →
          lookupValue
            (C12SegmentWotsSetup.c12StepLayerLoop
              (C12SegmentForsCompress.c12StepForsCompress
                (C12SegmentFors.c12StepFors
                  (C12SegmentSeed.c12StepSeed
                    (MkC13State.mkC13State pkSeed pkRoot message sig))))).bindings
              "currentNode" =
            SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 specRoot) :
    ByteLevel.ImplementsByteVerifier c12Primitives c12 runC12BodyObserved := by
  exact c12_refines_byte_spec_of_parsed_final_semantic_cover
    (c12_parsed_final_facts_of_current_node_binding hCurrentBinding)

/-- C12 byte-spec cover reduced to the precise remaining layer-loop model fact:
the final executable `"currentNode"` binding agrees with the `.ok` root of the
concrete C12 `foldHypertree` model. -/
theorem c12_refines_byte_spec_of_parsed_layer_loop_fold_cover
    (hLayerLoopFoldCurrent :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        ∀ specRoot,
          foldHypertree C12Concrete.c12PrimitivesConcrete c12
            { pkSeed := pkSeed, pkRoot := pkRoot }
            (C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
            ((C12Concrete.forsPkFromSigC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot }
                (C12Concrete.hMsgC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
                sigParsed.fors).getD ⟨#[]⟩)
            sigParsed.layers = .ok specRoot →
          lookupValue
            (C12SegmentWotsSetup.c12StepLayerLoop
              (C12SegmentForsCompress.c12StepForsCompress
                (C12SegmentFors.c12StepFors
                  (C12SegmentSeed.c12StepSeed
                    (MkC13State.mkC13State pkSeed pkRoot message sig))))).bindings
              "currentNode" =
            SphincsMinusVerifierSpec.C13Concrete.wordOfHash16 specRoot) :
    ByteLevel.ImplementsByteVerifier c12Primitives c12 runC12BodyObserved := by
  exact c12_refines_byte_spec_of_parsed_final_semantic_cover
    (c12_parsed_final_facts_of_layer_loop_fold_current_node
      hLayerLoopFoldCurrent)

/-- C12 byte-spec cover reduced past `foldHypertree` and the top-level
`c12FoldRootUnrolled5` wrapper: the remaining obligation is the final
executable layer-loop current node against the named layer-4 root. -/
theorem c12_refines_byte_spec_of_parsed_unrolled5_current_node_cover
    (hLayerRoot4 :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (C12SegmentWotsSetup.c12StepLayerLoop
            (C12SegmentForsCompress.c12StepForsCompress
              (C12SegmentFors.c12StepFors
                (C12SegmentSeed.c12StepSeed
                  (MkC13State.mkC13State pkSeed pkRoot message sig))))).bindings
          "currentNode" =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          (c12UnrolledLayerRoot4 pkSeed
            (C12Concrete.hMsgC12 c12
              { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex
            ((C12Concrete.forsPkFromSigC12 c12
                { pkSeed := pkSeed, pkRoot := pkRoot }
                (C12Concrete.hMsgC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
                sigParsed.fors).getD ⟨#[]⟩)
            sigParsed.layers)) :
    ByteLevel.ImplementsByteVerifier c12Primitives c12 runC12BodyObserved := by
  exact c12_refines_byte_spec_of_parsed_layer_loop_fold_cover
    (c12_layer_loop_fold_current_node_of_unrolled5_current_node
      (c12_unrolled5_current_node_of_layer_root4_current_node hLayerRoot4))

/-- C12 byte-spec cover reduced through the layer-4 entry-component interface.
The selector/calldata pre-body facts are discharged internally by
`c12Layer4PreBodyState_preserves_selector_calldata`; the remaining layer-4 facts
are the parsed entry bindings plus the curLeaf/WOTS handoffs. -/
theorem c12_refines_byte_spec_of_layer4_entry_components_cover
    (hLayer4EntryAuthPtr :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (c12Layer4XmssEntryState pkSeed pkRoot message sig).bindings "authPtr" =
          MkC13State.sigDataOffset + (2592 + 784 * 4 + 720))
    (hLayer4EntryXmssBase :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (c12Layer4XmssEntryState pkSeed pkRoot message sig).bindings "xmssBase" =
          c12Layer4ParsedBase pkSeed pkRoot message sigParsed)
    (hLayer4EntrySeed :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        ((c12Layer4XmssEntryState pkSeed pkRoot message sig).world.memory 0x00).val =
          c12Layer4ParsedSeed pkSeed)
    (hLayer4CurLeafAfter3 :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (c12LayerStateAfter3
            (C12SegmentForsCompress.c12StepForsCompress
              (C12SegmentFors.c12StepFors
                (C12SegmentSeed.c12StepSeed
                  (MkC13State.mkC13State pkSeed pkRoot message sig))))).bindings
          "curLeaf" =
        c12Layer4Leaf
          (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
    (hLayer4WotsPkBeforeNode :
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (C12SegmentWotsSetup.c12LayerStateBeforeXmssNode
            (c12LayerBodyInput4
              (C12SegmentForsCompress.c12StepForsCompress
                (C12SegmentFors.c12StepFors
                  (C12SegmentSeed.c12StepSeed
                    (MkC13State.mkC13State pkSeed pkRoot message sig)))))).bindings
          "wotsPk" =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          (c12Layer4WotsPkBytes pkSeed
            (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex
            (c12UnrolledLayerRoot3 pkSeed
              (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex
              ((C12Concrete.forsPkFromSigC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot }
                  (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed)
                  sigParsed.fors).getD ⟨#[]⟩)
              sigParsed.layers)
            ((sigParsed.layers[4]?).getD c12EmptyXmssLayerSig))) :
    ByteLevel.ImplementsByteVerifier c12Primitives c12 runC12BodyObserved := by
  exact
    c12_refines_byte_spec_of_parsed_unrolled5_current_node_cover
      (c12_layer_root4_current_node_of_layer4_wots_xmss_roundtrip
        (c12_layer4_wots_xmss_roundtrip_of_raw_xmssClimb
          (c12_layer4_raw_xmss_of_generic_merkle_fold
            (c12_layer4_generic_xmss_of_entry_components_and_handoffs
              hLayer4EntryAuthPtr
              hLayer4EntryXmssBase
              hLayer4EntrySeed
              hLayer4CurLeafAfter3
              hLayer4WotsPkBeforeNode))))

/-- Compact name for the layer-4 C12 body input state, used to keep later
WOTS handoff statements from repeatedly exposing the full seed/FORS prefix. -/
def c12Layer4InputState
    (pkSeed pkRoot message sig : ByteArray) : RuntimeState :=
  c12LayerBodyInput4
    (C12SegmentForsCompress.c12StepForsCompress
      (C12SegmentFors.c12StepFors
        (C12SegmentSeed.c12StepSeed
          (MkC13State.mkC13State pkSeed pkRoot message sig))))

theorem c12Layer4InputState_eq_preBodyState
    (pkSeed pkRoot message sig : ByteArray) :
    c12Layer4InputState pkSeed pkRoot message sig =
      c12Layer4PreBodyState pkSeed pkRoot message sig := rfl

def c12Layer4BeforeWotsPkState
    (pkSeed pkRoot message sig : ByteArray) : RuntimeState :=
  C12SegmentWotsSetup.c12LayerStateBeforeWotsPk
    (c12Layer4InputState pkSeed pkRoot message sig)

def c12Layer4BeforeWotsPkCopyState
    (pkSeed pkRoot message sig : ByteArray) : RuntimeState :=
  C12SegmentWotsSetup.c12LayerStateBeforeWotsPkCopy
    (c12Layer4InputState pkSeed pkRoot message sig)

def c12Layer4BeforePkAdrsState
    (pkSeed pkRoot message sig : ByteArray) : RuntimeState :=
  C12SegmentWotsSetup.c12LayerStateBeforePkAdrs
    (c12Layer4InputState pkSeed pkRoot message sig)

def c12Layer4BeforePkAdrsMessageStartState
    (pkSeed pkRoot message sig : ByteArray) : RuntimeState :=
  C12SegmentWotsSetup.c12LayerBeforePkAdrsMessageStart
    (c12Layer4InputState pkSeed pkRoot message sig)

def c12Layer4BeforePkAdrsMessageLoopState
    (pkSeed pkRoot message sig : ByteArray) : RuntimeState :=
  { c12Layer4BeforePkAdrsMessageStartState pkSeed pkRoot message sig with
    bindings :=
      bindValue
        (c12Layer4BeforePkAdrsMessageStartState pkSeed pkRoot message sig).bindings
        "i" (wordNormalize 0) }

def c12Layer4BeforePkAdrsChecksumStartState
    (pkSeed pkRoot message sig : ByteArray) : RuntimeState :=
  C12SegmentWotsSetup.c12LayerBeforePkAdrsChecksumStart
    (c12Layer4InputState pkSeed pkRoot message sig)

def c12Layer4BeforePkAdrsChecksumLoopState
    (pkSeed pkRoot message sig : ByteArray) : RuntimeState :=
  { c12Layer4BeforePkAdrsChecksumStartState pkSeed pkRoot message sig with
    bindings :=
      bindValue
        (c12Layer4BeforePkAdrsChecksumStartState pkSeed pkRoot message sig).bindings
        "j" (wordNormalize 0) }

/-- Any state whose world is the `j`-prefix world of the layer-4 WOTS message
loop reads the frozen layer-4 WOTS chain word at index `j` through
`calldataload(wotsPtr + (i << 4))`, provided its local bindings expose the same
`wotsPtr` and loop index. -/
theorem c12Layer4BeforePkAdrsMessageLoop_cdload_raw
    (pkSeed pkRoot message sig : ByteArray) (j : Nat) (hj : j < 42)
    (s : RuntimeState)
    (hWotsPtr :
      lookupValue s.bindings "wotsPtr" =
        MkC13State.sigDataOffset + (2592 + 784 * 4))
    (hI : lookupValue s.bindings "i" = j)
    (hWorld :
      s.world =
        (SphincsMinusVerifiers.ClimbLoop.foldLoop "i"
          C12SegmentWotsSetup.c12WotsMessageStep
          (c12Layer4BeforePkAdrsMessageLoopState pkSeed pkRoot message sig)
          0 j).world) :
    evalExpr [] s
        (.calldataload
          (.add (.localVar "wotsPtr")
            (.shl (.literal 4) (.localVar "i")))) =
      some
        (Compiler.Proofs.YulGeneration.calldataloadWord 0
          (MkC13State.headWords pkSeed pkRoot message sig.size ++
            MkC13State.bytesToWords sig)
          (MkC13State.sigDataOffset + (2592 + 784 * 4 + 16 * j))) := by
  let stLoop := c12Layer4BeforePkAdrsMessageLoopState pkSeed pkRoot message sig
  have hPrefixSc :=
    StateFrame.foldLoop_preserves_selector_calldata "i"
      C12SegmentWotsSetup.c12WotsMessageStep
      c12WotsMessageStep_preserves_sc stLoop 0 j
  have hLoopCd :
      (SphincsMinusVerifiers.ClimbLoop.foldLoop "i"
          C12SegmentWotsSetup.c12WotsMessageStep stLoop 0 j).world.calldata =
        MkC13State.headWords pkSeed pkRoot message sig.size ++
          MkC13State.bytesToWords sig := by
    rw [hPrefixSc.2]
    have hStartCd :
        stLoop.world.calldata =
          (c12Layer4PreBodyState pkSeed pkRoot message sig).world.calldata := by
      simpa [stLoop, c12Layer4BeforePkAdrsMessageLoopState,
        c12Layer4BeforePkAdrsMessageStartState, c12Layer4InputState] using
        C12SegmentWotsSetup.c12LayerBeforePkAdrsMessageLoopStart_preserves_calldata
          (c12Layer4InputState pkSeed pkRoot message sig)
    rw [hStartCd]
    exact c12Layer4PreBodyState_calldata_eq pkSeed pkRoot message sig
  have hCd : s.world.calldata =
      MkC13State.headWords pkSeed pkRoot message sig.size ++
        MkC13State.bytesToWords sig := by
    rw [hWorld]
    simpa [stLoop] using hLoopCd
  have hWotsEval :
      evalExpr [] s (.localVar "wotsPtr") =
        some (MkC13State.sigDataOffset + (2592 + 784 * 4)) := by
    show some (lookupValue s.bindings "wotsPtr") =
      some (MkC13State.sigDataOffset + (2592 + 784 * 4))
    rw [hWotsPtr]
  have hIEval : evalExpr [] s (.localVar "i") = some j := by
    show some (lookupValue s.bindings "i") = some j
    rw [hI]
  have hShift : j <<< 4 < 2 ^ 256 := by
    rw [Nat.shiftLeft_eq]
    have hj' : j < 42 := hj
    nlinarith [Nat.mul_lt_mul_of_pos_right hj' (by decide : 0 < 2 ^ 4)]
  have hSum :
      MkC13State.sigDataOffset + (2592 + 784 * 4) + (j <<< 4) < 2 ^ 256 := by
    rw [Nat.shiftLeft_eq]
    norm_num [MkC13State.sigDataOffset]
    nlinarith [hj]
  have hOff :
      MkC13State.sigDataOffset + (2592 + 784 * 4) + (j <<< 4) =
        MkC13State.sigDataOffset + (2592 + 784 * 4 + 16 * j) := by
    rw [Nat.shiftLeft_eq]
    ring
  exact c12_layer4_wots_raw_read_eq_frozen_any_selector
    s (.localVar "wotsPtr") (.localVar "i")
    pkSeed pkRoot message sig j
    (MkC13State.sigDataOffset + (2592 + 784 * 4)) j
    hCd hWotsEval hIEval
    (by norm_num [MkC13State.sigDataOffset])
    (lt_trans hj (by decide : 42 < 2 ^ 256))
    hShift hSum hOff

/-- Any state whose world is the `j`-prefix world of the layer-4 WOTS checksum
loop reads the frozen layer-4 WOTS chain word at checksum index `42 + j`. -/
theorem c12Layer4BeforePkAdrsChecksumLoop_cdload_raw
    (pkSeed pkRoot message sig : ByteArray) (j : Nat) (hj : j < 3)
    (s : RuntimeState)
    (hWotsPtr :
      lookupValue s.bindings "wotsPtr" =
        MkC13State.sigDataOffset + (2592 + 784 * 4))
    (hI : lookupValue s.bindings "i" = 42 + j)
    (hWorld :
      s.world =
        (SphincsMinusVerifiers.ClimbLoop.foldLoop "j"
          C12SegmentWotsSetup.c12WotsChecksumStep
          (c12Layer4BeforePkAdrsChecksumLoopState pkSeed pkRoot message sig)
          0 j).world) :
    evalExpr [] s
        (.calldataload
          (.add (.localVar "wotsPtr")
            (.shl (.literal 4) (.localVar "i")))) =
      some
        (Compiler.Proofs.YulGeneration.calldataloadWord 0
          (MkC13State.headWords pkSeed pkRoot message sig.size ++
            MkC13State.bytesToWords sig)
          (MkC13State.sigDataOffset + (2592 + 784 * 4 + 16 * (42 + j)))) := by
  let stLoop := c12Layer4BeforePkAdrsChecksumLoopState pkSeed pkRoot message sig
  have hPrefixSc :=
    StateFrame.foldLoop_preserves_selector_calldata "j"
      C12SegmentWotsSetup.c12WotsChecksumStep
      c12WotsChecksumStep_preserves_sc stLoop 0 j
  have hLoopCd :
      (SphincsMinusVerifiers.ClimbLoop.foldLoop "j"
          C12SegmentWotsSetup.c12WotsChecksumStep stLoop 0 j).world.calldata =
        MkC13State.headWords pkSeed pkRoot message sig.size ++
          MkC13State.bytesToWords sig := by
    rw [hPrefixSc.2]
    have hMessageCd :
        (C12SegmentWotsSetup.c12LayerBeforePkAdrsMessageEnd
            (c12Layer4InputState pkSeed pkRoot message sig)).world.calldata =
          (c12Layer4PreBodyState pkSeed pkRoot message sig).world.calldata := by
      let stMessageLoop := c12Layer4BeforePkAdrsMessageLoopState pkSeed pkRoot message sig
      have hPrefixSc :=
        StateFrame.foldLoop_preserves_selector_calldata "i"
          C12SegmentWotsSetup.c12WotsMessageStep
          c12WotsMessageStep_preserves_sc stMessageLoop 0 42
      have hStartCd :
          stMessageLoop.world.calldata =
            (c12Layer4PreBodyState pkSeed pkRoot message sig).world.calldata := by
        simpa [stMessageLoop, c12Layer4BeforePkAdrsMessageLoopState,
          c12Layer4BeforePkAdrsMessageStartState, c12Layer4InputState] using
          C12SegmentWotsSetup.c12LayerBeforePkAdrsMessageLoopStart_preserves_calldata
            (c12Layer4InputState pkSeed pkRoot message sig)
      have hState :=
        congrArg (fun s : RuntimeState => s.world.calldata)
          (C12SegmentWotsSetup.c12LayerBeforePkAdrsMessageEnd_eq_foldLoop42
            (c12Layer4InputState pkSeed pkRoot message sig))
      exact hState.trans (by
        simpa [stMessageLoop, c12Layer4BeforePkAdrsMessageLoopState,
          c12Layer4BeforePkAdrsMessageStartState] using hPrefixSc.2.trans hStartCd)
    have hStartCd :
        stLoop.world.calldata =
          (c12Layer4PreBodyState pkSeed pkRoot message sig).world.calldata := by
      simpa [stLoop, c12Layer4BeforePkAdrsChecksumLoopState,
        c12Layer4BeforePkAdrsChecksumStartState,
        C12SegmentWotsSetup.c12LayerBeforePkAdrsChecksumStart] using hMessageCd
    rw [hStartCd]
    exact c12Layer4PreBodyState_calldata_eq pkSeed pkRoot message sig
  have hCd : s.world.calldata =
      MkC13State.headWords pkSeed pkRoot message sig.size ++
        MkC13State.bytesToWords sig := by
    rw [hWorld]
    simpa [stLoop] using hLoopCd
  have hWotsEval :
      evalExpr [] s (.localVar "wotsPtr") =
        some (MkC13State.sigDataOffset + (2592 + 784 * 4)) := by
    show some (lookupValue s.bindings "wotsPtr") =
      some (MkC13State.sigDataOffset + (2592 + 784 * 4))
    rw [hWotsPtr]
  have hIEval : evalExpr [] s (.localVar "i") = some (42 + j) := by
    show some (lookupValue s.bindings "i") = some (42 + j)
    rw [hI]
  have hShift : (42 + j) <<< 4 < 2 ^ 256 := by
    rw [Nat.shiftLeft_eq]
    have hle : 42 + j ≤ 44 := by omega
    have hbound : (44 : Nat) * 2 ^ 4 < 2 ^ 256 := by decide
    nlinarith [Nat.mul_le_mul_right (2 ^ 4) hle]
  have hSum :
      MkC13State.sigDataOffset + (2592 + 784 * 4) + ((42 + j) <<< 4) <
        2 ^ 256 := by
    rw [Nat.shiftLeft_eq]
    norm_num [MkC13State.sigDataOffset]
    nlinarith [hj]
  have hOff :
      MkC13State.sigDataOffset + (2592 + 784 * 4) + ((42 + j) <<< 4) =
        MkC13State.sigDataOffset + (2592 + 784 * 4 + 16 * (42 + j)) := by
    rw [Nat.shiftLeft_eq]
    ring
  exact c12_layer4_wots_raw_read_eq_frozen_any_selector
    s (.localVar "wotsPtr") (.localVar "i")
    pkSeed pkRoot message sig (42 + j)
    (MkC13State.sigDataOffset + (2592 + 784 * 4)) (42 + j)
    hCd hWotsEval hIEval
    (by norm_num [MkC13State.sigDataOffset])
    (by omega)
    hShift hSum hOff

/-- The layer-4 message-loop prefix preserves the public-seed scratch word. -/
theorem c12Layer4BeforePkAdrsMessageLoop_seed_prefix
    (pkSeed pkRoot message sig : ByteArray) (j : Nat) (hj : j < 42) :
    ((SphincsMinusVerifiers.ClimbLoop.foldLoop "i"
        C12SegmentWotsSetup.c12WotsMessageStep
        (c12Layer4BeforePkAdrsMessageLoopState pkSeed pkRoot message sig)
        0 j).world.memory 0x00).val =
      c12Layer4ParsedSeed pkSeed := by
  let stLoop := c12Layer4BeforePkAdrsMessageLoopState pkSeed pkRoot message sig
  rw [C12SegmentWotsSetup.c12WotsMessageFold_preserves_memory_zero_bound
    stLoop j (by omega)]
  have hStart :
      (stLoop.world.memory 0x00).val =
        ((c12Layer4PreBodyState pkSeed pkRoot message sig).world.memory 0x00).val := by
    simpa [stLoop, c12Layer4BeforePkAdrsMessageLoopState,
      c12Layer4BeforePkAdrsMessageStartState, c12Layer4InputState,
      c12Layer4PreBodyState] using
      C12SegmentWotsSetup.c12LayerBeforePkAdrsMessageLoopStart_preserves_memory_zero
        (c12Layer4InputState pkSeed pkRoot message sig)
  rw [hStart]
  exact c12Layer4PreBodyState_preserves_memory_zero pkSeed pkRoot message sig

/-- The layer-4 message-loop prefix preserves the runtime current-node binding. -/
theorem c12Layer4BeforePkAdrsMessageLoop_currentNode_prefix
    (pkSeed pkRoot message sig : ByteArray) (j : Nat) :
    lookupValue
        (SphincsMinusVerifiers.ClimbLoop.foldLoop "i"
          C12SegmentWotsSetup.c12WotsMessageStep
          (c12Layer4BeforePkAdrsMessageLoopState pkSeed pkRoot message sig)
          0 j).bindings
        "currentNode" =
      lookupValue (c12Layer4PreBodyState pkSeed pkRoot message sig).bindings
        "currentNode" := by
  let stLoop := c12Layer4BeforePkAdrsMessageLoopState pkSeed pkRoot message sig
  rw [C12SegmentWotsSetup.c12WotsMessageFold_preserves_currentNode]
  have hStart :=
    C12SegmentWotsSetup.c12LayerBeforePkAdrsMessageLoopStart_currentNode_eq
      (c12Layer4InputState pkSeed pkRoot message sig)
  simpa [stLoop, c12Layer4BeforePkAdrsMessageLoopState,
    c12Layer4BeforePkAdrsMessageStartState, c12Layer4InputState,
    c12Layer4PreBodyState] using hStart

/-- The layer-4 message-loop prefix preserves the parsed WOTS-base binding. -/
theorem c12Layer4BeforePkAdrsMessageLoop_wotsBase_prefix
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature)
    (hParse : C12Concrete.parseSignatureC12 c12 sig = some sigParsed)
    (j : Nat) :
    lookupValue
        (SphincsMinusVerifiers.ClimbLoop.foldLoop "i"
          C12SegmentWotsSetup.c12WotsMessageStep
          (c12Layer4BeforePkAdrsMessageLoopState pkSeed pkRoot message sig)
          0 j).bindings
        "wotsBase" =
      C12Concrete.wotsBaseC12 4
        (c12Layer4NextTree
          (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
        (c12Layer4Leaf
          (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex) := by
  let stLoop := c12Layer4BeforePkAdrsMessageLoopState pkSeed pkRoot message sig
  rw [C12SegmentWotsSetup.c12WotsMessageFold_preserves_wotsBase]
  have hEval :=
    c12Layer4PreBodyState_wotsBase_eval pkSeed pkRoot message sig sigParsed hParse
  have hStart :=
    C12SegmentWotsSetup.c12LayerBeforePkAdrsMessageLoopStart_wotsBase_eq_of_eval
      (c12Layer4PreBodyState pkSeed pkRoot message sig)
      (C12Concrete.wotsBaseC12 4
        (c12Layer4NextTree
          (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
        (c12Layer4Leaf
          (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex))
      hEval
  simpa [stLoop, c12Layer4BeforePkAdrsMessageLoopState,
    c12Layer4BeforePkAdrsMessageStartState, c12Layer4InputState,
    c12Layer4PreBodyState] using hStart

/-- The layer-4 message-loop prefix preserves the layer-4 WOTS signature
pointer binding. -/
theorem c12Layer4BeforePkAdrsMessageLoop_wotsPtr_prefix
    (pkSeed pkRoot message sig : ByteArray) (j : Nat) :
    lookupValue
        (SphincsMinusVerifiers.ClimbLoop.foldLoop "i"
          C12SegmentWotsSetup.c12WotsMessageStep
          (c12Layer4BeforePkAdrsMessageLoopState pkSeed pkRoot message sig)
          0 j).bindings
        "wotsPtr" =
      MkC13State.sigDataOffset + (2592 + 784 * 4) := by
  let stLoop := c12Layer4BeforePkAdrsMessageLoopState pkSeed pkRoot message sig
  rw [C12SegmentWotsSetup.c12WotsMessageFold_preserves_wotsPtr]
  have hEval :=
    c12Layer4PreBodyState_wotsPtr_eval_after_wotsBase_bind
      pkSeed pkRoot message sig 0
  have hStart :=
    C12SegmentWotsSetup.c12LayerBeforePkAdrsMessageLoopStart_wotsPtr_eq_of_eval
      (c12Layer4PreBodyState pkSeed pkRoot message sig)
      (MkC13State.sigDataOffset + (2592 + 784 * 4))
      (by simpa using hEval)
  simpa [stLoop, c12Layer4BeforePkAdrsMessageLoopState,
    c12Layer4BeforePkAdrsMessageStartState, c12Layer4InputState,
    c12Layer4PreBodyState] using hStart

def c12Layer4BeforeAuthOffState
    (pkSeed pkRoot message sig : ByteArray) : RuntimeState :=
  C12SegmentWotsSetup.c12LayerStateBeforeAuthOff
    (c12Layer4InputState pkSeed pkRoot message sig)

def c12Layer4Node
    (pkSeed pkRoot message : ByteArray) (sigParsed : Signature) : ByteArray :=
  c12UnrolledLayerRoot3 pkSeed
    (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex
    ((C12Concrete.forsPkFromSigC12 c12
        { pkSeed := pkSeed, pkRoot := pkRoot }
        (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed)
        sigParsed.fors).getD ⟨#[]⟩)
    sigParsed.layers

def c12Layer4Sig (sigParsed : Signature) : XmssLayerSig :=
  (sigParsed.layers[4]?).getD c12EmptyXmssLayerSig

/-- Remaining public C12 layer-4 WOTS-PK premise, at the exact final-Keccak
boundary before the auth-offset setup suffix. -/
def C12Layer4WotsPkBeforeAuthOffPremise : Prop :=
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (C12SegmentWotsSetup.c12LayerStateBeforeAuthOff
            (c12LayerBodyInput4
              (C12SegmentForsCompress.c12StepForsCompress
                (C12SegmentFors.c12StepFors
                  (C12SegmentSeed.c12StepSeed
                    (MkC13State.mkC13State pkSeed pkRoot message sig)))))).bindings
          "wotsPk" =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          (c12Layer4WotsPkBytes pkSeed
            (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex
            (c12UnrolledLayerRoot3 pkSeed
              (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex
              ((C12Concrete.forsPkFromSigC12 c12
                  { pkSeed := pkSeed, pkRoot := pkRoot }
                  (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed)
                  sigParsed.fors).getD ⟨#[]⟩)
              sigParsed.layers)
            ((sigParsed.layers[4]?).getD c12EmptyXmssLayerSig))

/-- Smaller memory-image premise for the layer-4 WOTS-PK handoff: after the
WOTS message/checksum loops and public-key copy loop, the final-Keccak scratch
contains the seed, WOTS-PK address, and all 45 C12 chain-end words. -/
def C12Layer4WotsPkBeforeWotsPkMemoryPremise : Prop :=
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        (((c12Layer4BeforeWotsPkState pkSeed pkRoot message sig).world.memory 0x00).val =
          c12Layer4ParsedSeed pkSeed) ∧
        (((c12Layer4BeforeWotsPkState pkSeed pkRoot message sig).world.memory 0x20).val =
          C12Concrete.wotsPkAdrsC12 4
            (c12Layer4NextTree
              (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
            (c12Layer4Leaf
              (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)) ∧
        ∀ j, (h : j < 45) →
          ((c12Layer4BeforeWotsPkState pkSeed pkRoot message sig).world.memory
              (0x40 + 32 * j)).val =
          (c12WotsChainsEnd
              (c12Layer4ParsedSeed pkSeed) 4
              (c12Layer4NextTree
                (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
              (c12Layer4Leaf
                (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
              (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
                (c12Layer4Node pkSeed pkRoot message sigParsed))
              (c12Layer4Sig sigParsed).wots)[j]

/-- Smaller layer-4 WOTS-PK memory premise at the pre-copy cutpoint: the WOTS
message/checksum loops have generated the chain-end words at `0x80 + 32*j`, and
the WOTS-PK address has just been stored at `0x20`. -/
def C12Layer4WotsPkBeforeWotsPkCopyMemoryPremise : Prop :=
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        (((c12Layer4BeforeWotsPkCopyState pkSeed pkRoot message sig).world.memory 0x00).val =
          c12Layer4ParsedSeed pkSeed) ∧
        (((c12Layer4BeforeWotsPkCopyState pkSeed pkRoot message sig).world.memory 0x20).val =
          C12Concrete.wotsPkAdrsC12 4
            (c12Layer4NextTree
              (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
            (c12Layer4Leaf
              (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)) ∧
        ∀ j, (h : j < 45) →
          ((c12Layer4BeforeWotsPkCopyState pkSeed pkRoot message sig).world.memory
              (0x80 + 32 * j)).val =
          (c12WotsChainsEnd
              (c12Layer4ParsedSeed pkSeed) 4
              (c12Layer4NextTree
                (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
              (c12Layer4Leaf
                (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
              (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
                (c12Layer4Node pkSeed pkRoot message sigParsed))
              (c12Layer4Sig sigParsed).wots)[j]

/-- Layer-4 pre-copy WOTS-PK memory premise after discharging the seed cell:
only the final address store and generated chain-end cells remain. -/
def C12Layer4WotsPkBeforeWotsPkCopyAddrCellsPremise : Prop :=
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        (((c12Layer4BeforeWotsPkCopyState pkSeed pkRoot message sig).world.memory 0x20).val =
          C12Concrete.wotsPkAdrsC12 4
            (c12Layer4NextTree
              (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
            (c12Layer4Leaf
              (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)) ∧
        ∀ j, (h : j < 45) →
          ((c12Layer4BeforeWotsPkCopyState pkSeed pkRoot message sig).world.memory
              (0x80 + 32 * j)).val =
          (c12WotsChainsEnd
              (c12Layer4ParsedSeed pkSeed) 4
              (c12Layer4NextTree
                (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
              (c12Layer4Leaf
                (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
              (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
                (c12Layer4Node pkSeed pkRoot message sigParsed))
              (c12Layer4Sig sigParsed).wots)[j]

/-- Layer-4 pre-copy WOTS-PK memory premise after discharging the seed and
address cells: only the generated chain-end cells remain. -/
def C12Layer4WotsPkBeforeWotsPkCopyCellsPremise : Prop :=
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        ∀ j, (h : j < 45) →
          ((c12Layer4BeforeWotsPkCopyState pkSeed pkRoot message sig).world.memory
              (0x80 + 32 * j)).val =
          (c12WotsChainsEnd
              (c12Layer4ParsedSeed pkSeed) 4
              (c12Layer4NextTree
                (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
              (c12Layer4Leaf
                (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
              (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
                (c12Layer4Node pkSeed pkRoot message sigParsed))
              (c12Layer4Sig sigParsed).wots)[j]

/-- Smaller layer-4 WOTS-PK cell premise at the cutpoint immediately before the
WOTS-PK address binding/store.  The suffix from this state to
`beforeWotsPkCopy` only writes `0x20`, so the 45 generated chain-end cells are
preserved by `c12Layer4BeforeWotsPkCopy_chain_cell_eq_beforePkAdrs`. -/
def C12Layer4WotsPkBeforePkAdrsCellsPremise : Prop :=
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        ∀ j, (h : j < 45) →
          ((c12Layer4BeforePkAdrsState pkSeed pkRoot message sig).world.memory
              (0x80 + 32 * j)).val =
          (c12WotsChainsEnd
              (c12Layer4ParsedSeed pkSeed) 4
              (c12Layer4NextTree
                (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
              (c12Layer4Leaf
                (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
              (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
                (c12Layer4Node pkSeed pkRoot message sigParsed))
              (c12Layer4Sig sigParsed).wots)[j]

/-- Message-loop part of the smaller layer-4 `beforePkAdrs` generated-cell
premise.  These are the first 42 WOTS chain cells. -/
def C12Layer4WotsPkBeforePkAdrsMessageCellsPremise : Prop :=
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        ∀ j, (h : j < 42) →
          ((c12Layer4BeforePkAdrsState pkSeed pkRoot message sig).world.memory
              (0x80 + 32 * j)).val =
          (c12WotsChainsEnd
              (c12Layer4ParsedSeed pkSeed) 4
              (c12Layer4NextTree
                (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
              (c12Layer4Leaf
                (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
              (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
                (c12Layer4Node pkSeed pkRoot message sigParsed))
              (c12Layer4Sig sigParsed).wots)[j]'(by
                rw [c12WotsChainsEnd_length]
                omega)

/-- Checksum-loop part of the smaller layer-4 `beforePkAdrs` generated-cell
premise.  These are the final 3 WOTS chain cells, indexed globally as
`42 + j`. -/
def C12Layer4WotsPkBeforePkAdrsChecksumCellsPremise : Prop :=
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        ∀ j, (h : j < 3) →
          ((c12Layer4BeforePkAdrsState pkSeed pkRoot message sig).world.memory
              (0x80 + 32 * (42 + j))).val =
          (c12WotsChainsEnd
              (c12Layer4ParsedSeed pkSeed) 4
              (c12Layer4NextTree
                (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
              (c12Layer4Leaf
                (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
              (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
                (c12Layer4Node pkSeed pkRoot message sigParsed))
              (c12Layer4Sig sigParsed).wots)[42 + j]'(by
                rw [c12WotsChainsEnd_length]
                omega)

/-- Runtime-current-node form of the smaller layer-4 `beforePkAdrs`
message-cell premise.  This matches the executable WOTS message loop before
rewriting the pre-body `"currentNode"` through the layer-3 handoff. -/
def C12Layer4WotsPkBeforePkAdrsMessageCellsRuntimeNodePremise : Prop :=
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        ∀ j, (h : j < 42) →
          ((c12Layer4BeforePkAdrsState pkSeed pkRoot message sig).world.memory
              (0x80 + 32 * j)).val =
          (c12WotsChainsEnd
              (c12Layer4ParsedSeed pkSeed) 4
              (c12Layer4NextTree
                (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
              (c12Layer4Leaf
                (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
              (lookupValue
                (c12Layer4PreBodyState pkSeed pkRoot message sig).bindings
                "currentNode")
              (c12Layer4Sig sigParsed).wots)[j]'(by
                rw [c12WotsChainsEnd_length]
                omega)

/-- Runtime-current-node form of the smaller layer-4 `beforePkAdrs`
checksum-cell premise. -/
def C12Layer4WotsPkBeforePkAdrsChecksumCellsRuntimeNodePremise : Prop :=
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        ∀ j, (h : j < 3) →
          ((c12Layer4BeforePkAdrsState pkSeed pkRoot message sig).world.memory
              (0x80 + 32 * (42 + j))).val =
          (c12WotsChainsEnd
              (c12Layer4ParsedSeed pkSeed) 4
              (c12Layer4NextTree
                (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
              (c12Layer4Leaf
                (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
              (lookupValue
                (c12Layer4PreBodyState pkSeed pkRoot message sig).bindings
                "currentNode")
              (c12Layer4Sig sigParsed).wots)[42 + j]'(by
                rw [c12WotsChainsEnd_length]
                omega)

/-- Layer-4 pre-body current-node handoff needed to rewrite runtime-node WOTS
cell facts to the semantic layer-4 node used by `c12WotsChainsEnd`. -/
def C12Layer4PreBodyCurrentNodePremise : Prop :=
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (c12Layer4PreBodyState pkSeed pkRoot message sig).bindings
          "currentNode" =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          (c12Layer4Node pkSeed pkRoot message sigParsed)

/-- Exact post-layer-3 current-node handoff that feeds the layer-4 WOTS setup. -/
def C12Layer3After3CurrentNodePremise : Prop :=
      ∀ pkSeed pkRoot message sig sigParsed,
        C12Concrete.parseSignatureC12 c12 sig = some sigParsed →
        lookupValue
          (c12LayerStateAfter3
            (C12SegmentForsCompress.c12StepForsCompress
              (C12SegmentFors.c12StepFors
                (C12SegmentSeed.c12StepSeed
                  (MkC13State.mkC13State pkSeed pkRoot message sig))))).bindings
          "currentNode" =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          (c12Layer4Node pkSeed pkRoot message sigParsed)

/-- The layer-4 pre-body current-node premise follows from the exact post-layer-3
current-node handoff.  This packages the existing handoff reducer in the same
shape consumed by the runtime-node WOTS cell reducers below. -/
theorem c12Layer4PreBodyCurrentNode_of_after3_current_node
    (hAfter3 : C12Layer3After3CurrentNodePremise) :
    C12Layer4PreBodyCurrentNodePremise := by
  intro pkSeed pkRoot message sig sigParsed hParse
  exact
    c12Layer4PreBodyState_currentNode_eq_unrolledLayerRoot3_of_after3_currentNode
      hAfter3 pkSeed pkRoot message sig sigParsed hParse

/-- The runtime current-node at the layer-4 WOTS setup is EVM-word bounded once
the post-layer-3 handoff has been established. -/
theorem c12Layer4PreBodyState_currentNode_lt_of_after3_current_node
    (hAfter3 : C12Layer3After3CurrentNodePremise)
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature)
    (hParse : C12Concrete.parseSignatureC12 c12 sig = some sigParsed) :
    lookupValue
        (c12Layer4PreBodyState pkSeed pkRoot message sig).bindings
        "currentNode" < 2 ^ 256 := by
  rw [c12Layer4PreBodyState_currentNode_eq_unrolledLayerRoot3_of_after3_currentNode
    hAfter3 pkSeed pkRoot message sig sigParsed hParse]
  exact SphincsMinusVerifiers.SegmentS2.wordOfHash16_lt _

/-- The layer-4 message-loop prefix has a bounded checksum accumulator once the
runtime current-node is known to be the layer-3 handoff word. -/
theorem c12Layer4BeforePkAdrsMessageLoop_csum_add7_lt_of_after3_current_node
    (hAfter3 : C12Layer3After3CurrentNodePremise)
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature)
    (hParse : C12Concrete.parseSignatureC12 c12 sig = some sigParsed)
    (j : Nat) (hj : j < 42) :
    lookupValue
        (SphincsMinusVerifiers.ClimbLoop.foldLoop "i"
          C12SegmentWotsSetup.c12WotsMessageStep
          (c12Layer4BeforePkAdrsMessageLoopState pkSeed pkRoot message sig)
          0 j).bindings
        "csum" + 7 < 2 ^ 256 := by
  let currentNode :=
    lookupValue (c12Layer4PreBodyState pkSeed pkRoot message sig).bindings
      "currentNode"
  have hCNLt : currentNode < 2 ^ 256 := by
    simpa [currentNode] using
      c12Layer4PreBodyState_currentNode_lt_of_after3_current_node
        hAfter3 pkSeed pkRoot message sig sigParsed hParse
  simpa [c12Layer4BeforePkAdrsMessageLoopState,
    c12Layer4BeforePkAdrsMessageStartState, c12Layer4InputState,
    c12Layer4PreBodyState, currentNode] using
    C12SegmentWotsSetup.c12LayerBeforePkAdrsMessageLoop_csum_add7_lt
      (c12Layer4InputState pkSeed pkRoot message sig) j currentNode hj hCNLt
      (by rfl)

theorem c12Layer4BeforePkAdrsMessageEnd_csum_eq_wotsCsum
    (hAfter3 : C12Layer3After3CurrentNodePremise)
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature)
    (hParse : C12Concrete.parseSignatureC12 c12 sig = some sigParsed) :
    lookupValue
        (C12SegmentWotsSetup.c12LayerBeforePkAdrsMessageEnd
          (c12Layer4InputState pkSeed pkRoot message sig)).bindings
        "csum" =
      C12Concrete.wotsCsumC12
        (lookupValue (c12Layer4PreBodyState pkSeed pkRoot message sig).bindings
          "currentNode") := by
  let stInput := c12Layer4InputState pkSeed pkRoot message sig
  let stLoop := c12Layer4BeforePkAdrsMessageLoopState pkSeed pkRoot message sig
  let currentNode :=
    lookupValue (c12Layer4PreBodyState pkSeed pkRoot message sig).bindings
      "currentNode"
  have hCNLt : currentNode < 2 ^ 256 := by
    simpa [currentNode] using
      c12Layer4PreBodyState_currentNode_lt_of_after3_current_node
        hAfter3 pkSeed pkRoot message sig sigParsed hParse
  have hCN :
      lookupValue stLoop.bindings "currentNode" = currentNode := by
    simpa [stLoop, currentNode] using
      c12Layer4BeforePkAdrsMessageLoop_currentNode_prefix
        pkSeed pkRoot message sig 0
  have hCsum0 : lookupValue stLoop.bindings "csum" = 0 := by
    simpa [stLoop, c12Layer4BeforePkAdrsMessageLoopState,
      c12Layer4BeforePkAdrsMessageStartState, c12Layer4InputState,
      c12Layer4PreBodyState] using
      C12SegmentWotsSetup.c12LayerBeforePkAdrsMessageLoopStart_csum_eq
        (c12Layer4InputState pkSeed pkRoot message sig)
  have hFold :=
    C12SegmentWotsSetup.c12WotsMessageFold_csum_eq_wotsCsum
      stLoop currentNode hCNLt hCN hCsum0
  have hState :=
    congrArg (fun s : RuntimeState => lookupValue s.bindings "csum")
      (C12SegmentWotsSetup.c12LayerBeforePkAdrsMessageEnd_eq_foldLoop42
        stInput)
  simpa [stInput, stLoop, c12Layer4BeforePkAdrsMessageLoopState,
    c12Layer4BeforePkAdrsMessageStartState, currentNode] using hState.trans hFold

theorem c12Layer4BeforePkAdrsChecksumLoop_csumShifted_prefix
    (hAfter3 : C12Layer3After3CurrentNodePremise)
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature)
    (hParse : C12Concrete.parseSignatureC12 c12 sig = some sigParsed) :
    lookupValue
        (c12Layer4BeforePkAdrsChecksumLoopState pkSeed pkRoot message sig).bindings
        "csumShifted" =
      C12Concrete.wotsCsumC12
        (lookupValue (c12Layer4PreBodyState pkSeed pkRoot message sig).bindings
          "currentNode") <<< 7 := by
  let stInput := c12Layer4InputState pkSeed pkRoot message sig
  let stMessage :=
    C12SegmentWotsSetup.c12LayerBeforePkAdrsMessageEnd stInput
  let csum :=
    C12Concrete.wotsCsumC12
      (lookupValue (c12Layer4PreBodyState pkSeed pkRoot message sig).bindings
        "currentNode")
  have hCsum :
      lookupValue stMessage.bindings "csum" = csum := by
    simpa [stInput, stMessage, csum] using
      c12Layer4BeforePkAdrsMessageEnd_csum_eq_wotsCsum
        hAfter3 pkSeed pkRoot message sig sigParsed hParse
  have hCsumBound : csum ≤ 7 * 42 := by
    let stLoop := c12Layer4BeforePkAdrsMessageLoopState pkSeed pkRoot message sig
    let currentNode :=
      lookupValue (c12Layer4PreBodyState pkSeed pkRoot message sig).bindings
        "currentNode"
    have hCNLt : currentNode < 2 ^ 256 := by
      simpa [currentNode] using
        c12Layer4PreBodyState_currentNode_lt_of_after3_current_node
          hAfter3 pkSeed pkRoot message sig sigParsed hParse
    have hCN :
        lookupValue stLoop.bindings "currentNode" = currentNode := by
      simpa [stLoop, currentNode] using
        c12Layer4BeforePkAdrsMessageLoop_currentNode_prefix
          pkSeed pkRoot message sig 0
    have hCsum0 : lookupValue stLoop.bindings "csum" = 0 := by
      simpa [stLoop, c12Layer4BeforePkAdrsMessageLoopState,
        c12Layer4BeforePkAdrsMessageStartState, c12Layer4InputState,
        c12Layer4PreBodyState] using
        C12SegmentWotsSetup.c12LayerBeforePkAdrsMessageLoopStart_csum_eq
          (c12Layer4InputState pkSeed pkRoot message sig)
    have hBound :=
      C12SegmentWotsSetup.c12WotsMessageFold_csum_bound
        stLoop 42 currentNode (by omega) hCNLt hCN hCsum0
    have hState :=
      congrArg (fun s : RuntimeState => lookupValue s.bindings "csum")
        (C12SegmentWotsSetup.c12LayerBeforePkAdrsMessageEnd_eq_foldLoop42
          stInput)
    have hMessageBound : lookupValue stMessage.bindings "csum" ≤ 7 * 42 := by
      dsimp [stMessage]
      change
        (fun s : RuntimeState => lookupValue s.bindings "csum")
          (C12SegmentWotsSetup.c12LayerBeforePkAdrsMessageEnd stInput) ≤ 7 * 42
      rw [hState]
      simpa [stInput, stMessage, stLoop, c12Layer4BeforePkAdrsMessageLoopState,
        c12Layer4BeforePkAdrsMessageStartState] using hBound
    rw [← hCsum]
    exact hMessageBound
  have hShiftEval :
      evalExpr [] stMessage (C12SegmentWotsSetup.shlE (C12SegmentWotsSetup.u 7)
        (C12SegmentWotsSetup.v "csum")) = some (csum <<< 7) := by
    have h7 : evalExpr [] stMessage (C12SegmentWotsSetup.u 7) = some 7 := by
      rfl
    have hCsumEval : evalExpr [] stMessage (C12SegmentWotsSetup.v "csum") =
        some csum := by
      show some (lookupValue stMessage.bindings "csum") = some csum
      rw [hCsum]
    have hShiftLt : csum <<< 7 < 2 ^ 256 := by
      rw [Nat.shiftLeft_eq]
      have hSmall : csum * 2 ^ 7 ≤ (7 * 42) * 2 ^ 7 :=
        Nat.mul_le_mul_right _ hCsumBound
      have hBoundSmall : (7 * 42) * 2 ^ 7 < 2 ^ 256 := by decide
      omega
    exact SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded
      stMessage (C12SegmentWotsSetup.u 7) (C12SegmentWotsSetup.v "csum")
      7 csum h7 hCsumEval (by decide) (lt_of_le_of_lt hCsumBound (by decide))
      hShiftLt
  unfold c12Layer4BeforePkAdrsChecksumLoopState
    c12Layer4BeforePkAdrsChecksumStartState
    C12SegmentWotsSetup.c12LayerBeforePkAdrsChecksumStart
  rw [MemoryKit.lookupValue_bindValue_ne _ "j" "csumShifted" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_self]
  rw [hShiftEval]
  simp [csum]

/-- The layer-4 checksum-loop prefix preserves the public-seed scratch word. -/
theorem c12Layer4BeforePkAdrsChecksumLoop_seed_prefix
    (pkSeed pkRoot message sig : ByteArray) (j : Nat) (hj : j < 3) :
    ((SphincsMinusVerifiers.ClimbLoop.foldLoop "j"
        C12SegmentWotsSetup.c12WotsChecksumStep
        (c12Layer4BeforePkAdrsChecksumLoopState pkSeed pkRoot message sig)
        0 j).world.memory 0x00).val =
      c12Layer4ParsedSeed pkSeed := by
  let stChecksumLoop := c12Layer4BeforePkAdrsChecksumLoopState pkSeed pkRoot message sig
  rw [C12SegmentWotsSetup.c12WotsChecksumFold_preserves_memory_zero_bound
    stChecksumLoop j (by omega)]
  have hStart :=
    C12SegmentWotsSetup.c12LayerBeforePkAdrsChecksumLoopStart_preserves_memory_zero
      (c12Layer4InputState pkSeed pkRoot message sig)
  rw [show (stChecksumLoop.world.memory 0x00).val =
      ((c12Layer4InputState pkSeed pkRoot message sig).world.memory 0x00).val by
    simpa [stChecksumLoop, c12Layer4BeforePkAdrsChecksumLoopState,
      c12Layer4BeforePkAdrsChecksumStartState] using hStart]
  rw [c12Layer4InputState_eq_preBodyState]
  exact c12Layer4PreBodyState_preserves_memory_zero pkSeed pkRoot message sig

theorem c12Layer4BeforePkAdrsChecksumLoop_wotsBase_prefix
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature)
    (hParse : C12Concrete.parseSignatureC12 c12 sig = some sigParsed)
    (j : Nat) :
    lookupValue
        (SphincsMinusVerifiers.ClimbLoop.foldLoop "j"
          C12SegmentWotsSetup.c12WotsChecksumStep
          (c12Layer4BeforePkAdrsChecksumLoopState pkSeed pkRoot message sig)
          0 j).bindings
        "wotsBase" =
      C12Concrete.wotsBaseC12 4
        (c12Layer4NextTree
          (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
        (c12Layer4Leaf
          (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex) := by
  let stChecksumLoop := c12Layer4BeforePkAdrsChecksumLoopState pkSeed pkRoot message sig
  rw [C12SegmentWotsSetup.c12WotsChecksumFold_preserves_wotsBase]
  rw [show lookupValue stChecksumLoop.bindings "wotsBase" =
      lookupValue
        (SphincsMinusVerifiers.ClimbLoop.foldLoop "i"
          C12SegmentWotsSetup.c12WotsMessageStep
          (c12Layer4BeforePkAdrsMessageLoopState pkSeed pkRoot message sig)
          0 42).bindings
        "wotsBase" by
    simpa [stChecksumLoop, c12Layer4BeforePkAdrsChecksumLoopState,
      c12Layer4BeforePkAdrsChecksumStartState,
      c12Layer4BeforePkAdrsMessageLoopState,
      c12Layer4BeforePkAdrsMessageStartState] using
      C12SegmentWotsSetup.c12LayerBeforePkAdrsChecksumLoopStart_wotsBase_eq_foldLoop42
        (c12Layer4InputState pkSeed pkRoot message sig)]
  exact c12Layer4BeforePkAdrsMessageLoop_wotsBase_prefix
    pkSeed pkRoot message sig sigParsed hParse 42

theorem c12Layer4BeforePkAdrsChecksumLoop_wotsPtr_prefix
    (pkSeed pkRoot message sig : ByteArray) (j : Nat) :
    lookupValue
        (SphincsMinusVerifiers.ClimbLoop.foldLoop "j"
          C12SegmentWotsSetup.c12WotsChecksumStep
          (c12Layer4BeforePkAdrsChecksumLoopState pkSeed pkRoot message sig)
          0 j).bindings
        "wotsPtr" =
      MkC13State.sigDataOffset + (2592 + 784 * 4) := by
  let stChecksumLoop := c12Layer4BeforePkAdrsChecksumLoopState pkSeed pkRoot message sig
  rw [C12SegmentWotsSetup.c12WotsChecksumFold_preserves_wotsPtr]
  rw [show lookupValue stChecksumLoop.bindings "wotsPtr" =
      lookupValue
        (SphincsMinusVerifiers.ClimbLoop.foldLoop "i"
          C12SegmentWotsSetup.c12WotsMessageStep
          (c12Layer4BeforePkAdrsMessageLoopState pkSeed pkRoot message sig)
          0 42).bindings
        "wotsPtr" by
    simpa [stChecksumLoop, c12Layer4BeforePkAdrsChecksumLoopState,
      c12Layer4BeforePkAdrsChecksumStartState,
      c12Layer4BeforePkAdrsMessageLoopState,
      c12Layer4BeforePkAdrsMessageStartState] using
      C12SegmentWotsSetup.c12LayerBeforePkAdrsChecksumLoopStart_wotsPtr_eq_foldLoop42
        (c12Layer4InputState pkSeed pkRoot message sig)]
  exact c12Layer4BeforePkAdrsMessageLoop_wotsPtr_prefix
    pkSeed pkRoot message sig 42

theorem c12Layer4BeforePkAdrsChecksumLoop_csumShifted_fold_prefix
    (hAfter3 : C12Layer3After3CurrentNodePremise)
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature)
    (hParse : C12Concrete.parseSignatureC12 c12 sig = some sigParsed)
    (j : Nat) :
    lookupValue
        (SphincsMinusVerifiers.ClimbLoop.foldLoop "j"
          C12SegmentWotsSetup.c12WotsChecksumStep
          (c12Layer4BeforePkAdrsChecksumLoopState pkSeed pkRoot message sig)
          0 j).bindings
        "csumShifted" =
      C12Concrete.wotsCsumC12
        (lookupValue (c12Layer4PreBodyState pkSeed pkRoot message sig).bindings
          "currentNode") <<< 7 := by
  let stChecksumLoop := c12Layer4BeforePkAdrsChecksumLoopState pkSeed pkRoot message sig
  rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_preserves_lookup
    "j" "csumShifted" C12SegmentWotsSetup.c12WotsChecksumStep (by decide)
    (fun s => C12SegmentWotsSetup.c12WotsChecksumStep_preserves_lookup_of_fresh
      "csumShifted" (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) s)]
  exact c12Layer4BeforePkAdrsChecksumLoop_csumShifted_prefix
    hAfter3 pkSeed pkRoot message sig sigParsed hParse

/-- The raw layer-4 WOTS calldata word at message index `j`, once masked by the
message loop, is exactly the parsed WOTS chain word used by `c12WotsChainsEnd`. -/
theorem c12Layer4_message_raw_mask_eq_wots_chain
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature)
    (hParse : C12Concrete.parseSignatureC12 c12 sig = some sigParsed)
    (j : Nat) (hj : j < 42) :
    SphincsMinusVerifierSpec.C13Concrete.maskN
      (Compiler.Proofs.YulGeneration.calldataloadWord 0
        (MkC13State.headWords pkSeed pkRoot message sig.size ++
          MkC13State.bytesToWords sig)
        (MkC13State.sigDataOffset + (2592 + 784 * 4 + 16 * j))) =
      SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
        (((c12Layer4Sig sigParsed).wots.chains[j]?).getD ⟨#[]⟩) := by
  have hgen :=
    SphincsMinusVerifiers.SiblingCalldata.masked_sig_read_eq_wordOfHash16_gen
      pkSeed pkRoot message sig (2592 + 784 * 4 + 16 * j)
  have hRead :=
    c12_layer4_wotsChain_read16_of_parse sig sigParsed hParse j (by omega : j < 45)
  change
    (Compiler.Proofs.YulGeneration.calldataloadWord 0
        (MkC13State.headWords pkSeed pkRoot message sig.size ++
          MkC13State.bytesToWords sig)
        (MkC13State.sigDataOffset + (2592 + 784 * 4 + 16 * j))).land
      N_MASK =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          (((c12Layer4ParsedWotsChains sigParsed)[j]?).getD ⟨#[]⟩)
  rw [hgen]
  rw [← hRead]

/-- The raw layer-4 WOTS calldata word at checksum index `42 + j`, once masked,
is exactly the parsed WOTS chain word used by `c12WotsChainsEnd`. -/
theorem c12Layer4_checksum_raw_mask_eq_wots_chain
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature)
    (hParse : C12Concrete.parseSignatureC12 c12 sig = some sigParsed)
    (j : Nat) (hj : j < 3) :
    SphincsMinusVerifierSpec.C13Concrete.maskN
      (Compiler.Proofs.YulGeneration.calldataloadWord 0
        (MkC13State.headWords pkSeed pkRoot message sig.size ++
          MkC13State.bytesToWords sig)
        (MkC13State.sigDataOffset + (2592 + 784 * 4 + 16 * (42 + j)))) =
      SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
        (((c12Layer4Sig sigParsed).wots.chains[42 + j]?).getD ⟨#[]⟩) := by
  have hgen :=
    SphincsMinusVerifiers.SiblingCalldata.masked_sig_read_eq_wordOfHash16_gen
      pkSeed pkRoot message sig (2592 + 784 * 4 + 16 * (42 + j))
  have hRead :=
    c12_layer4_wotsChain_read16_of_parse sig sigParsed hParse (42 + j)
      (by omega : 42 + j < 45)
  change
    (Compiler.Proofs.YulGeneration.calldataloadWord 0
        (MkC13State.headWords pkSeed pkRoot message sig.size ++
          MkC13State.bytesToWords sig)
        (MkC13State.sigDataOffset + (2592 + 784 * 4 + 16 * (42 + j)))).land
      N_MASK =
        SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
          (((c12Layer4ParsedWotsChains sigParsed)[42 + j]?).getD ⟨#[]⟩)
  rw [hgen]
  rw [← hRead]

set_option maxHeartbeats 700000 in
/-- The executable layer-4 WOTS checksum loop writes the expected chain-hash
word at checksum index `42 + j`, in runtime-current-node form. -/
theorem c12Layer4BeforePkAdrsChecksumLoop_cell_chainHash_of_after3_current_node
    (hAfter3 : C12Layer3After3CurrentNodePremise)
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature)
    (hParse : C12Concrete.parseSignatureC12 c12 sig = some sigParsed)
    (j : Nat) (hj : j < 3) :
    ((SphincsMinusVerifiers.ClimbLoop.foldLoop "j"
        C12SegmentWotsSetup.c12WotsChecksumStep
        (c12Layer4BeforePkAdrsChecksumLoopState pkSeed pkRoot message sig)
        0 3).world.memory (0x80 + 32 * (42 + j))).val =
      SphincsMinusVerifierSpec.C12Concrete.chainHashC12
        (c12Layer4ParsedSeed pkSeed)
        (C12Concrete.wotsBaseC12 4
          (c12Layer4NextTree
            (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
          (c12Layer4Leaf
            (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
          ||| ((42 + j) <<< 64))
        (((C12Concrete.wotsCsumC12
            (lookupValue
              (c12Layer4PreBodyState pkSeed pkRoot message sig).bindings
              "currentNode") <<< 7) >>> (13 - 3 * j)) &&& 7)
        (7 - (((C12Concrete.wotsCsumC12
            (lookupValue
              (c12Layer4PreBodyState pkSeed pkRoot message sig).bindings
              "currentNode") <<< 7) >>> (13 - 3 * j)) &&& 7)) 0
        (SphincsMinusVerifierSpec.C13Concrete.maskN
          (Compiler.Proofs.YulGeneration.calldataloadWord 0
            (MkC13State.headWords pkSeed pkRoot message sig.size ++
              MkC13State.bytesToWords sig)
            (MkC13State.sigDataOffset + (2592 + 784 * 4 + 16 * (42 + j))))) := by
  let stLoop := c12Layer4BeforePkAdrsChecksumLoopState pkSeed pkRoot message sig
  let currentNode :=
    lookupValue (c12Layer4PreBodyState pkSeed pkRoot message sig).bindings
      "currentNode"
  let wotsBase :=
    C12Concrete.wotsBaseC12 4
      (c12Layer4NextTree
        (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
      (c12Layer4Leaf
        (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
  let wotsPtr := MkC13State.sigDataOffset + (2592 + 784 * 4)
  let csumShifted := C12Concrete.wotsCsumC12 currentNode <<< 7
  let digit := ((csumShifted >>> (13 - 3 * j)) &&& 7)
  let raw :=
    Compiler.Proofs.YulGeneration.calldataloadWord 0
      (MkC13State.headWords pkSeed pkRoot message sig.size ++
        MkC13State.bytesToWords sig)
      (MkC13State.sigDataOffset + (2592 + 784 * 4 + 16 * (42 + j)))
  have hCNLt : currentNode < 2 ^ 256 := by
    simpa [currentNode] using
      c12Layer4PreBodyState_currentNode_lt_of_after3_current_node
        hAfter3 pkSeed pkRoot message sig sigParsed hParse
  have hWBaseLt : wotsBase < 2 ^ 256 := by
    let idx := (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex
    let tree := c12Layer4NextTree idx
    let leaf := c12Layer4Leaf idx
    have hTree : tree < 2 ^ 64 := by
      simpa [tree, idx] using
        (by
          rw [c12Layer4NextTree_of_parsed_eq_zero]
          decide : c12Layer4NextTree idx < 2 ^ 64)
    have hLeaf : leaf < 2 ^ 64 := by
      exact lt_trans (c12Layer4Leaf_lt_16 idx) (by decide)
    simpa [wotsBase, tree, leaf, idx] using
      c12_wotsBaseC12_layer4_lt_two_pow_256 tree leaf hTree hLeaf
  have hRawLt : raw < 2 ^ 256 := by
    unfold raw
    have hoff4 :
        4 ≤ MkC13State.sigDataOffset + (2592 + 784 * 4 + 16 * (42 + j)) := by
      norm_num [MkC13State.sigDataOffset]
      omega
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.calldataloadWord_lt_of_ge4
      0
      (MkC13State.headWords pkSeed pkRoot message sig.size ++
        MkC13State.bytesToWords sig)
      (MkC13State.sigDataOffset + (2592 + 784 * 4 + 16 * (42 + j))) hoff4
  have hCsumShiftedLt : csumShifted < 2 ^ 256 := by
    have hBound : C12Concrete.wotsCsumC12 currentNode ≤ 7 * 42 := by
      let stMessageLoop := c12Layer4BeforePkAdrsMessageLoopState pkSeed pkRoot message sig
      have hCN :
          lookupValue stMessageLoop.bindings "currentNode" = currentNode := by
        simpa [stMessageLoop, currentNode] using
          c12Layer4BeforePkAdrsMessageLoop_currentNode_prefix
            pkSeed pkRoot message sig 0
      have hCsum0 : lookupValue stMessageLoop.bindings "csum" = 0 := by
        simpa [stMessageLoop, c12Layer4BeforePkAdrsMessageLoopState,
          c12Layer4BeforePkAdrsMessageStartState, c12Layer4InputState,
          c12Layer4PreBodyState] using
          C12SegmentWotsSetup.c12LayerBeforePkAdrsMessageLoopStart_csum_eq
            (c12Layer4InputState pkSeed pkRoot message sig)
      have hFoldBound :=
        C12SegmentWotsSetup.c12WotsMessageFold_csum_bound
          stMessageLoop 42 currentNode (by omega) hCNLt hCN hCsum0
      have hFoldEq :=
        C12SegmentWotsSetup.c12WotsMessageFold_csum_eq_wotsCsum
          stMessageLoop currentNode hCNLt hCN hCsum0
      omega
    unfold csumShifted
    rw [Nat.shiftLeft_eq]
    have hSmall : C12Concrete.wotsCsumC12 currentNode * 2 ^ 7 ≤
        (7 * 42) * 2 ^ 7 := Nat.mul_le_mul_right _ hBound
    have hBoundSmall : (7 * 42) * 2 ^ 7 < 2 ^ 256 := by decide
    omega
  have hDigitEval :
      evalExpr []
        { (SphincsMinusVerifiers.ClimbLoop.foldLoop "j"
            C12SegmentWotsSetup.c12WotsChecksumStep stLoop 0 j) with
          bindings :=
            bindValue
              (SphincsMinusVerifiers.ClimbLoop.foldLoop "j"
                C12SegmentWotsSetup.c12WotsChecksumStep stLoop 0 j).bindings
              "j" (wordNormalize j) }
        (C12SegmentWotsSetup.andE
          (C12SegmentWotsSetup.shrE
            (C12SegmentWotsSetup.subE (C12SegmentWotsSetup.u 13)
              (C12SegmentWotsSetup.mulE (C12SegmentWotsSetup.u 3)
                (C12SegmentWotsSetup.v "j")))
            (C12SegmentWotsSetup.v "csumShifted"))
          (C12SegmentWotsSetup.u 7)) =
        some digit := by
    let beforeJ :=
      SphincsMinusVerifiers.ClimbLoop.foldLoop "j"
        C12SegmentWotsSetup.c12WotsChecksumStep stLoop 0 j
    let atJ : RuntimeState :=
      { beforeJ with bindings := bindValue beforeJ.bindings "j" (wordNormalize j) }
    have hJ : lookupValue atJ.bindings "j" = j := by
      dsimp [atJ]
      rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self,
        C12SegmentWotsSetup.c12_wots_idxNorm67 j (by omega)]
    have hCsum :
        lookupValue atJ.bindings "csumShifted" = csumShifted := by
      dsimp [atJ, beforeJ]
      rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_ne
        _ "j" "csumShifted" _ (by decide)]
      simpa [stLoop, currentNode, csumShifted] using
        c12Layer4BeforePkAdrsChecksumLoop_csumShifted_fold_prefix
          hAfter3 pkSeed pkRoot message sig sigParsed hParse j
    simpa [atJ, beforeJ, stLoop, csumShifted, digit] using
      C12SegmentWotsSetup.evalExpr_checksum_digit_eq
        atJ j csumShifted hj hJ hCsum hCsumShiftedLt
  have hCdLoad : ∀ (s : RuntimeState),
      lookupValue s.bindings "wotsPtr" = wotsPtr →
      lookupValue s.bindings "i" = 42 + j →
      s.world =
        (SphincsMinusVerifiers.ClimbLoop.foldLoop "j"
          C12SegmentWotsSetup.c12WotsChecksumStep stLoop 0 j).world →
      evalExpr [] s
          (.calldataload
            (.add (.localVar "wotsPtr")
              (.shl (.literal 4) (.localVar "i")))) = some raw := by
    intro s hW hI hWorld
    simpa [raw, wotsPtr, stLoop] using
      c12Layer4BeforePkAdrsChecksumLoop_cdload_raw
        pkSeed pkRoot message sig j hj s
        (by simpa [wotsPtr] using hW) hI
        (by simpa [stLoop] using hWorld)
  simpa [stLoop, currentNode, wotsBase, wotsPtr, csumShifted, digit, raw] using
    C12SegmentWotsSetup.c12WotsChecksumLoop_mem_at_j_eq_at
      stLoop j (c12Layer4ParsedSeed pkSeed) digit wotsBase wotsPtr raw hj
      hWBaseLt (C12SegmentWotsSetup.and_seven_le_seven _)
      hRawLt
      (by
        simpa [stLoop] using
          c12Layer4BeforePkAdrsChecksumLoop_seed_prefix
            pkSeed pkRoot message sig j hj)
      (by
        simpa [stLoop, wotsBase] using
          c12Layer4BeforePkAdrsChecksumLoop_wotsBase_prefix
            pkSeed pkRoot message sig sigParsed hParse j)
      (by
        simpa [stLoop, wotsPtr] using
          c12Layer4BeforePkAdrsChecksumLoop_wotsPtr_prefix
            pkSeed pkRoot message sig j)
      hDigitEval hCdLoad

set_option maxHeartbeats 700000 in
/-- The executable layer-4 WOTS message loop writes the expected chain-hash
word at message index `j`, still in the runtime-current-node form and before
the checksum suffix is considered. -/
theorem c12Layer4BeforePkAdrsMessageLoop_cell_chainHash_of_after3_current_node
    (hAfter3 : C12Layer3After3CurrentNodePremise)
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature)
    (hParse : C12Concrete.parseSignatureC12 c12 sig = some sigParsed)
    (j : Nat) (hj : j < 42) :
    ((SphincsMinusVerifiers.ClimbLoop.foldLoop "i"
        C12SegmentWotsSetup.c12WotsMessageStep
        (c12Layer4BeforePkAdrsMessageLoopState pkSeed pkRoot message sig)
        0 42).world.memory (0x80 + 32 * j)).val =
      SphincsMinusVerifierSpec.C12Concrete.chainHashC12
        (c12Layer4ParsedSeed pkSeed)
        (C12Concrete.wotsBaseC12 4
          (c12Layer4NextTree
            (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
          (c12Layer4Leaf
            (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
          ||| (j <<< 64))
        ((lookupValue
            (c12Layer4PreBodyState pkSeed pkRoot message sig).bindings
            "currentNode" >>> (128 + 3 * j)) &&& 7)
        (7 - ((lookupValue
            (c12Layer4PreBodyState pkSeed pkRoot message sig).bindings
            "currentNode" >>> (128 + 3 * j)) &&& 7)) 0
        (SphincsMinusVerifierSpec.C13Concrete.maskN
          (Compiler.Proofs.YulGeneration.calldataloadWord 0
            (MkC13State.headWords pkSeed pkRoot message sig.size ++
              MkC13State.bytesToWords sig)
            (MkC13State.sigDataOffset + (2592 + 784 * 4 + 16 * j)))) := by
  let stLoop := c12Layer4BeforePkAdrsMessageLoopState pkSeed pkRoot message sig
  let currentNode :=
    lookupValue (c12Layer4PreBodyState pkSeed pkRoot message sig).bindings
      "currentNode"
  let wotsBase :=
    C12Concrete.wotsBaseC12 4
      (c12Layer4NextTree
        (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
      (c12Layer4Leaf
        (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
  let wotsPtr := MkC13State.sigDataOffset + (2592 + 784 * 4)
  let raw :=
    Compiler.Proofs.YulGeneration.calldataloadWord 0
      (MkC13State.headWords pkSeed pkRoot message sig.size ++
        MkC13State.bytesToWords sig)
      (MkC13State.sigDataOffset + (2592 + 784 * 4 + 16 * j))
  have hCNLt : currentNode < 2 ^ 256 := by
    simpa [currentNode] using
      c12Layer4PreBodyState_currentNode_lt_of_after3_current_node
        hAfter3 pkSeed pkRoot message sig sigParsed hParse
  have hWBaseLt : wotsBase < 2 ^ 256 := by
    let idx := (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex
    let tree := c12Layer4NextTree idx
    let leaf := c12Layer4Leaf idx
    have hTree : tree < 2 ^ 64 := by
      simpa [tree, idx] using
        (by
          rw [c12Layer4NextTree_of_parsed_eq_zero]
          decide : c12Layer4NextTree idx < 2 ^ 64)
    have hLeaf : leaf < 2 ^ 64 := by
      exact lt_trans (c12Layer4Leaf_lt_16 idx) (by decide)
    simpa [wotsBase, tree, leaf, idx] using
      c12_wotsBaseC12_layer4_lt_two_pow_256 tree leaf hTree hLeaf
  have hRawLt : raw < 2 ^ 256 := by
    unfold raw
    have hoff4 :
        4 ≤ MkC13State.sigDataOffset + (2592 + 784 * 4 + 16 * j) := by
      norm_num [MkC13State.sigDataOffset]
      omega
    exact SphincsMinusVerifiers.ClimbMemFrameMerkle.calldataloadWord_lt_of_ge4
      0
      (MkC13State.headWords pkSeed pkRoot message sig.size ++
        MkC13State.bytesToWords sig)
      (MkC13State.sigDataOffset + (2592 + 784 * 4 + 16 * j)) hoff4
  have hCdLoad : ∀ (s : RuntimeState),
      lookupValue s.bindings "wotsPtr" = wotsPtr →
      lookupValue s.bindings "i" = j →
      s.world =
        (SphincsMinusVerifiers.ClimbLoop.foldLoop "i"
          C12SegmentWotsSetup.c12WotsMessageStep stLoop 0 j).world →
      evalExpr [] s
          (.calldataload
            (.add (.localVar "wotsPtr")
              (.shl (.literal 4) (.localVar "i")))) = some raw := by
    intro s hW hI hWorld
    simpa [raw, wotsPtr, stLoop] using
      c12Layer4BeforePkAdrsMessageLoop_cdload_raw
        pkSeed pkRoot message sig j hj s
        (by simpa [wotsPtr] using hW) hI
        (by simpa [stLoop] using hWorld)
  simpa [stLoop, currentNode, wotsBase, wotsPtr, raw] using
    C12SegmentWotsSetup.c12WotsMessageLoop_mem_at_j_eq
      stLoop j (c12Layer4ParsedSeed pkSeed) currentNode
      (lookupValue
        (SphincsMinusVerifiers.ClimbLoop.foldLoop "i"
          C12SegmentWotsSetup.c12WotsMessageStep stLoop 0 j).bindings
        "csum")
      wotsBase wotsPtr raw hj hCNLt hWBaseLt
      (by
        simpa [stLoop, currentNode] using
          c12Layer4BeforePkAdrsMessageLoop_csum_add7_lt_of_after3_current_node
            hAfter3 pkSeed pkRoot message sig sigParsed hParse j hj)
      hRawLt
      (by
        simpa [stLoop] using
          c12Layer4BeforePkAdrsMessageLoop_seed_prefix
            pkSeed pkRoot message sig j hj)
      (by
        simpa [stLoop, currentNode] using
          c12Layer4BeforePkAdrsMessageLoop_currentNode_prefix
            pkSeed pkRoot message sig j)
      rfl
      (by
        simpa [stLoop, wotsBase] using
          c12Layer4BeforePkAdrsMessageLoop_wotsBase_prefix
            pkSeed pkRoot message sig sigParsed hParse j)
      (by
        simpa [stLoop, wotsPtr] using
          c12Layer4BeforePkAdrsMessageLoop_wotsPtr_prefix
            pkSeed pkRoot message sig j)
      hCdLoad

/-- Package the executable layer-4 WOTS message-loop cell theorem into the
runtime-current-node premise used by the final C12 WOTS-PK memory bridge. -/
theorem c12Layer4BeforePkAdrs_message_cells_runtime_node_of_after3_current_node
    (hAfter3 : C12Layer3After3CurrentNodePremise) :
    C12Layer4WotsPkBeforePkAdrsMessageCellsRuntimeNodePremise := by
  intro pkSeed pkRoot message sig sigParsed hParse j hj
  let stInput := c12Layer4InputState pkSeed pkRoot message sig
  let addr := 0x80 + 32 * j
  have hLoop :=
    c12Layer4BeforePkAdrsMessageLoop_cell_chainHash_of_after3_current_node
      hAfter3 pkSeed pkRoot message sig sigParsed hParse j hj
  have hRaw :=
    c12Layer4_message_raw_mask_eq_wots_chain
      pkSeed pkRoot message sig sigParsed hParse j hj
  have hLoop' :
      ((SphincsMinusVerifiers.ClimbLoop.foldLoop "i"
          C12SegmentWotsSetup.c12WotsMessageStep
          (c12Layer4BeforePkAdrsMessageLoopState pkSeed pkRoot message sig)
          0 42).world.memory addr).val =
        SphincsMinusVerifierSpec.C12Concrete.chainHashC12
          (c12Layer4ParsedSeed pkSeed)
          (C12Concrete.wotsBaseC12 4
            (c12Layer4NextTree
              (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
            (c12Layer4Leaf
              (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
            ||| (j <<< 64))
          ((lookupValue
              (c12Layer4PreBodyState pkSeed pkRoot message sig).bindings
              "currentNode" >>> (128 + 3 * j)) &&& 7)
          (7 - ((lookupValue
              (c12Layer4PreBodyState pkSeed pkRoot message sig).bindings
              "currentNode" >>> (128 + 3 * j)) &&& 7)) 0
          (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
            (((c12Layer4Sig sigParsed).wots.chains[j]?).getD ⟨#[]⟩)) := by
    simpa only [addr, hRaw] using hLoop
  have hList :=
    c12WotsChainsEnd_getElem_message
      (c12Layer4ParsedSeed pkSeed) 4
      (c12Layer4NextTree
        (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
      (c12Layer4Leaf
        (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
      (lookupValue (c12Layer4PreBodyState pkSeed pkRoot message sig).bindings
        "currentNode")
      (c12Layer4Sig sigParsed).wots j hj
  have hMessageEndEq :
      ((C12SegmentWotsSetup.c12LayerBeforePkAdrsMessageEnd stInput).world.memory
          addr).val =
        ((SphincsMinusVerifiers.ClimbLoop.foldLoop "i"
            C12SegmentWotsSetup.c12WotsMessageStep
            (c12Layer4BeforePkAdrsMessageLoopState pkSeed pkRoot message sig)
            0 42).world.memory addr).val := by
    have hState :=
      congrArg
        (fun s : RuntimeState => ((s.world.memory addr).val))
        (C12SegmentWotsSetup.c12LayerBeforePkAdrsMessageEnd_eq_foldLoop42
          stInput)
    simpa [stInput, c12Layer4BeforePkAdrsMessageLoopState,
      c12Layer4BeforePkAdrsMessageStartState] using hState
  have hBeforePkAdrsEq :
      ((C12SegmentWotsSetup.c12LayerStateBeforePkAdrs stInput).world.memory
          addr).val =
        ((C12SegmentWotsSetup.c12LayerBeforePkAdrsMessageEnd stInput).world.memory
          addr).val := by
    simpa [addr] using
      C12SegmentWotsSetup.c12LayerStateBeforePkAdrs_message_cell_eq_message_end
        stInput j hj
  have hEnd :
      ((C12SegmentWotsSetup.c12LayerStateBeforePkAdrs stInput).world.memory
          addr).val =
        (c12WotsChainsEnd
          (c12Layer4ParsedSeed pkSeed) 4
          (c12Layer4NextTree
            (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
          (c12Layer4Leaf
            (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
          (lookupValue (c12Layer4PreBodyState pkSeed pkRoot message sig).bindings
            "currentNode")
          (c12Layer4Sig sigParsed).wots)[j]'(by
            rw [c12WotsChainsEnd_length]
            omega) := by
    exact hBeforePkAdrsEq.trans (hMessageEndEq.trans (hLoop'.trans hList.symm))
  simpa [c12Layer4BeforePkAdrsState, stInput, addr] using hEnd

set_option maxHeartbeats 900000 in
/-- Package the executable layer-4 WOTS checksum-loop cell theorem into the
runtime-current-node premise used by the final C12 WOTS-PK memory bridge. -/
theorem c12Layer4BeforePkAdrs_checksum_cells_runtime_node_of_after3_current_node
    (hAfter3 : C12Layer3After3CurrentNodePremise) :
    C12Layer4WotsPkBeforePkAdrsChecksumCellsRuntimeNodePremise := by
  intro pkSeed pkRoot message sig sigParsed hParse j hj
  let stInput := c12Layer4InputState pkSeed pkRoot message sig
  let addr := 0x80 + 32 * (42 + j)
  have hLoop :=
    c12Layer4BeforePkAdrsChecksumLoop_cell_chainHash_of_after3_current_node
      hAfter3 pkSeed pkRoot message sig sigParsed hParse j hj
  have hRaw :=
    c12Layer4_checksum_raw_mask_eq_wots_chain
      pkSeed pkRoot message sig sigParsed hParse j hj
  have hLoop' :
      ((SphincsMinusVerifiers.ClimbLoop.foldLoop "j"
          C12SegmentWotsSetup.c12WotsChecksumStep
          (c12Layer4BeforePkAdrsChecksumLoopState pkSeed pkRoot message sig)
          0 3).world.memory addr).val =
        SphincsMinusVerifierSpec.C12Concrete.chainHashC12
          (c12Layer4ParsedSeed pkSeed)
          (C12Concrete.wotsBaseC12 4
            (c12Layer4NextTree
              (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
            (c12Layer4Leaf
              (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
            ||| ((42 + j) <<< 64))
          (((C12Concrete.wotsCsumC12
              (lookupValue
                (c12Layer4PreBodyState pkSeed pkRoot message sig).bindings
                "currentNode") <<< 7) >>> (13 - 3 * j)) &&& 7)
          (7 - (((C12Concrete.wotsCsumC12
              (lookupValue
                (c12Layer4PreBodyState pkSeed pkRoot message sig).bindings
                "currentNode") <<< 7) >>> (13 - 3 * j)) &&& 7)) 0
          (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
            (((c12Layer4Sig sigParsed).wots.chains[42 + j]?).getD ⟨#[]⟩)) := by
    simpa only [addr, hRaw] using hLoop
  have hList :=
    c12WotsChainsEnd_getElem_checksum
      (c12Layer4ParsedSeed pkSeed) 4
      (c12Layer4NextTree
        (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
      (c12Layer4Leaf
        (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
      (lookupValue (c12Layer4PreBodyState pkSeed pkRoot message sig).bindings
        "currentNode")
      (c12Layer4Sig sigParsed).wots j hj
  have hBeforePkAdrsEq :
      ((C12SegmentWotsSetup.c12LayerStateBeforePkAdrs stInput).world.memory
          addr).val =
        ((SphincsMinusVerifiers.ClimbLoop.foldLoop "j"
          C12SegmentWotsSetup.c12WotsChecksumStep
          (c12Layer4BeforePkAdrsChecksumLoopState pkSeed pkRoot message sig)
          0 3).world.memory addr).val := by
    have hState :=
      congrArg
        (fun s : RuntimeState => ((s.world.memory addr).val))
        (C12SegmentWotsSetup.c12LayerStateBeforePkAdrs_eq_checksum_fold
          stInput)
    have h3 : wordNormalize 3 = 3 := by
      rw [wordNormalize_eq_mod,
        show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
        Nat.mod_eq_of_lt (by decide)]
    simpa [stInput, c12Layer4BeforePkAdrsChecksumLoopState,
      c12Layer4BeforePkAdrsChecksumStartState, h3] using hState
  have hEnd :
      ((C12SegmentWotsSetup.c12LayerStateBeforePkAdrs stInput).world.memory
          addr).val =
        (c12WotsChainsEnd
          (c12Layer4ParsedSeed pkSeed) 4
          (c12Layer4NextTree
            (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
          (c12Layer4Leaf
            (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
          (lookupValue (c12Layer4PreBodyState pkSeed pkRoot message sig).bindings
            "currentNode")
          (c12Layer4Sig sigParsed).wots)[42 + j]'(by
            rw [c12WotsChainsEnd_length]
            omega) := by
    exact hBeforePkAdrsEq.trans (hLoop'.trans hList.symm)
  simpa [c12Layer4BeforePkAdrsState, stInput, addr] using hEnd

/-- The message-cell premise follows from the exact runtime-node WOTS message
cells plus the layer-4 pre-body current-node handoff. -/
theorem c12Layer4BeforePkAdrs_message_cells_of_runtime_node_cells
    (hRuntime : C12Layer4WotsPkBeforePkAdrsMessageCellsRuntimeNodePremise)
    (hCurrent : C12Layer4PreBodyCurrentNodePremise) :
    C12Layer4WotsPkBeforePkAdrsMessageCellsPremise := by
  intro pkSeed pkRoot message sig sigParsed hParse j hj
  have hCell := hRuntime pkSeed pkRoot message sig sigParsed hParse j hj
  have hNode := hCurrent pkSeed pkRoot message sig sigParsed hParse
  simpa only [hNode] using hCell

/-- The checksum-cell premise follows from the exact runtime-node WOTS checksum
cells plus the layer-4 pre-body current-node handoff. -/
theorem c12Layer4BeforePkAdrs_checksum_cells_of_runtime_node_cells
    (hRuntime : C12Layer4WotsPkBeforePkAdrsChecksumCellsRuntimeNodePremise)
    (hCurrent : C12Layer4PreBodyCurrentNodePremise) :
    C12Layer4WotsPkBeforePkAdrsChecksumCellsPremise := by
  intro pkSeed pkRoot message sig sigParsed hParse j hj
  have hCell := hRuntime pkSeed pkRoot message sig sigParsed hParse j hj
  have hNode := hCurrent pkSeed pkRoot message sig sigParsed hParse
  simpa only [hNode] using hCell

/-- Reassemble the 45 generated cells at `beforePkAdrs` from the exact
message-loop and checksum-loop components. -/
theorem c12Layer4BeforePkAdrs_cells_of_message_checksum_cells
    (hMsg : C12Layer4WotsPkBeforePkAdrsMessageCellsPremise)
    (hChecksum : C12Layer4WotsPkBeforePkAdrsChecksumCellsPremise) :
    C12Layer4WotsPkBeforePkAdrsCellsPremise := by
  intro pkSeed pkRoot message sig sigParsed hParse j hj
  by_cases hj42 : j < 42
  · have hCell := hMsg pkSeed pkRoot message sig sigParsed hParse j hj42
    exact hCell
  · have hjGe : 42 ≤ j := by omega
    have hjSub : j - 42 < 3 := by omega
    have hCell :=
      hChecksum pkSeed pkRoot message sig sigParsed hParse (j - 42) hjSub
    have hIdx : 42 + (j - 42) = j := by omega
    simpa [hIdx] using hCell

/-- The suffix from the layer-4 `beforePkAdrs` cutpoint to the pre-copy cutpoint
only binds/stores the WOTS-PK address at `0x20`, so it preserves every generated
chain-end cell at `0x80 + 32*j`. -/
theorem c12Layer4BeforeWotsPkCopy_chain_cell_eq_beforePkAdrs
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature)
    (hParse : C12Concrete.parseSignatureC12 c12 sig = some sigParsed) (j : Nat) :
    ((c12Layer4BeforeWotsPkCopyState pkSeed pkRoot message sig).world.memory
        (0x80 + 32 * j)).val =
      ((c12Layer4BeforePkAdrsState pkSeed pkRoot message sig).world.memory
        (0x80 + 32 * j)).val := by
  let st0 : RuntimeState :=
    C12SegmentWotsSetup.c12LayerStateBeforePkAdrs
      (c12Layer4InputState pkSeed pkRoot message sig)
  let pkAdrs : Nat :=
    C12Concrete.wotsPkAdrsC12 4
      (c12Layer4NextTree
        (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
      (c12Layer4Leaf
        (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
  have hEval : evalExpr [] st0 C12SegmentWotsSetup.c12LayerPkAdrsExpr = some pkAdrs := by
    simpa [st0, pkAdrs, c12Layer4InputState, c12Layer4PreBodyState] using
      c12Layer4BeforePkAdrs_wotsPkAdrs_eval
        pkSeed pkRoot message sig sigParsed hParse
  simpa [c12Layer4BeforeWotsPkCopyState, c12Layer4BeforePkAdrsState] using
    C12SegmentWotsSetup.c12LayerStateBeforeWotsPkCopy_chain_cell_eq_beforePkAdrs_of_eval
      (c12Layer4InputState pkSeed pkRoot message sig) pkAdrs hEval j

/-- The layer-4 pre-copy generated-cell premise reduces to the earlier
`beforePkAdrs` cutpoint. -/
theorem c12Layer4BeforeWotsPkCopy_cells_of_beforePkAdrs_cells
    (hCells : C12Layer4WotsPkBeforePkAdrsCellsPremise) :
    C12Layer4WotsPkBeforeWotsPkCopyCellsPremise := by
  intro pkSeed pkRoot message sig sigParsed hParse j hj
  rw [c12Layer4BeforeWotsPkCopy_chain_cell_eq_beforePkAdrs
    pkSeed pkRoot message sig sigParsed hParse j]
  exact hCells pkSeed pkRoot message sig sigParsed hParse j hj

/-- The layer-4 pre-copy WOTS-PK address slot is the concrete parsed C12
WOTS-PK ADRS word. -/
theorem c12Layer4BeforeWotsPkCopy_pkAdrs_slot
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature)
    (hParse : C12Concrete.parseSignatureC12 c12 sig = some sigParsed) :
    ((c12Layer4BeforeWotsPkCopyState pkSeed pkRoot message sig).world.memory 0x20).val =
      C12Concrete.wotsPkAdrsC12 4
        (c12Layer4NextTree
          (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
        (c12Layer4Leaf
          (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex) := by
  unfold c12Layer4BeforeWotsPkCopyState
  rw [C12SegmentWotsSetup.c12LayerStateBeforeWotsPkCopy_pkAdrs_slot_of_eval
    (c12Layer4InputState pkSeed pkRoot message sig)
    (C12Concrete.wotsPkAdrsC12 4
      (c12Layer4NextTree
        (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
      (c12Layer4Leaf
        (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex))]
  · rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl]
    rw [Nat.mod_eq_of_lt]
    unfold C12Concrete.wotsPkAdrsC12
    rw [c12Layer4NextTree_of_parsed_eq_zero]
    let idx := (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex
    let leaf := c12Layer4Leaf idx
    have h4ShiftLt : 4 <<< 224 < 2 ^ 256 := by decide
    have h0ShiftLt : 0 <<< 160 < 2 ^ 256 := by decide
    have h1ShiftLt : 1 <<< 128 < 2 ^ 256 := by decide
    have hLeafShiftLt : leaf <<< 96 < 2 ^ 256 := by
      have hLeafLt16 : leaf < 16 := c12Layer4Leaf_lt_16 idx
      rw [Nat.shiftLeft_eq]
      calc
        leaf * 2 ^ 96 < 16 * 2 ^ 96 :=
          Nat.mul_lt_mul_of_pos_right hLeafLt16 (by decide)
        _ < 2 ^ 256 := by decide
    exact c12_nat_lor_lt_two_pow
      (c12_nat_lor_lt_two_pow
        (c12_nat_lor_lt_two_pow h4ShiftLt h0ShiftLt)
        h1ShiftLt)
      hLeafShiftLt
  · simpa [c12Layer4InputState, c12Layer4PreBodyState] using
      c12Layer4BeforePkAdrs_wotsPkAdrs_eval
        pkSeed pkRoot message sig sigParsed hParse

/-- The pre-copy seed and address cells are proved, so the layer-4 pre-copy
memory premise reduces to only generated chain cells. -/
theorem c12Layer4BeforeWotsPkCopy_addr_cells_of_cells
    (hCells : C12Layer4WotsPkBeforeWotsPkCopyCellsPremise) :
    C12Layer4WotsPkBeforeWotsPkCopyAddrCellsPremise := by
  intro pkSeed pkRoot message sig sigParsed hParse
  exact ⟨
    c12Layer4BeforeWotsPkCopy_pkAdrs_slot pkSeed pkRoot message sig sigParsed hParse,
    hCells pkSeed pkRoot message sig sigParsed hParse⟩

/-- The pre-copy seed cell is proved by segment-level memory preservation, so
the layer-4 pre-copy memory premise reduces to the address and generated chain
cells. -/
theorem c12Layer4BeforeWotsPkCopy_memory_of_addr_cells
    (hAddrCells : C12Layer4WotsPkBeforeWotsPkCopyAddrCellsPremise) :
    C12Layer4WotsPkBeforeWotsPkCopyMemoryPremise := by
  intro pkSeed pkRoot message sig sigParsed hParse
  rcases hAddrCells pkSeed pkRoot message sig sigParsed hParse with ⟨hm1, hmC⟩
  refine ⟨?_, hm1, hmC⟩
  unfold c12Layer4BeforeWotsPkCopyState
  rw [C12SegmentWotsSetup.c12LayerStateBeforeWotsPkCopy_preserves_memory_zero]
  simpa [c12Layer4InputState, c12Layer4PreBodyState] using
    c12Layer4PreBodyState_preserves_memory_zero pkSeed pkRoot message sig

/-- The layer-4 pre-WOTS-PK cutpoint preserves the public seed scratch cell. -/
theorem c12Layer4BeforeWotsPk_seed
    (pkSeed pkRoot message sig : ByteArray) :
    ((c12Layer4BeforeWotsPkState pkSeed pkRoot message sig).world.memory 0x00).val =
      c12Layer4ParsedSeed pkSeed := by
  unfold c12Layer4BeforeWotsPkState
  rw [C12SegmentWotsSetup.c12LayerStateBeforeWotsPk_preserves_memory_zero]
  simpa [c12Layer4InputState, c12Layer4PreBodyState] using
    c12Layer4PreBodyState_preserves_memory_zero pkSeed pkRoot message sig

/-- Transport the layer-4 WOTS-PK memory premise across the final 45-word copy
loop.  The proof uses only the two slot-level copy-loop lemmas, avoiding the
large packaged transport theorem that is too expensive for Lean here. -/
theorem c12Layer4BeforeWotsPk_memory_of_beforeCopy_memory
    (hCopy : C12Layer4WotsPkBeforeWotsPkCopyMemoryPremise) :
    C12Layer4WotsPkBeforeWotsPkMemoryPremise := by
  intro pkSeed pkRoot message sig sigParsed hParse
  rcases hCopy pkSeed pkRoot message sig sigParsed hParse with ⟨_hm0, hm1, hmC⟩
  refine ⟨?_, ?_, ?_⟩
  · exact c12Layer4BeforeWotsPk_seed pkSeed pkRoot message sig
  · unfold c12Layer4BeforeWotsPkState
    rw [C12SegmentWotsSetup.c12LayerStateBeforeWotsPk_eq_copyLoop]
    unfold C12SegmentWotsSetup.c12LayerStateAfterWotsPkCopyLoop
    rw [C12SegmentWotsSetup.c12WotsPkCopyLoop_preserves_pkAdrs_slot]
    simpa [c12Layer4BeforeWotsPkCopyState] using hm1
  · intro j hj
    unfold c12Layer4BeforeWotsPkState
    rw [C12SegmentWotsSetup.c12LayerStateBeforeWotsPk_eq_copyLoop]
    unfold C12SegmentWotsSetup.c12LayerStateAfterWotsPkCopyLoop
    rw [C12SegmentWotsSetup.c12WotsPkCopyLoop_copies_chain_word _ j hj]
    simpa [c12Layer4BeforeWotsPkCopyState] using hmC j hj

/-- Layer-4 WOTS-PK handoff from explicit post-copy-loop scratch facts.  This
is the small core used before packaging the facts into a public premise. -/
theorem c12Layer4BeforeAuthOff_wotsPk_of_beforeWotsPk_memory_facts
    (pkSeed pkRoot message sig : ByteArray) (sigParsed : Signature)
    (hm0 :
      ((c12Layer4BeforeWotsPkState pkSeed pkRoot message sig).world.memory 0x00).val =
        c12Layer4ParsedSeed pkSeed)
    (hm1 :
      ((c12Layer4BeforeWotsPkState pkSeed pkRoot message sig).world.memory 0x20).val =
        C12Concrete.wotsPkAdrsC12 4
          (c12Layer4NextTree
            (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
          (c12Layer4Leaf
            (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex))
    (hmC : ∀ j, (h : j < 45) →
      ((c12Layer4BeforeWotsPkState pkSeed pkRoot message sig).world.memory
          (0x40 + 32 * j)).val =
        (c12WotsChainsEnd
          (c12Layer4ParsedSeed pkSeed) 4
          (c12Layer4NextTree
            (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
          (c12Layer4Leaf
            (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
          (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
            (c12Layer4Node pkSeed pkRoot message sigParsed))
          (c12Layer4Sig sigParsed).wots)[j]) :
    lookupValue
        (c12Layer4BeforeAuthOffState pkSeed pkRoot message sig).bindings
        "wotsPk" =
      SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
        (c12Layer4WotsPkBytes pkSeed
          (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex
          (c12Layer4Node pkSeed pkRoot message sigParsed)
          (c12Layer4Sig sigParsed)) := by
  have hWotsPk :
      lookupValue
          (C12SegmentWotsSetup.c12LayerStateBeforeAuthOff
            (c12Layer4InputState pkSeed pkRoot message sig)).bindings
          "wotsPk" =
        C12Concrete.wotsPkWordC12
          (c12Layer4ParsedSeed pkSeed)
          4
          (c12Layer4NextTree
            (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
          (c12Layer4Leaf
            (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
          (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
            (c12Layer4Node pkSeed pkRoot message sigParsed))
          (c12Layer4Sig sigParsed).wots :=
    c12LayerStateBeforeAuthOff_wotsPk_eq_wotsPkWord_of_beforeWotsPk_memory
      (c12Layer4InputState pkSeed pkRoot message sig)
      (c12Layer4ParsedSeed pkSeed)
      4
      (c12Layer4NextTree
        (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
      (c12Layer4Leaf
        (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex)
      (SphincsMinusVerifierSpec.C13Concrete.wordOfHash16
        (c12Layer4Node pkSeed pkRoot message sigParsed))
      (c12Layer4Sig sigParsed).wots
      (by simpa [c12Layer4BeforeWotsPkState] using hm0)
      (by simpa [c12Layer4BeforeWotsPkState] using hm1)
      (by
        intro j h
        simpa [c12Layer4BeforeWotsPkState] using hmC j h)
  rw [show
      lookupValue
          (c12Layer4BeforeAuthOffState pkSeed pkRoot message sig).bindings
          "wotsPk" =
        lookupValue
          (C12SegmentWotsSetup.c12LayerStateBeforeAuthOff
            (c12Layer4InputState pkSeed pkRoot message sig)).bindings
          "wotsPk" by rfl]
  rw [hWotsPk]
  exact
    (c12Layer4WotsPkBytes_wordOfHash16 pkSeed
      (c12Layer4ParsedMessage pkSeed pkRoot message sigParsed).hyperIndex
      (c12Layer4Node pkSeed pkRoot message sigParsed)
      (c12Layer4Sig sigParsed)).symm

/-- Pack the layer-4 post-copy-loop scratch premise into the existing
before-authOff WOTS-PK premise.  The substantive scratch-to-binding proof stays
in `c12Layer4BeforeAuthOff_wotsPk_of_beforeWotsPk_memory_facts`; this wrapper
only unpacks the pointwise memory facts. -/
theorem C12Layer4WotsPkBeforeAuthOffPremise_of_beforeWotsPk_memory
    (hMem : C12Layer4WotsPkBeforeWotsPkMemoryPremise) :
    C12Layer4WotsPkBeforeAuthOffPremise := by
  intro pkSeed pkRoot message sig sigParsed hParse
  rcases hMem pkSeed pkRoot message sig sigParsed hParse with ⟨hm0, hm1, hmC⟩
  exact c12Layer4BeforeAuthOff_wotsPk_of_beforeWotsPk_memory_facts
    pkSeed pkRoot message sig sigParsed hm0 hm1 hmC

/-- C12 byte-spec cover with the layer-4 `"authPtr"` entry fact discharged by
the segment-level `sigBase`/`sigOff` preservation chain and the layer-4 seed
entry fact discharged by the seed-cell memory frame.  The remaining caller
surface is now the layer-4 `"xmssBase"` site plus the WOTS-PK handoff. -/
theorem c12_refines_byte_spec_of_layer4_known_authPtr_cover
    (hLayer4WotsPkBeforeAuthOff : C12Layer4WotsPkBeforeAuthOffPremise) :
    ByteLevel.ImplementsByteVerifier c12Primitives c12 runC12BodyObserved := by
  exact
      c12_refines_byte_spec_of_layer4_entry_components_cover
      (fun pkSeed pkRoot message sig _ _ =>
        c12Layer4EntryAuthPtr pkSeed pkRoot message sig)
      c12Layer4EntryXmssBase
      (fun pkSeed pkRoot message sig sigParsed _ =>
        c12Layer4EntrySeed pkSeed pkRoot message sig sigParsed)
      c12Layer4CurLeafAfter3
      (c12_layer4_before_xmss_node_wotsPk_of_before_authOff
        hLayer4WotsPkBeforeAuthOff)

/-- C12 byte-spec cover reduced to the post-copy-loop layer-4 WOTS-PK scratch
memory image. -/
theorem c12_refines_byte_spec_of_layer4_beforeWotsPk_memory_cover
    (hMem : C12Layer4WotsPkBeforeWotsPkMemoryPremise) :
    ByteLevel.ImplementsByteVerifier c12Primitives c12 runC12BodyObserved := by
  exact c12_refines_byte_spec_of_layer4_known_authPtr_cover
    (C12Layer4WotsPkBeforeAuthOffPremise_of_beforeWotsPk_memory hMem)

end SphincsMinusVerifiers.C12BridgePrep
