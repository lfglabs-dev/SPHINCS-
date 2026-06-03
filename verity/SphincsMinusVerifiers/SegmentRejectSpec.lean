/-
  SegmentRejectSpec — the REVERT-subdomain companion to `SegmentAcceptSpec`.

  `SegmentAcceptSpec.accept_path_returns_verifyParsed_bool` closes the accept
  subdomain: under the three control-flow guards (and the residual `hCmp` data
  hypothesis) the compiled `c13VerifyBody` run over `mkC13State …` *returns* the
  boolean `verifyParsed` yields.  That theorem already covers `specBool = false`
  (a well-formed signature that simply fails to verify returns the boolean false
  word — a normal `.return`, NOT a revert).

  This file handles the DISJOINT revert subdomain: inputs on which the compiled
  body `.revert`s rather than `.return`s, and ties those to the byte spec's
  `none` outcome (`ByteLevel.verifyBytes … = none`, the spec's revert encoding).

  Two revert sources are addressed:

    1. **Bad signature length** (the first body statement, the `sig_length`
       guard).  Fully discharged on BOTH sides, framed over the same
       `mkC13State` constructor the accept path uses:
         * model:  `c13_body_reverts_on_bad_length`
         * spec:   `c13_verifyBytes_none_on_bad_length`
         * joint:  `c13_revert_on_bad_length`
       This reuses the generic `verifyBody_reverts_on_bad_length` (Model.lean)
       and `ByteLevel.verifyBytes_bad_length` (Spec.lean); no bridge axiom.

    2. **FORS forced-zero guard** (statement 12; `s3Guard ≠ 0`).  The MODEL side
       is fully discharged (`c13_body_reverts_on_forced_zero`): threading the
       length-guard pass-through and the S2 straight-line prefix, then reverting
       at `segmentS3`.  The older low-level joint theorem
       `c13_revert_on_forced_zero` still accepts the spec-side `none` result as
       an explicit `hCorr` premise.  The parse-shaped C13 theorem
       `c13_revert_on_forced_zero_of_parse` removes that raw premise by deriving
       the spec-side `forcedZeroOk = false` result from successful concrete
       parsing plus the non-zero model guard, contraposing
       `SegmentAcceptSpec.c13_s3Guard_of_parse_forcedZero`.

  These are the revert-side building blocks that, together with the accept
  theorem, let a later step prove `ByteLevel.ImplementsByteVerifier c13Primitives
  c13 execC13` once `execC13` is defined.  This file touches neither `execC13`
  nor the bridge axiom; `#print axioms` on the discharged theorems shows only
  `[propext, Classical.choice, Quot.sound]`.  No `sorry`, no new `axiom`,
  no `native_decide`.
-/

import SphincsMinusVerifiers.SegmentCompose
import SphincsMinusVerifiers.SegmentAcceptSpec
import SphincsMinusVerifiers.MkC13State
import SphincsMinusVerifiers.Proofs
import SphincsMinusVerifierSpec.Spec
import SphincsMinusVerifierSpec.C13Concrete

namespace SphincsMinusVerifiers.SegmentRejectSpec

open Compiler.Proofs.IRGeneration.SourceSemantics
open Compiler.CompilationModel (Expr Stmt)
open SphincsMinusVerifiers
open SphincsMinusVerifiers.SegmentCompose
open SphincsMinusVerifiers.MkC13State
open SphincsMinusVerifierSpec

/-! ## 1. Length-guard revert (fully discharged, both sides).

The accept path's `hlen` reads `lookupValue (mkC13State …).bindings "sig_length"
= wordNormalize 3688`; since the constructor binds `sig_length` to `sig.size`,
that lookup is definitionally `sig.size`.  On the complementary domain
(`sig.size ≠ 3688 = c13.sigBytes`) the body reverts and the spec is `none`. -/

/-- The frozen constructor binds `sig_length` to the raw `sig.size`. -/
theorem mkC13State_lookup_sigLength (pkSeed pkRoot message sig : ByteArray) :
    lookupValue (mkC13State pkSeed pkRoot message sig).bindings "sig_length" = sig.size := rfl

/-- **Model side.**  The compiled `c13VerifyBody` run over `mkC13State …` reverts
whenever the signature byte length is not the expected `3688`.  Direct
specialisation of the generic length-guard revert to the accept-path state
constructor. -/
theorem c13_body_reverts_on_bad_length
    (pkSeed pkRoot message sig : ByteArray)
    (hlen : sig.size ≠ 3688) :
    execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody = .revert := by
  apply c13VerifyBody_reverts_on_bad_length
  have h3688 : wordNormalize 3688 = 3688 := rfl
  rw [mkC13State_lookup_sigLength, h3688]
  exact hlen

/-- **Spec side.**  The byte spec rejects (`none`) whenever the signature byte
length is not `c13.sigBytes = 3688`.  Direct specialisation of
`ByteLevel.verifyBytes_bad_length`. -/
theorem c13_verifyBytes_none_on_bad_length
    (pkSeed pkRoot message sig : ByteArray)
    (hlen : sig.size ≠ 3688) :
    ByteLevel.verifyBytes c13Primitives c13 pkSeed pkRoot message sig = none := by
  apply ByteLevel.verifyBytes_bad_length
  exact hlen

/-- **`c13_revert_on_bad_length`** — the headline length-guard correspondence:
on every wrong-length input the compiled model `.revert`s AND the byte spec is
`none`.  Both sides framed over the same `mkC13State` constructor / `c13Primitives`
package the eventual `ImplementsByteVerifier` integration uses.  No bridge axiom. -/
theorem c13_revert_on_bad_length
    (pkSeed pkRoot message sig : ByteArray)
    (hlen : sig.size ≠ 3688) :
    execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody = .revert
      ∧ ByteLevel.verifyBytes c13Primitives c13 pkSeed pkRoot message sig = none :=
  ⟨c13_body_reverts_on_bad_length pkSeed pkRoot message sig hlen,
   c13_verifyBytes_none_on_bad_length pkSeed pkRoot message sig hlen⟩

/-! ## 2. FORS forced-zero guard revert (model side discharged).

When the length guard passes, the body threads through the S2 straight-line
prefix to `afterS2 st`, then runs `segmentS3`.  `SegmentS3.execSegmentS3`
reverts exactly when the FORS forced-zero guard value `s3Guard (afterS2 st)` is
non-zero, so the whole body reverts.  Pure control-flow; no data correspondence,
no bridge axiom. -/

/-- **Model side.**  Under the length guard, a non-zero FORS forced-zero guard
makes the entire compiled `c13VerifyBody` run revert. -/
theorem c13_body_reverts_on_forced_zero
    (st : RuntimeState)
    (hlen : lookupValue st.bindings "sig_length" = wordNormalize 3688)
    (hg3 : SegmentS3.s3Guard (afterS2 st) ≠ 0) :
    execStmtList [] st c13VerifyBody = .revert := by
  rw [c13VerifyBody_passes_length_guard st hlen, body_reshape]
  -- S2 (stmts 1..9) continues to afterS2 st
  rw [MemoryKit.execStmtList_append_continue _ _ _ _ (SegmentS2.execS2 st)]
  -- segmentS3 (stmts 10..13) reverts because the forced-zero guard is non-zero
  have hS3rev : execStmtList [] (afterS2 st) SegmentS3.segmentS3 = .revert := by
    rw [SegmentS3.execSegmentS3]; exact if_neg hg3
  exact MemoryKit.execStmtList_append_revert _ _ _ hS3rev

/-- **Forced-zero correspondence (spec connection surfaced as a hypothesis).**
Under the length guard and a non-zero model forced-zero guard, the body reverts;
and IF the model guard agreeing with the spec's `¬ forcedZeroOk` decision is
supplied as `hCorr`, the byte spec is `none` on the same input.

`hCorr` is the residual data-correspondence obligation: the model reads its
forced-zero guard off the keccak `digest` (H_msg) binding, while the spec reads
it off `p.hMsg v pk sig.R message`.  Equating the two is the carried Phase-3b
keccak/H_msg correspondence — surfaced here, not discharged (mirrors how
`SegmentAcceptSpec` surfaces `hCmp`). -/
theorem c13_revert_on_forced_zero
    (pkSeed pkRoot message sig : ByteArray)
    (hlen : lookupValue (mkC13State pkSeed pkRoot message sig).bindings "sig_length"
              = wordNormalize 3688)
    (hg3 : SegmentS3.s3Guard (afterS2 (mkC13State pkSeed pkRoot message sig)) ≠ 0)
    (hCorr : ByteLevel.verifyBytes c13Primitives c13 pkSeed pkRoot message sig = none) :
    execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody = .revert
      ∧ ByteLevel.verifyBytes c13Primitives c13 pkSeed pkRoot message sig = none :=
  ⟨c13_body_reverts_on_forced_zero (mkC13State pkSeed pkRoot message sig) hlen hg3, hCorr⟩

/-! ## 3. FORS forced-zero guard reject, parse-shaped spec side.

The previous theorem keeps the original low-level shape where the spec-side
`none` fact is supplied directly.  The lemmas below close the C13 spec side once
the concrete C13 parser has succeeded and the spec forced-zero decision is
known to be false, then derive that false decision from the non-zero model guard
by contraposing the existing accept-side guard correspondence. -/

/-- **Spec side.**  Once C13 byte parsing reaches `verifyParsed`, a failed
forced-zero decision makes `ByteLevel.verifyBytes` return `none`. -/
theorem c13_verifyBytes_none_on_forced_zero_of_parse
    (pkSeed pkRoot message sig : ByteArray)
    (sigParsed : Signature)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hZero : forcedZeroOk c13
        (C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = false) :
    ByteLevel.verifyBytes c13Primitives c13 pkSeed pkRoot message sig = none := by
  have hLen : sig.size = c13.sigBytes :=
    C13Concrete.parseSignatureC13_size hParse
  have hShape : signatureShapeOk c13 sigParsed = true :=
    C13Concrete.parseSignatureC13_shape hParse
  have hZero' : forcedZeroOk c13
      (C13Concrete.hMsgC13 c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = false := by
    simpa [C13Concrete.c13PrimitivesConcrete] using hZero
  unfold ByteLevel.verifyBytes
  simp [hLen, C13Concrete.parsePublicKey_c13, c13Primitives,
    C13Concrete.c13PrimitivesConcrete, hParse, verifyParsed, hShape, hZero']

/-- Successful C13 parsing plus a non-zero model forced-zero guard pins the
spec-side forced-zero decision to `false`.  This is the C13 reject-side analogue
of the accept path's `c13_s3Guard_of_parse_forcedZero`: if the spec decision had
been true, that theorem would force the model guard to be zero. -/
theorem c13_forcedZero_false_of_parse_s3Guard
    (pkSeed pkRoot message sig : ByteArray)
    (sigParsed : Signature)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hg3 : SegmentS3.s3Guard (afterS2 (mkC13State pkSeed pkRoot message sig)) ≠ 0) :
    forcedZeroOk c13
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = false := by
  cases hZero : forcedZeroOk c13
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) with
  | false => rfl
  | true =>
      have hGuard0 :=
        SegmentAcceptSpec.c13_s3Guard_of_parse_forcedZero
          pkSeed pkRoot message sig
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed rfl hParse hZero
      exact False.elim (hg3 hGuard0)

/-- **Forced-zero correspondence, parse-shaped.**  Under successful C13 parsing,
a non-zero model forced-zero guard makes the compiled body revert and the byte
spec return `none`, without taking a raw `hCorr` premise. -/
theorem c13_revert_on_forced_zero_of_parse
    (pkSeed pkRoot message sig : ByteArray)
    (sigParsed : Signature)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hg3 : SegmentS3.s3Guard (afterS2 (mkC13State pkSeed pkRoot message sig)) ≠ 0) :
    execStmtList [] (mkC13State pkSeed pkRoot message sig) c13VerifyBody = .revert
      ∧ ByteLevel.verifyBytes c13Primitives c13 pkSeed pkRoot message sig = none := by
  have hlen :
      lookupValue (mkC13State pkSeed pkRoot message sig).bindings "sig_length"
        = wordNormalize 3688 := by
    rw [mkC13State_lookup_sigLength]
    have hsz : sig.size = c13.sigBytes :=
      C13Concrete.parseSignatureC13_size hParse
    change sig.size = wordNormalize 3688
    rw [hsz]
    rfl
  have hZeroFalse :=
    c13_forcedZero_false_of_parse_s3Guard
      pkSeed pkRoot message sig sigParsed hParse hg3
  exact
    ⟨c13_body_reverts_on_forced_zero
        (mkC13State pkSeed pkRoot message sig) hlen hg3,
      c13_verifyBytes_none_on_forced_zero_of_parse
        pkSeed pkRoot message sig sigParsed hParse hZeroFalse⟩

/-! ## 4. Axiom audit. -/

#print axioms c13_body_reverts_on_bad_length
#print axioms c13_verifyBytes_none_on_bad_length
#print axioms c13_revert_on_bad_length
#print axioms c13_body_reverts_on_forced_zero
#print axioms c13_revert_on_forced_zero
#print axioms c13_verifyBytes_none_on_forced_zero_of_parse
#print axioms c13_forcedZero_false_of_parse_s3Guard
#print axioms c13_revert_on_forced_zero_of_parse

end SphincsMinusVerifiers.SegmentRejectSpec
