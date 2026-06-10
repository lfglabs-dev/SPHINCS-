/-
  SegmentForsSetup — S4 (FORS) pre-loop hoist segment for the FIPS 205
  uncompressed 32-byte ADRS layout.

  Three statements:

  ```
  13. letVar "idxLeaf0" := and(htIdx, 0x7FF)    -- low 11 bits of htIdx
  14. letVar "idxTree0" := shr(11, htIdx)       -- high 11 bits of htIdx
  15. letVar "forsBase" := or(shl(128, idxTree0),
                             or(shl(96, 3), shl(64, idxLeaf0)))
                                                -- FIPS 205 §11.2.2 ADRS base
  ```

  These are pure binder writes: no guard, no memory, no calldata — the
  *loop-invariant* ADRS base for the `forEach "i" (u 6)` FORS outer
  loop (statement 16).  In the spec mirror this is the construction of
  `C13Concrete.adrsForsBase idxTree0 idxLeaf0`
  (`C13Concrete.lean:453`) that the per-tree `forsLeafSetupStep`
  (`SegmentS4Fors.lean:567`) reads via `"forsBase"` and the inner
  climb's `mstore 0x20` (`ClimbKit.forsAdrs`) reads from.

  The headline lemma `execForsSetup` shows that running these three
  statements over the real Verity source interpreter unconditionally
  continues to `stepForsSetup st`.  Per the user's structural-plan
  (see PR #6), the lemma has *no* bound hypotheses; the
  word-normalizing interpreter is total, so `letVar_continue … rfl`
  discharges each step.  The `htIdx < 2^22` bound needed for the
  spec-identification is parametrised in `stepForsSetup_forsBase_eq`
  as `hhtLt : htIdx < 2^22` and discharged at the call site
  (`SegmentCompose` etc.) from the S3-segment hypertree-index bound.

  STATUS (see CLAUDE.md and the PR description for the full
  challenge breakdown):

  - `execForsSetup` proof body: 2 of the 3 `letVar_continue` `rfl`s
    close; the 3rd (the `orE` chain) times out because the post-step-14
    `RuntimeState` has a `let`-block in its `bindings`, so the
    `localVar` reads are not defeq to the eval result.  The fix is
    inlining the `stepForsSetup` let-block in its `def` (or
    `dsimp`/`unfold` of `bindValue`/`lookupValue` before the `rfl`).
  - `stepForsSetup_forsBase_eq` proof body: the bound chain
    (`h11shr` via `Nat.shiftRight_eq_div_pow` + `omega`, `hshl128`
    via `Nat.shiftLeft_eq` + `Nat.mul_le_mul_right` + `decide`) is
    in place.  The final `Nat`-form rewrite (closing via
    `simp [C13Concrete.adrsForsBase, Nat.lor_assoc, Nat.shiftLeft_eq]`)
    is incomplete.  Currently has a `sorry`; needs the `execForsSetup`
    fix first to unblock the build.
  - All other lemmas (`stepForsSetup_idxLeaf0`, `_idxTree0`,
    `forsSetup_preserves_*`, `stepForsSetup_preserves_*_step`) are
    written in the new (post-`stepForsSetup` form) and should build
    once the headline `rfl` issue is resolved.

  No new `axiom`; the existing `sorry` is the only one.
-/

import SphincsMinusVerifiers.Model
import SphincsMinusVerifierSpec.C13Concrete
import SphincsMinusVerifiers.BindingFrame
import SphincsMinusVerifiers.ClimbKeccakStep

namespace SphincsMinusVerifiers.SegmentForsSetup

open Compiler.Proofs.IRGeneration.SourceSemantics
open Compiler.CompilationModel (Expr Stmt)

/-! Local EDSL helpers (private, file-scoped — see `Model.lean` for the
canonical versions). -/
def u (n : Nat) : Expr := .literal n
def v (name : String) : Expr := .localVar name
def andE (a b : Expr) : Expr := .bitAnd a b
def orE (a b : Expr) : Expr := .bitOr a b
def shrE (a b : Expr) : Expr := .shr a b
def shlE (a b : Expr) : Expr := .shl a b
def mstore (off : Nat) (val : Expr) : Stmt := .mstore (u off) val

/-! ## 0. The three setup statements, replicated with bare public constructors. -/

/-- The FORS pre-loop setup segment (statements 13..15 of `c13VerifyBody`). -/
def forsSetupBody : List Stmt :=
  [ .letVar "idxLeaf0" (andE (.localVar "htIdx") (.literal 0x7FF))
  , .letVar "idxTree0" (shrE (.literal 11) (.localVar "htIdx"))
  , .letVar "forsBase"
      (orE (shlE (.literal 128) (v "idxTree0"))
        (orE (shlE (.literal 96) (.literal 3)) (shlE (.literal 64) (v "idxLeaf0")))) ]

/-- Faithfulness: `forsSetupBody` is *exactly* statements 13..15 of `c13VerifyBody`. -/
theorem forsSetup_eq_slice :
    forsSetupBody = (c13VerifyBodyTail.drop 13).take 3 := rfl

/-! ## 1. The accept-path state transformer. -/

/-- The setup state transformer: bind `idxLeaf0`, `idxTree0`, and
`forsBase` per the FIPS ADRS-base expression.  All three reads are
`localVar` lookups whose keys differ from the ones being written, so
the chained binds do not shadow them.  The values use the raw
`Verity.Core.Uint256` operations so they are definitionally equal to
the `evalExpr` reductions discharged by `rfl` in `execForsSetup` (the
interpreter's `bitAnd`/`shr`/`shl`/`bitOr` all reduce mod `2^256` to
`(Uint256.op …).val`, which is exactly what `rfl` resolves). -/
def stepForsSetup (st : RuntimeState) : RuntimeState :=
  let b1 := bindValue st.bindings "idxLeaf0"
                (Verity.Core.Uint256.and
                  (lookupValue st.bindings "htIdx")
                  (wordNormalize 0x7FF)).val
  let b2 := bindValue b1 "idxTree0"
                (Verity.Core.Uint256.shr
                  (wordNormalize 11)
                  (lookupValue st.bindings "htIdx")).val
  let b3 := bindValue b2 "forsBase"
                (Verity.Core.Uint256.or
                  (Verity.Core.Uint256.or
                    (Verity.Core.Uint256.shl
                      (wordNormalize 128)
                      (lookupValue
                        (bindValue
                          (bindValue st.bindings "idxLeaf0"
                            (Verity.Core.Uint256.and
                              (lookupValue st.bindings "htIdx")
                              (wordNormalize 0x7FF)).val)
                          "idxTree0"
                          (Verity.Core.Uint256.shr
                            (wordNormalize 11)
                            (lookupValue st.bindings "htIdx")).val)
                        "idxTree0"))
                    (Verity.Core.Uint256.shl (wordNormalize 96) (wordNormalize 3)))
                  (Verity.Core.Uint256.shl
                    (wordNormalize 64)
                    (lookupValue
                      (bindValue
                        (bindValue st.bindings "idxLeaf0"
                          (Verity.Core.Uint256.and
                            (lookupValue st.bindings "htIdx")
                            (wordNormalize 0x7FF)).val)
                        "idxTree0"
                        (Verity.Core.Uint256.shr
                          (wordNormalize 11)
                          (lookupValue st.bindings "htIdx")).val)
                      "idxLeaf0"))).val
  { st with bindings := b3 }

/-! ## 2. Local interpreter combinators (self-contained copies of the SegmentSeed
helpers, re-declared so this file stands alone). -/

private theorem letVar_continue
    (st : RuntimeState) (name : String) (e : Expr) (val : Nat)
    (h : evalExpr [] st e = some val) :
    execStmt [] st (.letVar name e) =
      .continue { st with bindings := bindValue st.bindings name val } := by
  show (match evalExpr [] st e with
        | some resolved =>
            StmtResult.continue { st with bindings := bindValue st.bindings name resolved }
        | none => .revert) = _
  rw [h]

private theorem execStmtList_cons_continue
    (st st' : RuntimeState) (s : Stmt) (rest : List Stmt)
    (h : execStmt [] st s = .continue st') :
    execStmtList [] st (s :: rest) = execStmtList [] st' rest := by
  show (match execStmt [] st s with
        | .continue n => execStmtList [] n rest
        | .stop n => .stop n
        | .return rval rst => .return rval rst
        | .revert => .revert) = execStmtList [] st' rest
  rw [h]

private theorem find_filter_ne
    (bs : List (String × Nat)) (k k' : String) (h : k ≠ k') :
    (bs.filter (fun e => e.1 != k)).find? (fun e => e.1 == k')
      = bs.find? (fun e => e.1 == k') := by
  induction bs with
  | nil => rfl
  | cons e rest ih =>
    by_cases he : e.1 = k
    · have hf : (e.1 != k) = false := by simp [he]
      have hk' : (e.1 == k') = false := by
        subst he; exact beq_eq_false_iff_ne.mpr h
      simp [List.filter_cons, hf, List.find?_cons, hk', ih]
    · have hf : (e.1 != k) = true := by simp [he]
      by_cases hk' : e.1 = k'
      · have hk't : (e.1 == k') = true := beq_iff_eq.mpr hk'
        simp [List.filter_cons, hf, List.find?_cons, hk't]
      · have hk'f : (e.1 == k') = false := beq_eq_false_iff_ne.mpr hk'
        simp [List.filter_cons, hf, List.find?_cons, hk'f, ih]

private theorem lookupValue_bindValue_ne
    (bs : List (String × Nat)) (k k' : String) (val : Nat) (h : k ≠ k') :
    lookupValue (bindValue bs k val) k' = lookupValue bs k' := by
  have hk : (k == k') = false := beq_eq_false_iff_ne.mpr h
  unfold lookupValue bindValue
  rw [List.find?_cons]
  simp only [hk, Bool.false_eq_true, if_false]
  rw [find_filter_ne bs k k' h]

private theorem lookupValue_bindValue_self
    (bs : List (String × Nat)) (k : String) (val : Nat) :
    lookupValue (bindValue bs k val) k = val := by
  simp [lookupValue, bindValue]

/-! ## 3. The headline segment lemma. -/

/-- **`execForsSetup`** — running statements 13..15 of `c13VerifyBody` over the
real interpreter unconditionally continues to `stepForsSetup st`.  These
are pure binder writes (no guard), so there is no revert branch.

The bound hypotheses `hHIdx : lookupValue st.bindings "htIdx" < 2^256`
and the value is reduced by `evalStmt`/`evalExpr` definitionally
(matching `execForsLeafSetup`'s pattern in `SegmentS4Fors.lean`).
The `evalExpr` of `bitAnd`/`bitOr`/`shl`/`shr` ultimately produces
`(Uint256.op …).val`, and the `letVar_continue … rfl` discharges
this definitionally — the word-normalization is total, so no
explicit bound hypotheses are needed for the *headline* lemma.  The
tight `htIdx < 2^22` bound is needed only for the *value-identification*
lemma `stepForsSetup_forsBase_eq`, where it's discharged as a separate
hypothesis (parametrised over the binding value `htIdx`). -/
theorem execForsSetup (st : RuntimeState) :
    execStmtList [] st forsSetupBody = .continue (stepForsSetup st) := by
  show execStmtList [] st
        ([.letVar "idxLeaf0" (andE (.localVar "htIdx") (.literal 0x7FF)),
          .letVar "idxTree0" (shrE (.literal 11) (.localVar "htIdx")),
          .letVar "forsBase"
            (orE (shlE (.literal 128) (v "idxTree0"))
              (orE (shlE (.literal 96) (.literal 3)) (shlE (.literal 64) (v "idxLeaf0"))))]
          : List Stmt)
      = (StmtResult.continue (stepForsSetup st))
  -- After 3 `letVar_continue` reductions, the LHS is `execStmtList [] s' []`
  -- and the RHS is `.continue (stepForsSetup st)`.  The `rfl` at the end
  -- closes by defeq because `stepForsSetup st` unfolds to the same
  -- `{st with bindings := b3}` form that the 3 `letVar` steps produce.
  rw [execStmtList_cons_continue _ _ _ _
        (letVar_continue st "idxLeaf0"
          (andE (.localVar "htIdx") (.literal 0x7FF))
          _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
        (letVar_continue _ "idxTree0"
          (shrE (.literal 11) (.localVar "htIdx"))
          _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
        (letVar_continue _ "forsBase"
          (orE (shlE (.literal 128) (v "idxTree0"))
            (orE (shlE (.literal 96) (.literal 3)) (shlE (.literal 64) (v "idxLeaf0"))))
          _ rfl)]
  rfl
  -- KNOWN LIMITATION (TODO, see CLAUDE.md and the PR description):
  -- The `_ rfl` for the `forsBase` `letVar_continue` is the one
  -- `rfl` that doesn't close: `evalExpr` of the nested
  -- `orE (shlE 128 idxTree0) (orE (shlE 96 3) (shlE 64 idxLeaf0))`
  -- returns a `(Uint256.or …).val` form, but the post-step-14
  -- `RuntimeState` (the `st2` after steps 13+14) has a `let`-block
  -- in its `bindings` (the `b1`/`b2`/`b3` from `stepForsSetup`'s
  -- definition), so the `localVar` reads of `"idxTree0"`/`"idxLeaf0"`
  -- are not defeq to the eval result.  The fix is one of:
  --   (a) Inline `stepForsSetup`'s let-block in its `def` so the
  --       bindings are fully unfolded; OR
  --   (b) Use a `show` + manual `lookupValue_bindValue_*` rewrite
  --       chain before the `rfl`; OR
  --   (c) Drop `stepForsSetup` in favour of a `match` on a pure
  --       function `forsBaseStep` that takes a `RuntimeState` and
  --       returns the new `bindings` directly.
  -- Once that's fixed, the rest of the file (accessor section,
  -- preservation lemmas, axiom audit) builds as written.

/-! ## 4. Accessor corollaries — the loop-invariant ADRS base for the FORS
outer loop. -/

/-- The bindings of `stepForsSetup st` as an explicit three-deep `bindValue`
chain (the structure-update projection reduces by `rfl`).  Values are
`Uint256`-form to match `execForsSetup`'s rfl. -/
private theorem stepForsSetup_bindings (st : RuntimeState) :
    (stepForsSetup st).bindings =
      bindValue
        (bindValue
          (bindValue st.bindings "idxLeaf0"
            (Verity.Core.Uint256.and
              (lookupValue st.bindings "htIdx")
              (wordNormalize 0x7FF)).val)
          "idxTree0"
          (Verity.Core.Uint256.shr
            (wordNormalize 11)
            (lookupValue
              (bindValue st.bindings "idxLeaf0"
                (Verity.Core.Uint256.and
                  (lookupValue st.bindings "htIdx")
                  (wordNormalize 0x7FF)).val)
              "htIdx")).val)
        "forsBase"
        (Verity.Core.Uint256.or
          (Verity.Core.Uint256.or
            (Verity.Core.Uint256.shl
              (wordNormalize 128)
              (lookupValue
                (bindValue
                  (bindValue st.bindings "idxLeaf0"
                    (Verity.Core.Uint256.and
                      (lookupValue st.bindings "htIdx")
                      (wordNormalize 0x7FF)).val)
                  "idxTree0"
                  (Verity.Core.Uint256.shr
                    (wordNormalize 11)
                    (lookupValue
                      (bindValue st.bindings "idxLeaf0"
                        (Verity.Core.Uint256.and
                          (lookupValue st.bindings "htIdx")
                          (wordNormalize 0x7FF)).val)
                      "htIdx")).val)
                "idxTree0"))
            (Verity.Core.Uint256.shl (wordNormalize 96) (wordNormalize 3)))
          (Verity.Core.Uint256.shl
            (wordNormalize 64)
            (lookupValue
              (bindValue
                (bindValue st.bindings "idxLeaf0"
                  (Verity.Core.Uint256.and
                    (lookupValue st.bindings "htIdx")
                    (wordNormalize 0x7FF)).val)
                "idxTree0"
                (Verity.Core.Uint256.shr
                  (wordNormalize 11)
                  (lookupValue
                    (bindValue st.bindings "idxLeaf0"
                      (Verity.Core.Uint256.and
                        (lookupValue st.bindings "htIdx")
                        (wordNormalize 0x7FF)).val)
                    "htIdx")).val)
              "idxLeaf0"))).val := rfl

/-- After the FORS pre-loop setup the `"idxLeaf0"` binding is the
low 11 bits of `htIdx` (interpreter's `(htIdx &&& 0x7FF)`).  The value
is the raw `Uint256.and` form; the `Nat.land`-form identification
(used by the spec-side chain) is discharged in `stepForsSetup_forsBase_eq`. -/
theorem stepForsSetup_idxLeaf0 (st : RuntimeState) :
    lookupValue (stepForsSetup st).bindings "idxLeaf0"
      = (Verity.Core.Uint256.and
          (lookupValue st.bindings "htIdx")
          (wordNormalize 0x7FF)).val := by
  rw [stepForsSetup_bindings,
      lookupValue_bindValue_ne _ "forsBase" "idxLeaf0" _ (by decide),
      lookupValue_bindValue_ne _ "idxTree0" "idxLeaf0" _ (by decide),
      lookupValue_bindValue_self]

/-- After the FORS pre-loop setup the `"idxTree0"` binding is the
high 11 bits of `htIdx` (interpreter's `htIdx >>> 11`). -/
theorem stepForsSetup_idxTree0 (st : RuntimeState) :
    lookupValue (stepForsSetup st).bindings "idxTree0"
      = (Verity.Core.Uint256.shr
          (wordNormalize 11)
          (lookupValue st.bindings "htIdx")).val := by
  rw [stepForsSetup_bindings, lookupValue_bindValue_self]
  -- The bound value's `b1["htIdx"]` read reduces to `st["htIdx"]`
  -- (the step-13 bind on `"idxLeaf0"` is irrelevant for `"htIdx"`).
  rw [show (Verity.Core.Uint256.shr
              (wordNormalize 11)
              (lookupValue
                (bindValue st.bindings "idxLeaf0"
                  (Verity.Core.Uint256.and
                    (lookupValue st.bindings "htIdx")
                    (wordNormalize 0x7FF)).val)
                "htIdx")).val
          = (Verity.Core.Uint256.shr (wordNormalize 11)
              (lookupValue st.bindings "htIdx")).val from by
        rw [lookupValue_bindValue_ne _ "idxLeaf0" "htIdx"
          (Verity.Core.Uint256.and
            (lookupValue st.bindings "htIdx")
            (wordNormalize 0x7FF)).val (by decide)]]

/-- The keystone corollary.  After the FORS pre-loop setup the
`"forsBase"` binding is exactly `C13Concrete.adrsForsBase (htIdx >>> 11)
(htIdx &&& 0x7FF)`.  The hypothesis `(htIdx : Nat)` with
`(hht : lookupValue st.bindings "htIdx" = htIdx)` lifts the binding
value to a `Nat` so the bound chain (`htIdx < 2^22` for C13) can be
discharged cleanly.  Composed with the
`SegmentS4Fors.forsLeafSetup_preserves_forsBase` preservation fact
(`SegmentS4Fors.lean:622`) this is what the `SegmentAcceptSpec` /
`SegmentS4ForsDataObligations` data-suppliers read off the post-S3
state.

The `rfl`-level equalities between `Uint256.and` and `Nat.land` (and
`<<<`/`>>>`/`|||`) are not defeq — they require `hht` to bridge the
binding, then `Nat.shiftRight_eq_div_pow` and `Nat.shiftLeft_eq` and
`Nat.lor_assoc` to massage the bound chain.  The final bound uses the
user-supplied `hhtLt : htIdx < 2^22` (true for C13, where
`htIdx` is `h ||| d` with `h = 22` and `d = 2`, so `htIdx < 2^24 <
2^22` only for `h + d < 22`; if C13's `h + d > 22` the bound must be
adjusted at the call site). -/
theorem stepForsSetup_forsBase_eq
    (st : RuntimeState) (htIdx : Nat)
    (hht : lookupValue st.bindings "htIdx" = htIdx)
    (hhtLt : htIdx < 2 ^ 22) :
    lookupValue (stepForsSetup st).bindings "forsBase"
      = SphincsMinusVerifierSpec.C13Concrete.adrsForsBase
          (htIdx >>> 11) (htIdx &&& 0x7FF) := by
  -- Bridge the binding value to `htIdx` via `hht`, then unwrap the
  -- three-deep `bindValue` chain.  Each `lookupValue` reduces to a
  -- `Uint256` op on `htIdx`, then to a `Nat` op after `hht`-rewrite.
  rw [stepForsSetup_bindings, lookupValue_bindValue_self,
      lookupValue_bindValue_self,
      lookupValue_bindValue_ne _ "idxTree0" "htIdx" _ (by decide)]
  rw [hht]  -- now LHS uses `htIdx` instead of `st["htIdx"]`
  -- The `b1["idxLeaf0"]` read on the b2-form: outer bind on `"idxTree0"`
  -- is shadowed (different key), self-read on `"idxLeaf0"` returns
  -- the bound value.
  rw [lookupValue_bindValue_ne _ "idxTree0" "idxLeaf0"
        ((Verity.Core.Uint256.shr (wordNormalize 11) htIdx).val) (by decide),
      lookupValue_bindValue_self]
  -- Now: `(((htIdx &&& 0x7FF) <<< 64) ||| (3 <<< 96)) |||
  --        ((htIdx >>> 11) <<< 128)`
  -- Need to reach `adrsForsBase (htIdx >>> 11) (htIdx &&& 0x7FF)`:
  --   `(htIdx >>> 11) <<< 128 ||| ((3 <<< 96) ||| ((htIdx &&& 0x7FF) <<< 64))`.
  -- First, `Uint256.and` / `.shr` / `.shl` / `.or` reduce to
  -- `Nat.land` / `.shiftRight` / `.shiftLeft` / `.lor` when the
  -- operands are already bounded.  The bound chain uses `hhtLt`:
  -- `htIdx < 2^22`, so `htIdx >>> 11 < 2^11` (via `Nat.shiftRight_eq_div_pow`
  -- + `omega`), and `htIdx &&& 0x7FF < 2^11` (via `Nat.and_lt_two_pow`).
  -- The `hbound` chain is `Nat.shiftLeft_eq` → `Nat.mul_le_mul_right` →
  -- `decide` (literal comparison).
  have h11shr : htIdx >>> 11 < 2 ^ 11 := by
    rw [Nat.shiftRight_eq_div_pow]
    have : (2 : Nat) ^ 22 = 4194304 := by norm_num
    rw [show (2 : Nat) ^ 11 = 2048 from by norm_num]
    omega
  have hshl128 : (htIdx >>> 11) <<< 128 < 2 ^ 256 := by
    rw [Nat.shiftLeft_eq]
    have hle : htIdx >>> 11 ≤ 2 ^ 11 - 1 := Nat.le_of_lt_succ h11shr
    have : (htIdx >>> 11) * 2 ^ 128 ≤ (2 ^ 11 - 1) * 2 ^ 128 :=
      Nat.mul_le_mul_right _ hle
    rw [show (2 ^ 11 - 1 : Nat) * 2 ^ 128 = 2 ^ 139 - 2 ^ 128 from by
      rw [Nat.pow_sub (by decide : 0 < 2^11) (by decide : 11 < 139),
          Nat.mul_comm]
      ring_nf] at this
    omega
  -- The full `evalExpr` chain is the unwinding of the three letVar
  -- statements; since `evalExpr` is definitional with `Uint256` ops,
  -- the `Nat.land`/`Nat.lor` form is reachable by `show`.
  -- (`execForsSetup` proves the same step-by-step via `letVar_continue rfl`.)
  -- We close by direct `decide`-on-literal once we've reduced the LHS
  -- to a `Nat`-form chain.
  -- Final discharge: `simp [SphincsMinusVerifierSpec.C13Concrete.adrsForsBase,
  -- Nat.lor_assoc]` after the `Nat`-form rewrite.
  -- KNOWN LIMITATION (TODO): the final `Nat`-form rewrite is not
  -- implemented.  The bound chain (`h11shr`, `hshl128`) is in place
  -- but the `Uint256`-form → `Nat`-form bridge is missing.  The
  -- right pattern is `simp [C13Concrete.adrsForsBase, Nat.lor_assoc,
  -- Nat.shiftLeft_eq]` after the `Nat`-form rewrite.  Tracked in
  -- CLAUDE.md and the PR description.
  -- (This branch is currently unreachable in practice — the build
  -- fails at the `rfl` in `execForsSetup` before reaching this point.
  -- Once that `rfl` is fixed, the proof here will need to be
  -- completed via the `Nat.lor_assoc` rewrite described above.)
  /- TODO: complete the `Nat`-form rewrite. The shape should be:
       `simp [C13Concrete.adrsForsBase, Nat.lor_assoc, Nat.shiftLeft_eq]`
     after reducing `(a &&& 0x7FF) <<< 64` to `((a &&& 0x7FF) <<< 64)` and
     `(a >>> 11) <<< 128` to the same.  The re-association is right-assoc
     → left-assoc, so the lemma is `(Nat.lor_assoc _ _ _).symm`. -/
  -- Placeholder: this proof body is incomplete.  See the comment
  -- block above.  The file is committed as a structural WIP —
  -- the `rfl` issue in `execForsSetup` must be resolved first
  -- before the rest of the file can be completed.
  sorry

/-! ## 5. Binding-frame preservation.

The pre-loop setup binds three fresh keys (`"idxLeaf0"`, `"idxTree0"`,
`"forsBase"`) and does not rebind any of the keys that were bound earlier
in the accept path (`"sigBase"`, `"dVal"`, `"htIdx"`).  Per-key
preservation lemmas. -/

open SphincsMinusVerifiers.BindingFrame in
theorem forsSetup_preserves_sigBase
    (st s' : RuntimeState)
    (h : execStmtList [] st forsSetupBody = .continue s') :
    lookupValue s'.bindings "sigBase" = lookupValue st.bindings "sigBase" := by
  refine execStmtList_preserves_lookup "sigBase" forsSetupBody st s' ?_ h
  intro s s'' stmt hmem hexec
  simp [forsSetupBody] at hmem
  rcases hmem with hstmt | hstmt | hstmt
  · subst stmt
    exact execStmt_letVar_preserves_lookup s s'' "idxLeaf0" "sigBase" _ (by decide) hexec
  · subst stmt
    exact execStmt_letVar_preserves_lookup s s'' "idxTree0" "sigBase" _ (by decide) hexec
  · subst stmt
    exact execStmt_letVar_preserves_lookup s s'' "forsBase" "sigBase" _ (by decide) hexec

open SphincsMinusVerifiers.BindingFrame in
theorem forsSetup_preserves_dVal
    (st s' : RuntimeState)
    (h : execStmtList [] st forsSetupBody = .continue s') :
    lookupValue s'.bindings "dVal" = lookupValue st.bindings "dVal" := by
  refine execStmtList_preserves_lookup "dVal" forsSetupBody st s' ?_ h
  intro s s'' stmt hmem hexec
  simp [forsSetupBody] at hmem
  rcases hmem with hstmt | hstmt | hstmt
  · subst stmt
    exact execStmt_letVar_preserves_lookup s s'' "idxLeaf0" "dVal" _ (by decide) hexec
  · subst stmt
    exact execStmt_letVar_preserves_lookup s s'' "idxTree0" "dVal" _ (by decide) hexec
  · subst stmt
    exact execStmt_letVar_preserves_lookup s s'' "forsBase" "dVal" _ (by decide) hexec

open SphincsMinusVerifiers.BindingFrame in
theorem forsSetup_preserves_htIdx
    (st s' : RuntimeState)
    (h : execStmtList [] st forsSetupBody = .continue s') :
    lookupValue s'.bindings "htIdx" = lookupValue st.bindings "htIdx" := by
  refine execStmtList_preserves_lookup "htIdx" forsSetupBody st s' ?_ h
  intro s s'' stmt hmem hexec
  simp [forsSetupBody] at hmem
  rcases hmem with hstmt | hstmt | hstmt
  · subst stmt
    exact execStmt_letVar_preserves_lookup s s'' "idxLeaf0" "htIdx" _ (by decide) hexec
  · subst stmt
    exact execStmt_letVar_preserves_lookup s s'' "idxTree0" "htIdx" _ (by decide) hexec
  · subst stmt
    exact execStmt_letVar_preserves_lookup s s'' "forsBase" "htIdx" _ (by decide) hexec

/-- Step-form: combine the transformer `stepForsSetup` with the
preservation fact into a single, easy-to-chain statement.  No bounds
needed — the headline `execForsSetup` has none. -/
theorem stepForsSetup_preserves_sigBase_step (st : RuntimeState) :
    lookupValue (stepForsSetup st).bindings "sigBase"
      = lookupValue st.bindings "sigBase" :=
  forsSetup_preserves_sigBase st (stepForsSetup st) (execForsSetup st)

theorem stepForsSetup_preserves_dVal_step (st : RuntimeState) :
    lookupValue (stepForsSetup st).bindings "dVal"
      = lookupValue st.bindings "dVal" :=
  forsSetup_preserves_dVal st (stepForsSetup st) (execForsSetup st)

theorem stepForsSetup_preserves_htIdx_step (st : RuntimeState) :
    lookupValue (stepForsSetup st).bindings "htIdx"
      = lookupValue st.bindings "htIdx" :=
  forsSetup_preserves_htIdx st (stepForsSetup st) (execForsSetup st)

/-! ## 6. Axiom audit. -/

#print axioms execForsSetup
#print axioms forsSetup_eq_slice
#print axioms stepForsSetup_forsBase_eq
#print axioms forsSetup_preserves_sigBase
#print axioms forsSetup_preserves_dVal
#print axioms forsSetup_preserves_htIdx

end SphincsMinusVerifiers.SegmentForsSetup
