import SphincsMinusVerifiers.C12SegmentFors
import SphincsMinusVerifiers.ClimbLoop
import SphincsMinusVerifiers.ProofCore
import SphincsMinusVerifiers.BindingFrame
import SphincsMinusVerifiers.StateFrame
import SphincsMinusVerifiers.MemoryFrame
import SphincsMinusVerifiers.ClimbKeccakStep

namespace SphincsMinusVerifiers.C12SegmentForsCompress

open Compiler.CompilationModel (Stmt Expr)
open Compiler.Proofs.IRGeneration.SourceSemantics
open SphincsMinusVerifiers.ClimbKit (N_MASK execStmtList_cons_continue)
open SphincsMinusVerifiers.ClimbLoop (execStmt_forEach_of_step)
open SphincsMinusVerifiers.MemoryKit (execStmt_mstore_continue execStmtList_append_continue)

private def u (n : Nat) : Expr := .literal n
private def v (name : String) : Expr := .localVar name
private def addE (a b : Expr) : Expr := .add a b
private def shlE (a b : Expr) : Expr := .shl a b
private def orE (a b : Expr) : Expr := .bitOr a b
private def andE (a b : Expr) : Expr := .bitAnd a b
private def keccak (off size : Nat) : Expr := .keccak256 (u off) (u size)
private def mloadE (off : Expr) : Expr := .mload off
private def mstore (off : Nat) (val : Expr) : Stmt := .mstore (u off) val
private def mstoreE (off val : Expr) : Stmt := .mstore off val

def c12ForsRootCopyBody : List Stmt := [
  mstoreE (addE (u 0x40) (shlE (u 5) (v "t")))
    (mloadE (addE (u 0x80) (shlE (u 5) (v "t"))))
]

def c12ForsRootCopyStep (st : RuntimeState) : RuntimeState :=
  match execStmtList [] st c12ForsRootCopyBody with
  | .continue s' => s'
  | _ => st

theorem execC12ForsRootCopyBody (st : RuntimeState) :
    execStmtList [] st c12ForsRootCopyBody =
      .continue (c12ForsRootCopyStep st) := by
  unfold c12ForsRootCopyStep c12ForsRootCopyBody mstoreE mloadE
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rfl

def c12ForsCompressSegment : List Stmt := [
  .letVar "adrsRoots" (orE (orE (shlE (u 160) (v "treeIdx")) (shlE (u 128) (u 4)))
    (shlE (u 96) (v "leafIdx"))),
  mstore 0x20 (v "adrsRoots"),
  .forEach "t" (u 20) c12ForsRootCopyBody,
  .letVar "currentNode" (andE (keccak 0x00 0x2C0) (u N_MASK)),
  .letVar "curTree" (v "treeIdx"),
  .letVar "curLeaf" (v "leafIdx"),
  .letVar "sigOff" (u 2592)
]

theorem c12ForsCompressSegment_eq_slice :
    c12ForsCompressSegment = C12SegmentFors.c12AfterFors.take 7 := rfl

def c12AfterForsCompress : List Stmt :=
  C12SegmentFors.c12AfterFors.drop 7

theorem c12AfterFors_eq :
    C12SegmentFors.c12AfterFors =
      c12ForsCompressSegment ++ c12AfterForsCompress := rfl

def c12StepForsCompress (st : RuntimeState) : RuntimeState :=
  match execStmtList [] st c12ForsCompressSegment with
  | .continue s' => s'
  | _ => st

private abbrev PreservesLookup (key : String) (body : List Stmt) : Prop :=
  ∀ (s s'' : RuntimeState) (stmt : Stmt),
    stmt ∈ body → execStmt [] s stmt = .continue s'' →
    lookupValue s''.bindings key = lookupValue s.bindings key

theorem execC12ForsCompressSegment (st : RuntimeState) :
    execStmtList [] st c12ForsCompressSegment =
      .continue (c12StepForsCompress st) := by
  unfold c12StepForsCompress c12ForsCompressSegment mstore
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue st "adrsRoots" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_forEach_of_step "t" (u 20) c12ForsRootCopyBody _ (wordNormalize 20)
      c12ForsRootCopyStep rfl execC12ForsRootCopyBody)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "currentNode" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "curTree" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "curLeaf" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "sigOff" _ _ rfl)]
  rfl

/-- C12 FORS-root compression initializes the hypertree signature offset. -/
theorem c12StepForsCompress_sigOff_eq (st : RuntimeState) :
    lookupValue (c12StepForsCompress st).bindings "sigOff" =
      wordNormalize 2592 := by
  unfold c12StepForsCompress c12ForsCompressSegment mstore
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue st "adrsRoots" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_forEach_of_step "t" (u 20) c12ForsRootCopyBody _ (wordNormalize 20)
      c12ForsRootCopyStep rfl execC12ForsRootCopyBody)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "currentNode" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "curTree" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "curLeaf" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "sigOff" _ _ rfl)]
  rw [MemoryKit.lookupValue_bindValue_self]
  rfl

private theorem c12ForsRootCopyBody_preserves_lookup (key : String) :
    PreservesLookup key c12ForsRootCopyBody := by
  intro s s'' stmt hmem hexec
  simp only [c12ForsRootCopyBody, List.mem_cons, List.not_mem_nil, or_false] at hmem
  subst hmem
  exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
    _ _ key _ _ hexec

private theorem c12ForsRootCopyStep_preserves_lookup (key : String) (st : RuntimeState) :
    lookupValue (c12ForsRootCopyStep st).bindings key =
      lookupValue st.bindings key :=
  SphincsMinusVerifiers.BindingFrame.execStmtList_preserves_lookup
    key c12ForsRootCopyBody st (c12ForsRootCopyStep st)
    (c12ForsRootCopyBody_preserves_lookup key)
    (execC12ForsRootCopyBody st)

private theorem lookup_match_execStmtList_nil
    (fallback st : RuntimeState) (key : String) :
    lookupValue
        (match execStmtList [] st ([] : List Stmt) with
         | .continue s' => s'
         | _ => fallback).bindings key =
      lookupValue st.bindings key := rfl

/-- C12 FORS-root compression initializes the hypertree tree index from
`"treeIdx"`. -/
theorem c12StepForsCompress_curTree_eq (st : RuntimeState) :
    lookupValue (c12StepForsCompress st).bindings "curTree" =
      lookupValue st.bindings "treeIdx" := by
  unfold c12StepForsCompress c12ForsCompressSegment mstore
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue st "adrsRoots" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_forEach_of_step "t" (u 20) c12ForsRootCopyBody _ (wordNormalize 20)
      c12ForsRootCopyStep rfl execC12ForsRootCopyBody)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "currentNode" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "curTree" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "curLeaf" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "sigOff" _ _ rfl)]
  rw [lookup_match_execStmtList_nil]
  repeat rw [MemoryKit.lookupValue_bindValue_ne _ _ "curTree" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_self]
  rw [MemoryKit.lookupValue_bindValue_ne _ "currentNode" "treeIdx" _ (by decide)]
  rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_preserves_lookup
    "t" "treeIdx" c12ForsRootCopyStep (by decide)
    (c12ForsRootCopyStep_preserves_lookup "treeIdx")]
  rw [MemoryKit.lookupValue_bindValue_ne _ "t" "treeIdx" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "adrsRoots" "treeIdx" _ (by decide)]

/-- C12 FORS-root compression initializes the hypertree leaf index from
`"leafIdx"`. -/
theorem c12StepForsCompress_curLeaf_eq (st : RuntimeState) :
    lookupValue (c12StepForsCompress st).bindings "curLeaf" =
      lookupValue st.bindings "leafIdx" := by
  unfold c12StepForsCompress c12ForsCompressSegment mstore
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue st "adrsRoots" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (execStmt_forEach_of_step "t" (u 20) c12ForsRootCopyBody _ (wordNormalize 20)
      c12ForsRootCopyStep rfl execC12ForsRootCopyBody)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "currentNode" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "curTree" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "curLeaf" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "sigOff" _ _ rfl)]
  rw [lookup_match_execStmtList_nil]
  repeat rw [MemoryKit.lookupValue_bindValue_ne _ _ "curLeaf" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_self]
  rw [MemoryKit.lookupValue_bindValue_ne _ "curTree" "leafIdx" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "currentNode" "leafIdx" _ (by decide)]
  rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_preserves_lookup
    "t" "leafIdx" c12ForsRootCopyStep (by decide)
    (c12ForsRootCopyStep_preserves_lookup "leafIdx")]
  rw [MemoryKit.lookupValue_bindValue_ne _ "t" "leafIdx" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "adrsRoots" "leafIdx" _ (by decide)]

theorem c12AfterFors_observed_eq_after_fors_compress
    (st : RuntimeState) :
    observeStmtResultBool
        (execStmtList [] st C12SegmentFors.c12AfterFors)
      =
    observeStmtResultBool
        (execStmtList [] (c12StepForsCompress st) c12AfterForsCompress) := by
  rw [c12AfterFors_eq]
  rw [execStmtList_append_continue _ _ _ _ (execC12ForsCompressSegment st)]

private abbrev PreservesRoot (body : List Stmt) : Prop :=
  ∀ (s s'' : RuntimeState) (stmt : Stmt),
    stmt ∈ body → execStmt [] s stmt = .continue s'' →
    lookupValue s''.bindings "root" = lookupValue s.bindings "root"

private abbrev PreservesSC (body : List Stmt) : Prop :=
  ∀ (s s'' : RuntimeState) (stmt : Stmt),
    stmt ∈ body → execStmt [] s stmt = .continue s'' →
    SphincsMinusVerifiers.StateFrame.PreservesSelectorCalldata s s''

private theorem c12_idxNorm20 (idx : Nat) (hidx : idx < 20) :
    wordNormalize idx = idx := by
  rw [wordNormalize_eq_mod]
  exact Nat.mod_eq_of_lt (lt_trans hidx (by decide))

private theorem c12_idxShl5_lt20 (idx : Nat) (hidx : idx < 20) :
    idx <<< 5 < 2 ^ 256 := by
  rw [Nat.shiftLeft_eq]
  have hle : idx * 2 ^ 5 ≤ 19 * 2 ^ 5 :=
    Nat.mul_le_mul_right _ (Nat.le_of_lt_succ hidx)
  exact lt_of_le_of_lt hle (by decide)

private theorem c12_addIdxShl5_lt20 (base idx : Nat)
    (hbase : base ≤ 0x80) (hidx : idx < 20) :
    base + (idx <<< 5) < 2 ^ 256 := by
  rw [Nat.shiftLeft_eq]
  have hle : base + idx * 2 ^ 5 ≤ 128 + 19 * 2 ^ 5 :=
    Nat.add_le_add hbase (Nat.mul_le_mul_right _ (Nat.le_of_lt_succ hidx))
  exact lt_of_le_of_lt hle (by decide)

private theorem evalC12RootCopyOffset (s : RuntimeState) (base idx : Nat)
    (hbase : base ≤ 0x80) (hidx : idx < 20) :
    evalExpr [] { s with bindings := bindValue s.bindings "t" (wordNormalize idx) }
      (addE (u base) (shlE (u 5) (v "t"))) = some (base + 32 * idx) := by
  let st : RuntimeState :=
    { s with bindings := bindValue s.bindings "t" (wordNormalize idx) }
  have h5 : evalExpr [] st (u 5) = some 5 := by
    show some (wordNormalize 5) = some 5
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (by decide)]
  have ht : evalExpr [] st (v "t") = some idx := by
    show some (lookupValue (bindValue s.bindings "t" (wordNormalize idx)) "t") = some idx
    rw [SphincsMinusVerifiers.MemoryKit.lookupValue_bindValue_self, c12_idxNorm20 idx hidx]
  have hsh : evalExpr [] st (shlE (u 5) (v "t")) = some (idx <<< 5) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded st (u 5) (v "t")
      5 idx h5 ht (by decide) (lt_trans hidx (by decide)) (c12_idxShl5_lt20 idx hidx)
  have hbaseLit : evalExpr [] st (u base) = some base := by
    show some (wordNormalize base) = some base
    rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
      Nat.mod_eq_of_lt (lt_of_le_of_lt hbase (by decide))]
  have hadd := SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_add_bounded st (u base)
    (shlE (u 5) (v "t")) base (idx <<< 5) hbaseLit hsh
    (lt_of_le_of_lt hbase (by decide)) (c12_idxShl5_lt20 idx hidx)
    (c12_addIdxShl5_lt20 base idx hbase hidx)
  convert hadd using 1
  rw [Nat.shiftLeft_eq]
  ring_nf

private theorem c12ForsRootCopyBody_preserves_memory_zero_bound
    (s : RuntimeState) (idx : Nat) (hidx : idx < 20) (s'' : RuntimeState)
    (hExec : execStmtList []
      { s with bindings := bindValue s.bindings "t" (wordNormalize idx) }
      c12ForsRootCopyBody = .continue s'') :
    (s''.world.memory 0x00).val = (s.world.memory 0x00).val := by
  let st : RuntimeState :=
    { s with bindings := bindValue s.bindings "t" (wordNormalize idx) }
  have hoff : evalExpr [] st (addE (u 0x40) (shlE (u 5) (v "t"))) =
      some (0x40 + 32 * idx) :=
    evalC12RootCopyOffset s 0x40 idx (by decide) hidx
  have hsrc : evalExpr [] st (addE (u 0x80) (shlE (u 5) (v "t"))) =
      some (0x80 + 32 * idx) :=
    evalC12RootCopyOffset s 0x80 idx (by decide) hidx
  have hval : evalExpr [] st (mloadE (addE (u 0x80) (shlE (u 5) (v "t")))) =
      some (s.world.memory (0x80 + 32 * idx)).val :=
    SphincsMinusVerifiers.MemoryKit.evalExpr_mload_eq st
      (addE (u 0x80) (shlE (u 5) (v "t"))) (0x80 + 32 * idx) hsrc
  rw [show c12ForsRootCopyBody =
      [mstoreE (addE (u 0x40) (shlE (u 5) (v "t")))
        (mloadE (addE (u 0x80) (shlE (u 5) (v "t"))))] by rfl] at hExec
  change execStmtList [] st
      [Stmt.mstore (addE (u 0x40) (shlE (u 5) (v "t")))
        (mloadE (addE (u 0x80) (shlE (u 5) (v "t"))))] =
      .continue s'' at hExec
  rw [execStmtList_cons_continue _ _ _ _
      (MemoryKit.execStmt_mstore_continue st
        (addE (u 0x40) (shlE (u 5) (v "t")))
        (mloadE (addE (u 0x80) (shlE (u 5) (v "t"))))
        (0x40 + 32 * idx) (s.world.memory (0x80 + 32 * idx)).val
        hoff hval)] at hExec
  injection hExec with hs
  subst s''
  show (MemoryKit.memUpdate st.world.memory (0x40 + 32 * idx)
      (s.world.memory (0x80 + 32 * idx)).val 0x00).val =
    (s.world.memory 0x00).val
  rw [MemoryKit.memUpdate_diff _ _ _ _ (by omega)]

private theorem c12ForsCompressSegment_preserves_memory_zero_body :
    ∀ (s s'' : RuntimeState) (stmt : Stmt),
      stmt ∈ c12ForsCompressSegment → execStmt [] s stmt = .continue s'' →
      (s''.world.memory 0x00).val = (s.world.memory 0x00).val := by
  intro s s'' stmt hmem hexec
  simp only [c12ForsCompressSegment, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      _ _ 0x00 "adrsRoots" _ hexec
  · refine SphincsMinusVerifiers.MemoryFrame.execStmt_mstore_preserves_memory_val
      _ _ 0x00 _ _ ?_ hexec
    intro ro rv hoff hval
    change evalExpr [] s (.literal 0x20) = some ro at hoff
    rw [show evalExpr [] s (.literal 0x20) = some 0x20 from rfl] at hoff
    injection hoff with hro
    subst ro
    decide
  · refine SphincsMinusVerifiers.MemoryFrame.execStmt_forEach_preserves_memory_val_range
      "t" 0x00 _ _ (fun idx => idx < 20) _ _ ?_ ?_ hexec
    · intro s idx hidx s'' hExec
      exact c12ForsRootCopyBody_preserves_memory_zero_bound s idx hidx s'' hExec
    · intro bound i hbound _ hi
      change evalExpr [] s (u 20) = some bound at hbound
      rw [show evalExpr [] s (u 20) = some 20 from rfl] at hbound
      injection hbound with hb
      subst bound
      exact hi
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      _ _ 0x00 "currentNode" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      _ _ 0x00 "curTree" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      _ _ 0x00 "curLeaf" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      _ _ 0x00 "sigOff" _ hexec

/-- C12 FORS-root compression and hypertree setup preserve the public-seed scratch cell. -/
theorem c12StepForsCompress_preserves_memory_zero (st : RuntimeState) :
    ((c12StepForsCompress st).world.memory 0x00).val =
      (st.world.memory 0x00).val := by
  exact SphincsMinusVerifiers.MemoryFrame.execStmtList_preserves_memory_val
    0x00 c12ForsCompressSegment st (c12StepForsCompress st)
    c12ForsCompressSegment_preserves_memory_zero_body
    (execC12ForsCompressSegment st)

private theorem c12ForsRootCopyBody_preserves_sc :
    PreservesSC c12ForsRootCopyBody := by
  intro s s'' stmt hmem hexec
  simp only [c12ForsRootCopyBody, List.mem_cons, List.not_mem_nil, or_false] at hmem
  subst hmem
  exact SphincsMinusVerifiers.StateFrame.execStmt_mstore_preserves_selector_calldata
    _ _ _ _ hexec

private theorem c12ForsCompressSegment_preserves_sc :
    PreservesSC c12ForsCompressSegment := by
  intro s s'' stmt hmem hexec
  simp only [c12ForsCompressSegment, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      _ _ "adrsRoots" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_mstore_preserves_selector_calldata
      _ _ _ _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_forEach_preserves_selector_calldata
      "t" _ _ _ _ c12ForsRootCopyBody_preserves_sc hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      _ _ "currentNode" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      _ _ "curTree" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      _ _ "curLeaf" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      _ _ "sigOff" _ hexec

/-- C12 FORS-root compression and hypertree setup preserve selector/calldata. -/
theorem c12StepForsCompress_preserves_selector_calldata (st : RuntimeState) :
    SphincsMinusVerifiers.StateFrame.PreservesSelectorCalldata
      st (c12StepForsCompress st) := by
  exact SphincsMinusVerifiers.StateFrame.execStmtList_preserves_selector_calldata
    c12ForsCompressSegment st (c12StepForsCompress st)
    c12ForsCompressSegment_preserves_sc
    (execC12ForsCompressSegment st)

private theorem c12ForsRootCopyBody_preserves_root :
    PreservesRoot c12ForsRootCopyBody := by
  intro s s'' stmt hmem hexec
  simp only [c12ForsRootCopyBody, List.mem_cons, List.not_mem_nil, or_false] at hmem
  subst hmem
  exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
    _ _ "root" _ _ hexec

private theorem c12ForsCompressSegment_preserves_root :
    PreservesRoot c12ForsCompressSegment := by
  intro s s'' stmt hmem hexec
  simp only [c12ForsCompressSegment, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "adrsRoots" "root" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      _ _ "root" _ _ hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
      "t" "root" _ _ _ _ (by decide) c12ForsRootCopyBody_preserves_root hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "currentNode" "root" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "curTree" "root" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "curLeaf" "root" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "sigOff" "root" _ (by decide) hexec

/-- C12 FORS-root compression and hypertree setup preserve `"root"`. -/
theorem c12StepForsCompress_preserves_root (st : RuntimeState) :
    lookupValue (c12StepForsCompress st).bindings "root" =
      lookupValue st.bindings "root" :=
  SphincsMinusVerifiers.BindingFrame.execStmtList_preserves_lookup
    "root" c12ForsCompressSegment st (c12StepForsCompress st)
    c12ForsCompressSegment_preserves_root
    (execC12ForsCompressSegment st)

private theorem c12ForsRootCopyBody_preserves_sigBase :
    ∀ (s s'' : RuntimeState) (stmt : Stmt),
      stmt ∈ c12ForsRootCopyBody → execStmt [] s stmt = .continue s'' →
      lookupValue s''.bindings "sigBase" = lookupValue s.bindings "sigBase" := by
  intro s s'' stmt hmem hexec
  simp only [c12ForsRootCopyBody, List.mem_cons, List.not_mem_nil, or_false] at hmem
  subst hmem
  exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
    _ _ "sigBase" _ _ hexec

private theorem c12ForsCompressSegment_preserves_sigBase :
    ∀ (s s'' : RuntimeState) (stmt : Stmt),
      stmt ∈ c12ForsCompressSegment → execStmt [] s stmt = .continue s'' →
      lookupValue s''.bindings "sigBase" = lookupValue s.bindings "sigBase" := by
  intro s s'' stmt hmem hexec
  simp only [c12ForsCompressSegment, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "adrsRoots" "sigBase" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      _ _ "sigBase" _ _ hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
      "t" "sigBase" _ _ _ _ (by decide) c12ForsRootCopyBody_preserves_sigBase hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "currentNode" "sigBase" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "curTree" "sigBase" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "curLeaf" "sigBase" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "sigOff" "sigBase" _ (by decide) hexec

/-- C12 FORS-root compression and hypertree setup preserve `"sigBase"`. -/
theorem c12StepForsCompress_preserves_sigBase (st : RuntimeState) :
    lookupValue (c12StepForsCompress st).bindings "sigBase" =
      lookupValue st.bindings "sigBase" :=
  SphincsMinusVerifiers.BindingFrame.execStmtList_preserves_lookup
    "sigBase" c12ForsCompressSegment st (c12StepForsCompress st)
    c12ForsCompressSegment_preserves_sigBase
    (execC12ForsCompressSegment st)

#print axioms execC12ForsRootCopyBody
#print axioms execC12ForsCompressSegment
#print axioms c12StepForsCompress_sigOff_eq
#print axioms c12StepForsCompress_curTree_eq
#print axioms c12StepForsCompress_curLeaf_eq
#print axioms c12AfterFors_observed_eq_after_fors_compress
#print axioms c12StepForsCompress_preserves_root
#print axioms c12StepForsCompress_preserves_sigBase
#print axioms c12StepForsCompress_preserves_selector_calldata
#print axioms c12StepForsCompress_preserves_memory_zero

end SphincsMinusVerifiers.C12SegmentForsCompress
