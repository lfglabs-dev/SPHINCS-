import SphincsMinusVerifiers.C12SegmentSeed
import SphincsMinusVerifiers.ClimbLoop
import SphincsMinusVerifiers.ProofCore
import SphincsMinusVerifiers.BindingFrame
import SphincsMinusVerifiers.StateFrame
import SphincsMinusVerifiers.MemoryFrame
import SphincsMinusVerifiers.ClimbMemFrameMerkle
import SphincsMinusVerifiers.ClimbKeccakStep
import SphincsMinusVerifiers.SegmentS4ForsDataObligations

namespace SphincsMinusVerifiers.C12SegmentFors

open Compiler.CompilationModel (Stmt Expr)
open Compiler.Proofs.IRGeneration.SourceSemantics
open SphincsMinusVerifiers.ClimbKit (N_MASK execStmtList_cons_continue)
open SphincsMinusVerifiers.ClimbLoop (foldLoop execStmt_forEach_of_step)
open SphincsMinusVerifiers.MemoryKit (execStmt_mstore_continue execStmtList_append_continue)

private def u (n : Nat) : Expr := .literal n
private def v (name : String) : Expr := .localVar name
private def addE (a b : Expr) : Expr := .add a b
private def subE (a b : Expr) : Expr := .sub a b
private def mulE (a b : Expr) : Expr := .mul a b
private def andE (a b : Expr) : Expr := .bitAnd a b
private def orE (a b : Expr) : Expr := .bitOr a b
private def xorE (a b : Expr) : Expr := .bitXor a b
private def shlE (a b : Expr) : Expr := .shl a b
private def shrE (a b : Expr) : Expr := .shr a b
private def cdload (off : Expr) : Expr := .calldataload off
private def keccak (off size : Nat) : Expr := .keccak256 (u off) (u size)
private def mstore (off : Nat) (val : Expr) : Stmt := .mstore (u off) val
private def mstoreE (off val : Expr) : Stmt := .mstore off val

def c12ForsInnerBody : List Stmt := [
  .letVar "sibling" (andE (cdload (addE (v "authPtr") (shlE (u 4) (v "j")))) (u N_MASK)),
  .letVar "parentIdx" (shrE (u 1) (v "pathIdx")),
  .letVar "globalY" (orE (shlE (subE (u 6) (v "j")) (v "t")) (v "parentIdx")),
  mstore 0x20 (orE (v "forsBase") (orE (shlE (u 32) (addE (v "j") (u 1))) (v "globalY"))),
  .letVar "s" (shlE (u 5) (andE (v "pathIdx") (u 1))),
  mstoreE (xorE (u 0x40) (v "s")) (v "node"),
  mstoreE (xorE (u 0x60) (v "s")) (v "sibling"),
  .assignVar "node" (andE (keccak 0x00 0x80) (u N_MASK)),
  .assignVar "pathIdx" (v "parentIdx")
]

def c12ForsInnerStep (st : RuntimeState) : RuntimeState :=
  match execStmtList [] st c12ForsInnerBody with
  | .continue s' => s'
  | _ => st

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

private theorem assignVar_continue
    (st : RuntimeState) (name : String) (e : Expr) (val : Nat)
    (h : evalExpr [] st e = some val) :
    execStmt [] st (.assignVar name e) =
      .continue { st with bindings := bindValue st.bindings name val } := by
  show (match evalExpr [] st e with
        | some resolved =>
            StmtResult.continue { st with bindings := bindValue st.bindings name resolved }
        | none => .revert) = _
  rw [h]

theorem execC12ForsInner (st : RuntimeState) :
    execStmtList [] st c12ForsInnerBody = .continue (c12ForsInnerStep st) := by
  unfold c12ForsInnerStep c12ForsInnerBody mstore mstoreE u
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue st "sibling" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "parentIdx" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "globalY" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "s" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "node" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (assignVar_continue _ "pathIdx" _ _ rfl)]
  rfl

set_option maxHeartbeats 800000 in
/-- One C12 FORS inner Merkle step preserves the public-seed scratch cell. -/
theorem c12ForsInnerStep_preserves_memory_zero (st : RuntimeState) :
    ((c12ForsInnerStep st).world.memory 0x00).val =
      (st.world.memory 0x00).val := by
  let n : Nat := lookupValue st.bindings "pathIdx" % 2 ^ 256
  let sval : Nat := (Nat.land n 1) <<< 5
  let o5 : Nat := (0x40 : Nat) ^^^ sval
  let o6 : Nat := (0x60 : Nat) ^^^ sval
  have hsvalt : sval < 2 ^ 256 := by
    show (Nat.land n 1) <<< 5 < 2 ^ 256
    rw [Nat.shiftLeft_eq]
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul Nat.and_le_right (le_refl _)) (by decide)
  obtain ⟨vsib, h1⟩ : ∃ v, evalExpr [] st
      (.bitAnd (.calldataload (.add (.localVar "authPtr")
        (.shl (.literal 4) (.localVar "j"))))
        (.literal N_MASK)) = some v := ⟨_, rfl⟩
  obtain ⟨vpar, h2⟩ : ∃ v,
      evalExpr [] { st with bindings := bindValue st.bindings "sibling" vsib }
        (.shr (.literal 1) (.localVar "pathIdx")) = some v := ⟨_, rfl⟩
  obtain ⟨vgy, hG⟩ : ∃ v, evalExpr []
      { st with bindings :=
          bindValue (bindValue st.bindings "sibling" vsib) "parentIdx" vpar }
      (.bitOr (.shl (.sub (.literal 6) (.localVar "j")) (.localVar "t"))
        (.localVar "parentIdx")) = some v := ⟨_, rfl⟩
  obtain ⟨vadr, h3⟩ : ∃ v, evalExpr []
      { st with bindings :=
        bindValue (bindValue (bindValue st.bindings "sibling" vsib)
          "parentIdx" vpar) "globalY" vgy }
      (.bitOr (.localVar "forsBase")
        (.bitOr (.shl (.literal 32) (.add (.localVar "j") (.literal 1)))
          (.localVar "globalY"))) = some v := ⟨_, rfl⟩
  let vnode : Nat :=
    lookupValue (bindValue
      (bindValue (bindValue (bindValue st.bindings "sibling" vsib)
        "parentIdx" vpar) "globalY" vgy) "s" sval) "node"
  let vsib2 : Nat :=
    lookupValue (bindValue
      (bindValue (bindValue (bindValue st.bindings "sibling" vsib)
        "parentIdx" vpar) "globalY" vgy) "s" sval) "sibling"
  have hpathH4 :
      lookupValue
        (bindValue (bindValue (bindValue st.bindings "sibling" vsib)
          "parentIdx" vpar) "globalY" vgy) "pathIdx" =
        lookupValue st.bindings "pathIdx" := by
    rw [MemoryKit.lookupValue_bindValue_ne _ "globalY" "pathIdx" _ (by decide),
      MemoryKit.lookupValue_bindValue_ne _ "parentIdx" "pathIdx" _ (by decide),
      MemoryKit.lookupValue_bindValue_ne _ "sibling" "pathIdx" _ (by decide)]
  have hbitand : evalExpr []
      { st with
        world := { st.world with memory :=
          (MemoryKit.memUpdate st.world.memory 0x20 vadr) },
        bindings :=
          bindValue (bindValue (bindValue st.bindings "sibling" vsib)
            "parentIdx" vpar) "globalY" vgy }
      (.bitAnd (.localVar "pathIdx") (.literal 1)) = some (Nat.land n 1) := by
    have hbase := SphincsMinusVerifiers.SegmentS4ForsDataObligations.evalExpr_bitAnd_literal_modself
      { st with
        world := { st.world with memory :=
          (MemoryKit.memUpdate st.world.memory 0x20 vadr) },
        bindings :=
          bindValue (bindValue (bindValue st.bindings "sibling" vsib)
            "parentIdx" vpar) "globalY" vgy }
      (.localVar "pathIdx")
      (lookupValue
        (bindValue (bindValue (bindValue st.bindings "sibling" vsib)
          "parentIdx" vpar) "globalY" vgy) "pathIdx")
      1 rfl (by decide)
    rw [hpathH4] at hbase
    exact hbase
  have h4 : evalExpr []
      { st with
        world := { st.world with memory :=
          (MemoryKit.memUpdate st.world.memory 0x20 vadr) },
        bindings :=
          bindValue (bindValue (bindValue st.bindings "sibling" vsib)
            "parentIdx" vpar) "globalY" vgy }
      (.shl (.literal 5) (.bitAnd (.localVar "pathIdx") (.literal 1))) =
      some sval := by
    have hlit5 : evalExpr []
        { st with
          world := { st.world with memory :=
            (MemoryKit.memUpdate st.world.memory 0x20 vadr) },
          bindings :=
            bindValue (bindValue (bindValue st.bindings "sibling" vsib)
              "parentIdx" vpar) "globalY" vgy }
        (.literal 5) = some 5 := by
      show some (wordNormalize 5) = some 5
      rw [wordNormalize_eq_mod, show Compiler.Constants.evmModulus = 2 ^ 256 from rfl,
        Nat.mod_eq_of_lt (by decide)]
    exact SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded
      { st with
        world := { st.world with memory :=
          (MemoryKit.memUpdate st.world.memory 0x20 vadr) },
        bindings :=
          bindValue (bindValue (bindValue st.bindings "sibling" vsib)
            "parentIdx" vpar) "globalY" vgy }
      (.literal 5) (.bitAnd (.localVar "pathIdx") (.literal 1))
      5 (Nat.land n 1) hlit5 hbitand (by decide)
      (Nat.lt_of_le_of_lt Nat.and_le_right (by decide)) hsvalt
  have hs5 :
      lookupValue
        (bindValue
          (bindValue (bindValue (bindValue st.bindings "sibling" vsib)
            "parentIdx" vpar) "globalY" vgy) "s" sval) "s" =
        sval :=
    MemoryKit.lookupValue_bindValue_self _ "s" sval
  have h5off : evalExpr []
      { st with
        world := { st.world with memory :=
          (MemoryKit.memUpdate st.world.memory 0x20 vadr) },
        bindings :=
          bindValue (bindValue (bindValue (bindValue st.bindings "sibling" vsib)
            "parentIdx" vpar) "globalY" vgy) "s" sval }
      (.bitXor (.literal 0x40) (.localVar "s")) = some o5 :=
    SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_childOffset_xor
      { st with
        world := { st.world with memory :=
          (MemoryKit.memUpdate st.world.memory 0x20 vadr) },
        bindings :=
          bindValue (bindValue (bindValue (bindValue st.bindings "sibling" vsib)
            "parentIdx" vpar) "globalY" vgy) "s" sval }
      0x40 sval hs5 (by decide) hsvalt
  have h5val : evalExpr []
      { st with
        world := { st.world with memory :=
          (MemoryKit.memUpdate st.world.memory 0x20 vadr) },
        bindings :=
          bindValue (bindValue (bindValue (bindValue st.bindings "sibling" vsib)
            "parentIdx" vpar) "globalY" vgy) "s" sval }
      (.localVar "node") = some vnode := rfl
  have h6off : evalExpr []
      { st with
        world := { st.world with memory :=
          (MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode) },
        bindings :=
          bindValue (bindValue (bindValue (bindValue st.bindings "sibling" vsib)
            "parentIdx" vpar) "globalY" vgy) "s" sval }
      (.bitXor (.literal 0x60) (.localVar "s")) = some o6 :=
    SphincsMinusVerifiers.ClimbMemFrameMerkle.eval_childOffset_xor
      { st with
        world := { st.world with memory :=
          (MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode) },
        bindings :=
          bindValue (bindValue (bindValue (bindValue st.bindings "sibling" vsib)
            "parentIdx" vpar) "globalY" vgy) "s" sval }
      0x60 sval hs5 (by decide) hsvalt
  have h6val : evalExpr []
      { st with
        world := { st.world with memory :=
          (MemoryKit.memUpdate (MemoryKit.memUpdate st.world.memory 0x20 vadr) o5 vnode) },
        bindings :=
          bindValue (bindValue (bindValue (bindValue st.bindings "sibling" vsib)
            "parentIdx" vpar) "globalY" vgy) "s" sval }
      (.localVar "sibling") = some vsib2 := rfl
  have hpar : n % 2 = 0 ∨ n % 2 = 1 := by
    have hlt : n % 2 < 2 := Nat.mod_lt n (by decide)
    omega
  have hparOff : (n % 2 = 0 ∧ o5 = 0x40 ∧ o6 = 0x60)
      ∨ (n % 2 = 1 ∧ o5 = 0x60 ∧ o6 = 0x40) := by
    rcases hpar with hzero | hone
    · left
      have ho := SphincsMinusVerifiers.ClimbMemFrameMerkle.merkle_offsets_even n hzero
      have ho5 : o5 = 0x40 := by
        dsimp [o5, sval]
        change (0x40 : Nat) ^^^ ((n &&& 1) <<< 5) = 0x40
        exact ho.1
      have ho6 : o6 = 0x60 := by
        dsimp [o6, sval]
        change (0x60 : Nat) ^^^ ((n &&& 1) <<< 5) = 0x60
        exact ho.2
      exact ⟨hzero, ho5, ho6⟩
    · right
      have ho := SphincsMinusVerifiers.ClimbMemFrameMerkle.merkle_offsets_odd n hone
      have ho5 : o5 = 0x60 := by
        dsimp [o5, sval]
        change (0x40 : Nat) ^^^ ((n &&& 1) <<< 5) = 0x60
        exact ho.1
      have ho6 : o6 = 0x40 := by
        dsimp [o6, sval]
        change (0x60 : Nat) ^^^ ((n &&& 1) <<< 5) = 0x40
        exact ho.2
      exact ⟨hone, ho5, ho6⟩
  have ho5 : (0x00 : Nat) ≠ o5 := by
    rcases hparOff with ⟨_, h5, _⟩ | ⟨_, h5, _⟩ <;> rw [h5] <;> decide
  have ho6 : (0x00 : Nat) ≠ o6 := by
    rcases hparOff with ⟨_, _, h6⟩ | ⟨_, _, h6⟩ <;> rw [h6] <;> decide
  have hs1 := MemoryKit.execStmt_letVar_continue st "sibling" _ vsib h1
  set st1 : RuntimeState :=
    { st with bindings := bindValue st.bindings "sibling" vsib } with hst1
  have hs2 := MemoryKit.execStmt_letVar_continue st1 "parentIdx" _ vpar h2
  set st2 : RuntimeState :=
    { st1 with bindings := bindValue st1.bindings "parentIdx" vpar } with hst2
  have hsG := MemoryKit.execStmt_letVar_continue st2 "globalY" _ vgy hG
  set stG : RuntimeState :=
    { st2 with bindings := bindValue st2.bindings "globalY" vgy } with hstG
  have hoff3 : evalExpr [] stG (.literal 0x20) = some 0x20 := rfl
  have hs3 := MemoryKit.execStmt_mstore_continue stG (.literal 0x20) _ 0x20 vadr hoff3 h3
  set st3 : RuntimeState :=
    { stG with world := { stG.world with memory := MemoryKit.memUpdate stG.world.memory 0x20 vadr } }
    with hst3
  have hs4 := MemoryKit.execStmt_letVar_continue st3 "s" _ sval h4
  set st4 : RuntimeState :=
    { st3 with bindings := bindValue st3.bindings "s" sval } with hst4
  have hs5stmt := MemoryKit.execStmt_mstore_continue st4
    (.bitXor (.literal 0x40) (.localVar "s")) _ o5 vnode h5off h5val
  set st5 : RuntimeState :=
    { st4 with world := { st4.world with memory := MemoryKit.memUpdate st4.world.memory o5 vnode } }
    with hst5
  have hs6stmt := MemoryKit.execStmt_mstore_continue st5
    (.bitXor (.literal 0x60) (.localVar "s")) _ o6 vsib2 h6off h6val
  set st6 : RuntimeState :=
    { st5 with world := { st5.world with memory := MemoryKit.memUpdate st5.world.memory o6 vsib2 } }
    with hst6
  set kv : Nat :=
    (Verity.Core.Uint256.and
      (keccakMemorySlice st6.world.memory (wordNormalize 0x00) (wordNormalize 0x80))
      (wordNormalize N_MASK)).val with hkv
  have hval8 : evalExpr [] st6
      (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x80)) (.literal N_MASK)) =
      some kv := rfl
  have hs8 := assignVar_continue st6 "node" _ _ hval8
  set st8 : RuntimeState :=
    { st6 with bindings := bindValue st6.bindings "node" kv } with hst8
  have hval9 : evalExpr [] st8 (.localVar "parentIdx") =
      some (lookupValue st8.bindings "parentIdx") := rfl
  have hs9 := assignVar_continue st8 "pathIdx" _ _ hval9
  show ((match execStmtList [] st c12ForsInnerBody with
        | .continue s' => s' | _ => st).world.memory 0x00).val =
      (st.world.memory 0x00).val
  show ((match execStmtList [] st
          [ Stmt.letVar "sibling"
              (.bitAnd (.calldataload (.add (.localVar "authPtr")
                (.shl (.literal 4) (.localVar "j")))) (.literal N_MASK))
          , Stmt.letVar "parentIdx" (.shr (.literal 1) (.localVar "pathIdx"))
          , Stmt.letVar "globalY"
              (.bitOr (.shl (.sub (.literal 6) (.localVar "j")) (.localVar "t"))
                (.localVar "parentIdx"))
          , Stmt.mstore (.literal 0x20)
              (.bitOr (.localVar "forsBase")
                (.bitOr (.shl (.literal 32) (.add (.localVar "j") (.literal 1)))
                  (.localVar "globalY")))
          , Stmt.letVar "s" (.shl (.literal 5) (.bitAnd (.localVar "pathIdx") (.literal 1)))
          , Stmt.mstore (.bitXor (.literal 0x40) (.localVar "s")) (.localVar "node")
          , Stmt.mstore (.bitXor (.literal 0x60) (.localVar "s")) (.localVar "sibling")
          , Stmt.assignVar "node"
              (.bitAnd (.keccak256 (.literal 0x00) (.literal 0x80)) (.literal N_MASK))
          , Stmt.assignVar "pathIdx" (.localVar "parentIdx") ] with
        | .continue s' => s' | _ => st).world.memory 0x00).val =
      (st.world.memory 0x00).val
  rw [execStmtList_cons_continue _ _ _ _ hs1]
  rw [execStmtList_cons_continue _ _ _ _ hs2]
  rw [execStmtList_cons_continue _ _ _ _ hsG]
  rw [execStmtList_cons_continue _ _ _ _ hs3]
  rw [execStmtList_cons_continue _ _ _ _ hs4]
  rw [execStmtList_cons_continue _ _ _ _ hs5stmt]
  rw [execStmtList_cons_continue _ _ _ _ hs6stmt]
  rw [execStmtList_cons_continue _ _ _ _ hs8]
  rw [execStmtList_cons_continue _ _ _ _ hs9]
  show (st6.world.memory 0x00).val = (st.world.memory 0x00).val
  rw [hst6, hst5, hst4, hst3, hstG, hst2, hst1]
  simp only
  rw [MemoryKit.memUpdate_diff _ o6 0x00 vsib2 ho6,
      MemoryKit.memUpdate_diff _ o5 0x00 vnode ho5,
      MemoryKit.memUpdate_diff _ 0x20 0x00 vadr (by decide)]

def c12ForsOuterBody : List Stmt := [
  .letVar "mdT" (andE (shrE (mulE (u 7) (v "t")) (v "dVal")) (u 0x7F)),
  .letVar "treeOff" (addE (v "forsOff") (mulE (v "t") (u 128))),
  .letVar "sk" (andE (cdload (addE (v "sigBase") (v "treeOff"))) (u N_MASK)),
  mstore 0x20 (orE (v "forsBase") (orE (shlE (u 7) (v "t")) (v "mdT"))),
  mstore 0x40 (v "sk"),
  .letVar "node" (andE (keccak 0x00 0x60) (u N_MASK)),
  .letVar "authPtr" (addE (v "sigBase") (addE (v "treeOff") (u 16))),
  .letVar "pathIdx" (v "mdT"),
  .forEach "j" (u 7) c12ForsInnerBody,
  mstoreE (addE (u 0x80) (shlE (u 5) (v "t"))) (v "node")
]

private def c12ForsOuterPrefix : List Stmt := [
  .letVar "mdT" (andE (shrE (mulE (u 7) (v "t")) (v "dVal")) (u 0x7F)),
  .letVar "treeOff" (addE (v "forsOff") (mulE (v "t") (u 128))),
  .letVar "sk" (andE (cdload (addE (v "sigBase") (v "treeOff"))) (u N_MASK)),
  mstore 0x20 (orE (v "forsBase") (orE (shlE (u 7) (v "t")) (v "mdT"))),
  mstore 0x40 (v "sk"),
  .letVar "node" (andE (keccak 0x00 0x60) (u N_MASK)),
  .letVar "authPtr" (addE (v "sigBase") (addE (v "treeOff") (u 16))),
  .letVar "pathIdx" (v "mdT"),
  .forEach "j" (u 7) c12ForsInnerBody
]

private def c12ForsOuterTail : Stmt :=
  mstoreE (addE (u 0x80) (shlE (u 5) (v "t"))) (v "node")

private theorem c12ForsOuterBody_eq_prefix_tail :
    c12ForsOuterBody = c12ForsOuterPrefix ++ [c12ForsOuterTail] := rfl

private def c12ForsOuterPrefixStep (st : RuntimeState) : RuntimeState :=
  match execStmtList [] st c12ForsOuterPrefix with
  | .continue s' => s'
  | _ => st

private theorem execC12ForsOuterPrefix (st : RuntimeState) :
    execStmtList [] st c12ForsOuterPrefix = .continue (c12ForsOuterPrefixStep st) := by
  unfold c12ForsOuterPrefixStep c12ForsOuterPrefix mstore
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue st "mdT" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "treeOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "sk" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "node" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "authPtr" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "pathIdx" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
      (execStmt_forEach_of_step "j" (u 7) c12ForsInnerBody _ (wordNormalize 7)
        c12ForsInnerStep rfl execC12ForsInner)]
  rfl

def c12ForsOuterStep (st : RuntimeState) : RuntimeState :=
  match execStmtList [] st c12ForsOuterBody with
  | .continue s' => s'
  | _ => st

theorem execC12ForsOuterBody (st : RuntimeState) :
    execStmtList [] st c12ForsOuterBody = .continue (c12ForsOuterStep st) := by
  unfold c12ForsOuterStep c12ForsOuterBody mstore mstoreE
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue st "mdT" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "treeOff" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "sk" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "node" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "authPtr" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _ (letVar_continue _ "pathIdx" _ _ rfl)]
  rw [execStmtList_cons_continue _ _ _ _
      (execStmt_forEach_of_step "j" (u 7) c12ForsInnerBody _ (wordNormalize 7)
        c12ForsInnerStep rfl execC12ForsInner)]
  rw [execStmtList_cons_continue _ _ _ _ (execStmt_mstore_continue _ _ _ _ _ rfl rfl)]
  rfl

def c12ForsOuterStmt : Stmt :=
  .forEach "t" (u 20) c12ForsOuterBody

theorem c12ForsOuterStmt_eq_slice :
    [c12ForsOuterStmt] = C12SegmentSeed.c12AfterSeedSetup.take 1 := rfl

def c12AfterFors : List Stmt :=
  C12SegmentSeed.c12AfterSeedSetup.drop 1

theorem c12AfterSeedSetup_eq :
    C12SegmentSeed.c12AfterSeedSetup = [c12ForsOuterStmt] ++ c12AfterFors := rfl

def c12StepFors (st : RuntimeState) : RuntimeState :=
  match execStmtList [] st [c12ForsOuterStmt] with
  | .continue s' => s'
  | _ => st

theorem execC12ForsOuter (st : RuntimeState) :
    execStmtList [] st [c12ForsOuterStmt] = .continue (c12StepFors st) := by
  unfold c12StepFors c12ForsOuterStmt
  rw [execStmtList_cons_continue _ _ _ _
      (execStmt_forEach_of_step "t" (u 20) c12ForsOuterBody st (wordNormalize 20)
        c12ForsOuterStep rfl execC12ForsOuterBody)]
  rfl

theorem c12AfterSeedSetup_observed_eq_after_fors
    (st : RuntimeState) :
    observeStmtResultBool
        (execStmtList [] st C12SegmentSeed.c12AfterSeedSetup)
      =
    observeStmtResultBool
        (execStmtList [] (c12StepFors st) c12AfterFors) := by
  rw [c12AfterSeedSetup_eq]
  rw [execStmtList_append_continue _ _ _ _ (execC12ForsOuter st)]

private abbrev PreservesRoot (body : List Stmt) : Prop :=
  ∀ (s s'' : RuntimeState) (stmt : Stmt),
    stmt ∈ body → execStmt [] s stmt = .continue s'' →
    lookupValue s''.bindings "root" = lookupValue s.bindings "root"

private abbrev PreservesSC (body : List Stmt) : Prop :=
  ∀ (s s'' : RuntimeState) (stmt : Stmt),
    stmt ∈ body → execStmt [] s stmt = .continue s'' →
    SphincsMinusVerifiers.StateFrame.PreservesSelectorCalldata s s''

private abbrev PreservesLookup (key : String) (body : List Stmt) : Prop :=
  ∀ (s s'' : RuntimeState) (stmt : Stmt),
    stmt ∈ body → execStmt [] s stmt = .continue s'' →
    lookupValue s''.bindings key = lookupValue s.bindings key

private theorem c12ForsInnerBody_preserves_t : PreservesLookup "t" c12ForsInnerBody := by
  intro s s'' stmt hmem hexec
  simp only [c12ForsInnerBody, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "sibling" "t" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "parentIdx" "t" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "globalY" "t" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      _ _ "t" _ _ hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "s" "t" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      _ _ "t" _ _ hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      _ _ "t" _ _ hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
      _ _ "node" "t" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup
      _ _ "pathIdx" "t" _ (by decide) hexec

private theorem c12ForsOuterPrefix_preserves_t : PreservesLookup "t" c12ForsOuterPrefix := by
  intro s s'' stmt hmem hexec
  simp only [c12ForsOuterPrefix, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "mdT" "t" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "treeOff" "t" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "sk" "t" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      _ _ "t" _ _ hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup
      _ _ "t" _ _ hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "node" "t" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "authPtr" "t" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup
      _ _ "pathIdx" "t" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
      "j" "t" _ _ _ _ (by decide) c12ForsInnerBody_preserves_t hexec

private theorem c12ForsOuterPrefix_preserves_memory_zero
    (st s' : RuntimeState)
    (hExec : execStmtList [] st c12ForsOuterPrefix = .continue s') :
    (s'.world.memory 0x00).val = (st.world.memory 0x00).val := by
  refine SphincsMinusVerifiers.MemoryFrame.execStmtList_preserves_memory_val
    0x00 c12ForsOuterPrefix st s' ?_ hExec
  intro s s'' stmt hmem hexec
  simp only [c12ForsOuterPrefix, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      _ _ 0x00 "mdT" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      _ _ 0x00 "treeOff" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      _ _ 0x00 "sk" _ hexec
  · refine SphincsMinusVerifiers.MemoryFrame.execStmt_mstore_preserves_memory_val
      s s'' 0x00 (.literal 0x20)
      (orE (v "forsBase") (orE (shlE (u 7) (v "t")) (v "mdT"))) ?_ hexec
    intro ro rv hoff hval
    have hro : ro = 0x20 := by
      rw [show evalExpr [] s (.literal 0x20) = some 0x20 from rfl] at hoff
      cases hoff
      rfl
    rw [hro]
    decide
  · refine SphincsMinusVerifiers.MemoryFrame.execStmt_mstore_preserves_memory_val
      s s'' 0x00 (.literal 0x40) (v "sk") ?_ hexec
    intro ro rv hoff hval
    have hro : ro = 0x40 := by
      rw [show evalExpr [] s (.literal 0x40) = some 0x40 from rfl] at hoff
      cases hoff
      rfl
    rw [hro]
    decide
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      _ _ 0x00 "node" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      _ _ 0x00 "authPtr" _ hexec
  · exact SphincsMinusVerifiers.MemoryFrame.execStmt_letVar_preserves_memory_val
      _ _ 0x00 "pathIdx" _ hexec
  · refine SphincsMinusVerifiers.MemoryFrame.execStmt_forEach_preserves_memory_val_bound
      "j" 0x00 (u 7) c12ForsInnerBody s s'' ?_ hexec
    intro ls idx out hbody
    have hstep := execC12ForsInner { ls with
      bindings := bindValue ls.bindings "j" (wordNormalize idx) }
    rw [hbody] at hstep
    have hout : out = c12ForsInnerStep { ls with
        bindings := bindValue ls.bindings "j" (wordNormalize idx) } := by
      cases hstep
      rfl
    rw [hout]
    exact c12ForsInnerStep_preserves_memory_zero { ls with
      bindings := bindValue ls.bindings "j" (wordNormalize idx) }

private theorem c12_fors_idxNorm20 (idx : Nat) (hidx : idx < 20) :
    wordNormalize idx = idx := by
  rw [wordNormalize_eq_mod]
  exact Nat.mod_eq_of_lt (lt_trans hidx (by decide))

private theorem c12_fors_idxShl5_lt20 (idx : Nat) (hidx : idx < 20) :
    idx <<< 5 < 2 ^ 256 := by
  rw [Nat.shiftLeft_eq]
  have hle : idx * 2 ^ 5 ≤ 19 * 2 ^ 5 :=
    Nat.mul_le_mul_right _ (Nat.le_of_lt_succ hidx)
  exact lt_of_le_of_lt hle (by decide)

private theorem c12_fors_addIdxShl5_lt20 (base idx : Nat)
    (hbase : base ≤ 0x80) (hidx : idx < 20) :
    base + (idx <<< 5) < 2 ^ 256 := by
  rw [Nat.shiftLeft_eq]
  have hle : base + idx * 2 ^ 5 ≤ 128 + 19 * 2 ^ 5 :=
    Nat.add_le_add hbase (Nat.mul_le_mul_right _ (Nat.le_of_lt_succ hidx))
  exact lt_of_le_of_lt hle (by decide)

private theorem evalC12ForsTailOffset_of_lookup (s : RuntimeState) (idx : Nat)
    (hidx : idx < 20) (ht : lookupValue s.bindings "t" = idx) :
    evalExpr [] s (addE (u 0x80) (shlE (u 5) (v "t"))) =
      some (0x80 + 32 * idx) := by
  have h5 : evalExpr [] s (u 5) = some 5 := by rfl
  have htEval : evalExpr [] s (v "t") = some idx := by
    show some (lookupValue s.bindings "t") = some idx
    rw [ht]
  have hsh : evalExpr [] s (shlE (u 5) (v "t")) = some (idx <<< 5) :=
    SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_shl_bounded s (u 5) (v "t")
      5 idx h5 htEval (by decide) (lt_trans hidx (by decide))
      (c12_fors_idxShl5_lt20 idx hidx)
  have hbaseLit : evalExpr [] s (u 0x80) = some 0x80 := by rfl
  have hadd := SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_add_bounded s (u 0x80)
    (shlE (u 5) (v "t")) 0x80 (idx <<< 5) hbaseLit hsh
    (by decide) (c12_fors_idxShl5_lt20 idx hidx)
    (c12_fors_addIdxShl5_lt20 0x80 idx (by decide) hidx)
  convert hadd using 1
  rw [Nat.shiftLeft_eq]
  ring_nf

set_option maxHeartbeats 1000000 in
private theorem c12ForsOuterStep_preserves_memory_zero_bound
    (s : RuntimeState) (idx : Nat) (hidx : idx < 20) :
    ((c12ForsOuterStep
        { s with bindings := bindValue s.bindings "t" (wordNormalize idx) }).world.memory 0x00).val =
      (s.world.memory 0x00).val := by
  let st : RuntimeState :=
    { s with bindings := bindValue s.bindings "t" (wordNormalize idx) }
  have hall := execC12ForsOuterBody st
  rw [c12ForsOuterBody_eq_prefix_tail] at hall
  let mid : RuntimeState := c12ForsOuterPrefixStep st
  have hp : execStmtList [] st c12ForsOuterPrefix = .continue mid := by
    dsimp [mid]
    exact execC12ForsOuterPrefix st
  rw [execStmtList_append_continue _ _ _ _ hp] at hall
  have hprefixMem := c12ForsOuterPrefix_preserves_memory_zero st mid hp
  have hprefixT := SphincsMinusVerifiers.BindingFrame.execStmtList_preserves_lookup
    "t" c12ForsOuterPrefix st mid c12ForsOuterPrefix_preserves_t hp
  have hstT : lookupValue st.bindings "t" = idx := by
    dsimp [st]
    rw [MemoryKit.lookupValue_bindValue_self, c12_fors_idxNorm20 idx hidx]
  have hmidT : lookupValue mid.bindings "t" = idx := by
    rw [hprefixT, hstT]
  have hoff := evalC12ForsTailOffset_of_lookup mid idx hidx hmidT
  have hval : evalExpr [] mid (v "node") = some (lookupValue mid.bindings "node") := rfl
  have ht := MemoryKit.execStmt_mstore_continue mid
    (addE (u 0x80) (shlE (u 5) (v "t"))) (v "node")
    (0x80 + 32 * idx) (lookupValue mid.bindings "node") hoff hval
  set out : RuntimeState :=
    { mid with world := { mid.world with
        memory := MemoryKit.memUpdate mid.world.memory (0x80 + 32 * idx)
          (lookupValue mid.bindings "node") } } with hout
  have ht' : execStmt [] mid c12ForsOuterTail = .continue out := by
    dsimp [c12ForsOuterTail, out]
    exact ht
  rw [show execStmtList [] mid [c12ForsOuterTail] = .continue out by
    rw [execStmtList_cons_continue _ _ _ _ ht']
    rfl] at hall
  have houtMem :
      ((c12ForsOuterStep st).world.memory 0x00).val =
        (out.world.memory 0x00).val :=
    (congrArg (fun r => match r with
      | .continue ss => (ss.world.memory 0x00).val
      | _ => 0) hall).symm
  have htailMem : (out.world.memory 0x00).val = (mid.world.memory 0x00).val := by
    rw [hout]
    simp only
    rw [MemoryKit.memUpdate_diff _ (0x80 + 32 * idx) 0x00
      (lookupValue mid.bindings "node") (by omega)]
  rw [houtMem, htailMem, hprefixMem]

theorem c12StepFors_preserves_memory_zero (st : RuntimeState) :
    ((c12StepFors st).world.memory 0x00).val =
      (st.world.memory 0x00).val := by
  have hExec : execStmtList [] st [c12ForsOuterStmt] =
      .continue
        (foldLoop "t" c12ForsOuterStep
          { st with bindings := bindValue st.bindings "t" (wordNormalize 0) }
          0 (wordNormalize 20)) := by
    unfold c12ForsOuterStmt
    rw [execStmtList_cons_continue _ _ _ _
      (execStmt_forEach_of_step "t" (u 20) c12ForsOuterBody st (wordNormalize 20)
        c12ForsOuterStep rfl execC12ForsOuterBody)]
    rfl
  unfold c12StepFors
  rw [hExec]
  rw [SphincsMinusVerifiers.ClimbLoop.foldLoop_preserves_memory_val_range
    "t" c12ForsOuterStep 0x00 (fun idx => idx < 20)
    (fun s idx hidx => c12ForsOuterStep_preserves_memory_zero_bound s idx hidx)
    { st with bindings := bindValue st.bindings "t" (wordNormalize 0) }
    0 (wordNormalize 20)]
  · intro i hi0 hi
    rw [show wordNormalize 20 = 20 by rfl] at hi
    exact hi

private theorem c12ForsInnerBody_preserves_sc : PreservesSC c12ForsInnerBody := by
  intro s s'' stmt hmem hexec
  simp only [c12ForsInnerBody, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      _ _ "sibling" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      _ _ "parentIdx" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      _ _ "globalY" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_mstore_preserves_selector_calldata
      _ _ _ _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      _ _ "s" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_mstore_preserves_selector_calldata
      _ _ _ _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_mstore_preserves_selector_calldata
      _ _ _ _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_assignVar_preserves_selector_calldata
      _ _ "node" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_assignVar_preserves_selector_calldata
      _ _ "pathIdx" _ hexec

private theorem c12ForsOuterBody_preserves_sc : PreservesSC c12ForsOuterBody := by
  intro s s'' stmt hmem hexec
  simp only [c12ForsOuterBody, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      _ _ "mdT" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      _ _ "treeOff" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      _ _ "sk" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_mstore_preserves_selector_calldata
      _ _ _ _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_mstore_preserves_selector_calldata
      _ _ _ _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      _ _ "node" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      _ _ "authPtr" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_letVar_preserves_selector_calldata
      _ _ "pathIdx" _ hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_forEach_preserves_selector_calldata
      "j" _ _ _ _ c12ForsInnerBody_preserves_sc hexec
  · exact SphincsMinusVerifiers.StateFrame.execStmt_mstore_preserves_selector_calldata
      _ _ _ _ hexec

/-- The C12 FORS reconstruction loop preserves the byte-facing selector/calldata frame. -/
theorem c12StepFors_preserves_selector_calldata (st : RuntimeState) :
    SphincsMinusVerifiers.StateFrame.PreservesSelectorCalldata st (c12StepFors st) := by
  refine SphincsMinusVerifiers.StateFrame.execStmtList_preserves_selector_calldata
    [c12ForsOuterStmt] st (c12StepFors st) ?_ (execC12ForsOuter st)
  intro s s'' stmt hmem hexec
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  subst hmem
  exact SphincsMinusVerifiers.StateFrame.execStmt_forEach_preserves_selector_calldata
    "t" _ _ _ _ c12ForsOuterBody_preserves_sc hexec

private theorem c12ForsInnerBody_preserves_root : PreservesRoot c12ForsInnerBody := by
  intro s s'' stmt hmem hexec
  simp only [c12ForsInnerBody, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup _ _ "sibling" "root" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup _ _ "parentIdx" "root" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup _ _ "globalY" "root" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup _ _ "root" _ _ hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup _ _ "s" "root" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup _ _ "root" _ _ hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup _ _ "root" _ _ hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup _ _ "node" "root" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup _ _ "pathIdx" "root" _ (by decide) hexec

private theorem c12ForsOuterBody_preserves_root : PreservesRoot c12ForsOuterBody := by
  intro s s'' stmt hmem hexec
  simp only [c12ForsOuterBody, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup _ _ "mdT" "root" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup _ _ "treeOff" "root" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup _ _ "sk" "root" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup _ _ "root" _ _ hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup _ _ "root" _ _ hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup _ _ "node" "root" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup _ _ "authPtr" "root" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup _ _ "pathIdx" "root" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup "j" "root" _ _ _ _
      (by decide) c12ForsInnerBody_preserves_root hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup _ _ "root" _ _ hexec

/-- The C12 FORS reconstruction loop never writes the executable `"root"` binding. -/
theorem c12StepFors_preserves_root (st : RuntimeState) :
    lookupValue (c12StepFors st).bindings "root" =
      lookupValue st.bindings "root" :=
  SphincsMinusVerifiers.BindingFrame.execStmtList_preserves_lookup "root" [c12ForsOuterStmt] st
    (c12StepFors st)
    (by
      intro s s'' stmt hmem hexec
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      subst hmem
      exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup "t" "root" _ _ _ _
        (by decide) c12ForsOuterBody_preserves_root hexec)
    (execC12ForsOuter st)

private theorem c12ForsInnerBody_preserves_treeIdx :
    ∀ (s s'' : RuntimeState) (stmt : Stmt),
      stmt ∈ c12ForsInnerBody → execStmt [] s stmt = .continue s'' →
      lookupValue s''.bindings "treeIdx" = lookupValue s.bindings "treeIdx" := by
  intro s s'' stmt hmem hexec
  simp only [c12ForsInnerBody, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup _ _ "sibling" "treeIdx" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup _ _ "parentIdx" "treeIdx" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup _ _ "globalY" "treeIdx" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup _ _ "treeIdx" _ _ hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup _ _ "s" "treeIdx" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup _ _ "treeIdx" _ _ hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup _ _ "treeIdx" _ _ hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup _ _ "node" "treeIdx" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup _ _ "pathIdx" "treeIdx" _ (by decide) hexec

private theorem c12ForsOuterBody_preserves_treeIdx :
    ∀ (s s'' : RuntimeState) (stmt : Stmt),
      stmt ∈ c12ForsOuterBody → execStmt [] s stmt = .continue s'' →
      lookupValue s''.bindings "treeIdx" = lookupValue s.bindings "treeIdx" := by
  intro s s'' stmt hmem hexec
  simp only [c12ForsOuterBody, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup _ _ "mdT" "treeIdx" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup _ _ "treeOff" "treeIdx" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup _ _ "sk" "treeIdx" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup _ _ "treeIdx" _ _ hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup _ _ "treeIdx" _ _ hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup _ _ "node" "treeIdx" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup _ _ "authPtr" "treeIdx" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup _ _ "pathIdx" "treeIdx" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
      "j" "treeIdx" _ _ _ _ (by decide) c12ForsInnerBody_preserves_treeIdx hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup _ _ "treeIdx" _ _ hexec

/-- The C12 FORS reconstruction loop preserves `"treeIdx"`. -/
theorem c12StepFors_preserves_treeIdx (st : RuntimeState) :
    lookupValue (c12StepFors st).bindings "treeIdx" =
      lookupValue st.bindings "treeIdx" :=
  SphincsMinusVerifiers.BindingFrame.execStmtList_preserves_lookup "treeIdx" [c12ForsOuterStmt] st
    (c12StepFors st)
    (by
      intro s s'' stmt hmem hexec
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      subst hmem
      exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup "t" "treeIdx" _ _ _ _
        (by decide) c12ForsOuterBody_preserves_treeIdx hexec)
    (execC12ForsOuter st)

private theorem c12ForsInnerBody_preserves_sigBase :
    ∀ (s s'' : RuntimeState) (stmt : Stmt),
      stmt ∈ c12ForsInnerBody → execStmt [] s stmt = .continue s'' →
      lookupValue s''.bindings "sigBase" = lookupValue s.bindings "sigBase" := by
  intro s s'' stmt hmem hexec
  simp only [c12ForsInnerBody, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup _ _ "sibling" "sigBase" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup _ _ "parentIdx" "sigBase" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup _ _ "globalY" "sigBase" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup _ _ "sigBase" _ _ hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup _ _ "s" "sigBase" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup _ _ "sigBase" _ _ hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup _ _ "sigBase" _ _ hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup _ _ "node" "sigBase" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_assignVar_preserves_lookup _ _ "pathIdx" "sigBase" _ (by decide) hexec

private theorem c12ForsOuterBody_preserves_sigBase :
    ∀ (s s'' : RuntimeState) (stmt : Stmt),
      stmt ∈ c12ForsOuterBody → execStmt [] s stmt = .continue s'' →
      lookupValue s''.bindings "sigBase" = lookupValue s.bindings "sigBase" := by
  intro s s'' stmt hmem hexec
  simp only [c12ForsOuterBody, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup _ _ "mdT" "sigBase" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup _ _ "treeOff" "sigBase" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup _ _ "sk" "sigBase" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup _ _ "sigBase" _ _ hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup _ _ "sigBase" _ _ hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup _ _ "node" "sigBase" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup _ _ "authPtr" "sigBase" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_letVar_preserves_lookup _ _ "pathIdx" "sigBase" _ (by decide) hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup
      "j" "sigBase" _ _ _ _ (by decide) c12ForsInnerBody_preserves_sigBase hexec
  · exact SphincsMinusVerifiers.BindingFrame.execStmt_mstore_preserves_lookup _ _ "sigBase" _ _ hexec

/-- The C12 FORS reconstruction loop preserves `"sigBase"`. -/
theorem c12StepFors_preserves_sigBase (st : RuntimeState) :
    lookupValue (c12StepFors st).bindings "sigBase" =
      lookupValue st.bindings "sigBase" :=
  SphincsMinusVerifiers.BindingFrame.execStmtList_preserves_lookup "sigBase" [c12ForsOuterStmt] st
    (c12StepFors st)
    (by
      intro s s'' stmt hmem hexec
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      subst hmem
      exact SphincsMinusVerifiers.BindingFrame.execStmt_forEach_preserves_lookup "t" "sigBase" _ _ _ _
        (by decide) c12ForsOuterBody_preserves_sigBase hexec)
    (execC12ForsOuter st)

#print axioms execC12ForsInner
#print axioms c12ForsInnerStep_preserves_memory_zero
#print axioms execC12ForsOuterBody
#print axioms execC12ForsOuter
#print axioms c12AfterSeedSetup_observed_eq_after_fors
#print axioms c12StepFors_preserves_root
#print axioms c12StepFors_preserves_treeIdx
#print axioms c12StepFors_preserves_sigBase
#print axioms c12StepFors_preserves_selector_calldata
#print axioms c12StepFors_preserves_memory_zero

end SphincsMinusVerifiers.C12SegmentFors
