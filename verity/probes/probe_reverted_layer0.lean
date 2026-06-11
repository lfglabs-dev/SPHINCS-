/-
  Probe v2: discharge of the
  `c13_reverted_layer0_beforeAuthOff_wotsPk_lightweight_chain_cells_residual`
  axiom (Proofs.lean:12014).  Same concrete entry state as the ok-path
  layer-0 inputs obligation; the entry scalar facts feed the verified
  reverted closure `c13RevertedLayer0_copyFold43_wotsChainsEnd_cells_of_inputs`.
  Split into per-fact lemmas so each declaration gets a fresh heartbeat
  budget and any divergence is localized.
-/
import SphincsMinusVerifiers.Proofs

namespace SphincsMinusVerifiers

open SphincsMinusVerifierSpec
open Compiler.Proofs.IRGeneration.SourceSemantics
open SphincsMinusVerifiers.MkC13State
open SphincsMinusVerifiers.SegmentCompose

/-- Lightweight entry state world projection (bindings-only updates). -/
private theorem probe_light_world (ls : RuntimeState) :
    (c13BeforeWotsPkLightState ls).world = (SegmentLayer3.afterDigit ls).world := rfl

/-- Lightweight entry state bindings shape. -/
private theorem probe_light_bindings (ls : RuntimeState) :
    (c13BeforeWotsPkLightState ls).bindings =
      bindValue
        (bindValue (SegmentLayer3.afterDigit ls).bindings "wotsPtr"
          ((evalExpr [] (SegmentLayer3.afterDigit ls)
            (.add (.localVar "sigBase") (.localVar "sigOff"))).getD 0))
        "i" (wordNormalize 0) := rfl

/-- The two trailing `letVar`s of the pre-checksum prefix (`"d"`, `"digitSum"`)
preserve every other binding from the pre-digest cutpoint. -/
private theorem probe_beforeDigitLoop_lookup_eq_beforeDigest_of_ne
    (ls : RuntimeState) (key : String)
    (hneD : "d" ≠ key) (hneSum : "digitSum" ≠ key) :
    lookupValue (SegmentLayer3.beforeDigitLoop ls).bindings key =
      lookupValue (SegmentLayer3.beforeDigest ls).bindings key := by
  have h : execStmtList [] ls
      (SegmentLayer3.prefixBeforeDigest ++
        [ Compiler.CompilationModel.Stmt.letVar "d"
            (.keccak256 (.literal 0x00) (.literal 0x80))
        , Compiler.CompilationModel.Stmt.letVar "digitSum" (.literal 0) ]) =
      .continue (SegmentLayer3.beforeDigitLoop ls) :=
    SegmentLayer3.beforeDigitLoop_eq ls
  rw [MemoryKit.execStmtList_append_continue _ _ _ _
    (SegmentLayer3.beforeDigest_eq ls)] at h
  rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "d" _ _ rfl)] at h
  rw [SphincsMinusVerifiers.ClimbKit.execStmtList_cons_continue _ _ _ _
    (MemoryKit.execStmt_letVar_continue _ "digitSum" _ _ rfl)] at h
  have hnil : ∀ (s : RuntimeState), execStmtList [] s [] = StmtResult.continue s :=
    fun _ => rfl
  rw [hnil] at h
  have he := StmtResult.continue.inj h
  rw [← he]
  rw [MemoryKit.lookupValue_bindValue_ne _ "digitSum" key _ hneSum]
  rw [MemoryKit.lookupValue_bindValue_ne _ "d" key _ hneD]

/-- The pre-checksum prefix does not rebind `"sigOff"`. -/
private theorem probe_beforeDigitLoop_preserves_sigOff (ls : RuntimeState) :
    lookupValue (SegmentLayer3.beforeDigitLoop ls).bindings "sigOff" =
      lookupValue ls.bindings "sigOff" := by
  refine BindingFrame.execStmtList_preserves_lookup "sigOff"
    SegmentLayer3.prefixBeforeDigitLoop
    ls (SegmentLayer3.beforeDigitLoop ls) ?_ (SegmentLayer3.beforeDigitLoop_eq ls)
  intro s s'' stmt hmem hexec
  simp [SegmentLayer3.prefixBeforeDigitLoop] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact BindingFrame.execStmt_letVar_preserves_lookup _ _ "idxLeaf" "sigOff" _ (by decide) hexec
  · exact BindingFrame.execStmt_assignVar_preserves_lookup _ _ "idxTree" "sigOff" _ (by decide) hexec
  · exact BindingFrame.execStmt_letVar_preserves_lookup _ _ "wotsAdrs" "sigOff" _ (by decide) hexec
  · exact BindingFrame.execStmt_letVar_preserves_lookup _ _ "countOff" "sigOff" _ (by decide) hexec
  · exact BindingFrame.execStmt_letVar_preserves_lookup _ _ "count" "sigOff" _ (by decide) hexec
  · exact BindingFrame.execStmt_mstore_preserves_lookup _ _ "sigOff" _ _ hexec
  · exact BindingFrame.execStmt_mstore_preserves_lookup _ _ "sigOff" _ _ hexec
  · exact BindingFrame.execStmt_mstore_preserves_lookup _ _ "sigOff" _ _ hexec
  · exact BindingFrame.execStmt_letVar_preserves_lookup _ _ "d" "sigOff" _ (by decide) hexec
  · exact BindingFrame.execStmt_letVar_preserves_lookup _ _ "digitSum" "sigOff" _ (by decide) hexec

set_option maxHeartbeats 2000000 in
/-- Seed cell at the lightweight entry state. -/
private theorem probe_seed0 (pkSeed pkRoot message sig : Bytes) :
    ((c13BeforeWotsPkLightState
        (c13FirstLayerGuardState pkSeed pkRoot message sig)).world.memory 0x00).val =
      C13Concrete.wordOfHash16 pkSeed := by
  rw [probe_light_world]
  rw [SegmentLayer3.afterDigit_preserves_memory_zero]
  exact c13FirstLayerGuardState_seed_slot pkSeed pkRoot message sig

set_option maxHeartbeats 2000000 in
/-- `"d"` binding at the lightweight entry state. -/
private theorem probe_d0 (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature) (forsPk : Bytes) (lsig : XmssLayerSig)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed)
    (hFors : C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      sigParsed.fors = some forsPk)
    (hLayer0 : sigParsed.layers[0]? = some lsig) :
    lookupValue
        (c13BeforeWotsPkLightState
          (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings "d" =
      C13Concrete.wotsDigest (C13Concrete.wordOfHash16 pkSeed)
        0
        ((C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048)
        ((C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex % 2048)
        lsig.wots.count (C13Concrete.wordOfHash16 forsPk) := by
  rw [probe_light_bindings]
  rw [MemoryKit.lookupValue_bindValue_ne _ "i" "d" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "wotsPtr" "d" _ (by decide)]
  rw [SegmentLayer3.afterDigit_preserves_lookup_of_ne
    (c13FirstLayerGuardState pkSeed pkRoot message sig) "d"
    (by decide) (by decide)]
  exact SegmentLayer3.beforeDigitLoop_d_eq_wotsDigest_of_scratch
    (c13FirstLayerGuardState pkSeed pkRoot message sig)
    (C13Concrete.wordOfHash16 pkSeed) 0
    ((C13Concrete.c13PrimitivesConcrete.hMsg c13
      { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048)
    ((C13Concrete.c13PrimitivesConcrete.hMsg c13
      { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex % 2048)
    lsig.wots.count
    (C13Concrete.wordOfHash16 forsPk)
    (c13FirstLayerBeforeDigest_seed_slot pkSeed pkRoot message sig)
    (c13FirstLayerBeforeDigest_wotsAdrs_slot_hyperIndex
      pkSeed pkRoot message sig sigParsed hParse)
    (c13FirstLayerBeforeDigest_currentNode_slot
      pkSeed pkRoot message sig forsPk
      (c13AfterFinalize_forsPk_of_parse_fors
        pkSeed pkRoot message sig sigParsed forsPk hParse hFors))
    (c13FirstLayerBeforeDigest_count_slot_hyperIndex
      pkSeed pkRoot message sig sigParsed lsig hParse hLayer0)

set_option maxHeartbeats 2000000 in
/-- `"wotsAdrs"` binding at the lightweight entry state. -/
private theorem probe_adrs0 (pkSeed pkRoot message sig : Bytes)
    (sigParsed : Signature)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed) :
    lookupValue
        (c13BeforeWotsPkLightState
          (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings "wotsAdrs" =
      C13Concrete.adrsWotsHashBase 0
        ((C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex / 2048)
        ((C13Concrete.c13PrimitivesConcrete.hMsg c13
          { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message).hyperIndex % 2048) := by
  rw [probe_light_bindings]
  rw [MemoryKit.lookupValue_bindValue_ne _ "i" "wotsAdrs" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_ne _ "wotsPtr" "wotsAdrs" _ (by decide)]
  rw [SegmentLayer3.afterDigit_preserves_lookup_of_ne
    (c13FirstLayerGuardState pkSeed pkRoot message sig) "wotsAdrs"
    (by decide) (by decide)]
  rw [probe_beforeDigitLoop_lookup_eq_beforeDigest_of_ne
    (c13FirstLayerGuardState pkSeed pkRoot message sig) "wotsAdrs"
    (by decide) (by decide)]
  exact c13FirstLayerBeforeDigest_wotsAdrs_hyperIndex
    pkSeed pkRoot message sig sigParsed hParse

set_option maxHeartbeats 2000000 in
/-- `"wotsPtr"` value at the lightweight entry state. -/
private theorem probe_wptr0 (pkSeed pkRoot message sig : Bytes) :
    lookupValue
        (c13BeforeWotsPkLightState
          (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings "wotsPtr" =
      sigDataOffset + 1952 := by
  rw [probe_light_bindings]
  rw [MemoryKit.lookupValue_bindValue_ne _ "i" "wotsPtr" _ (by decide)]
  rw [MemoryKit.lookupValue_bindValue_self]
  have hSigBase : evalExpr []
      (SegmentLayer3.afterDigit
        (c13FirstLayerGuardState pkSeed pkRoot message sig))
      (.localVar "sigBase") = some sigDataOffset := by
    show some (lookupValue
      (SegmentLayer3.afterDigit
        (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
      "sigBase") = _
    rw [SegmentLayer3.afterDigit_preserves_lookup_of_ne
      (c13FirstLayerGuardState pkSeed pkRoot message sig) "sigBase"
      (by decide) (by decide)]
    rw [SegmentLayer3.beforeDigitLoop_preserves_sigBase]
    rw [c13FirstLayerGuardState_sigBase]
  have hSigOff : evalExpr []
      (SegmentLayer3.afterDigit
        (c13FirstLayerGuardState pkSeed pkRoot message sig))
      (.localVar "sigOff") = some 1952 := by
    show some (lookupValue
      (SegmentLayer3.afterDigit
        (c13FirstLayerGuardState pkSeed pkRoot message sig)).bindings
      "sigOff") = _
    rw [SegmentLayer3.afterDigit_preserves_lookup_of_ne
      (c13FirstLayerGuardState pkSeed pkRoot message sig) "sigOff"
      (by decide) (by decide)]
    rw [probe_beforeDigitLoop_preserves_sigOff]
    rw [c13FirstLayerGuardState_sigOff]
    rw [SegmentS2.wordNormalize_of_lt (by decide : 1952 < 2 ^ 256)]
  rw [SphincsMinusVerifiers.ClimbKeccakStep.evalExpr_add_bounded
    _ _ _ _ _ hSigBase hSigOff
    (by decide) (by decide) (by decide)]
  rfl

set_option maxHeartbeats 2000000 in
/-- Frozen calldata at the lightweight entry state. -/
private theorem probe_cd0 (pkSeed pkRoot message sig : Bytes) :
    (c13BeforeWotsPkLightState
        (c13FirstLayerGuardState pkSeed pkRoot message sig)).world.calldata =
      headWords pkSeed pkRoot message sig.size ++ bytesToWords sig := by
  rw [probe_light_world]
  rw [(SegmentLayer3.afterDigit_preserves_selector_calldata
    (c13FirstLayerGuardState pkSeed pkRoot message sig)).2]
  exact c13FirstLayerGuardState_calldata pkSeed pkRoot message sig

set_option maxHeartbeats 2000000 in
/-- Probe twin of the axiom
`c13_reverted_layer0_beforeAuthOff_wotsPk_lightweight_chain_cells_residual`. -/
theorem probe_c13_reverted_layer0 :
  ∀ pkSeed pkRoot message sig sigParsed forsPk,
    C13Concrete.parseSignatureC13 c13 sig = some sigParsed →
    forcedZeroOk c13
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message) = true →
    C13Concrete.c13PrimitivesConcrete.forsPkFromSig c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      sigParsed.fors = some forsPk →
    foldHypertree C13Concrete.c13PrimitivesConcrete c13
      { pkSeed := pkSeed, pkRoot := pkRoot }
      (C13Concrete.c13PrimitivesConcrete.hMsg c13
        { pkSeed := pkSeed, pkRoot := pkRoot } sigParsed.R message)
      forsPk sigParsed.layers = .reverted →
    let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
    let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
    ∀ d : C13Concrete.FoldHypertreeC13RevertedLayer1Data
        pk digest forsPk sigParsed.layers,
      ∀ j, (h : j < 43) →
        ((ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.copyStep
          (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep
            (c13BeforeWotsPkLightState
              (c13FirstLayerGuardState pkSeed pkRoot message sig))
            0 43)
          0 43).world.memory (0x40 + 32 * j)).val =
          (InitialNodeKeccak.wotsChainsEnd
            (C13Concrete.wordOfHash16 pkSeed) 0
            (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
            (C13Concrete.wordOfHash16 forsPk) d.lsig0.wots)[j]'(by
              rw [InitialNodeKeccak.wotsChainsEnd_length]
              omega) := by
  intro pkSeed pkRoot message sig sigParsed forsPk
    hParse _hZero hFors _hFold pk digest d
  have hSeed0 := probe_seed0 pkSeed pkRoot message sig
  have hD0 := probe_d0 pkSeed pkRoot message sig sigParsed forsPk d.lsig0
    hParse hFors d.hLayer0
  have hAdrs0 := probe_adrs0 pkSeed pkRoot message sig sigParsed hParse
  have hWPtrVal := probe_wptr0 pkSeed pkRoot message sig
  have hCdSt := probe_cd0 pkSeed pkRoot message sig
  have hHyLt :
      (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message).hyperIndex
        < 2 ^ 22 :=
    C13Concrete.hMsgC13_hyperIndex_lt pk sigParsed.R message
  have hDigestLt :
      C13Concrete.wotsDigest (C13Concrete.wordOfHash16 pkSeed)
        0 (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
        d.lsig0.wots.count (C13Concrete.wordOfHash16 forsPk) < 2 ^ 256 :=
    c13_wotsDigest_lt (C13Concrete.wordOfHash16 pkSeed)
      0 (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
      d.lsig0.wots.count (C13Concrete.wordOfHash16 forsPk)
  have hAdrsLt :
      C13Concrete.adrsWotsHashBase 0
        (digest.hyperIndex / 2048) (digest.hyperIndex % 2048) < 2 ^ 256 := by
    have hT : (digest.hyperIndex / 2048) <<< 128 < 2 ^ 256 := by
      rw [Nat.shiftLeft_eq]
      calc
        (digest.hyperIndex / 2048) * 2 ^ 128 ≤ 2 ^ 22 * 2 ^ 128 :=
          Nat.mul_le_mul_right _
            (le_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hHyLt))
        _ < 2 ^ 256 := by decide
    have hL : (digest.hyperIndex % 2048) <<< 64 < 2 ^ 256 := by
      rw [Nat.shiftLeft_eq]
      calc
        (digest.hyperIndex % 2048) * 2 ^ 64 ≤ 2047 * 2 ^ 64 :=
          Nat.mul_le_mul_right _
            (Nat.le_of_lt_succ (Nat.mod_lt _ (by decide : 0 < 2048)))
        _ < 2 ^ 256 := by decide
    have h224 : (0 : Nat) <<< 224 < 2 ^ 256 := by decide
    exact Nat.bitwise_lt_two_pow
      (Nat.bitwise_lt_two_pow h224 hT) hL
  have e : C13WotsOuterEntry pkSeed
      (c13BeforeWotsPkLightState
        (c13FirstLayerGuardState pkSeed pkRoot message sig))
      (C13Concrete.wotsDigest (C13Concrete.wordOfHash16 pkSeed)
        0 (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
        d.lsig0.wots.count (C13Concrete.wordOfHash16 forsPk))
      (C13Concrete.adrsWotsHashBase 0
        (digest.hyperIndex / 2048) (digest.hyperIndex % 2048))
      (sigDataOffset + 1952) :=
    { seed0 := hSeed0, d0 := hD0, adrs0 := hAdrs0, wptr0 := hWPtrVal }
  exact
    c13RevertedLayer0_copyFold43_wotsChainsEnd_cells_of_inputs
      pkSeed pkRoot message sig sigParsed
      (c13BeforeWotsPkLightState
        (c13FirstLayerGuardState pkSeed pkRoot message sig))
      (digest.hyperIndex / 2048) (digest.hyperIndex % 2048)
      (C13Concrete.wordOfHash16 forsPk)
      pk digest forsPk d hParse hDigestLt hAdrsLt e hCdSt

#print axioms probe_c13_reverted_layer0

end SphincsMinusVerifiers
