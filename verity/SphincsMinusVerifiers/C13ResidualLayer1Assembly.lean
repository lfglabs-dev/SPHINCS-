import SphincsMinusVerifiers.C13ResidualLayer1Inputs
import SphincsMinusVerifiers.C13WotsPkKeccak

namespace SphincsMinusVerifiers

open SphincsMinusVerifierSpec
open Compiler.Proofs.IRGeneration.SourceSemantics
open SphincsMinusVerifiers.MkC13State
open SphincsMinusVerifiers.SegmentCompose

set_option maxHeartbeats 2000000 in
theorem c13_ok_beforeAuthOff_wotsPk_lightweight_chain_cells_residual_layer1_proved :
  ∀ pkSeed pkRoot message sig sigParsed forsPk specRoot,
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
      forsPk sigParsed.layers = .ok specRoot →
    let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
    let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
    ∀ d : C13Concrete.FoldHypertreeC13OkTwoLayerData
        pk digest forsPk sigParsed.layers specRoot,
      ∀ j, (h : j < 43) →
        ((ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.copyStep
          (ClimbLoop.foldLoop "i" SegmentLayer3CopyCells.wotsOuterStep
            (c13BeforeWotsPkLightState
              (CurrentNodeFrame.c13LayerLoopState1
                (mkC13State pkSeed pkRoot message sig)))
            0 43)
          0 43).world.memory (0x40 + 32 * j)).val =
          (InitialNodeKeccak.wotsChainsEnd
            (C13Concrete.wordOfHash16 pkSeed) 1
            ((digest.hyperIndex / 2048) / 2048)
            ((digest.hyperIndex / 2048) % 2048)
            (C13Concrete.wordOfHash16 d.root0) d.lsig1.wots)[j]'(by
              rw [InitialNodeKeccak.wotsChainsEnd_length]
              omega) := by
  intro pkSeed pkRoot message sig sigParsed forsPk specRoot
    hParse hZero hFors hFold pk digest d
  rw [← c13ResidualSecondLayerGuardState_eq_c13LayerLoopState1 pkSeed pkRoot message sig]
  have hStepSeed :
      ((SegmentLayer3.stepLayer
        (c13ResidualFirstLayerGuardState pkSeed pkRoot message sig)).world.memory 0x00).val =
        C13Concrete.wordOfHash16 pkSeed :=
    c13ResidualFirstLayerStep_seed_slot_of_parse
      pkSeed pkRoot message sig sigParsed hParse
  have hSeed1 := c13_layer1_light_seed1 pkSeed pkRoot message sig hStepSeed
  have hCurrent0Root :=
    c13Residual_layer1_current0Root pkSeed pkRoot message sig sigParsed forsPk specRoot
      hParse hZero hFors hFold d
  have hD1 := c13_layer1_light_d1 pkSeed pkRoot message sig sigParsed d.root0 d.lsig1
    hParse d.hLayer1 hStepSeed hCurrent0Root
  have hAdrs1 := c13_layer1_light_adrs1 pkSeed pkRoot message sig sigParsed hParse
  have hWPtrVal := c13_layer1_light_wptr1 pkSeed pkRoot message sig
  have hCdSt := c13_layer1_light_cd1 pkSeed pkRoot message sig
  have hHyLt :
      (C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message).hyperIndex
        < 2 ^ 22 :=
    C13Concrete.hMsgC13_hyperIndex_lt pk sigParsed.R message
  have hDigestLt :
      C13Concrete.wotsDigest (C13Concrete.wordOfHash16 pkSeed)
        1 ((digest.hyperIndex / 2048) / 2048) ((digest.hyperIndex / 2048) % 2048)
        d.lsig1.wots.count (C13Concrete.wordOfHash16 d.root0) < 2 ^ 256 :=
    c13Residual_wotsDigest_lt (C13Concrete.wordOfHash16 pkSeed)
      1 ((digest.hyperIndex / 2048) / 2048) ((digest.hyperIndex / 2048) % 2048)
      d.lsig1.wots.count (C13Concrete.wordOfHash16 d.root0)
  have hAdrsLt :
      C13Concrete.adrsWotsHashBase 1
        ((digest.hyperIndex / 2048) / 2048)
        ((digest.hyperIndex / 2048) % 2048) < 2 ^ 256 := by
    have hT : ((digest.hyperIndex / 2048) / 2048) <<< 128 < 2 ^ 256 := by
      rw [Nat.shiftLeft_eq]
      calc
        ((digest.hyperIndex / 2048) / 2048) * 2 ^ 128 ≤ 2 ^ 22 * 2 ^ 128 :=
          Nat.mul_le_mul_right _
            (le_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _)
              (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hHyLt)))
        _ < 2 ^ 256 := by decide
    have hL : ((digest.hyperIndex / 2048) % 2048) <<< 64 < 2 ^ 256 := by
      rw [Nat.shiftLeft_eq]
      calc
        ((digest.hyperIndex / 2048) % 2048) * 2 ^ 64 ≤ 2047 * 2 ^ 64 :=
          Nat.mul_le_mul_right _
            (Nat.le_of_lt_succ (Nat.mod_lt _ (by decide : 0 < 2048)))
        _ < 2 ^ 256 := by decide
    have h224 : (1 : Nat) <<< 224 < 2 ^ 256 := by decide
    exact Nat.bitwise_lt_two_pow
      (Nat.bitwise_lt_two_pow h224 hT) hL
  have e : C13WotsOuterEntry pkSeed
      (c13BeforeWotsPkLightState
        (c13ResidualSecondLayerGuardState pkSeed pkRoot message sig))
      (C13Concrete.wotsDigest (C13Concrete.wordOfHash16 pkSeed)
        1 ((digest.hyperIndex / 2048) / 2048) ((digest.hyperIndex / 2048) % 2048)
        d.lsig1.wots.count (C13Concrete.wordOfHash16 d.root0))
      (C13Concrete.adrsWotsHashBase 1
        ((digest.hyperIndex / 2048) / 2048)
        ((digest.hyperIndex / 2048) % 2048))
      (sigDataOffset + (1952 + 868)) :=
    { seed0 := hSeed1, d0 := hD1, adrs0 := hAdrs1, wptr0 := hWPtrVal }
  exact
    c13Layer1_copyFold43_wotsChainsEnd_cells_of_inputs
      pkSeed pkRoot message sig sigParsed
      (c13BeforeWotsPkLightState
        (c13ResidualSecondLayerGuardState pkSeed pkRoot message sig))
      ((digest.hyperIndex / 2048) / 2048) ((digest.hyperIndex / 2048) % 2048)
      (C13Concrete.wordOfHash16 d.root0)
      d.lsig1 hParse d.hLayer1 hDigestLt hAdrsLt e hCdSt

#print axioms c13_ok_beforeAuthOff_wotsPk_lightweight_chain_cells_residual_layer1_proved

end SphincsMinusVerifiers
