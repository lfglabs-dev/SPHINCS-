import SphincsMinusVerifiers.C13ResidualLayer0Inputs

namespace SphincsMinusVerifiers

open SphincsMinusVerifierSpec
open Compiler.Proofs.IRGeneration.SourceSemantics
open SphincsMinusVerifiers.MkC13State
open SphincsMinusVerifiers.SegmentCompose

set_option maxHeartbeats 2000000 in
theorem c13_reverted_layer0_beforeAuthOff_wotsPk_lightweight_chain_cells_residual_proved :
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
  have hSeed0 := c13_layer0_light_seed0 pkSeed pkRoot message sig
  have hD0 := c13_layer0_light_d0 pkSeed pkRoot message sig sigParsed forsPk d.lsig0
    hParse hFors d.hLayer0
  have hAdrs0 := c13_layer0_light_adrs0 pkSeed pkRoot message sig sigParsed hParse
  have hWPtrVal := c13_layer0_light_wptr0 pkSeed pkRoot message sig
  have hCdSt := c13_layer0_light_cd0 pkSeed pkRoot message sig
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

#print axioms c13_reverted_layer0_beforeAuthOff_wotsPk_lightweight_chain_cells_residual_proved

end SphincsMinusVerifiers
