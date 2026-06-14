import SphincsMinusVerifiers.C13ResidualLayer1StateFacts

namespace SphincsMinusVerifiers

open SphincsMinusVerifierSpec
open Compiler.Proofs.IRGeneration.SourceSemantics

theorem c13ResidualSecondLayerBeforeDigest_wotsAdrs_hyperIndex
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed) :
    let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
    let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
    lookupValue
        (SegmentLayer3.beforeDigest
          (c13ResidualSecondLayerGuardState pkSeed pkRoot message sig)).bindings
        "wotsAdrs" =
      C13Concrete.adrsWotsHashBase
        1 ((digest.hyperIndex / 2048) / 2048)
          ((digest.hyperIndex / 2048) % 2048) := by
  intro pk digest
  exact SegmentLayer3.beforeDigest_wotsAdrs_eq_of_layer_idxTree
    (c13ResidualSecondLayerGuardState pkSeed pkRoot message sig)
    1 (digest.hyperIndex / 2048)
    (c13ResidualSecondLayerGuardState_layer pkSeed pkRoot message sig)
    (c13ResidualSecondLayerGuardState_idxTree_hyperIndex
      pkSeed pkRoot message sig hParse)
    (by decide : 1 < 2 ^ 32)
    (lt_of_le_of_lt
      (Nat.div_le_self _ _)
      (C13Concrete.hMsgC13_hyperIndex_lt pk sigParsed.R message))

theorem c13ResidualSecondLayer_wotsAdrs_hyperIndex_norm
    (pkSeed pkRoot message : Bytes) (sigParsed : Signature) :
    let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
    let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
    wordNormalize
        (C13Concrete.adrsWotsHashBase
          1 ((digest.hyperIndex / 2048) / 2048)
            ((digest.hyperIndex / 2048) % 2048))
      =
        C13Concrete.adrsWotsHashBase
          1 ((digest.hyperIndex / 2048) / 2048)
            ((digest.hyperIndex / 2048) % 2048) := by
  intro pk digest
  have h128 :
      (((digest.hyperIndex / 2048) / 2048) <<< 128) < 2 ^ 256 := by
    have hnext : (digest.hyperIndex / 2048) / 2048 < 2 ^ 22 :=
      lt_of_le_of_lt
        (Nat.div_le_self _ _)
        (lt_of_le_of_lt
          (Nat.div_le_self _ _)
          (C13Concrete.hMsgC13_hyperIndex_lt pk sigParsed.R message))
    rw [Nat.shiftLeft_eq]
    calc
      ((digest.hyperIndex / 2048) / 2048) * 2 ^ 128 < 2 ^ 22 * 2 ^ 128 :=
        Nat.mul_lt_mul_of_pos_right hnext (by decide)
      _ < 2 ^ 256 := by decide
  have h64 :
      (((digest.hyperIndex / 2048) % 2048) <<< 64) < 2 ^ 256 := by
    have hleaf : (digest.hyperIndex / 2048) % 2048 < 2048 :=
      Nat.mod_lt _ (by decide : 0 < 2048)
    rw [Nat.shiftLeft_eq]
    calc
      ((digest.hyperIndex / 2048) % 2048) * 2 ^ 64 < 2048 * 2 ^ 64 :=
        Nat.mul_lt_mul_of_pos_right hleaf (by decide)
      _ < 2 ^ 256 := by decide
  have hLayer : (1 : Nat) <<< 224 < 2 ^ 256 := by
    norm_num [Nat.shiftLeft_eq]
  have hinner :
      (((digest.hyperIndex / 2048) / 2048) <<< 128 |||
          (((digest.hyperIndex / 2048) % 2048) <<< 64)) < 2 ^ 256 :=
    Nat.bitwise_lt_two_pow h128 h64
  have haddr :
      ((1 : Nat) <<< 224 |||
        ((((digest.hyperIndex / 2048) / 2048) <<< 128) |||
          (((digest.hyperIndex / 2048) % 2048) <<< 64))) < 2 ^ 256 :=
    Nat.bitwise_lt_two_pow hLayer hinner
  simpa [C13Concrete.adrsWotsHashBase, Nat.lor_assoc] using
    SegmentS2.wordNormalize_of_lt haddr

theorem c13ResidualSecondLayerBeforeDigest_wotsAdrs_slot_hyperIndex
    (pkSeed pkRoot message sig : Bytes) (sigParsed : Signature)
    (hParse : C13Concrete.parseSignatureC13 c13 sig = some sigParsed) :
    let pk : PublicKey := { pkSeed := pkSeed, pkRoot := pkRoot }
    let digest := C13Concrete.c13PrimitivesConcrete.hMsg c13 pk sigParsed.R message
    ((SegmentLayer3.beforeDigest
        (c13ResidualSecondLayerGuardState pkSeed pkRoot message sig)).world.memory 0x20).val =
      C13Concrete.adrsWotsHashBase
        1 ((digest.hyperIndex / 2048) / 2048)
          ((digest.hyperIndex / 2048) % 2048) := by
  intro pk digest
  rw [SegmentLayer3.beforeDigest_memory_0x20_eq_of_wotsAdrs
    (c13ResidualSecondLayerGuardState pkSeed pkRoot message sig)
    (C13Concrete.adrsWotsHashBase
      1 ((digest.hyperIndex / 2048) / 2048)
        ((digest.hyperIndex / 2048) % 2048))
    (c13ResidualSecondLayerBeforeDigest_wotsAdrs_hyperIndex
      pkSeed pkRoot message sig sigParsed hParse)]
  exact c13ResidualSecondLayer_wotsAdrs_hyperIndex_norm
    pkSeed pkRoot message sigParsed

theorem c13ResidualSecondLayerBeforeDigest_currentNode_slot
    (pkSeed pkRoot message sig root0 : Bytes)
    (hCurrent :
      lookupValue
          (c13ResidualSecondLayerGuardState pkSeed pkRoot message sig).bindings
          "currentNode" = C13Concrete.wordOfHash16 root0) :
    ((SegmentLayer3.beforeDigest
        (c13ResidualSecondLayerGuardState pkSeed pkRoot message sig)).world.memory 0x40).val =
      C13Concrete.wordOfHash16 root0 :=
  SegmentLayer3.beforeDigest_memory_0x40_eq_wordOfHash16
    (c13ResidualSecondLayerGuardState pkSeed pkRoot message sig) root0 hCurrent

end SphincsMinusVerifiers
