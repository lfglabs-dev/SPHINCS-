import SphincsMinusVerifiers.C13ResidualLayer1StateBase

namespace SphincsMinusVerifiers

open SphincsMinusVerifierSpec
open Compiler.Proofs.IRGeneration.SourceSemantics

theorem c13Residual_adrsXmssTree_lt_of_bounds
    (layer treeIdx : Nat)
    (hLayer : layer < 2 ^ 32)
    (hTree : treeIdx < 2 ^ 22) :
    C13Concrete.adrsXmssTree layer treeIdx < 2 ^ 256 := by
  have h224 : layer <<< 224 < 2 ^ 256 := by
    rw [Nat.shiftLeft_eq]
    calc
      layer * 2 ^ 224 < 2 ^ 32 * 2 ^ 224 :=
        Nat.mul_lt_mul_of_pos_right hLayer (by decide)
      _ = 2 ^ 256 := by norm_num [Nat.pow_add]
  have h128 : treeIdx <<< 128 < 2 ^ 256 := by
    rw [Nat.shiftLeft_eq]
    calc
      treeIdx * 2 ^ 128 < 2 ^ 22 * 2 ^ 128 :=
        Nat.mul_lt_mul_of_pos_right hTree (by decide)
      _ < 2 ^ 256 := by decide
  have h96 : 2 <<< 96 < 2 ^ 256 := by
    rw [Nat.shiftLeft_eq]
    decide
  have hinner : (treeIdx <<< 128 ||| 2 <<< 96) < 2 ^ 256 :=
    Nat.bitwise_lt_two_pow h128 h96
  simpa [C13Concrete.adrsXmssTree, Nat.lor_assoc] using
    Nat.bitwise_lt_two_pow h224 hinner

theorem c13Residual_wordNormalize_mod_2048 (n : Nat) :
    wordNormalize (n % 2048) = n % 2048 :=
  SegmentS2.wordNormalize_of_lt
    (lt_trans (Nat.mod_lt n (by decide : 0 < 2048))
      (by decide : 2048 < 2 ^ 256))

end SphincsMinusVerifiers
