import Lake
open Lake DSL

package SphincsC6Verity where
  leanOptions := #[⟨`autoImplicit, false⟩]

require verity from "../../verity-framework"

lean_lib SphincsC6 where
  srcDir := "SphincsC6"
  roots := #[`Types, `Hash, `WotsC, `ForsC, `Hypertree, `Contract, `Spec]

lean_lib Proofs where
  srcDir := "SphincsC6/Proofs"
  roots := #[`Correctness]

lean_lib SphincsKernel where
  srcDir := "."
  roots := #[`SphincsKernel.Model, `SphincsKernel.MerkleKernel, `SphincsKernel.Spec,
    `SphincsKernel.Examples, `SphincsKernel.Proofs.Basic, `SphincsKernel.Proofs.Correctness]

lean_lib SphincsMinusVerifierSpec where
  srcDir := "."
  roots := #[`SphincsMinusVerifierSpec.Spec, `SphincsMinusVerifierSpec.C13Concrete, `SphincsMinusVerifierSpec.C12Concrete, `SphincsMinusVerifierSpec.C13ConcreteAxioms, `SphincsMinusVerifierSpec.C13Mirror, `SphincsMinusVerifierSpec.C13MirrorAxioms]

lean_lib SphincsMinusVerifiers where
  srcDir := "."
  roots := #[`SphincsMinusVerifiers.Model, `SphincsMinusVerifiers.ProofCore,
             `SphincsMinusVerifiers.Proofs,
             `SphincsMinusVerifiers.MemoryKit, `SphincsMinusVerifiers.MemoryFrame,
             `SphincsMinusVerifiers.ClimbKit,
             `SphincsMinusVerifiers.ClimbLoop,
             `SphincsMinusVerifiers.BindingFrame,
             `SphincsMinusVerifiers.StateFrame,
             `SphincsMinusVerifiers.RootFrame,
             `SphincsMinusVerifiers.ClimbStepSpec,
             `SphincsMinusVerifiers.ClimbKeccakStep,
             `SphincsMinusVerifiers.ClimbMemFrame,
             `SphincsMinusVerifiers.ClimbMemFrameMerkle,
             `SphincsMinusVerifiers.ClimbLoopGuarded,
             `SphincsMinusVerifiers.SegmentS3,
             `SphincsMinusVerifiers.SegmentSeed,
             `SphincsMinusVerifiers.SegmentS4Fors,
             `SphincsMinusVerifiers.SegmentS4ForsMerkleFrame,
             `SphincsMinusVerifiers.SegmentS4Finalize,
             `SphincsMinusVerifiers.SegmentS2,
             `SphincsMinusVerifiers.SegmentS2R,
             `SphincsMinusVerifiers.SiblingCalldata,
             `SphincsMinusVerifiers.MkC13State,
             `SphincsMinusVerifiers.KeccakBridge,
             `SphincsMinusVerifiers.InitialNodeKeccak,
             `SphincsMinusVerifiers.CurrentNodeFrame,
             `SphincsMinusVerifiers.C13AddressArithmetic,
             `SphincsMinusVerifiers.SegmentLayer3CopyCells,
             `SphincsMinusVerifiers.C13ChainCells,
             `SphincsMinusVerifiers.C13WotsPkKeccak,
             `SphincsMinusVerifiers.SegmentLayer3AddressCells,
             `SphincsMinusVerifiers.SegmentLayer3,
             `SphincsMinusVerifiers.SegmentLayer3MerkleFrame,
             `SphincsMinusVerifiers.SegmentCompose,
             `SphincsMinusVerifiers.SegmentAcceptSpec,
             `SphincsMinusVerifiers.SegmentS4ForsDataObligations,
             `SphincsMinusVerifiers.SegmentRejectSpec,
             `SphincsMinusVerifiers.C13BridgePrep, `SphincsMinusVerifiers.C12BridgePrep,
             `SphincsMinusVerifiers.C12SegmentSeed, `SphincsMinusVerifiers.C12SegmentFors,
             `SphincsMinusVerifiers.C12SegmentForsCompress,
             `SphincsMinusVerifiers.C12SegmentWotsSetup,
             `SphincsMinusVerifiers.C12SegmentFinal]
