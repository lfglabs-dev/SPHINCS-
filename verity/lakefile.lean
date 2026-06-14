import Lake
open Lake DSL

package SphincsVerity where
  -- maxHeartbeats: a runaway whnf/decide aborts as an elaboration error instead
  -- of ballooning a lean worker to multi-GB RSS (the proof files here are large
  -- enough that 8 parallel workers can OOM a 16 GB machine; always build with
  -- `scripts/build.sh` or `lake build -j2`).
  leanOptions := #[⟨`autoImplicit, false⟩,
                   ⟨`maxHeartbeats, (1000000 : Nat)⟩]

require verity from "../../verity-framework"

lean_lib SphincsMinusVerifierSpec where
  srcDir := "."
  roots := #[`SphincsMinusVerifierSpec.Spec, `SphincsMinusVerifierSpec.C13Concrete, `SphincsMinusVerifierSpec.C13ConcreteAxioms, `SphincsMinusVerifierSpec.C13Mirror, `SphincsMinusVerifierSpec.C13MirrorAxioms]

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
             `SphincsMinusVerifiers.SegmentForsSetup,
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
             `SphincsMinusVerifiers.C13WotsOuterInputs,
             `SphincsMinusVerifiers.C13WotsPkKeccak,
             `SphincsMinusVerifiers.C13ResidualInterface,
             `SphincsMinusVerifiers.C13ResidualLayer0StateFacts,
             `SphincsMinusVerifiers.C13ResidualLayer0Facts,
             `SphincsMinusVerifiers.C13ResidualLayer0BeforeDigitLookup,
             `SphincsMinusVerifiers.C13ResidualLayer0BeforeDigitSigOff,
             `SphincsMinusVerifiers.C13ResidualLayer0InputSeed,
             `SphincsMinusVerifiers.C13ResidualLayer0InputD,
             `SphincsMinusVerifiers.C13ResidualLayer0InputAdrs,
             `SphincsMinusVerifiers.C13ResidualLayer0InputWptr,
             `SphincsMinusVerifiers.C13ResidualLayer0InputCd,
             `SphincsMinusVerifiers.C13ResidualLayer0Inputs,
             `SphincsMinusVerifiers.C13ResidualLayer0AssemblyFields,
             `SphincsMinusVerifiers.C13ResidualLayer0Assembly,
             `SphincsMinusVerifiers.C13ResidualLayer1FirstStateFacts,
             `SphincsMinusVerifiers.C13ResidualLayer1SecondStateDef,
             `SphincsMinusVerifiers.C13ResidualLayer1StateBase,
             `SphincsMinusVerifiers.C13ResidualLayer1SeedFacts,
             `SphincsMinusVerifiers.C13ResidualLayer1StateBindings,
             `SphincsMinusVerifiers.C13ResidualLayer1ScalarFacts,
             `SphincsMinusVerifiers.C13ResidualLayer1StateFacts,
             `SphincsMinusVerifiers.C13ResidualLayer1AdrsFacts,
             `SphincsMinusVerifiers.C13ResidualLayer1CountFacts,
             `SphincsMinusVerifiers.C13ResidualLayer1MerkleBridge,
             `SphincsMinusVerifiers.C13ResidualLayer1Facts,
             `SphincsMinusVerifiers.C13ResidualLayer1FirstMerkleSite,
             `SphincsMinusVerifiers.C13ResidualLayer1StepSeedFrame,
             `SphincsMinusVerifiers.C13ResidualLayer1Inputs,
             `SphincsMinusVerifiers.C13ResidualLayer1Assembly,
             `SphincsMinusVerifiers.C13ResidualRevertedLayer0Assembly,
             `SphincsMinusVerifiers.SegmentLayer3AddressCells,
             `SphincsMinusVerifiers.SegmentLayer3,
             `SphincsMinusVerifiers.SegmentLayer3MerkleFrame,
             `SphincsMinusVerifiers.SegmentCompose,
             `SphincsMinusVerifiers.SegmentAcceptSpec,
             `SphincsMinusVerifiers.SegmentS4ForsDataObligations,
             `SphincsMinusVerifiers.SegmentRejectSpec,
             `SphincsMinusVerifiers.C13BridgePrep]
