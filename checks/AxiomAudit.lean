import CertificationGaussian.BellPartialTranspose
import CertificationGaussian.BellTensorIdentity
import CertificationGaussian.CardinalityComplementRemainder
import CertificationGaussian.CardinalityReadoutMoments
import CertificationGaussian.ChangedSiteContraction
import CertificationGaussian.CombinedWickPermutation
import CertificationGaussian.CompleteMUBFullControl
import CertificationGaussian.CompleteMUBFullSecond
import CertificationGaussian.CompleteMUBGraphIntegrals
import CertificationGaussian.CompleteMUBGraphKappa
import CertificationGaussian.CompleteMUBReadoutControl
import CertificationGaussian.CompleteMUBRecords
import CertificationGaussian.CompleteMUBRemainder
import CertificationGaussian.CompleteMUBSpectrum
import CertificationGaussian.CompleteMUBStrictLoss
import CertificationGaussian.CompleteMUBTwirl
import CertificationGaussian.ComplexGaussianBlockWick
import CertificationGaussian.ComplexGaussianChaos
import CertificationGaussian.ComplexGaussianDecoupling
import CertificationGaussian.ComplexGaussianFourBlockWick
import CertificationGaussian.ComplexGaussianMatrixWick
import CertificationGaussian.ComplexGaussianNormalMatrix
import CertificationGaussian.ComplexGaussianNormalOrder
import CertificationGaussian.ComplexGaussianRotation
import CertificationGaussian.ComplexGaussianWick
import CertificationGaussian.ComplexGaussianWirtinger
import CertificationGaussian.Consumers.BellPartialTranspose
import CertificationGaussian.Consumers.ChangedSiteContraction
import CertificationGaussian.Consumers.CompleteMUB
import CertificationGaussian.Consumers.CompleteMUBFullControl
import CertificationGaussian.Consumers.ComplexGaussianChaos
import CertificationGaussian.Consumers.ComplexGaussianNormalWick
import CertificationGaussian.Consumers.ComplexGaussianWick
import CertificationGaussian.Consumers.CubicTail
import CertificationGaussian.Consumers.FiniteComplementContraction
import CertificationGaussian.Consumers.FiniteComplementRemainder
import CertificationGaussian.Consumers.GaussianChaos
import CertificationGaussian.Consumers.GaussianIBP
import CertificationGaussian.Consumers.GaussianMatrixMoments
import CertificationGaussian.Consumers.GramPolarCorrection
import CertificationGaussian.Consumers.HaarChangedSiteTensor
import CertificationGaussian.Consumers.HaarGraphKappa
import CertificationGaussian.Consumers.HaarMoments
import CertificationGaussian.Consumers.HaarSphere
import CertificationGaussian.Consumers.HaarSpherePacking
import CertificationGaussian.Consumers.Kernel
import CertificationGaussian.Consumers.LocalHaarTwirl
import CertificationGaussian.Consumers.Membership
import CertificationGaussian.Consumers.Model
import CertificationGaussian.Consumers.Moments
import CertificationGaussian.Consumers.NetProbability
import CertificationGaussian.Consumers.PackingNetProbability
import CertificationGaussian.Consumers.PauliLocalReadout
import CertificationGaussian.Consumers.RadialBellChoi
import CertificationGaussian.Consumers.RadialChoi
import CertificationGaussian.Consumers.RadialHighGaussian
import CertificationGaussian.Consumers.RadialHighSphere
import CertificationGaussian.Consumers.RadialHighWeights
import CertificationGaussian.Consumers.RadialLinearHigh
import CertificationGaussian.Consumers.RadialLowLabels
import CertificationGaussian.Consumers.RadialOrder
import CertificationGaussian.Consumers.RadialReadoutPolar
import CertificationGaussian.Consumers.ReadoutFullControl
import CertificationGaussian.Consumers.ReadoutGoodEvents
import CertificationGaussian.Consumers.ReadoutLinearFullControl
import CertificationGaussian.Consumers.ReadoutMomentIdentities
import CertificationGaussian.Consumers.ReadoutRadialSpectrum
import CertificationGaussian.Consumers.ReadoutRemainderAsymptotics
import CertificationGaussian.Consumers.ReadoutRemainderTail
import CertificationGaussian.Consumers.RectangularGaussian
import CertificationGaussian.Consumers.Sphere
import CertificationGaussian.Consumers.UnchangedSiteContraction
import CertificationGaussian.Consumers.UniformSphere
import CertificationGaussian.Consumers.UniformSpherePacking
import CertificationGaussian.Consumers.UnitaryGaussianChaos
import CertificationGaussian.Consumers.UnitaryNet
import CertificationGaussian.Consumers.UnitaryOrbitGram
import CertificationGaussian.Consumers.Variance
import CertificationGaussian.Coordinates
import CertificationGaussian.FiniteComplementContraction
import CertificationGaussian.FiniteComplementExpansion
import CertificationGaussian.FiniteComplementRemainder
import CertificationGaussian.FiniteWickInclusionExclusion
import CertificationGaussian.FiniteWickInclusionExclusionAssembly
import CertificationGaussian.FiniteWickInclusionExclusionBounds
import CertificationGaussian.FiniteWickInclusionExclusionCompletion
import CertificationGaussian.FiniteWickInclusionExclusionExpansion
import CertificationGaussian.FiniteWickInclusionExclusionFiber
import CertificationGaussian.FiniteWickInclusionExclusionFourBlock
import CertificationGaussian.FourRecordTensorAverage
import CertificationGaussian.FourVertexOverlap
import CertificationGaussian.GaussianBlocks
import CertificationGaussian.GaussianChaosExpectation
import CertificationGaussian.GaussianChaosFlattenings
import CertificationGaussian.GaussianDensity
import CertificationGaussian.GaussianMatrixExpectation
import CertificationGaussian.GaussianMatrixOperatorMoments
import CertificationGaussian.GaussianMatrixPolynomial
import CertificationGaussian.GaussianMatrixTraceDerivative
import CertificationGaussian.GaussianMatrixTraceMoments
import CertificationGaussian.GaussianPolynomialIBP
import CertificationGaussian.GaussianRadialSixth
import CertificationGaussian.GaussianRecordFubini
import CertificationGaussian.GaussianRotation
import CertificationGaussian.GaussianTail
import CertificationGaussian.GaussianVariance
import CertificationGaussian.GaussianWick4
import CertificationGaussian.GramPolarCorrection
import CertificationGaussian.HaarBasisRecords
import CertificationGaussian.HaarChangedSiteTensor
import CertificationGaussian.HaarGraphKappa
import CertificationGaussian.HaarOrbit
import CertificationGaussian.HaarOverlapSixth
import CertificationGaussian.HammingKernel
import CertificationGaussian.HermiteIntegral
import CertificationGaussian.HermitianTraceBound
import CertificationGaussian.HermitianTraceSandwich
import CertificationGaussian.IncidentHolderContractions
import CertificationGaussian.IncidentOverlapHolder
import CertificationGaussian.IndependentQuadratic
import CertificationGaussian.KernelAsymptotics
import CertificationGaussian.KernelOperator
import CertificationGaussian.KernelTrace
import CertificationGaussian.LocalHaarTwirl
import CertificationGaussian.MatrixHermitianDilation
import CertificationGaussian.MatrixKroneckerNorm
import CertificationGaussian.Model
import CertificationGaussian.Moments
import CertificationGaussian.NetAsymptotics
import CertificationGaussian.OrbitLowHighDecomposition
import CertificationGaussian.PackingNetAsymptotics
import CertificationGaussian.PauliBasisRecords
import CertificationGaussian.PauliChangedSiteTensor
import CertificationGaussian.PauliGraphIntegrals
import CertificationGaussian.PauliGraphKappa
import CertificationGaussian.PauliTwirl
import CertificationGaussian.PolynomialMembership
import CertificationGaussian.PositiveTensorTrace
import CertificationGaussian.ProductReadoutContraction
import CertificationGaussian.QuarticRadiusSphereTransfer
import CertificationGaussian.Radial
import CertificationGaussian.RadialBellChoi
import CertificationGaussian.RadialBellWeights
import CertificationGaussian.RadialBinomialEntropy
import CertificationGaussian.RadialChoiLocal
import CertificationGaussian.RadialChoiTensor
import CertificationGaussian.RadialCoefficientBounds
import CertificationGaussian.RadialCoefficientMass
import CertificationGaussian.RadialHighChoi
import CertificationGaussian.RadialHighGaussian
import CertificationGaussian.RadialHighSphere
import CertificationGaussian.RadialHighTail
import CertificationGaussian.RadialHighWeights
import CertificationGaussian.RadialLinearCardinality
import CertificationGaussian.RadialLinearEntropy
import CertificationGaussian.RadialLinearHighChoi
import CertificationGaussian.RadialLinearHighGaussian
import CertificationGaussian.RadialLinearHighSphere
import CertificationGaussian.RadialLinearHighTail
import CertificationGaussian.RadialLinearHighWeights
import CertificationGaussian.RadialLinearLowOrbit
import CertificationGaussian.RadialLinearPolarApproximation
import CertificationGaussian.RadialLinearReadoutPolar
import CertificationGaussian.RadialLowAsymptotics
import CertificationGaussian.RadialLowCardinality
import CertificationGaussian.RadialLowOrbit
import CertificationGaussian.RadialPolarApproximation
import CertificationGaussian.RadialProjection
import CertificationGaussian.RadialReadoutPolar
import CertificationGaussian.RankOneWickContraction
import CertificationGaussian.ReadoutChoiAction
import CertificationGaussian.ReadoutChoiLocal
import CertificationGaussian.ReadoutChoiTensor
import CertificationGaussian.ReadoutFullControl
import CertificationGaussian.ReadoutFullSecondControl
import CertificationGaussian.ReadoutFullSecondTail
import CertificationGaussian.ReadoutGoodEvents
import CertificationGaussian.ReadoutKernelAlgebra
import CertificationGaussian.ReadoutLinearFullControl
import CertificationGaussian.ReadoutLinearFullSecondControl
import CertificationGaussian.ReadoutLinearFullSecondTail
import CertificationGaussian.ReadoutMomentContinuity
import CertificationGaussian.ReadoutMomentError
import CertificationGaussian.ReadoutMomentOperators
import CertificationGaussian.ReadoutNormalization
import CertificationGaussian.ReadoutPolarNorm
import CertificationGaussian.ReadoutRadialControl
import CertificationGaussian.ReadoutRadialSpectrum
import CertificationGaussian.ReadoutRemainderAsymptotics
import CertificationGaussian.ReadoutRemainderFourthMoment
import CertificationGaussian.ReadoutRemainderModel
import CertificationGaussian.ReadoutRemainderPolynomial
import CertificationGaussian.ReadoutRemainderTail
import CertificationGaussian.RectangularGaussianExpectation
import CertificationGaussian.ScalarMoments
import CertificationGaussian.SphereComplexMoments
import CertificationGaussian.SphereHomogeneous
import CertificationGaussian.SpherePolar
import CertificationGaussian.SphereQuadraticMoments
import CertificationGaussian.SphereRealMoments
import CertificationGaussian.SphereScore
import CertificationGaussian.SphereScoreL1
import CertificationGaussian.SphereTransfer
import CertificationGaussian.SphereTransport
import CertificationGaussian.StandardGaussian
import CertificationGaussian.TailAsymptotics
import CertificationGaussian.TensorOperatorNorm
import CertificationGaussian.TensorReadoutFactorization
import CertificationGaussian.TensorUnitaryNet
import CertificationGaussian.TensorUnitaryPackingNet
import CertificationGaussian.UnchangedSiteContraction
import CertificationGaussian.UnitaryBellFlattenings
import CertificationGaussian.UnitaryChaosCoefficients
import CertificationGaussian.UnitaryFrobeniusPacking
import CertificationGaussian.UnitaryGaussianChaos
import CertificationGaussian.UnitaryNet
import CertificationGaussian.UnitaryOrbitGram
import CertificationGaussian.UnitarySphereConjugation
import CertificationGaussian.WickAlgebra
import CertificationGaussian.WickFourVertexGraph
import CertificationGaussian.WickOrthogonality
import GaussianHilbert.HermitePolynomials
import GaussianHilbert.HypercontractivityFromBE
import GaussianHilbert.OUEigenfunctions
import GaussianHilbert.PolynomialChaosConcentration
import GaussianHilbert.PolynomialDensity
import GaussianHilbert.WienerChaos
import LocalCertification
import LocalCertification.Asymptotic.BlaschkeBoundary
import LocalCertification.Asymptotic.BlaschkeCoefficients
import LocalCertification.Asymptotic.BlaschkeEuler
import LocalCertification.Asymptotic.BlaschkeTermwiseDerivatives
import LocalCertification.Asymptotic.BlaschkeUniformSeries
import LocalCertification.Asymptotic.BoundaryAmplitude
import LocalCertification.Asymptotic.CoefficientL1
import LocalCertification.Asymptotic.CoefficientUpper
import LocalCertification.Asymptotic.CriticalDegree
import LocalCertification.Asymptotic.EulerMomentAsymptotics
import LocalCertification.Asymptotic.EulerMomentDual
import LocalCertification.Asymptotic.EulerMoments
import LocalCertification.Asymptotic.InfiniteDual
import LocalCertification.Asymptotic.InversionBounds
import LocalCertification.Asymptotic.LogarithmicInversion
import LocalCertification.Asymptotic.OscillatoryCandidate
import LocalCertification.Asymptotic.OscillatoryIntegral
import LocalCertification.Asymptotic.OscillatoryRegularization
import LocalCertification.Asymptotic.OscillatoryVariation
import LocalCertification.Asymptotic.PhaseComplex
import LocalCertification.Asymptotic.PhaseScalar
import LocalCertification.Asymptotic.PoissonBoundary
import LocalCertification.Asymptotic.RationalNumerator
import LocalCertification.Asymptotic.RationalTail
import LocalCertification.Asymptotic.RootLimit
import LocalCertification.Asymptotic.RootMoments
import LocalCertification.Asymptotic.SharpRate
import LocalCertification.Asymptotic.SharpTheorem
import LocalCertification.Asymptotic.SharpUpper
import LocalCertification.Asymptotic.UpperCandidate
import LocalCertification.Asymptotic.WeightKernel
import LocalCertification.Asymptotic.WeightedSquares
import LocalCertification.Certificates.CandidateDecision
import LocalCertification.Certificates.CanonicalCandidate
import LocalCertification.Certificates.CanonicalCertificate
import LocalCertification.Certificates.CanonicalCertificateConsumers
import LocalCertification.Certificates.CanonicalRawCheck
import LocalCertification.Certificates.Consumers
import LocalCertification.Certificates.Examples.Degree10
import LocalCertification.Certificates.Examples.Degree2
import LocalCertification.Certificates.Examples.Degree3
import LocalCertification.Certificates.Examples.Degree4
import LocalCertification.Certificates.Examples.Degree5
import LocalCertification.Certificates.Examples.Degree6
import LocalCertification.Certificates.Examples.Degree7
import LocalCertification.Certificates.Examples.Degree8
import LocalCertification.Certificates.Examples.Degree9
import LocalCertification.Certificates.ExecutableTail
import LocalCertification.Certificates.Existence
import LocalCertification.Certificates.FairSearch
import LocalCertification.Certificates.PolynomialTail
import LocalCertification.Certificates.RationalDual
import LocalCertification.Certificates.RealLowDegree
import LocalCertification.Certificates.RealLowDegreeConsumers
import LocalCertification.Certificates.SearchConsumers
import LocalCertification.Certificates.Soundness
import LocalCertification.Certificates.StagedSearch
import LocalCertification.Certificates.StagedSearchConsumers
import LocalCertification.Certificates.TableValues
import LocalCertification.Certificates.TailTermination
import LocalCertification.Comparisons.BoundedIIDTail
import LocalCertification.Comparisons.GlobalProjectorBorn
import LocalCertification.Comparisons.GlobalProjectorTest
import LocalCertification.Extremal.Alternation
import LocalCertification.Extremal.BinomialMoments
import LocalCertification.Extremal.CompactConvexHull
import LocalCertification.Extremal.ContactHull
import LocalCertification.Extremal.DegreeHierarchy
import LocalCertification.Extremal.DegreeZero
import LocalCertification.Extremal.DualMasses
import LocalCertification.Extremal.DualNormalization
import LocalCertification.Extremal.ElementaryDecay
import LocalCertification.Extremal.Envelope
import LocalCertification.Extremal.EnvelopeUniqueness
import LocalCertification.Extremal.EvaluationMatrix
import LocalCertification.Extremal.ExactSupport
import LocalCertification.Extremal.Extremizer
import LocalCertification.Extremal.FiniteDual
import LocalCertification.Extremal.FirstResidual
import LocalCertification.Extremal.Gamma
import LocalCertification.Extremal.GeometricSeriesDecay
import LocalCertification.Extremal.GeometricSeriesDerivatives
import LocalCertification.Extremal.InfinityMatrix
import LocalCertification.Extremal.InfinitySupport
import LocalCertification.Extremal.IntegerDual
import LocalCertification.Extremal.Interpolation
import LocalCertification.Extremal.LagrangeSigns
import LocalCertification.Extremal.OnePointModel
import LocalCertification.Extremal.OrderedDual
import LocalCertification.Extremal.OrderedMatrix
import LocalCertification.Extremal.RationalExtremizer
import LocalCertification.Extremal.ResidualCancellation
import LocalCertification.Extremal.ResidualMass
import LocalCertification.Extremal.SupportCompression
import LocalCertification.Extremal.Uniqueness
import LocalCertification.Extremal.ZeroCount
import LocalCertification.Information.BinaryKLMonotonicity
import LocalCertification.Information.BinarySupport
import LocalCertification.Information.ConfidenceRange
import LocalCertification.Information.ContinuousConfidenceRatio
import LocalCertification.Information.ExponentialSupport
import LocalCertification.Information.FiniteAtomLogIntegrability
import LocalCertification.Information.FiniteAtoms
import LocalCertification.Information.FiniteDomination
import LocalCertification.Information.FiniteHistoryKL
import LocalCertification.Information.FiniteKL
import LocalCertification.Information.FinitePrefixProductDensity
import LocalCertification.Information.JointFiniteKL
import LocalCertification.Information.ProductDensityChainRule
import LocalCertification.Information.SeedCountingReference
import LocalCertification.Information.SingularFiniteKL
import LocalCertification.Information.StoppedKernel
import LocalCertification.Information.TestingLog
import LocalCertification.LegacyPaper
import LocalCertification.Probability.BinaryKLLowerSemicontinuity
import LocalCertification.Probability.BlockAmplification
import LocalCertification.Protocol.BehaviorTree
import LocalCertification.Protocol.BlockRecordGrouping
import LocalCertification.Protocol.BornExecution
import LocalCertification.Protocol.BornTrajectory
import LocalCertification.Protocol.BudgetHierarchy
import LocalCertification.Protocol.BudgetLower
import LocalCertification.Protocol.Budgets
import LocalCertification.Protocol.CalibratedTesting
import LocalCertification.Protocol.CanonicalProtocol
import LocalCertification.Protocol.CardinalityAchievability
import LocalCertification.Protocol.CompleteMUBAchievability
import LocalCertification.Protocol.CompleteMUBAchievabilityConsumers
import LocalCertification.Protocol.CompleteRecordLaw
import LocalCertification.Protocol.ConditionalBorn
import LocalCertification.Protocol.ConfidenceConstantLower
import LocalCertification.Protocol.ConfidenceExponentialLower
import LocalCertification.Protocol.ConfidenceHierarchy
import LocalCertification.Protocol.ConsistentHistory
import LocalCertification.Protocol.ConstantLowerBound
import LocalCertification.Protocol.CoordinateResampling
import LocalCertification.Protocol.Executor
import LocalCertification.Protocol.ExponentialHierarchy
import LocalCertification.Protocol.ExponentialLowerBound
import LocalCertification.Protocol.ExponentialUpperBound
import LocalCertification.Protocol.FixedBlockBudgets
import LocalCertification.Protocol.FixedBlockConfidence
import LocalCertification.Protocol.FixedBlockConsequences
import LocalCertification.Protocol.FixedBlockConsumers
import LocalCertification.Protocol.FixedBlockHierarchy
import LocalCertification.Protocol.FixedBlockLogCriterion
import LocalCertification.Protocol.FixedBlockProtocol
import LocalCertification.Protocol.FixedBornProtocol
import LocalCertification.Protocol.FixedErrorHierarchy
import LocalCertification.Protocol.FixedHorizon
import LocalCertification.Protocol.FixedSamplingLaw
import LocalCertification.Protocol.FixedScoreAchievability
import LocalCertification.Protocol.FixedScoreAchievabilityCanonical
import LocalCertification.Protocol.FixedScoreAchievabilityConsumers
import LocalCertification.Protocol.FixedScoreAchievabilityInstances
import LocalCertification.Protocol.FixedWordPrefix
import LocalCertification.Protocol.FullRecord
import LocalCertification.Protocol.HaarAchievability
import LocalCertification.Protocol.ImmediateStop
import LocalCertification.Protocol.IndependentRecords
import LocalCertification.Protocol.LegalFiltration
import LocalCertification.Protocol.LegalPaths
import LocalCertification.Protocol.LegalStopping
import LocalCertification.Protocol.LinearAchievability
import LocalCertification.Protocol.LogicalMeasurability
import LocalCertification.Protocol.LogicalRun
import LocalCertification.Protocol.MajorityBornProtocol
import LocalCertification.Protocol.PauliAchievability
import LocalCertification.Protocol.PowerLowerBound
import LocalCertification.Protocol.ProductDensityCalibratedTesting
import LocalCertification.Protocol.ProductDensityConfidenceEvent
import LocalCertification.Protocol.ProductDensityTerminalInformation
import LocalCertification.Protocol.ProductDensityTestingScale
import LocalCertification.Protocol.PublicRecordTransition
import LocalCertification.Protocol.QubitQuartic
import LocalCertification.Protocol.RadialAchievability
import LocalCertification.Protocol.RawLawExt
import LocalCertification.Protocol.RuleFactorization
import LocalCertification.Protocol.Rules
import LocalCertification.Protocol.SameConfidenceEvent
import LocalCertification.Protocol.ScoreBudgetUpper
import LocalCertification.Protocol.ScoreGap
import LocalCertification.Protocol.SeedTransport
import LocalCertification.Protocol.SphereHierarchy
import LocalCertification.Protocol.StoppingTime
import LocalCertification.Protocol.TerminalEvents
import LocalCertification.Protocol.TerminalInformation
import LocalCertification.Protocol.TestingScaleLower
import LocalCertification.Protocol.Trajectory
import LocalCertification.Protocol.TrajectoryCost
import LocalCertification.Protocol.TrajectoryEncoding
import LocalCertification.Protocol.TrajectoryExecution
import LocalCertification.Protocol.TreeBornPrefix
import LocalCertification.Protocol.TreeExecution
import LocalCertification.Protocol.TreeFullRecord
import LocalCertification.Protocol.TreeLaw
import LocalCertification.Protocol.UniformConfidenceHierarchy
import LocalCertification.Protocol.UniformFixedBlockConfidence
import LocalCertification.Protocol.UpperBound
import LocalCertification.Quantum.BornKernel
import LocalCertification.Quantum.BornMeasure
import LocalCertification.Quantum.Boundary
import LocalCertification.Quantum.CalibratedDistance
import LocalCertification.Quantum.CalibratedInformation
import LocalCertification.Quantum.Calibration
import LocalCertification.Quantum.CalibrationBase
import LocalCertification.Quantum.CalibrationEvent
import LocalCertification.Quantum.CalibrationFloor
import LocalCertification.Quantum.CommonHaarEvent
import LocalCertification.Quantum.CompactTargetTransfer
import LocalCertification.Quantum.CompleteBornRecord
import LocalCertification.Quantum.CompleteMUBReadout
import LocalCertification.Quantum.CompleteReadoutLoewner
import LocalCertification.Quantum.CompleteReadoutLoewnerConsumers
import LocalCertification.Quantum.ConstantHardPair
import LocalCertification.Quantum.DualKernelOrder
import LocalCertification.Quantum.DualReadout
import LocalCertification.Quantum.DualStates
import LocalCertification.Quantum.ExponentialCalibrationScale
import LocalCertification.Quantum.ExponentialHardStates
import LocalCertification.Quantum.FiniteBornInformation
import LocalCertification.Quantum.FixedBlockIndex
import LocalCertification.Quantum.FixedBlockMeasurement
import LocalCertification.Quantum.GaussianMoments
import LocalCertification.Quantum.HaarMeasurement
import LocalCertification.Quantum.HaarProductBasis
import LocalCertification.Quantum.HaarShellControl
import LocalCertification.Quantum.HaarWeylOverlap
import LocalCertification.Quantum.HardStateInformation
import LocalCertification.Quantum.IsometryEnvelopes
import LocalCertification.Quantum.LinearWeylOrbit
import LocalCertification.Quantum.PauliMeasurement
import LocalCertification.Quantum.PauliProductMeasurement
import LocalCertification.Quantum.ProductMeasurement
import LocalCertification.Quantum.QubitPhaseConsumers
import LocalCertification.Quantum.QubitWeylPhase
import LocalCertification.Quantum.RadialPolynomial
import LocalCertification.Quantum.RadialWeylOrbit
import LocalCertification.Quantum.RadialWeylScore
import LocalCertification.Quantum.ReadoutScoreMoments
import LocalCertification.Quantum.ShellReadout
import LocalCertification.Quantum.ShellReadoutExpansion
import LocalCertification.Quantum.ShellReadoutLocal
import LocalCertification.Quantum.ShellReadoutNormalization
import LocalCertification.Quantum.SpectralScoreBounds
import LocalCertification.Quantum.StateMixture
import LocalCertification.Quantum.StateTraceBounds
import LocalCertification.Quantum.TensorMatrix
import LocalCertification.Quantum.UniformProductBasis
import LocalCertification.Quantum.Weyl
import LocalCertification.Quantum.WeylFin
import LocalCertification.Quantum.WeylGaussianChaos
import LocalCertification.Quantum.WeylOrbit
import LocalCertification.Quantum.WeylOrbitProjection
import LocalCertification.Quantum.WeylShellState
import LocalCertification.Quantum.WeylSupport
import LocalCertification.Quantum.WeylTensor
import MarkovSemigroups.Abstract.DirichletForm
import MarkovSemigroups.Abstract.GrossODE
import MarkovSemigroups.Abstract.Hypercontractivity
import MarkovSemigroups.Diffusion.CarreDuChamp
import MarkovSemigroups.Diffusion.StroockVaropoulos
import MarkovSemigroups.General.OUEntropyDecomposition
import MarkovSemigroups.Instances.WorkInProgress.Euclidean
import MarkovSemigroups.Instances.WorkInProgress.EuclideanEntropyDecay
import MarkovSemigroups.Instances.WorkInProgress.EuclideanFin
import MarkovSemigroups.Instances.WorkInProgress.EuclideanFinBE
import MarkovSemigroups.Instances.WorkInProgress.EuclideanFinLp
import MarkovSemigroups.Instances.WorkInProgress.EuclideanGenerator
import MarkovSemigroups.Instances.WorkInProgress.EuclideanGeneratorLimit
import MarkovSemigroups.Instances.WorkInProgress.EuclideanGeneratorLp
import MarkovSemigroups.Instances.WorkInProgress.EuclideanHermite
import MarkovSemigroups.Instances.WorkInProgress.EuclideanHypercontractive
import MarkovSemigroups.Instances.WorkInProgress.EuclideanStein
import Lean

open Lean Elab Command
set_option maxHeartbeats 0
set_option maxRecDepth 100000
run_elab do
  let env ← getEnv
  let names : List Name := [
`LocalCertification.Protocol.fixedBlock_same_event_continuous_confidence_hierarchy,
`LocalCertification.Protocol.fixedBlock_same_event_continuous_confidence_criterion,
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "Fin") "consEquiv") "eq_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "blaschkeCoeff_hasSum_positive_polynomial"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "blaschkeCoeff_hasSum_root_moment"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "blaschkeCoeff_hasSum_root_moment") "_simp_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "blaschkeCoeff_hasSum_root_moment") "_simp_1_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "blaschkeCoeff_hasSum_root_moment") "_simp_1_3"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "blaschkeCoeff_hasSum_root_polynomial"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "blaschkeDual_hasSum_abs"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "blaschkeDual_hasSum_polynomial"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "blaschkeDual_hasSum_polynomial") "_simp_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "blaschkeDual_hasSum_polynomial") "_simp_1_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "blaschkeDual_hasSum_polynomial") "_simp_1_3"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "blaschkeDual_hasSum_polynomial") "_simp_1_4"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "blaschkeDual_hasSum_polynomial") "_simp_1_5"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "blaschkeDual_hasSum_polynomial") "_simp_1_6"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "blaschkeDual_hasSum_polynomial") "_simp_1_7"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "blaschkeDual_hasSum_reproduction"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "blaschkeDual_reproduces_node"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "blaschkeDual_reproduces_node") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "blaschkeDual_totalVariation"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "blaschke_deriv_root_zero"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "blaschke_eulerExpansion_hasSum"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "blaschke_euler_hasSum"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "criticalDegree_explicit_eventually"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "criticalDegree_implicit_bound"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "criticalDegree_implicit_bound") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "criticalDegree_implicit_div_tendsto_zero"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "criticalDegree_implicit_div_tendsto_zero") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "criticalDegree_implicit_eventually"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "criticalDegree_log_bracket"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "criticalDegree_log_bracket") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "criticalDegree_log_bracket") "_proof_1_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "criticalDegree_log_bracket") "_proof_1_3"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "criticalDegree_log_bracket") "_simp_1_10"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "criticalDegree_log_bracket") "_simp_1_4"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "criticalDegree_log_bracket") "_simp_1_5"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "criticalDegree_log_bracket") "_simp_1_6"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "criticalDegree_log_bracket") "_simp_1_7"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "criticalDegree_log_bracket") "_simp_1_8"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "criticalDegree_log_bracket") "_simp_1_9"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "criticalDegree_logarithmic_inversion"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "criticalDegree_logb_inversion"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "degreeLogModel_step_bound"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "degreeLogModel_step_bound") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "euler"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "euler") "_f"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "euler") "_sunfold"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "euler") "_unsafe_rec"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "euler") "eq_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "euler") "eq_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "euler") "eq_def"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "euler") "match_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "eulerExpansion"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "eulerExpansion") "eq_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "eulerExpansion_eq_euler"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "eulerExpansion_monomial"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "eulerExpansion_monomial") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "eulerExpansion_root_zero"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "eulerExpansion_root_zero") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "eulerExpansion_succ"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "euler_root_zero"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "extremalValue_le_blaschke_totalVariation"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "gamma_blaschke_coefficient_lower"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "gamma_blaschke_coefficient_lower") "_simp_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "gamma_blaschke_lower"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "gamma_blaschke_lower") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "gamma_log_bounds"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "gamma_log_bounds") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "gamma_rate_lower"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "gamma_sharp_rate"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "log_gap_sub_log_degree_tendsto_zero"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "log_gap_sub_log_degree_tendsto_zero") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "logarithmicGap_div_criticalDegree_tendsto_one"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "logarithmicGap_div_criticalDegree_tendsto_one") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "logarithmicGap_div_criticalDegree_tendsto_one") "_simp_1_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "logarithmicGap_div_criticalDegree_tendsto_one") "_simp_1_3"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "logarithmicGap_div_criticalDegree_tendsto_one") "_simp_1_4"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "logarithmicGap_div_criticalDegree_tendsto_one") "_simp_1_5"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "logarithmicGap_div_criticalDegree_tendsto_one") "_simp_1_6"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "logarithmicGap_div_criticalDegree_tendsto_one") "_simp_1_7"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "logarithmicGap_div_criticalDegree_tendsto_one") "_simp_1_8"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "logarithmicGap_eq_logb"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "logarithmicGap_pos"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "sharp_order"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "EulerMoments") "sharp_order_and_inversion"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "amplitudeSupremum"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "amplitudeVariation"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "blaschke"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "blaschkeCoeff"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "blaschkeCoeff_hasSum_positive_polynomial"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "blaschkeCoeff_hasSum_root_moment"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "blaschkeCoeff_hasSum_sq"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "blaschkeCoeff_hasSum_weighted_sq"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "blaschkeCoeff_moment_succ"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "blaschkeCoeff_summable_norm"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "blaschkeCoeff_tsum_abs_le_q"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "blaschkeCoeff_weighted_radius_summable"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "blaschkeCoeff_zero_index"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "blaschkeCoefficientConstant"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "blaschkeDualInfinity"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "blaschkeDualWeight"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "blaschkeDual_hasSum_mass"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "blaschkeDual_hasSum_reproduction"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "blaschkeDual_reproduces_node"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "blaschkeDual_totalVariation"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "blaschke_derivative_series_uniform"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "blaschke_iteratedDeriv_eq_tsum"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "blaschke_norm_of_norm_eq_one"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "boundaryAmplitude_control"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "boundaryAmplitude_norm"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "complexRegularizedReciprocal"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "criticalDegree"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "criticalDegree_at_critical_value"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "criticalDegree_bracket"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "criticalDegree_explicit_eventually"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "criticalDegree_implicit_bound"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "criticalDegree_le_iff"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "criticalDegree_log_bracket"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "criticalDegree_logb_inversion"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "criticalDegree_spec"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "criticalDegree_tendsto_atTop"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "envelopeRatio_le_twice_absolute_bound"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "exists_degree_for_positive_gap"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "extremalValue_le_blaschke_totalVariation"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "gamma_blaschke_coefficient_lower"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "gamma_blaschke_lower"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "gamma_log_div_degree_tendsto"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "gamma_root_limit"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "gamma_sharp_rate"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "gamma_sharp_upper"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "gamma_tendsto_zero"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "integral_abs_arctan_weight_le"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "integral_arctan_weight"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "log_gap_sub_log_degree_tendsto_zero"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "logarithmicGap_div_criticalDegree_tendsto_one"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "lowerRateConstant"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "lt_criticalDegree_iff"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "numeratorTailPolynomial_eval_zero"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "numerator_partialFractions"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "numerator_tendsto_atTop"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "oscillatory_integral_bound"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "oscillatory_integral_regularized"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "oscillatory_regularization_bound"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "oscillatory_scale_bound"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "poissonBoundary_integral_norm_sq"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "qudit_base_gt_one"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "qudit_critical_boundary"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "qudit_logarithmic_inversion"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "qudit_root_limit"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "qudit_sharp_order"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "rational_tail_exists"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "realPhase"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "realPhase_contDiff"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "realPhase_deriv_half_monotone"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "realPhase_lifts_blaschke"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "realPhase_second_deriv"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "reciprocal_blaschke_all_derivatives"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "regularization_identity"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "regularizedReciprocalDerivative"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "sharp_order_and_inversion"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "upperCandidate_rational_identity"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "upperCoefficient_bound"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "upperCoefficient_eq_oscillatory_integral"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "upperNormalizedPolynomial"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "upperNormalizedPolynomial_admissible"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "upperNormalizedPolynomial_weighted"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "upperNumerator"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "upperNumerator_tendsto_atTop"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "upperOscillationConstant"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "upperOscillationConstant_pos"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "upperPolynomial_eval_zero"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "upperRateConstant"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Asymptotic") "weightKernel_tsum_le_scaled"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CertificateData"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Consumers") "degreeOneCertificate"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Consumers") "degree_one_exact_value"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Consumers") "degree_zero_exact_certificate"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Consumers") "proposition_five_six"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Consumers") "staged_degree_one_bound"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Consumers") "staged_degree_one_bound") "_simp_1_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Consumers") "staged_degree_one_bound") "_simp_1_3"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Consumers") "staged_degree_one_value"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Consumers") "staged_degree_ten_covered"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Consumers") "staged_degree_ten_covered") "_simp_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Consumers") "staged_degree_two_bound"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Consumers") "staged_degree_two_bound") "_simp_1_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Consumers") "staged_degree_two_bound") "_simp_1_3"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Consumers") "staged_degree_two_raw_passes"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Consumers") "staged_degree_two_raw_passes") "_simp_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Consumers") "staged_degree_zero_bound"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Consumers") "staged_degree_zero_bound") "_simp_1_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Consumers") "staged_degree_zero_bound") "_simp_1_3"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Consumers") "staged_degree_zero_value"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Consumers") "canonical_degree_one_passes"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Consumers") "canonical_degree_one_passes") "_simp_1_3"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Consumers") "canonical_degree_one_value"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Consumers") "canonical_degree_zero_passes"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Consumers") "canonical_degree_zero_passes") "_simp_1_3"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Consumers") "canonical_degree_zero_value"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Examples") "Degree10") "certificate_passes"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Examples") "Degree10") "data"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Examples") "Degree10") "exact_value"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Examples") "Degree2") "certificate_passes"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Examples") "Degree2") "data"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Examples") "Degree2") "exact_value"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Examples") "Degree2") "prefix_passes"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Examples") "Degree2") "tail_passes"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Examples") "Degree3") "certificate_passes"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Examples") "Degree3") "data"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Examples") "Degree3") "exact_value"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Examples") "Degree4") "certificate_passes"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Examples") "Degree4") "data"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Examples") "Degree4") "exact_value"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Examples") "Degree4") "prefix_passes"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Examples") "Degree5") "certificate_passes"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Examples") "Degree5") "data"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Examples") "Degree5") "exact_value"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Examples") "Degree6") "certificate_passes"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Examples") "Degree6") "data"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Examples") "Degree6") "exact_value"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Examples") "Degree7") "certificate_passes"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Examples") "Degree7") "data"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Examples") "Degree7") "exact_value"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Examples") "Degree8") "certificate_passes"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Examples") "Degree8") "data"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Examples") "Degree8") "exact_value"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Examples") "Degree9") "certificate_passes"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Examples") "Degree9") "data"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Examples") "Degree9") "exact_value"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Examples") "critical_values_zero_through_ten"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Examples") "quarticPolynomial"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Examples") "quartic_difference_tail_array"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Examples") "quartic_normalized_numerator"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Examples") "quartic_positive_tail_array"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "Examples") "quartic_unique_optimizer"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate") "Q"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate") "Q") "eq_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate") "Q_degree"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate") "Q_positive_multiple"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate") "R"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate") "R_zero"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate") "R_zero_pos"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate") "optimality"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate") "optimality") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate") "array_optimality"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate") "_sizeOf_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate") "_sizeOf_inst"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate") "beta"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate") "beta") "eq_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate") "beta_gt_one"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate") "beta_gt_one") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate") "canonicalArrayCheck"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate") "canonicalArrayCheck_general"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate") "canonicalArrayCheck_iff"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate") "canonicalArrayCheck_iff") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate") "canonicalArrayCheck_iff") "_proof_1_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate") "canonicalCheck"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate") "canonicalCheck_general"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate") "canonicalCheck_general") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate") "canonical_integer_tail"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate") "canonical_real_ray"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate") "casesOn"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate") "contact"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate") "ctorIdx"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate") "data"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate") "data") "eq_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate") "degree"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate") "infinity"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate") "mass"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate") "mk"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate") "mk") "_flat_ctor"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate") "mk") "congr_simp"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate") "mk") "inj"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate") "mk") "injEq"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate") "mk") "noConfusion"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate") "mk") "sizeOf_spec"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate") "moments"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate") "noConfusion"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate") "noConfusionType"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate") "ordered"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate") "p"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate") "p") "eq_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate") "p_zero"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate") "rec"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate") "recOn"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate") "signs"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate") "tail_iff"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate") "x"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "CanonicalCandidate") "ν"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "arrayPrefixCheck"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "arrayTailCheck"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "arrayTailCheck_complete"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "arrayTailCheck_sound"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "certificateAt_exists"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "certificateAt_fair"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "certificateCheck"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "decodeCertificate"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "degreeOneRealCandidate"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "degreeOneRealCandidate_eval"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "degreeOneRealCandidate_feasible"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "degreeOneRealDual_reproduces"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "degreeTwoRealCandidate"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "degreeTwoRealCandidate_eval"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "degreeTwoRealCandidate_feasible"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "degreeTwoRealDual_reproduces"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "eval_nonneg_of_coefficients"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "exists_tailCheck_after"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "extremalValue_one_real"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "extremalValue_two_real"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "feasible_oriented_leading_positive"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "finite_prefix_tail_sound"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "finite_rational_certificate_exists"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "finite_rational_certificate_optimal"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "finite_rational_reproduction"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "gamma_one_real"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "gamma_two_real"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "hasseDeriv_leading_positive"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "mem_stagedArrays"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "mem_stagedArrays") "_simp_1_4"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "mem_stagedArrays") "_simp_1_5"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "mem_stagedData"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "mem_stagedData") "_proof_1_5"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "mem_stagedData") "_proof_1_6"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "mem_stagedData") "_proof_1_7"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "mem_stagedData") "_simp_1_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "mem_stagedData") "_simp_1_3"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "mem_stagedData") "_simp_1_4"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "mem_stagedNodes"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "mem_stagedNodes") "_simp_1_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "mem_stagedNodes") "_simp_1_3"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "mem_stagedRationals"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "mem_stagedRationals") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "mem_stagedRationals") "_proof_1_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "mem_stagedRationals") "_proof_1_7"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "mem_stagedRationals") "_proof_1_8"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "mem_stagedRationals") "_simp_1_4"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "mem_stagedRationals") "_simp_1_5"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "mem_stagedRationals") "_simp_1_6"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "rationalNodeMonomial"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "rational_dual_finite_checks"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "rational_dual_weights"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "rational_normalization_of_attainment"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "real_weighted_tail"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "searchCertificateIndex"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "searchCertificateIndex_le"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "searchCertificate_correct"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "searchCertificate_passes"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "seedCertificate") "eq_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "shiftArrayCoeff"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "shifted_coefficients_eventually_nonnegative"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "stagedArrays"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "stagedArrays") "_f"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "stagedArrays") "_sunfold"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "stagedArrays") "_unsafe_rec"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "stagedArrays") "eq_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "stagedArrays") "eq_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "stagedArrays") "eq_def"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "stagedArrays") "match_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "stagedData"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "stagedData") "eq_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "stagedDataBound"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "stagedDataBound") "eq_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "stagedData_canonical"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "stagedData_exhaustive"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "stagedData_finite"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "stagedData_zero"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "stagedFind"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "stagedFind_exists"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "stagedFind_first"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "stagedFind_success_iff"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "stagedGamma"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "stagedNodes"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "stagedNodes") "eq_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "stagedOutput_correct"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "stagedPolynomial"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "stagedPolynomial") "eq_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "stagedPolynomial_eq"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "stagedRationals"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "stagedRationals") "eq_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "stagedRationals_bounded"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "stagedRationals_bounded") "_proof_1_5"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "stagedRationals_bounded") "_proof_1_6"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "stagedRationals_bounded") "_proof_1_7"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "stagedRationals_bounded") "_proof_1_8"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "stagedRationals_bounded") "_simp_1_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "stagedRationals_bounded") "_simp_1_3"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "stagedRationals_bounded") "_simp_1_4"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "stagedSearch"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "stagedSearch") "congr_simp"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "stagedSearchIndex"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "stagedSearchIndex") "congr_simp"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "stagedSearchIndex_first"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "stagedSearchIndex_le"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "stagedSearch_correct"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "stagedSearch_mem"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "stagedSearch_passes"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "stagedSearch_same_optimizer"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "stagedSearch_terminates"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "tailCheck") "eq_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "canonicalCandidate_exists"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "canonicalCandidate_exists") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "canonicalNodeLt"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "canonicalNodeLt") "_sparseCasesOn_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "canonicalNodeLt") "_sparseCasesOn_1") "else_eq"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "canonicalNodeLt") "eq_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "canonicalNodeLt") "eq_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "canonicalNodeLt") "eq_3"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "canonicalNodeLt") "match_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "canonicalNodeLt_complete"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "canonicalNodeLt_complete") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "canonicalNodeLt_sound"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "canonicalParity"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "canonicalParity") "eq_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "canonicalRawCandidate"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "canonicalRawCandidate") "_proof_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "canonicalRawCandidate") "_proof_10"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "canonicalRawCandidate") "_proof_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "canonicalRawCandidate") "_proof_3"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "canonicalRawCandidate") "_proof_4"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "canonicalRawCandidate") "_proof_5"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "canonicalRawCandidate") "_proof_6"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "canonicalRawCandidate") "_proof_7"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "canonicalRawCandidate") "_proof_8"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "canonicalRawCandidate") "_proof_9"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "canonicalRawCandidate") "_simp_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "canonicalRawCandidate") "eq_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "canonicalRawCandidateCheck"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "canonicalRawCandidateCheck") "eq_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "canonicalRawCheck"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "canonicalRawCheck") "eq_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "canonicalRawCheck_optimality"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "canonicalRawCheck_complete"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "canonicalRawCheck_complete") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "canonicalRawCheck_exists"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "canonicalRawCheck_general"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "canonicalRawCheck_sound"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "canonicalRawQ"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "canonicalRawQ") "eq_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "canonicalRawQ_eq"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "canonicalRawValue"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "canonicalRawValue") "eq_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "canonicalRawValue") "eq_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "canonicalRawValue") "match_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "canonicalRawValue_cast"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "canonical_certificate_exists"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "canonical_certificate_exists") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "canonical_array_certificate_exists"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "canonical_coefficients_real_ray"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "canonical_coefficients_smul_iff"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "canonical_shifted_real_ray"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "canonical_tail_smul_iff"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Certificates") "weightedDifference_degree_leading"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Comparisons") "bounded_integrable"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Comparisons") "globalProjectorCopies"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Comparisons") "globalProjectorCopies") "_proof_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Comparisons") "globalProjectorCopies_confidence"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Comparisons") "globalProjectorCopies_pos"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Comparisons") "globalProjectorCopies_rounding"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Comparisons") "globalProjectorCopies_upper"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Comparisons") "globalProjectorLaw"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Comparisons") "globalProjectorLaw") "eq_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Comparisons") "globalProjectorLaw_eq_bernoulli"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Comparisons") "globalProjectorLaw_probability"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Comparisons") "globalProjectorMean"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Comparisons") "globalProjectorPOVM"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Comparisons") "globalProjectorPOVM") "_proof_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Comparisons") "globalProjectorPOVM_false"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Comparisons") "globalProjectorPOVM_true"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Comparisons") "globalProjectorParameter"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Comparisons") "globalProjectorParameter") "_proof_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Comparisons") "globalProjectorParameter") "eq_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Comparisons") "globalProjectorRecordLaw"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Comparisons") "globalProjectorTest"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Comparisons") "globalProjectorTest") "eq_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Comparisons") "globalProjectorTest_measurable"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Comparisons") "globalProjector_error_high"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Comparisons") "globalProjector_error_low"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Comparisons") "globalProjector_iid"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Comparisons") "globalProjector_integral"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Comparisons") "globalProjector_marginal"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Comparisons") "globalProjector_prob_false"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Comparisons") "globalProjector_prob_true"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Comparisons") "global_projector_comparison"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Comparisons") "iid_bounded_lower_tail"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Comparisons") "iid_bounded_upper_tail"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Comparisons") "iid_bounded_upper_tail") "_simp_1_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Comparisons") "iid_bounded_upper_tail") "_simp_1_3"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Comparisons") "iid_bounded_upper_tail") "_simp_1_4"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Comparisons") "iid_bounded_upper_tail") "_simp_1_5"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Comparisons") "iid_bounded_upper_tail") "_simp_1_6"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Comparisons") "iid_bounded_upper_tail") "_simp_1_7"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Comparisons") "iid_bounded_upper_tail") "_simp_1_8"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Comparisons") "projectorOutcome"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Comparisons") "projectorOutcome") "eq_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Comparisons") "projectorOutcome_mem"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Comparisons") "target_projector_le_one"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "IntegerDualCertificate") "binomial_moments"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "IntegerDualCertificate") "coefficient_mass"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "IntegerDualCertificate") "coefficient_variation"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "IntegerDualCertificate") "negative_mass"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "IntegerDualCertificate") "positive_mass"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "GeometricSeries") "exists_finite_degree_for_gap"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "GeometricSeries") "gamma_binomial_bound"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "GeometricSeries") "gamma_elementary_decay"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "GeometricSeries") "gamma_tendsto_zero_of_two_lt"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "GeometricSeries") "geometric_derivative_hasSum"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "GeometricSeries") "geometric_derivative_norm_bound"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "GeometricSeries") "geometric_derivative_norm_bound") "_simp_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "GeometricSeries") "geometric_derivative_norm_bound") "_simp_1_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "GeometricSeries") "geometric_derivative_norm_bound") "_simp_1_3"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "GeometricSeries") "geometric_derivative_norm_bound") "_simp_1_4"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "GeometricSeries") "geometric_derivative_norm_bound") "_simp_1_5"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "GeometricSeries") "geometric_derivative_norm_bound") "_simp_1_6"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "GeometricSeries") "geometric_derivative_norm_bound") "_simp_1_7"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "GeometricSeries") "geometric_derivative_summable_bound"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "GeometricSeries") "geometric_iteratedDeriv_eq_tsum"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "GeometricSeries") "geometric_iteratedDeriv_value"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "GeometricSeries") "hasSum_choose_mul_geometric_via_derivatives"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "GeometricSeries") "hasSum_choose_mul_geometric_via_derivatives") "_simp_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "GeometricSeries") "hasSum_choose_mul_geometric_via_derivatives") "_simp_1_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "GeometricSeries") "hasSum_choose_mul_geometric_via_derivatives") "_simp_1_3"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "GeometricSeries") "hasSum_choose_mul_geometric_via_derivatives") "_simp_1_4"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "GeometricSeries") "hasSum_choose_mul_geometric_via_derivatives") "_simp_1_5"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "GeometricSeries") "hasSum_choose_mul_geometric_via_derivatives") "_simp_1_6"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "GeometricSeries") "hasSum_choose_mul_geometric_via_derivatives") "_simp_1_7"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "GeometricSeries") "weighted_choose_le_geometric"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "GeometricSeries") "weighted_choose_le_geometric") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "alternating_contacts_infinity"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "alternating_offset_degree_lower"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "barycentricDenominator"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "barycentricDenominator_formula"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "barycentric_signed_pos"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "barycentric_sum_eq_zero"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "basicCandidate_extrapolation"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "basicCandidate_feasible"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "binomialPolynomial_eval_nat"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "coefficient_mass_identities"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "compact_convexHull"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "contact_nodes_compression"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "continuousNodeMap_injective"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "convexHull_eq_finite_combinations"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "decayPolynomial"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "decayPolynomial_admissible"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "decayPolynomial_eval_positive"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "decayPolynomial_weighted"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "degreeZero_extrapolation"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "dual_support_lower_bound"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "envelopeCandidate"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "envelopeCandidate_extrapolation"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "envelopeCandidate_feasible"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "envelopeCandidate_maximizes"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "envelopeCandidate_recover"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "envelopeRatio_le_of_nonnegative_bound"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "envelopeRatio_le_of_nonpositive_bound"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "envelopeRatio_lower"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "envelope_denominator_pos"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "envelope_minimizer_degree_eq"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "envelope_minimizer_rational"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "envelope_minimizer_unique"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "envelope_zero_bounds"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "evaluationMatrix_det_ne_zero"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "existsUnique_envelope_minimizer"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "existsUnique_extremizer"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "exists_extremizer"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "exists_finite_degree_for_gap"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "expPolynomial_not_many_zeros"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "extendedDictionary_linearIndependent"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "extendedEval_bijective"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "extendedFunction_nodeToExtended"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "extendedFunction_zero_data"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "extremalValue_attained"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "extremalValue_rational"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "extremalValue_strict_succ"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "extremalValue_zero"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "extremizerPolynomial_admissible"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "extremizerPolynomial_envelope_bounds"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "extremizerPolynomial_ratio_le"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "extremizer_coefficients_rational"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "extremizer_limit_value"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "extremizer_unique"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "feasible_compact"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "finite_dual_binomial_moments"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "finite_dual_mass"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "finite_dual_of_extremizer"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "finite_dual_polynomial"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "finite_dual_positive_negative_mass"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "finite_extremal_dual_complete"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "finite_extremal_dual_exact"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "finite_extremal_dual_ordered"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "finite_integer_binomial_certificate"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "finite_label_zero"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "first_residual_formula"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "first_residual_ne_zero"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "full_interpolation"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "gamma_attained"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "gamma_binomial_bound"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "gamma_elementary_decay"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "gamma_eq_extremalValue"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "gamma_le_inverse"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "gamma_pos"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "gamma_rational"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "gamma_strictAnti"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "gamma_strict_succ"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "gamma_tendsto_zero_of_two_lt"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "gamma_zero"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "integerDualCertificate_nonempty"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "inverse_pow_eq_real_decay"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "le_upperEnvelope"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "linearIndependent_of_affine_of_functional"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "lowerEnvelope_le"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "nodeFunctionSpace_continuous"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "nodeFunctionSpace_finrank"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "nodeFunctionSpace_mem_iff"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "normalizedExtrapolation_mem_contactHull"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "normalizedExtrapolation_mem_signedHull"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "norming_of_maximizer"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "one_lt_extremalValue"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "orderedEvaluationMatrix_det_same_sign"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "ordered_finite_labels"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "ordered_reproduction_alternating"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "partial_interpolation"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "polynomialNode") "eq_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "polynomialNode_envelope_bounds"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "positive_support_compression"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "rationalEvaluationMatrix_cast"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "rationalEvaluationMatrix_det_ne_zero"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "rational_coefficients_of_values"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "realEvaluationMatrix_det_same_sign"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "real_infinity_det_same_sign"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "signedDictionary_compact"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "weightedValue_tendsto"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "weighted_choose_le_geometric"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Extremal") "weightsSet_compact"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "FiniteSlots"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "FiniteSlots") "_f"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "FiniteSlots") "_sunfold"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "FiniteSlots") "_unsafe_rec"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "FiniteSlots") "match_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "SlotHistory"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "binaryRelativeEntropy"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "binaryRelativeEntropy") "eq_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "binaryRelativeEntropy_anti_target"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "binaryRelativeEntropy_at_error"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "binaryRelativeEntropy_deriv_source"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "binaryRelativeEntropy_deriv_source_paper"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "binaryRelativeEntropy_deriv_target"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "binaryRelativeEntropy_deriv_target") "_simp_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "binaryRelativeEntropy_deriv_target") "_simp_1_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "binaryRelativeEntropy_deriv_target") "_simp_1_3"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "binaryRelativeEntropy_deriv_target") "_simp_1_4"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "binaryRelativeEntropy_deriv_target") "_simp_1_5"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "binaryRelativeEntropy_deriv_target") "_simp_1_6"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "binaryRelativeEntropy_deriv_target") "_simp_1_7"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "binaryRelativeEntropy_mono_source"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "binaryRelativeEntropy_source_continuous"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "binaryMeasure_event"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "binarySupport_at_error"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "binarySupport_mono"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "binary_klDiv_eq_binaryRelativeEntropy"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "binary_klDiv_event_le"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "binary_klDiv_formula"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "binary_klDiv_le_liminf"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "binary_klDiv_source_one"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "binary_klDiv_target_zero"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "confidenceFactor"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "continuousConfidenceRatio"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "continuousConfidenceRatio") "_proof_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "continuousConfidenceRatio") "eq_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "continuousConfidenceRatio_continuousAt"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "continuousConfidenceRatio_continuousAt_zero"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "continuousConfidenceRatio_continuousOn"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "continuousConfidenceRatio_eq_testing"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "continuousConfidenceRatio_eq_testing") "_simp_1_3"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "continuousConfidenceRatio_eq_testing") "_simp_1_4"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "continuousConfidenceRatio_eq_testing") "_simp_1_5"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "continuousConfidenceRatio_eq_testing") "_simp_1_6"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "continuousConfidenceRatio_eq_testing") "_simp_1_7"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "continuousConfidenceRatio_eq_testing") "_simp_1_8"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "continuousConfidenceRatio_eq_testing") "_simp_1_9"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "continuousConfidenceRatio_pos"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "continuousConfidenceRatio_positive_minimum"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "continuousConfidenceRatio_tendsto_zero_right"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "continuousConfidenceRatio_zero"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "count_finiteSlots_succ"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "finiteSlotsFintype"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "finiteSlotsFintype") "_aux_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "finiteSlotsFintype") "_aux_4"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "finiteSlotsFintype") "_f"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "finiteSlotsFintype") "_proof_3"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "finiteSlotsFintype") "_proof_6"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "finiteSlotsFintype") "_sunfold"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "finiteSlotsFintype") "_unsafe_rec"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "finiteSlotsMeasurable"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "finiteSlotsMeasurable") "_aux_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "finiteSlotsMeasurable") "_aux_3"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "finiteSlotsMeasurable") "_f"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "finiteSlotsMeasurable") "_proof_5"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "finiteSlotsMeasurable") "_proof_6"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "finiteSlotsMeasurable") "_proof_7"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "finiteSlotsMeasurable") "_sunfold"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "finiteSlotsMeasurable") "_unsafe_rec"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "finiteSlotsSingleton"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "finiteSlotsSingleton") "_f"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "finiteSlotsSingleton") "_proof_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "finiteSlotsSingleton") "_proof_4"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "finiteSlotsSingleton") "_unsafe_rec"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "finiteSlotsSingleton") "match_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "finite_absolutelyContinuous_iff_atoms"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "integrable_finite_logLikelihood"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "finite_withDensity"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "flattenHistory"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "flattenHistory") "_f"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "flattenHistory") "_sunfold"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "flattenHistory") "_unsafe_rec"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "flatten_prefixLaw_product_density"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "flatten_prefixCountingReference"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "integrable_slotLogLikelihood"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "integral_slotLogLikelihood"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "inv_log_continuousAt_zero"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "jointDensity"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "joint_absolutelyContinuous_iff"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "joint_klDiv_eq_lintegral_full"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "joint_withDensity"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "lowerSemicontinuous_binary_klDiv"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "measurable_prefixProductLikelihood"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "measurable_prefixLogLikelihoodSum"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "measurable_prefixProductDensity"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "measurable_slotLogLikelihood"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "neg_mul_log_le_exp_neg_one"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "neg_mul_log_le_exp_neg_one") "_simp_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "negativeRelativeEntropyAtom"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "negativeRelativeEntropyAtom") "eq_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "negativeRelativeEntropyAtom_le"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "negativeRelativeEntropyAtom_le") "_simp_1_10"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "negativeRelativeEntropyAtom_le") "_simp_1_3"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "negativeRelativeEntropyAtom_le") "_simp_1_4"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "negativeRelativeEntropyAtom_le") "_simp_1_5"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "negativeRelativeEntropyAtom_le") "_simp_1_6"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "negativeRelativeEntropyAtom_le") "_simp_1_7"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "negativeRelativeEntropyAtom_le") "_simp_1_8"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "negativeRelativeEntropyAtom_le") "_simp_1_9"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "originalSeedHistory"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "originalSeed_prefixLaw_product_density"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "originalSeed_prefixCountingReference"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "positiveRelativeEntropyAtom"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "prefixActiveCount_lintegral"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "prefixLaw"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "prefixLaw") "eq_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "prefixLaw") "eq_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "prefixLaw") "eq_def"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "prefixLaw_ac_of_finite_bound_product_density"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "prefixLaw_klDiv_eq_sum"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "prefixLaw_klDiv_eq_sum_product_density"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "prefixLaw_stopped_klDiv_le"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "prefixLaw_stopped_klDiv_le_product_density"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "prefixLaw_withDensity_productLikelihood"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "prefixLaw_withDensity_productDensity"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "prefixProductLikelihood"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "prefixProductLikelihood") "_f"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "prefixProductLikelihood") "_sunfold"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "prefixProductLikelihood") "_unsafe_rec"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "prefixProductLikelihood") "eq_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "prefixProductLikelihood") "eq_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "prefixProductLikelihood") "eq_def"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "prefixProductLikelihood") "match_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "prefixProductLikelihood_log_expand"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "prefixProductLikelihood_mul_density"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "prefixProductLikelihood_ne_top"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "prefixLogLikelihoodSum"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "prefixLogLikelihoodSum") "_f"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "prefixLogLikelihoodSum") "_sunfold"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "prefixLogLikelihoodSum") "_unsafe_rec"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "prefixLogLikelihoodSum") "eq_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "prefixLogLikelihoodSum") "eq_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "prefixLogLikelihoodSum") "eq_def"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "prefixLogLikelihoodSum_integrable"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "prefixLogLikelihoodSum_integral"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "prefixProductDensity"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "prefixProductDensity") "_f"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "prefixProductDensity") "_sunfold"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "prefixProductDensity") "_unsafe_rec"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "prefixProductDensity") "eq_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "prefixProductDensity") "eq_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "prefixProductDensity") "eq_def"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "prefixCountingReference"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "prefixCountingReference") "_f"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "prefixCountingReference") "_sunfold"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "prefixCountingReference") "_unsafe_rec"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "prefixCountingReference") "eq_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "prefixCountingReference") "eq_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "prefixCountingReference") "eq_def"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "prefixCountingReference") "match_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "prefixCountingReference_finite"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "prefixCountingReference_finite") "_f"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "prefixCountingReference_finite") "_proof_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "prefixCountingReference_finite") "_proof_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "prefixCountingReference_finite") "_unsafe_rec"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "prefix_llr_eq_logLikelihoodSum"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "relativeEntropyAtom"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "relativeEntropyAtom") "eq_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "slotLogLikelihood"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "slotLogLikelihood") "eq_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "stopContinue_ac"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "stopContinue_kl"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "sum_real_finite_atoms"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "sum_relativeEntropyAtom_eq_klDiv"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "sum_relativeEntropyAtom_eq_klDiv") "_simp_1_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "sum_relativeEntropyAtom_eq_klDiv") "_simp_1_3"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "sum_relativeEntropyAtom_eq_klDiv") "_simp_1_4"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "sum_relativeEntropyAtom_eq_klDiv") "_simp_1_5"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "sum_relativeEntropyAtom_eq_klDiv") "_simp_1_6"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "sum_relativeEntropyAtom_eq_klDiv") "_simp_1_7"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "sum_relativeEntropyAtom_eq_klDiv") "_simp_1_8"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "testingThreshold"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "testingThreshold") "eq_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "testingThreshold_confidence_lower"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "testingThreshold_confidence_lower_via_continuous_ratio"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "testingThreshold_le_binarySupport"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "testingThreshold_le_binary_klDiv_via_derivatives"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "sum_abs_relativeEntropyAtom_le"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "sum_negativeRelativeEntropyAtom_le"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "sum_positiveRelativeEntropyAtom_le"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Information") "zero_source_of_zero_denominator_product_density"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Probability") "blockCopies"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Probability") "blockCopies_chebyshev_constant"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Probability") "blockCopies_upper"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Probability") "blockCount"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Probability") "blockCount_budget"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Probability") "block_total_budget"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "FixedBlockConsumers") "two_qubit_block_boundary"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "FixedScoreAchievable"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "FixedScoreCanonicalConclusion"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "ProductSetting"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "QuditProtocol"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "RawProtocol"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "RawRules"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "Record"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "Terminates"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "Valid"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "calibrated_terminal_information_finite_via_product_density"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "canonical_protocol_coverage"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "capped_iff_legal_all_points"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "completeMUB_corollary_three_six"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "constant_budget_testing_scale"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "constant_budget_testing_scale_via_product_density"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "constant_budget_testing_scale_via_product_density") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "decodePublicPrefix_publicPrefix"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "executionLaw"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "executionLaw_prefix"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "executionSlotKernel"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "execution_expected_min"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "execution_expected_truncations"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "execution_klDiv_le_truncated_cost"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "execution_klDiv_le_truncated_cost_finite_via_product_density"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "expectedBudget"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "expectedBudget_le_maximumBudget"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "expectedBudget_lower"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "expectedCopies"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "expectedCopies_le_protocolCost"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "exponentialHaar_budget_testing_scale"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "exponentialHaar_budget_testing_scale_via_product_density"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "exponentialHaar_budget_testing_scale_via_product_density") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "fixedBlockExecutionLaw_eq"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "fixedBlockExpectedBudget_eq"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "fixedBlockMaximumBudget_eq"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "fixedBlockValid_iff"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "fixedBlock_all_path_cap"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "fixedBlock_canonical_coverage"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "fixedBlock_corollary_six_two_confidence"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "fixedBlock_log_budget_criterion_continuous_confidence"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "fixedBlock_degree_at_threshold"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "fixedBlock_degree_positive_iff"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "fixedBlock_degree_zero_iff"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "fixedBlock_hierarchy_confidence"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "fixedBlock_hierarchy_continuous_confidence"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "fixedScore_achievable_of_full_control_eventually"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "fixedScore_completeMUB_canonical"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "fixedScore_haar_canonical"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "fixedScore_pauli_canonical"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "iUnion_truncatedDecisionEvent"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "klDiv_map_retract_ae"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "legal_isStoppingTime"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "legal_terminalDecision_stopped_measurable"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "maximumBudget"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "polynomial_log_budget_diverges"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "prefixDecisionEvent_measurable"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "prefixDecisionEvent_measure"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "prefixDecisionEvent_probability_tendsto"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "prefixLaw_ae_consistent"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "promisedStates"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "publicPrefix"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "publicPrefix_klDiv"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "publicPrefix_measurable"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "qubit_quartic_lower_endpoint"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "qubit_quartic_window"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "qudit_budget_power_testing_scale"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "qudit_budget_power_testing_scale_via_product_density"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "qudit_budget_power_testing_scale_via_product_density") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "qudit_budget_power_testing_scale_via_product_density") "_simp_1_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "qudit_budget_power_testing_scale_via_product_density") "_simp_1_3"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "qudit_budget_sphere_testing_scale"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "qudit_budget_sphere_testing_scale_via_product_density"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "qudit_budget_sphere_testing_scale_via_product_density") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "qudit_budget_sphere_testing_scale_via_product_density") "_proof_1_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "qudit_exponential_testing_hierarchy"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "qudit_exponential_testing_hierarchy_via_product_density"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "qudit_raw_filtration_rules_exist"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "qudit_same_event_all_confidence_ranges"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "qudit_same_event_confidence_hierarchy"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "sufficientBlockSize_log_bound"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "sufficientBlockSize_threshold"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "terminal_binary_information"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "terminal_binary_information_finite_via_product_density"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "terminal_binary_information_via_product_density"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "terminal_information_of_errors"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "terminal_information_of_errors_finite_via_product_density"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "terminal_information_of_errors_via_product_density"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "terminal_klDiv_finite_via_product_density"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "terminal_klDiv_of_truncated_bounds_via_product_density"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "terminal_klDiv_via_product_density"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "truncatedDecisionEvent_measurable"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "truncatedDecisionEvent_mono"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "qudit_continuous_confidence_hierarchy"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "qudit_same_event_continuous_confidence_hierarchy"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "valid_information_high_low"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "valid_information_high_low_finite_via_product_density"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "valid_information_high_low_finite_via_product_density") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "valid_information_high_low_via_product_density"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "valid_information_high_low_via_product_density") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "valid_information_low_high"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "valid_information_low_high_finite_via_product_density"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "valid_information_low_high_finite_via_product_density") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "valid_information_low_high_via_product_density"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Protocol") "valid_information_low_high_via_product_density") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Quantum") "calibratedHaar_hard_states"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Quantum") "calibratedInformationScale_eventually"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Quantum") "calibrated_error_bounds"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Quantum") "calibrated_productBorn_difference"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Quantum") "completeBornRecordLaw_integral"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Quantum") "completeHaarReadout_scorebounds"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Quantum") "completePauliReadout_scorebounds"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Quantum") "completeReadoutLoewner"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Quantum") "constantLowState"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Quantum") "constantLowState_fidelity"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Quantum") "constantLowState_klDiv"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Quantum") "constantLowState_promised"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Quantum") "dualHighState_uniform_floor_even"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Quantum") "dualLowState_fidelity_le"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Quantum") "dualLowState_uniform_floor_odd"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Quantum") "dualResidualKernel_power_order"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Quantum") "dualStates_difference_explicit"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Quantum") "dualStates_productBorn_difference"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Quantum") "exists_radialPolynomial"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Quantum") "exponentialOverlapCutoff_eq_rpow"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Quantum") "exponentialOverlapCutoff_failure_le"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Quantum") "exponentialOverlapCutoff_square_dimension"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Quantum") "fixedBlockBornMeasure_eq"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Quantum") "fixedBlockSphere_measure"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Quantum") "fixedBlock_local_basis_surjective"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Quantum") "localWeyl"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Quantum") "localWeyl_hilbertSchmidt"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Quantum") "localWeyl_mul_apply"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Quantum") "optimal_radial_parameters"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Quantum") "productBornKernel"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Quantum") "productBornMeasure_atom_real"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Quantum") "productBorn_shell_readout"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Quantum") "pureTargetShell_readout"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Quantum") "qitProductBasis"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Quantum") "qitProductBasis") "eq_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Quantum") "qitProductBasis_apply"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Quantum") "qitProductBasis_processed_coordinate"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Quantum") "qudit_haar_orbit_eq_sphere"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Quantum") "qudit_haar_orbit_eq_sphere") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Quantum") "qudit_haar_product_basis_score_bound"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Quantum") "qudit_uniform_product_basis_score_bound"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Quantum") "radialFirstCoefficient_eq_polynomial"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Quantum") "stoppedBornPrefixLaw_klDiv_le"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Quantum") "tensorBasis") "eq_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "Quantum") "tensorBasis_qitProductBasis"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "LegacyPaper") "S11_Haar"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "LegacyPaper") "S11_MUB"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "LegacyPaper") "S11_Pauli"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "LegacyPaper") "S12_Haar"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "LegacyPaper") "S12_Pauli"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "LegacyPaper") "S12_Wick"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "LegacyPaper") "S12_Wick_bound"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "LegacyPaper") "S15"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "LegacyPaper") "S15_budgets"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "LegacyPaper") "S17_Haar"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "LegacyPaper") "S17_sphere"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "LegacyPaper") "S18"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "LegacyPaper") "S19"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "LegacyPaper") "S19_finite"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "LegacyPaper") "S20_raw"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "LegacyPaper") "S21"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "LegacyPaper") "S22"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "LegacyPaper") "S22_criterion"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "LegacyPaper") "S24"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "LegacyPaper") "S24_coefficient"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "LegacyPaper") "S29"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "LegacyPaper") "S30"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "LegacyPaper") "S31_correct"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "LegacyPaper") "S31_termination"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "LegacyPaper") "S7_bound"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "LegacyPaper") "S7_decay"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "LegacyPaper") "S8_Haar"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "LegacyPaper") "S8_Haar_protocol"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "LegacyPaper") "S8_Pauli"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "LegacyPaper") "S8_Pauli_protocol"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "LegacyPaper") "global_comparison"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "LegacyPaper") "theorem_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "LocalCertification") "LegacyPaper") "theorem_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "Consumers") "actual_net_and_radius_package_via_frobenius_packing"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "Consumers") "actual_net_and_radius_package_via_frobenius_packing") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "Consumers") "uniform_product_score_haar_orbit_via_packing"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "Consumers") "uniform_product_score_haar_orbit_via_packing") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "Consumers") "uniform_haar_orbit_processed_probability_via_packing"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "Consumers") "uniform_haar_orbit_processed_probability_via_packing") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "Consumers") "uniform_haar_orbit_processed_probability_via_packing") "_simp_1_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "Consumers") "uniform_haar_orbit_processed_probability_via_packing") "_simp_1_3"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "Consumers") "uniform_standard_sphere_processed_probability_via_packing"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "Consumers") "uniform_standard_sphere_processed_probability_via_packing") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "Consumers") "uniform_standard_sphere_processed_probability_via_packing") "_simp_1_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "Consumers") "uniform_standard_sphere_processed_probability_via_packing") "_simp_1_3"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "Consumers") "uniform_standard_sphere_processed_probability_via_packing") "_simp_1_4"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "FourVertexMultigraph") "overlapProduct") "eq_1"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "FourWickChoice"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "FourWickCompatibleChoice"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "FourWickInternalSubset"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "FourWickPosition"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "LocalWickEdge"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "LocalWickPartialMatching"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "IncidentHolder") "compact_integrable"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "IncidentHolder") "incident_overlap_holder"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "IncidentHolder") "incident_overlap_holder_left"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "IncidentHolder") "integral_incident_holder"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "IncidentHolder") "integral_incident_holder") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "IncidentHolder") "integral_six_holder"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "IncidentHolder") "integral_three_incident"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "IncidentHolder") "overlap_integral_le"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "IncidentHolder") "overlap_integral_le") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "IncidentHolder") "overlap_integral_le") "_proof_1_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "IncidentHolder") "overlap_integral_le") "_proof_1_3"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "IncidentHolder") "sixthRoot_pow_six"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "IncidentHolder") "triangle_elimination"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "IncidentHolder") "triangle_elimination") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "WickCompletion"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "actual_kernel_net_cubic_via_frobenius_packing"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "actual_kernel_net_cubic_via_frobenius_packing") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "allProductSphereGood_exception_two"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "allProductSphereGood_exception_two_quartic_radius"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "allProductSphereGood_exception_two_quartic_radius") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "allProductSphereGood_exception_two_quartic_radius") "_proof_1_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "allProductSphereGood_exception_two_quartic_radius") "_proof_1_3"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "all_product_score_of_net_good_quartic_radius"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "all_product_score_bound_quartic_radius"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "all_product_score_bound_quartic_radius") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "all_product_score_bound_quartic_radius") "_proof_1_2"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "basisProbability_l1_difference_bound"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "basisProbability_norm_difference_via_l1"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "cardinalityHaar_remainder_bound"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "cardinalityHaar_second_direction_identity"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "cardinalityPauli_remainder_bound"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "cardinalityPauli_second_direction_identity"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "cardinalityReadoutKernel_trace"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "cardinalityReadoutKernel_trace_sq"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "choose_le_exp_binEntropy"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "completeMUBChangedSiteContraction_le"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "completeMUBChangedSiteIntegral_eq_tensor"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "completeMUBChangedSiteTensor"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "completeMUBChangedSiteTensor") "eq_1"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "completeMUBChangedSiteTensor_posSemidef"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "completeMUBChangedSiteTensor_trace"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "completeMUBChangedSiteTensor_trace_le"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "completeMUBChangedSiteTensor_trace_power"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "completeMUBChangedSite_four_unitary_bound"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "completeMUBChangedSite_integrand_integrable"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "completeMUBConditionalIntegral_le_via_incident_holder"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "completeMUBFourOverlapIntegral_scaled_le_via_incident_holder"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "completeMUBFourOverlapIntegral_scaled_le_via_incident_holder") "_simp_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "completeMUBFourOverlapIntegral_scaled_le_via_incident_holder") "_simp_1_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "completeMUBFourOverlapIntegral_scaled_le_via_incident_holder") "_simp_1_3"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "completeMUBFourOverlapIntegral_scaled_le_via_incident_holder") "_simp_1_4"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "completeMUBFourOverlapIntegral_scaled_le_via_incident_holder") "_simp_1_5"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "completeMUBFourOverlapIntegral_scaled_le_via_incident_holder") "_simp_1_6"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "completeMUBFourOverlapIntegral_scaled_le_via_incident_holder") "_simp_1_7"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "completeMUBFourOverlapIntegral_strict_via_incident_holder"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "completeMUBRecords_choi_entries"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "completeMUBResidualProduct_integral_le_via_incident_holder"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "completeMUBResidualProduct_integral_le_via_incident_holder") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "completeMUBResidualProduct_integral_le_via_incident_holder") "_proof_1_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "completeMUBResidualProduct_integral_le_via_incident_holder") "_proof_1_3"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "completeMUBUnchangedSiteContraction_le"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "completeMUBUnchangedSiteIntegrand"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "completeMUBUnchangedSiteIntegrand") "eq_1"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "completeMUBUnchangedSiteIntegrand_eq"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "completeMUB_local_graph_contraction"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "completeMUB_local_graph_contraction_via_incident_holder"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "complexGaussianBlockPairingSum_four"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "complexGaussian_four_matrix_blocks_entries"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "complexGaussian_four_matrix_blocks_integrable"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "complexGaussian_four_matrix_blocks_trace"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "complexGaussian_four_normal_blocks"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "complexGaussian_four_normal_blocks_all_equal"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "complexGaussian_four_normal_blocks_finite_inclusion_exclusion"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "complexGaussian_four_normal_blocks_finite_norm_le"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "complexGaussian_four_normal_blocks_inclusion_exclusion_sum"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "complexGaussian_four_normal_blocks_repeated_labels"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "complexSphere_coordinate_fourth_moment"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "distanceAverage_column_sum"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "distanceAverage_row_sum"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "exists_maximal_separated_net"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "exists_maximal_separated_net") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "exists_radialLinearLowLabels_exponential_via_binomial_entropy"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "exists_unitary_frobenius_packing_net"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "finiteComplementGaussianFourthIntegral_eq_sum"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "finiteComplementGaussianFourthIntegrand"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "finiteComplementGaussianFourthIntegrand") "congr_simp"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "finiteComplementGaussianFourthIntegrand_eq_sum"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "finiteComplementGaussianFourthIntegrand_integrable"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "finiteComplementKernel"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "finiteComplementWickIntegral_bound"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "finiteComplementWickIntegral_eq_sum"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "finiteComplementWickIntegrand"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "finiteComplementWickIntegrand") "congr_simp"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "finiteComplementWickIntegrand_eq_sum"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "finiteComplementWickIntegrand_integrable"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "finiteWickContractedPolynomial"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "finiteWickContractedPolynomial") "congr_simp"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "finiteWickContractedPolynomial") "eq_1"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "finiteWickContractedPolynomial_eq_deletion"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "finiteWickContractedPolynomial_eq_deletion") "_simp_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "finiteWickContractedPolynomial_eq_deletion") "_simp_1_2"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "finiteWick_contracted_monomial"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "finiteWick_deleted_monomial"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "finiteWick_monomial"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "finiteWick_subset_cancellation"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "finite_choice_coefficient_mass"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "finite_choice_sum_norm_le"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourBlockDerangements_card"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourBlockDerangements_card_finite_inclusion_exclusion"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourBlockDerangements_card_le_eight_factorial"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourBlockDerangements_inv"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourBlockDerangements_inv") "_simp_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourBlockDerangements_inv") "_simp_1_2"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourBlockWick_sum_norm_le"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourNormalQuartics_completion_expansion"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourNormalQuartics_finite_expansion"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourRecordAt"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourRecordAt") "eq_1"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourRecordAt_continuous"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourWickChoiceDomain"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourWickChoiceDomain") "eq_1"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourWickChoiceDomainEquiv"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourWickChoiceDomainEquiv") "_proof_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourWickChoiceDomainEquiv") "_proof_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourWickChoiceDomainEquiv") "_proof_3"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourWickChoiceDomainEquiv") "_proof_4"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourWickChoiceDomainEquiv") "_proof_5"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourWickChoiceDomainEquiv") "_proof_6"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourWickChoiceDomain_card"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourWickChoicePermutation"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourWickChoicePermutation") "eq_1"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourWickChoiceSign"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourWickChoiceSubset"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourWickChoiceSubset") "_proof_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourWickChoiceSubset") "eq_1"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourWickChoiceSubset_eq_domain"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourWickChoice_completion_iff"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourWickChoice_completion_iff") "_simp_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourWickChoice_completion_iff") "_simp_1_2"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourWickChoice_polynomial"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourWickChoice_polynomial") "_simp_1_5"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourWickChoice_polynomial") "_simp_1_6"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourWickExpansionFiberEquiv"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourWickExpansionFiberEquiv") "_proof_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourWickExpansionFiberEquiv") "_proof_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourWickExpansionFiberEquiv") "_simp_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourWickExpansionFiberEquiv") "_simp_3"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourWickExpansionFiberEquiv_sign"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourWickInclusionExclusionSum"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourWickInclusionExclusionSum") "congr_simp"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourWickInclusionExclusionSum_eq"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourWickInternalPositions"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourWickInternalPositions") "eq_1"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourWickInternalPositions_empty_iff"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourWickInternalPositions_empty_iff") "_simp_1_2"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourWickSubsetChoice"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourWickSubsetChoice") "_proof_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourWickSubsetChoice") "_proof_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourWickSubsetChoice") "eq_1"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourWick_completion_sum"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourWick_completion_sum") "_simp_1_1"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourWick_expansion_coefficient"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourWick_expansion_coefficient") "_simp_1_1"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourWick_expansion_coefficient_via_fiber"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourWick_matching_coefficient"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "fourWick_matching_coefficient") "_simp_1_1"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "gaussianMatrixChaos_expectation_bound"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "gaussianMatrixChaos_integral_prod"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "gaussianNormalMatrixPolynomial_as_positions"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "gaussianNormalMatrixPolynomial_prod_positions"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "gaussianNormalMatrixPolynomial_prod_positions") "_simp_1_1"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "gaussianNormalQuartic_finite_expansion"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "haarFourOverlapIntegral") "eq_1"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "haarFourOverlapIntegral_le_via_incident_holder"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "haarFourOverlapIntegral_scaled_le_via_incident_holder"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "haarUnchangedSiteContraction_le"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "haarUnchangedSiteIntegrand"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "haarUnchangedSiteIntegrand") "eq_1"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "haarUnchangedSiteIntegrand_eq"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "haarUnchangedSiteIntegrand_integrable"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "haar_local_graph_contraction"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "haar_local_graph_contraction_via_incident_holder"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "haar_local_graph_contraction_via_incident_holder") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "haar_unitaryComplementDephasing_entry"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "haar_unitaryDephasing_entry"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "hamming_sphere_card"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "hasDerivAt_weightedEntropy"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "instDecidableLocalWickPartialMatching"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "instFintypeWickCompletion"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "kernelNetMesh"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "kernelPackingMesh"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "kernelPackingMesh") "_proof_1"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "kernelPackingMesh_base_eventually"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "kernelPackingMesh_base_eventually") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "kernelPackingMesh_eventually_pos"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "kernelPackingMesh_eventually_pos") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "kernelPackingMesh_inverse_le"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "kernelPackingMesh_inverse_le") "_simp_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "kernelPackingMesh_inverse_le") "_simp_1_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "kernelPackingMesh_inverse_le") "_simp_1_3"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "kernelPackingMesh_inverse_le") "_simp_1_4"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "kernelPackingMesh_inverse_le") "_simp_1_5"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "kernelPackingMesh_inverse_le") "_simp_1_6"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "kernelPackingMesh_inverse_le") "_simp_1_7"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "kernelPackingMesh_pos"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "kernelPackingMesh_pos") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "kernelPackingMesh_transfer_scale"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "kernelPackingMesh_transfer_scale") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "kernelPackingMesh_transfer_scale") "_proof_1_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "kernelPackingMesh_transfer_scale") "_simp_1_3"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "kernelPackingMesh_transfer_scale") "_simp_1_4"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "kernelPackingMesh_transfer_scale") "_simp_1_5"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "kernelPackingMesh_transfer_scale") "_simp_1_6"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "kernelPackingMesh_transfer_scale") "_simp_1_7"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "kernelPackingMesh_transfer_scale") "_simp_1_8"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "kernelPackingMesh_transfer_scale") "_simp_1_9"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "kernelProductPackingNet_eventually_card"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "localWickContractionPolynomial"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "localWickContractionPolynomial") "eq_1"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "localWickContractionPolynomial_deletion"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "localWickContractionPolynomial_deletion") "_simp_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "localWickContractionPolynomial_deletion") "_simp_1_2"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "localWickContractions"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "localWickContractions") "_proof_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "localWickContractions") "eq_1"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "localWickContractions_mem_iff"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "localWickInternalEdges"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "localWickInternalEdges") "eq_1"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "localWickInternalEdges_all_empty_iff"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "localWickInternalEdges_all_empty_iff") "_simp_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "localWickInternalEdges_all_empty_iff") "_simp_1_2"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "localWickInternalEdges_subset_term"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "localWickPermutation"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "localWickPermutation") "_proof_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "localWickPermutation") "eq_1"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "localWickPermutation_edges"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "localWick_expansion_coefficient"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "localWick_expansion_fiber"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "localWick_expansion_fiber") "_simp_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "localWick_expansion_fiber") "_simp_1_2"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "matrixKroneckerLeftHom"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "matrixKroneckerLeftHom") "_proof_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "matrixKroneckerLeftHom") "_proof_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "matrixKroneckerLeftHom") "_proof_3"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "matrixKroneckerLeftHom") "_proof_4"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "matrixKroneckerLeftHom") "_proof_5"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "matrixKroneckerRightHom"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "matrixKroneckerRightHom") "_proof_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "matrixKroneckerRightHom") "_proof_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "matrixKroneckerRightHom") "_proof_3"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "matrixKroneckerRightHom") "_proof_4"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "matrixKroneckerRightHom") "_proof_5"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "matrixReindexStarAlgEquiv"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "matrixReindexStarAlgEquiv") "_proof_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "matrixReindexStarAlgEquiv") "_proof_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "matrixReindexStarAlgEquiv") "_proof_3"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "matrixReindexStarAlgEquiv") "_proof_4"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "matrix_kronecker_operator_norm_le_of_star_hom"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "matrix_reindex_operator_norm_le_of_star_equiv"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "matrix_unitary_operator_norm_le_one"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "matrix_wick_delta_contraction"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "uniform_product_score_standard_sphere"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "uniform_product_score_standard_sphere_via_packing"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "uniform_product_score_standard_sphere_via_packing") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "pauliBasisRecords_complement"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "pauliBasisRecords_success"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "pauliConditionalIntegral_le_via_incident_holder"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "pauliFourOverlapIntegral_scaled_le_via_incident_holder"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "pauliFourOverlapIntegral_strict_via_incident_holder"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "pauliResidualProduct_integral_le_via_incident_holder"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "pauliResidualProduct_integral_le_via_incident_holder") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "pauliResidualProduct_integral_le_via_incident_holder") "_proof_1_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "pauliResidualProduct_integral_le_via_incident_holder") "_proof_1_3"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "pauliUnchangedSiteContraction_le"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "pauliUnchangedSiteIntegrand"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "pauliUnchangedSiteIntegrand") "eq_1"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "pauliUnchangedSiteIntegrand_eq"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "pauliUnchangedSiteIntegrand_integrable"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "pauli_local_graph_contraction"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "pauli_local_graph_contraction_via_incident_holder"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "prod_coordinate_delta"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "productPackingMatrixNet"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "productPackingMatrixNet_card"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "productPackingMatrixNet_card") "_simp_1_2"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "productPackingMatrixNet_covers"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "productPackingMatrixNet_unitary"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "productPackingTupleNet"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "productPackingTupleNet") "eq_1"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "productUnitaryMatrixNet_covers"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "quditRadius_power_eventually_cubic"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "quditRadius_power_eventually_linear"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "quditReadout_good_radius"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "quditSphereScore_lipschitz_via_l1"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialChoiTail_eventually_exponential"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialChoiTail_eventually_exponential") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialChoiTail_eventually_exponential") "_proof_1_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialChoiTail_eventually_exponential") "_proof_1_3"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialChoiTail_eventually_exponential") "_proof_1_4"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialFirstCoefficient_abs_mass"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialFirstCoefficient_bell_partialTranspose_bound"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialFirstCoefficient_sum"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialFirstHigh_bell_partialTranspose_le"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialHaar_readout_exponential"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearChoiRate"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearChoiRate") "_proof_1"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearChoiRate_pos"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearChoiRate_pos") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearChoiRate_pos") "_proof_1_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearFirstHighWeights") "congr_simp"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearFirstHighWeights_abs_le"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearFirstHighWeights_abs_mass"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearFirstHighWeights_sqrt_eventually"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearFirstHighWeights_square_eventually"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearFirstHigh_bell_partialTranspose_eventually"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearFirstHigh_bell_partialTranspose_eventually") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearFirstHigh_bell_partialTranspose_eventually") "_proof_1_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearFirstHigh_bell_partialTranspose_eventually") "_proof_1_3"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearFirstHigh_bell_partialTranspose_le"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearFirstHigh_bell_partialTranspose_le") "_abel_1_3"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearFirstHigh_gaussian_expectation"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearFirstHigh_gaussian_parameters"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearFirstHigh_sphere_of_good_radius"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearFirstLow_mean_eventually"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearFirstLow_mean_eventually") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearFirstLow_mean_eventually") "_proof_1_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearFirstLow_mean_eventually") "_proof_1_3"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearFirst_polar_approx_eventually"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearFirst_polar_approx_eventually") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearFirst_polar_approx_eventually") "_proof_1_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearFirst_polar_approx_eventually") "_proof_1_3"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearFirst_polar_approx_eventually") "_proof_1_4"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearHaarReadoutPolar_control_eventually"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearHaar_full_second_canonicalSphere_tail"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearHaar_full_second_control_eventually"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearHighLow_canonicalSphere_joint_tail"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearHigh_canonicalSphere_joint_tail"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearHigh_gaussian_joint_tail"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearLowLabels_card_le_entropy"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearLowLabels_card_le_entropy_via_binomial_entropy"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearLowLabels_polynomial_ratio_via_binomial_entropy"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearLowLabels_polynomial_ratio_via_binomial_entropy") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearLowOrbitFamily"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearLowOrbitFamily") "eq_1"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearLowOrbitFamily_hilbertSchmidt"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearLowOrbitFamily_hilbertSchmidt") "_simp_1_2"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearLowOrbitFamily_unitary"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearLowSphereBad"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearLowSphereBad") "_proof_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearLowSphereBad") "_proof_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearLowSphereBad") "_proof_3"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearLowSphereBad") "_proof_4"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearLowSphereBad_measurable"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearLow_canonicalSphere_tail"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearLow_canonicalSphere_tail") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearLow_canonicalSphere_tail") "_proof_1_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearLow_canonicalSphere_tail") "_simp_1_10"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearLow_canonicalSphere_tail") "_simp_1_4"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearLow_canonicalSphere_tail") "_simp_1_5"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearLow_canonicalSphere_tail") "_simp_1_6"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearLow_canonicalSphere_tail") "_simp_1_7"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearLow_canonicalSphere_tail") "_simp_1_8"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearLow_canonicalSphere_tail") "_simp_1_9"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearLow_gram_factor_eventually"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearLow_gram_factor_eventually") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearLow_haar_tail"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearLow_haar_tail") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearLow_polar_on_good_event"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearLow_polar_on_good_event") "_proof_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearLow_polar_on_good_event") "_proof_1_2"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearPauliReadoutPolar_control_eventually"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearPauli_full_second_canonicalSphere_tail"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearPauli_full_second_control_eventually"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearPolarCompression"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearPolarCompression") "congr_simp"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearPolarCompression_weight_smul"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearReadoutFullBad_measurable"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearReadoutFullControl"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearReadoutPolarControl"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearSecondHighWeights_eq"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearSecondHigh_gaussian_expectation"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearSecondHigh_sphere_of_good_radius"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialLinearSecond_polar_approx_eventually"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialPairOutcome_moment_four"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialPairOutcome_moment_two"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialPauli_readout_exponential"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialSecondCoefficient_bell_partialTranspose_bound"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialSecondCoefficient_sum"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "radialWeightCutoff"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "inverse_fourth_power_le_inverse_square"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "quarticRadius_denominator_pos"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "quarticRadius_score_factor_le"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "readoutSecondOperator_direction_identity"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "readoutSecondOperator_gaussian_identity"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "score_bound_of_good_quartic_radius"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "score_bound_with_quartic_radius_denominator"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "separated_card_le_ball_volume_ratio"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "signedHammingKernel_sq_diag"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "signedHammingKernel_sq_trace"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "signedHammingKernel_trace_four_le"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "sphereScore_abs_lipschitz_via_l1"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "sphereScore_lipschitz"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "sphereScore_lipschitz_via_l1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "sphereScore_lipschitz_via_l1") "_abel_1_1"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "sum_finTwo_function"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "tensorUnitaryMatrix_operator_close_of_local_operator"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "tensorUnitaryMatrix_operator_close_of_local_frobenius"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "tensorUnitaryMatrix_succ_kronecker"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "unchangedLocalContraction"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "unchangedLocalContraction") "congr_simp"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "unchangedLocalContraction") "eq_1"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "unchangedLocalContraction_continuous"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "unchangedLocalContraction_norm"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "unitaryFrobeniusVector"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "unitaryFrobeniusVector") "_proof_1"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "unitaryFrobeniusVector_injective"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "unitaryFrobeniusVector_norm"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "unitaryFrobeniusVector_norm_sq"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "unitaryFrobeniusVector_sub_norm_sq"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "unitaryFrobenius_real_dimension"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "unitaryGaussianConjugation_expectation_bound"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "unitaryNet_card"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "unitaryOrbitGramSquareSum_moment"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "unitaryOrbitGram_haar_tail"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "unitaryOrbitGram_sphere_tail"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "unitaryPackingNet"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "unitaryPackingNet") "congr_simp"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "unitaryPackingNet_card"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "unitaryPackingNet_covers_operator"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "unitaryPackingNet_covers_sq"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "unitaryPackingNet_separated"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "vectorRankOne_pauliRecord"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "weightedEntropy_strictMonoOn"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "weighted_binomial_floor_entropy_bound"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "weighted_binomial_floor_entropy_bound_termwise"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "weighted_binomial_floor_entropy_bound_termwise") "_simp_1_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "weighted_binomial_floor_entropy_bound_termwise") "_simp_1_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "weighted_binomial_floor_entropy_bound_termwise") "_simp_1_3"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "weighted_binomial_floor_entropy_bound_termwise") "_simp_1_4"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "weighted_binomial_floor_entropy_bound_termwise") "_simp_1_5"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "weighted_binomial_floor_entropy_bound_termwise") "_simp_1_6"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "weighted_binomial_floor_entropy_bound_termwise") "_simp_1_7"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "wickCompletionEquiv"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "wickCompletionEquiv") "_proof_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "wickCompletionEquiv") "_proof_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "wickCompletionEquiv") "_proof_3"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "wickCompletionEquiv") "_proof_4"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "wickCompletionEquiv") "_proof_5"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "wickCompletionEquiv") "_proof_6"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "wickCompletionEquiv_apply"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "wickDeletionPolynomial"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "wickDeletionPolynomial") "congr_simp"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "wickDeletionPolynomial") "eq_1"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "wickDeletionPolynomial_expectation"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "wickTensorCoordinatePermutation"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "wickTensorCoordinatePermutation") "_proof_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "wickTensorCoordinatePermutation") "_proof_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "wickTensorCoordinatePermutation") "eq_1"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "wickTensorMatrix"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "wickTensorMatrix") "eq_1"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "wickTensorMatrix_permutation_trace"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "wickTensorMatrix_weighted_sum_trace"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "wickTensorPermutationMatrix"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "wickTensorPermutationMatrix") "congr_simp"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "wickTensorPermutationMatrix") "eq_1"),
(Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "wickTensorPermutationMatrix_unitary"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "CertificationGaussian") "wickTensorPermutationMatrix_unitary") "_simp_1_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "LocalCertification") "Asymptotic") "EulerMoments") 0) "LocalCertification") "Asymptotic") "EulerMoments") "euler") "match_1") "eq_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "LocalCertification") "Asymptotic") "EulerMoments") 0) "LocalCertification") "Asymptotic") "EulerMoments") "euler") "match_1") "eq_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "LocalCertification") "Asymptotic") "EulerMoments") 0) "LocalCertification") "Asymptotic") "EulerMoments") "euler") "match_1") "splitter"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "LocalCertification") "Asymptotic") "EulerMomentDual") 0) "LocalCertification") "Asymptotic") "EulerMoments") "signed_mul_le_abs"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "LocalCertification") "Certificates") "StagedSearch") 0) "LocalCertification") "Certificates") "stagedArrays") "match_1") "eq_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "LocalCertification") "Certificates") "StagedSearch") 0) "LocalCertification") "Certificates") "stagedArrays") "match_1") "eq_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "LocalCertification") "Certificates") "StagedSearch") 0) "LocalCertification") "Certificates") "stagedArrays") "match_1") "splitter"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "LocalCertification") "Certificates") "StagedSearchConsumers") 0) "LocalCertification") "Certificates") "executableNodeMonomial") "match_1") "eq_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "LocalCertification") "Certificates") "StagedSearchConsumers") 0) "LocalCertification") "Certificates") "executableNodeMonomial") "match_1") "eq_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "LocalCertification") "Certificates") "StagedSearchConsumers") 0) "LocalCertification") "Certificates") "executableNodeMonomial") "match_1") "splitter"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "LocalCertification") "Certificates") "StagedSearchConsumers") 0) "LocalCertification") "Certificates") "canonicalNodeLt") "match_1") "eq_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "LocalCertification") "Certificates") "StagedSearchConsumers") 0) "LocalCertification") "Certificates") "canonicalNodeLt") "match_1") "eq_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "LocalCertification") "Certificates") "StagedSearchConsumers") 0) "LocalCertification") "Certificates") "canonicalNodeLt") "match_1") "eq_3"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "LocalCertification") "Certificates") "StagedSearchConsumers") 0) "LocalCertification") "Certificates") "canonicalNodeLt") "match_1") "splitter"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "LocalCertification") "Certificates") "StagedSearchConsumers") 0) "LocalCertification") "Certificates") "canonicalNodeLt") "match_1") "splitter") "_sparseCasesOn_3"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "LocalCertification") "Certificates") "StagedSearchConsumers") 0) "LocalCertification") "Certificates") "canonicalRawValue") "match_1") "eq_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "LocalCertification") "Certificates") "StagedSearchConsumers") 0) "LocalCertification") "Certificates") "canonicalRawValue") "match_1") "eq_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "LocalCertification") "Certificates") "StagedSearchConsumers") 0) "LocalCertification") "Certificates") "canonicalRawValue") "match_1") "splitter"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "LocalCertification") "Certificates") "CanonicalCertificateConsumers") 0) "LocalCertification") "Certificates") "executableNodeMonomial") "match_1") "eq_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "LocalCertification") "Certificates") "CanonicalCertificateConsumers") 0) "LocalCertification") "Certificates") "executableNodeMonomial") "match_1") "eq_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "LocalCertification") "Certificates") "CanonicalCertificateConsumers") 0) "LocalCertification") "Certificates") "executableNodeMonomial") "match_1") "splitter"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "LocalCertification") "Certificates") "CanonicalCertificateConsumers") 0) "LocalCertification") "Certificates") "canonicalNodeLt") "match_1") "eq_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "LocalCertification") "Certificates") "CanonicalCertificateConsumers") 0) "LocalCertification") "Certificates") "canonicalNodeLt") "match_1") "eq_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "LocalCertification") "Certificates") "CanonicalCertificateConsumers") 0) "LocalCertification") "Certificates") "canonicalNodeLt") "match_1") "eq_3"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "LocalCertification") "Certificates") "CanonicalCertificateConsumers") 0) "LocalCertification") "Certificates") "canonicalNodeLt") "match_1") "splitter"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "LocalCertification") "Certificates") "CanonicalCertificateConsumers") 0) "LocalCertification") "Certificates") "canonicalNodeLt") "match_1") "splitter") "_sparseCasesOn_3"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "LocalCertification") "Certificates") "CanonicalCertificateConsumers") 0) "LocalCertification") "Certificates") "canonicalRawValue") "match_1") "eq_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "LocalCertification") "Certificates") "CanonicalCertificateConsumers") 0) "LocalCertification") "Certificates") "canonicalRawValue") "match_1") "eq_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "LocalCertification") "Certificates") "CanonicalCertificateConsumers") 0) "LocalCertification") "Certificates") "canonicalRawValue") "match_1") "splitter"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "LocalCertification") "Certificates") "CanonicalRawCheck") 0) "LocalCertification") "Certificates") "canonicalNodeLt") "match_1") "eq_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "LocalCertification") "Certificates") "CanonicalRawCheck") 0) "LocalCertification") "Certificates") "canonicalNodeLt") "match_1") "eq_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "LocalCertification") "Certificates") "CanonicalRawCheck") 0) "LocalCertification") "Certificates") "canonicalNodeLt") "match_1") "eq_3"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "LocalCertification") "Certificates") "CanonicalRawCheck") 0) "LocalCertification") "Certificates") "canonicalNodeLt") "match_1") "splitter"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "LocalCertification") "Certificates") "CanonicalRawCheck") 0) "LocalCertification") "Certificates") "canonicalRawValue") "match_1") "eq_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "LocalCertification") "Certificates") "CanonicalRawCheck") 0) "LocalCertification") "Certificates") "canonicalRawValue") "match_1") "eq_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "LocalCertification") "Certificates") "CanonicalRawCheck") 0) "LocalCertification") "Certificates") "canonicalRawValue") "match_1") "splitter"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "LocalCertification") "Information") "ProductDensityChainRule") 0) "LocalCertification") "Information") "prefixProductLikelihood") "match_1") "eq_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "LocalCertification") "Information") "ProductDensityChainRule") 0) "LocalCertification") "Information") "prefixProductLikelihood") "match_1") "eq_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "LocalCertification") "Information") "ProductDensityChainRule") 0) "LocalCertification") "Information") "prefixProductLikelihood") "match_1") "splitter"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "LocalCertification") "Information") "FinitePrefixProductDensity") 0) "LocalCertification") "Information") "SlotHistory") "match_1") "eq_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "LocalCertification") "Information") "FinitePrefixProductDensity") 0) "LocalCertification") "Information") "SlotHistory") "match_1") "eq_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "LocalCertification") "Information") "FinitePrefixProductDensity") 0) "LocalCertification") "Information") "SlotHistory") "match_1") "splitter"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "LocalCertification") "Information") "FinitePrefixProductDensity") 0) "LocalCertification") "Information") "prefixCountingReference") "match_1") "eq_1"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "LocalCertification") "Information") "FinitePrefixProductDensity") 0) "LocalCertification") "Information") "prefixCountingReference") "match_1") "eq_2"),
(Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "LocalCertification") "Information") "FinitePrefixProductDensity") 0) "LocalCertification") "Information") "prefixCountingReference") "match_1") "splitter")
]
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  for n in names do
    unless env.contains n do throwError "Missing audited declaration: {n}"
    let axioms ← collectAxioms n
    let axioms := axioms.qsort Name.quickLt
    unless axioms.all (fun a => allowed.contains a) do
      throwError "Disallowed axiom in {n}: {axioms}"
    logInfo m!"AXIOM_AUDIT\t{(Json.mkObj [("declaration",toJson n.toString),
      ("axioms",toJson (axioms.map toString))]).compress}"
