module

public meta import Lean.Elab.Command
import all Cited.HalesVajjha.CompactDomain
import all SmoothedOctagon
import all SmoothedOctagon.Bridge.Classical
import all SmoothedOctagon.Bridge.Density
import all SmoothedOctagon.Bridge.Octagon
import all SmoothedOctagon.Certificates.SmallerShort
import all SmoothedOctagon.Defs
import all SmoothedOctagon.Equality.Converse
import all SmoothedOctagon.Equality.Frontier
import all SmoothedOctagon.Equality.Transport
import all SmoothedOctagon.Exclusion.Forward
import all SmoothedOctagon.Exclusion.Forward.Budget
import all SmoothedOctagon.Exclusion.Forward.Cap
import all SmoothedOctagon.Exclusion.Forward.Casimir
import all SmoothedOctagon.Exclusion.Forward.Core
import all SmoothedOctagon.Exclusion.Forward.Edge
import all SmoothedOctagon.Exclusion.Forward.Interface
import all SmoothedOctagon.Exclusion.Forward.Log
import all SmoothedOctagon.Exclusion.Forward.Reduce
import all SmoothedOctagon.Exclusion.Forward.Scalar
import all SmoothedOctagon.Exclusion.Forward.Scalars.Canon
import all SmoothedOctagon.Exclusion.Forward.Scalars.LargerNorm
import all SmoothedOctagon.Exclusion.Forward.Scalars.Neighbor
import all SmoothedOctagon.Exclusion.Forward.Scalars.SmallMin
import all SmoothedOctagon.Exclusion.Forward.Scalars.SumSym
import all SmoothedOctagon.Exclusion.Forward.Window
import all SmoothedOctagon.Exclusion.Forward.Wire
import all SmoothedOctagon.Exclusion.Minimum.ThreeArc
import all SmoothedOctagon.Exclusion.MinimumStructure
import all SmoothedOctagon.Exclusion.Mixed.Centre
import all SmoothedOctagon.Exclusion.Mixed.ChartAux.Root
import all SmoothedOctagon.Exclusion.Mixed.Comparison
import all SmoothedOctagon.Exclusion.Mixed.Defect.Algebra
import all SmoothedOctagon.Exclusion.Mixed.Defect.Angle
import all SmoothedOctagon.Exclusion.Mixed.Defect.Field
import all SmoothedOctagon.Exclusion.Mixed.Defect.Frame
import all SmoothedOctagon.Exclusion.Mixed.Defect.Window
import all SmoothedOctagon.Exclusion.Mixed.Density.Bound
import all SmoothedOctagon.Exclusion.Mixed.Density.Local
import all SmoothedOctagon.Exclusion.Mixed.Density.Winding
import all SmoothedOctagon.Exclusion.Mixed.Extract.Compact
import all SmoothedOctagon.Exclusion.Mixed.Extract.Reflect
import all SmoothedOctagon.Exclusion.Mixed.Extract.Reverse
import all SmoothedOctagon.Exclusion.Mixed.Extract.Transport
import all SmoothedOctagon.Exclusion.Mixed.Extract.WindowAlg
import all SmoothedOctagon.Exclusion.Mixed.Extraction
import all SmoothedOctagon.Exclusion.Mixed.ForwardHand
import all SmoothedOctagon.Exclusion.Mixed.Frames
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.Basic
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.Bern
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.Bern2
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.Casimir
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.CertChi
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.CertEn
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.CertLRb
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.CertPn
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.CertQC
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.CertQD
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.Chi
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.Clear
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.Coef
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.Envelope
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.HighRatioLower
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.HighRatioLowerBounds
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.HighRatioLowerFace
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.HighRatioShape
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.LargeGap
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.LowRatio
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.LowRatioHand
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.LowRatioHandSigns
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.LowTCircuit
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.LowTCurv
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.LowTFaces
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.LowTHRed
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.LowTHorner
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.LowTInit
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.LowTQmax
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.LowTShape
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.LowTTools
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.LowTUnit
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.PolyDeriv
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.QElim
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.Secant
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.SmallGap
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.Swap
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.Window
import all SmoothedOctagon.Exclusion.Mixed.Hand.Basic
import all SmoothedOctagon.Exclusion.Mixed.Hand.Bern
import all SmoothedOctagon.Exclusion.Mixed.Hand.CertHighT
import all SmoothedOctagon.Exclusion.Mixed.Hand.CertLow
import all SmoothedOctagon.Exclusion.Mixed.Hand.CertOrder
import all SmoothedOctagon.Exclusion.Mixed.Hand.CertStrip
import all SmoothedOctagon.Exclusion.Mixed.Hand.CertUnit
import all SmoothedOctagon.Exclusion.Mixed.Hand.Gap
import all SmoothedOctagon.Exclusion.Mixed.Hand.HighT
import all SmoothedOctagon.Exclusion.Mixed.Hand.Link
import all SmoothedOctagon.Exclusion.Mixed.Hand.Low
import all SmoothedOctagon.Exclusion.Mixed.Hand.Order
import all SmoothedOctagon.Exclusion.Mixed.Hand.OrderFace
import all SmoothedOctagon.Exclusion.Mixed.Hand.Prereq
import all SmoothedOctagon.Exclusion.Mixed.Hand.ReverseCore
import all SmoothedOctagon.Exclusion.Mixed.Hand.Scale
import all SmoothedOctagon.Exclusion.Mixed.Hand.Secant
import all SmoothedOctagon.Exclusion.Mixed.Hand.Strip
import all SmoothedOctagon.Exclusion.Mixed.Hand.Unit
import all SmoothedOctagon.Exclusion.Mixed.Interface
import all SmoothedOctagon.Exclusion.Mixed.Location
import all SmoothedOctagon.Exclusion.Mixed.LowScaleHand
import all SmoothedOctagon.Exclusion.Mixed.NonshortScalar
import all SmoothedOctagon.Exclusion.Mixed.Reflection
import all SmoothedOctagon.Exclusion.Mixed.ReverseHand
import all SmoothedOctagon.Exclusion.Mixed.Scalar
import all SmoothedOctagon.Exclusion.Mixed.Short.Calc
import all SmoothedOctagon.Exclusion.Mixed.Short.Centre
import all SmoothedOctagon.Exclusion.Mixed.Short.Cover
import all SmoothedOctagon.Exclusion.Mixed.Short.Order
import all SmoothedOctagon.Exclusion.Mixed.Short.Point
import all SmoothedOctagon.Exclusion.Mixed.Short.Residual
import all SmoothedOctagon.Exclusion.Mixed.Short.Window
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Assembly
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Basic
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Envelope
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0Bern
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0C2
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0C8
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0CT
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0Faces
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0O2
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0O2Cert
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0O8
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0O8Cert
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0OT
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0OTCert
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1Base
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1CAux
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1CClaimA
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1CClaimB
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1CClaimU
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1CClaimX
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1CDefs
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1CDeriv
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1CSteps
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1CUni
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1Central
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1OClaimB1
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1OClaimB2
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1OClaimF
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1OClaimS
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1OClaimW1
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1OClaimW2
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1OConc
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1OCurv0
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1OCurv1
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1OCurv2
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1OCurv3
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1ODefs
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1ODeriv
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1ORep
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1OSteps
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1OUni
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1Outer
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1Tw
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2Bern
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2CenL0
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2CenL0a
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2CenL1
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2CenL1a
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2CenL2
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2CenL2a
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2CenL3
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2CenL3a
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2CenL4
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2CenL4a
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2CenLinkA
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2CenLinkD
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2CenLinkG
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2CenPoly
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2CenStage
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2Central
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2Face
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2Large
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2LargeCertA
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2LargeCertB
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2Small
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2SmallCertA0
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2SmallCertA1
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2SmallCertB
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2SmallLinkA
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2SmallLinkB
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2SmallPolyA
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2SmallShift
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S3Base
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S3Central
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S3CentralA0
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S3CentralA1
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S3CentralB0
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S3CentralB1
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S3Outer
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S3OuterA0
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S3OuterA1
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S3OuterB0a
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S3OuterB0b
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S3OuterB0c
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S3OuterB0d
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S3OuterB1a
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S3OuterB1b
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S3OuterB1c
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4Bern
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4Beta
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4Beta1
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4Beta2
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4Closed
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4Face
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4IdPhiA
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4IdPhiB
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4IdPsiA
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4IdPsiB
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4PosPhiA
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4PosPhiB
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4PosPsiA
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4PosPsiB
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4Surr
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S6
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S6Bern
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S6Id135
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S6Id3
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S6Link
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S6Pos135
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S6Pos3
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Hs02.Common
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Hs14.Basic
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Hs14.Cap
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Hs14.Data
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Hs14.Ratio
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Hs14.Slope
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Hs35.Central
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Hs35.Cont
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Hs35.Zero
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Hs6.Angle
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Hs6.Concave
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Hs6.Shear
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Hso.Barrier
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Hso.Poly
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Interface
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Order
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.S0
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.S1
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.S2
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.S2Defs
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.S3
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.S3Leaves
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.S4
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.S4Defs
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.S5
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.S6
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.S6Defs
import all SmoothedOctagon.Exclusion.Mixed.SmallForwardMinimum
import all SmoothedOctagon.Exclusion.Mixed.SmallMin.Scalar
import all SmoothedOctagon.Exclusion.Mixed.SmallMin.Window
import all SmoothedOctagon.Exclusion.Mixed.Window
import all SmoothedOctagon.Exclusion.Mixed.Wire
import all SmoothedOctagon.Exclusion.Nonshort
import all SmoothedOctagon.Exclusion.Reverse
import all SmoothedOctagon.Exclusion.Reverse.Four
import all SmoothedOctagon.Exclusion.ShortRun.Centre
import all SmoothedOctagon.Exclusion.ShortRun.Gap.Core
import all SmoothedOctagon.Exclusion.ShortRun.Gap.Log
import all SmoothedOctagon.Exclusion.ShortRun.Pattern
import all SmoothedOctagon.Exclusion.ShortRun.Scalar
import all SmoothedOctagon.Exclusion.ShortRun.TwoCentre
import all SmoothedOctagon.Exclusion.ShortRun.Wind.Angle
import all SmoothedOctagon.Exclusion.ShortRun.Wind.Frame
import all SmoothedOctagon.Exclusion.ShortRun.Wind.Kappa
import all SmoothedOctagon.Exclusion.ShortRun.Wind.Main
import all SmoothedOctagon.Exclusion.ShortRun.Wind.Polar
import all SmoothedOctagon.Exclusion.ShortRun.Winding
import all SmoothedOctagon.Exclusion.ShortRuns
import all SmoothedOctagon.Foundations.AdmissibleRealization
import all SmoothedOctagon.Foundations.AdmissibleRegularity
import all SmoothedOctagon.Foundations.ArcLength
import all SmoothedOctagon.Foundations.BalancedClock
import all SmoothedOctagon.Foundations.BalancedReduction
import all SmoothedOctagon.Foundations.BalancedTargets
import all SmoothedOctagon.Foundations.BoundaryTrace
import all SmoothedOctagon.Foundations.CircleExclusion
import all SmoothedOctagon.Foundations.ContactLift
import all SmoothedOctagon.Foundations.ControlBounds
import all SmoothedOctagon.Foundations.ControlTrajectory
import all SmoothedOctagon.Foundations.CyclicClock
import all SmoothedOctagon.Foundations.CyclicExtension
import all SmoothedOctagon.Foundations.DeterminantClock
import all SmoothedOctagon.Foundations.LowCostWinding
import all SmoothedOctagon.Foundations.Normalization
import all SmoothedOctagon.Foundations.Problem
import all SmoothedOctagon.Foundations.RadialRegularity
import all SmoothedOctagon.Foundations.ReverseComparison
import all SmoothedOctagon.Foundations.ReverseGeometry
import all SmoothedOctagon.Foundations.SingularArc
import all SmoothedOctagon.Foundations.SingularLocus
import all SmoothedOctagon.Foundations.StrongSwitching
import all SmoothedOctagon.Foundations.SupportNormal
import all SmoothedOctagon.Foundations.SwitchingMargin
import all SmoothedOctagon.LowerBound
import all SmoothedOctagon.Main
import all SmoothedOctagon.Period.Costate
import all SmoothedOctagon.Period.Defs
import all SmoothedOctagon.Period.Elliptic
import all SmoothedOctagon.Period.Hamiltonian
import all SmoothedOctagon.Period.Partition
import all SmoothedOctagon.Period.Twist
import all SmoothedOctagon.Period.VertexFlow
import all SmoothedOctagon.Reduction.Clearance.Algebra
import all SmoothedOctagon.Reduction.Clearance.Budget
import all SmoothedOctagon.Reduction.Clearance.Frame
import all SmoothedOctagon.Reduction.Clearance.Winding
import all SmoothedOctagon.Reduction.CompactDomain
import all SmoothedOctagon.Reduction.Defs
import all SmoothedOctagon.Reduction.Edge.BangBang
import all SmoothedOctagon.Reduction.Edge.Calculus
import all SmoothedOctagon.Reduction.Edge.Minimizer
import all SmoothedOctagon.Reduction.Edge.Splice
import all SmoothedOctagon.Reduction.Edge.System
import all SmoothedOctagon.Reduction.EdgeBound
import all SmoothedOctagon.Reduction.FiniteNormal
import all SmoothedOctagon.Reduction.Normal.Bridge
import all SmoothedOctagon.Reduction.Normal.Flow
import all SmoothedOctagon.Reduction.Normal.Word
import all SmoothedOctagon.Reduction.Normality
import all SmoothedOctagon.Reduction.Rebase
import all SmoothedOctagon.Reduction.SingularClearance
import all SmoothedOctagon.Reduction.Switch.Glue
import all SmoothedOctagon.Reduction.Switch.Local
import all SmoothedOctagon.Reduction.SwitchCount
import all SmoothedOctagon.Reduction.WordReduction
import all SmoothedOctagon.Terminal.Analysis.FiveEnvelope
import all SmoothedOctagon.Terminal.Analysis.FourDensity
import all SmoothedOctagon.Terminal.Analysis.LogBounds
import all SmoothedOctagon.Terminal.Comparison
import all SmoothedOctagon.Terminal.Cycle
import all SmoothedOctagon.Terminal.FivePiece
import all SmoothedOctagon.Terminal.FourPiece
import all SmoothedOctagon.Terminal.Identification
import all SmoothedOctagon.Terminal.Words
import all ReinhardtSolution

/-!
# Axiom audit

Run with `lake env lean scripts/Audit.lean` after `lake build` (regenerate the imports first with
`python3 scripts/gen_audit.py`). Every module of the libraries is imported with `import all`, so
that the proofs are visible. The audit prints the axioms of the theorems of `ReinhardtSolution.lean` (the
statements of `ReinhardtChallenge.lean`) and fails if any declaration of the libraries, or any of those
theorems, depends on an axiom other than Lean's standard `propext`, `Classical.choice` and
`Quot.sound` (a `sorry` would show up as `sorryAx`).
-/

open Lean Elab Command

namespace Audit

/-- The theorems that Palomar's comparator checks (`theorem_names` of `comparator.json`). -/
meta def solutionResults : List Name :=
  [``ReinhardtChallenge.octagon_density, ``ReinhardtChallenge.reinhardt,
   ``ReinhardtChallenge.reinhardt_equality]

/-- Lean's standard axioms. -/
meta def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Whether `m` is a module of the project's libraries. -/
meta def isLibraryModule (m : Name) : Bool :=
  (`SmoothedOctagon).isPrefixOf m || (`Cited).isPrefixOf m || m == `ReinhardtSolution

elab "#audit" : command => do
  let env ← getEnv
  let mut bad : Array (Name × Array Name) := #[]
  let mut count : Nat := 0
  for m in env.header.moduleNames, d in env.header.moduleData do
    if isLibraryModule m then
      for c in d.constNames do
        if c.isInternal then continue
        count := count + 1
        let axs ← liftCoreM <| collectAxioms c
        let extra := axs.filter (fun a => !standardAxioms.contains a)
        if !extra.isEmpty then bad := bad.push (c, extra)
  for t in solutionResults do
    let axs ← liftCoreM <| collectAxioms t
    logInfo m!"{t}: {axs}"
    let extra := axs.filter (fun a => !standardAxioms.contains a)
    if !extra.isEmpty then bad := bad.push (t, extra)
  if bad.isEmpty then
    logInfo m!"audit: {count} declarations of the libraries depend only on the standard axioms"
  else
    for (c, e) in bad.toList.take 50 do logError m!"{c} depends on {e}"
    throwError m!"audit failed: {bad.size} declarations use non-standard axioms"

end Audit

#audit
