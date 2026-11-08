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
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0Hand
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0HandCen
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0HandCen2a
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0HandCen2b
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0HandCen8a
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0HandCen8b
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0HandCenFin
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0HandCenLow
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0HandCenTa
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0HandCenTb
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0HandOut
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0HandOutF2a
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0HandOutF2b
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0HandOutF8a
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0HandOutF8b
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0HandOutFTa
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0HandOutFTb
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0HandOutL
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0HandOutS
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0HandTools
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1Base
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1CAux
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1CDefs
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1CDeriv
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1HandBase
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1HandBeta
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1HandC1
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1HandC2
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1HandC3
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1HandC3b
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1HandC4
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1HandC5
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1HandCentral
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1HandExpl
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1HandOA1
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1HandOA2
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1HandOA3
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1HandOB1
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1HandOB2
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1HandOB3
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1HandOB4
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1HandOB5
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1HandOS1
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1HandOS2
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1HandOuter
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1HandRecip
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1ODefs
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1ODeriv
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2HandBase
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2HandCenBeta
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2HandCenBetaCoef
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2HandCenBetaDefs
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2HandCenBetaEdge
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2HandCenDefs
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2HandCenTerm
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2HandCenTermPoly
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2HandCenX
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2HandCenXDefs
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2HandCenXDeriv
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2HandCenXNorm
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2HandCenXSign
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2HandCentral
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2HandLarge
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2HandRecip
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2HandRecipDefs
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2HandRecipPoly
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2HandSmall
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2HandSmallLink
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2HandSmallNorm
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2HandTerm
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2HandTermDefs
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2HandTermPoly
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S3HandCDeriv
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S3HandCentral
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S3HandOCurv
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S3HandODefs
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S3HandOLowC
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S3HandOLowX
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S3HandOLowY
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S3HandOMid
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S3HandOUp
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S3HandOuter
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4Closed
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4Hand
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4HandDefs
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4HandEnd
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4HandW1
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4HandW1a
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4HandW1b
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4HandW1c
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4HandW1d
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4HandW2
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4HandW2a
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4HandW2b
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4HandW2c
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4HandW3
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4HandW3a
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4HandW3b
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4HandW3c
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4HandW3d
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4HandW3e
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4HandW4
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4HandW4a
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4HandW4b
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4HandW4c
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4HandW5
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4HandW6
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4HandW6a
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S6Hand
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S6HandD
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S6HandJet
import all SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S6HandR
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

/-!
# Axiom audit

Run with `lake env lean scripts/Audit.lean` after `lake build` (regenerate the imports first with
`python3 scripts/gen_audit.py`). Every module of the libraries is imported with `import all`, so
that the proofs are visible. The audit prints the axioms of the theorems of `SmoothedOctagon.lean` (the
statements of `Palomar/Challenge.lean`) and fails if any declaration of the libraries, or any of those
theorems, depends on an axiom other than Lean's standard `propext`, `Classical.choice` and
`Quot.sound` (a `sorry` would show up as `sorryAx`).
-/

open Lean Elab Command

namespace Audit

/-- The theorems that Palomar's comparator checks (`theorem_names` of `Palomar/comparator.json`). -/
meta def solutionResults : List Name :=
  [``ReinhardtChallenge.octagon_density, ``ReinhardtChallenge.reinhardt,
   ``ReinhardtChallenge.reinhardt_equality]

/-- Lean's standard axioms. -/
meta def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Whether `m` is a module of the project's libraries. -/
meta def isLibraryModule (m : Name) : Bool :=
  (`SmoothedOctagon).isPrefixOf m || (`Cited).isPrefixOf m

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
