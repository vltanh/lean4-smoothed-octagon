module

public meta import Lean.Elab.Command
import all Cited.HalesVajjha.CompactDomain
import all SmoothedOctagon
import all SmoothedOctagon.Bridge.Classical
import all SmoothedOctagon.Bridge.Density
import all SmoothedOctagon.Bridge.Octagon
import all SmoothedOctagon.Defs
import all SmoothedOctagon.Equality.Converse
import all SmoothedOctagon.Equality.Frontier
import all SmoothedOctagon.Equality.Transport
import all SmoothedOctagon.Exclusion.Forward
import all SmoothedOctagon.Exclusion.Forward.Budget
import all SmoothedOctagon.Exclusion.Forward.Budget.Concavity
import all SmoothedOctagon.Exclusion.Forward.Cap
import all SmoothedOctagon.Exclusion.Forward.Casimir
import all SmoothedOctagon.Exclusion.Forward.Casimir.Branch
import all SmoothedOctagon.Exclusion.Forward.Casimir.Curvature
import all SmoothedOctagon.Exclusion.Forward.Casimir.Kernels
import all SmoothedOctagon.Exclusion.Forward.Casimir.Shape
import all SmoothedOctagon.Exclusion.Forward.Core
import all SmoothedOctagon.Exclusion.Forward.Edge
import all SmoothedOctagon.Exclusion.Forward.Interface
import all SmoothedOctagon.Exclusion.Forward.Log
import all SmoothedOctagon.Exclusion.Forward.Reduce
import all SmoothedOctagon.Exclusion.Forward.Scalar
import all SmoothedOctagon.Exclusion.Forward.Scalars.Canon
import all SmoothedOctagon.Exclusion.Forward.Scalars.LargerNorm
import all SmoothedOctagon.Exclusion.Forward.Scalars.LargerNorm.Endpoints
import all SmoothedOctagon.Exclusion.Forward.Scalars.Neighbor
import all SmoothedOctagon.Exclusion.Forward.Scalars.Neighbor.Asymmetric
import all SmoothedOctagon.Exclusion.Forward.Scalars.Neighbor.Asymmetric.Endpoints
import all SmoothedOctagon.Exclusion.Forward.Scalars.Neighbor.Asymmetric.Majorant
import all SmoothedOctagon.Exclusion.Forward.Scalars.Neighbor.Asymmetric.Moments
import all SmoothedOctagon.Exclusion.Forward.Scalars.Neighbor.Asymmetric.Row
import all SmoothedOctagon.Exclusion.Forward.Scalars.Neighbor.Asymmetric.Scale
import all SmoothedOctagon.Exclusion.Forward.Scalars.Neighbor.Slope
import all SmoothedOctagon.Exclusion.Forward.Scalars.Neighbor.Value
import all SmoothedOctagon.Exclusion.Forward.Scalars.SmallMin
import all SmoothedOctagon.Exclusion.Forward.Scalars.SumSym
import all SmoothedOctagon.Exclusion.Forward.Scalars.SumSym.Constant
import all SmoothedOctagon.Exclusion.Forward.Scalars.SumSym.Integrals
import all SmoothedOctagon.Exclusion.Forward.Scalars.SumSym.Lower
import all SmoothedOctagon.Exclusion.Forward.Scalars.SumSym.Tangent
import all SmoothedOctagon.Exclusion.Forward.Scalars.SumSym.Upper.Curvature
import all SmoothedOctagon.Exclusion.Forward.Scalars.SumSym.Upper.Sign
import all SmoothedOctagon.Exclusion.Forward.Window
import all SmoothedOctagon.Exclusion.Forward.Wire
import all SmoothedOctagon.Exclusion.MinimumStructure
import all SmoothedOctagon.Exclusion.MinimumStructure.ThreeArc
import all SmoothedOctagon.Exclusion.Mixed
import all SmoothedOctagon.Exclusion.Mixed.CentralScale
import all SmoothedOctagon.Exclusion.Mixed.Centre
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
import all SmoothedOctagon.Exclusion.Mixed.Frames
import all SmoothedOctagon.Exclusion.Mixed.Interface
import all SmoothedOctagon.Exclusion.Mixed.Location
import all SmoothedOctagon.Exclusion.Mixed.Nonshort
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.Bernstein
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.CentreGap
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.Core
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.Bernstein
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.BoundaryRoot
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.Casimir
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.Clearing
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.EventFactor
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.EventFactor.Barrier
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.HighRatio.LowerShape
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.HighRatio.LowerShape.Derivatives
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.HighRatio.LowerShape.TerminalFace
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.HighRatio.Shape
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LargeGap
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowRatio
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowRatio.OrderShapeSigns
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowRatio.UnitShape
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowRatio.UnitShape.Coefficients
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowT.Circuit
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowT.Curvature
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowT.Faces
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowT.Horner
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowT.InitialDerivative
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowT.MaxDuration
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowT.Monomials
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowT.Monotone
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowT.Shape
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowT.UnitShape
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.ResidualAffine
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.Secant
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.SmallGap
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.SmallGap.EnvelopeBound
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.SmallGap.Chi
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.SmallGap.ChiConcavity
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.SmallGap.ChiEndpoint
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.SmallGap.EnvelopeCasimir
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.SmallGap.NormDerivative
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.SwappedSecant
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.Window
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.HighRatio
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.HighRatio.Incoming
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.HighRatio.Quadratic
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.HighRatio.Secant
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.HighRatio.Transport
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.LowScale
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.LowScale.Signs
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.NecessaryBounds
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.OrderFace
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.OrderFace.Boundary
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.Reverse
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.ScaleStrip
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.ScaleStrip.Monotonicity
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.UnitShape
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.UnitShape.Boundary
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.UnitShape.Bounds
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.UnitShape.Coordinates
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.UnitShape.Cubic
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.UnitShape.Jensen
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.UnitShape.Leading
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.UnitShape.Monotonicity
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.UnitShape.Remainder
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.UnitShape.Signs
import all SmoothedOctagon.Exclusion.Mixed.Nonshort.UnitShape.Slope
import all SmoothedOctagon.Exclusion.Mixed.OrderBounds
import all SmoothedOctagon.Exclusion.Mixed.PolyDeriv
import all SmoothedOctagon.Exclusion.Mixed.Reflection
import all SmoothedOctagon.Exclusion.Mixed.Residual
import all SmoothedOctagon.Exclusion.Mixed.RootCurve
import all SmoothedOctagon.Exclusion.Mixed.Scalar
import all SmoothedOctagon.Exclusion.Mixed.SmallForwardMinimum
import all SmoothedOctagon.Exclusion.Mixed.SmallMin.Scalar
import all SmoothedOctagon.Exclusion.Mixed.SmallMin.Window
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Basic
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.CasimirFloor
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.CasimirFloor.ClosedForms
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.CasimirFloor.Defs
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.CasimirFloor.Endpoints
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.CasimirFloor.FloorBox
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.CasimirFloor.Norm
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.CasimirFloor.PhiDisplacement
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.CasimirFloor.PhiDisplacement.OtherPartials
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.CasimirFloor.PhiDisplacement.Partials
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.CasimirFloor.PhiDisplacement.ShapeDerivative
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.CasimirFloor.PhiDisplacement.ShapeSource
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.CasimirFloor.PhiRatio
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.CasimirFloor.PhiRatio.CasimirSlope
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.CasimirFloor.PhiRatio.NormMotion
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.CasimirFloor.PhiRatio.Numerator
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.CasimirFloor.PhiShape
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.CasimirFloor.PsiRatio
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.CasimirFloor.PsiRatio.CasimirPart
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.CasimirFloor.PsiRatio.IncomingNorm
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.CasimirFloor.PsiRatio.LowerNorm
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.CasimirFloor.PsiRatio.NormCoefficient
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.CasimirFloor.PsiRatio.Numerator
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.CasimirFloor.PsiShape
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.CasimirFloor.PsiShape.Coefficients
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.CasimirFloor.PsiShape.Numerator
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.CasimirFloor.PsiShape.Shifted
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.CasimirFloor.ShapeCurve
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.CasimirFloor.TerminalConcavity
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.CasimirFloor.TerminalConcavity.Jets
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.Angle
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.AngleCancellation
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.CentralShear
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.Continuation
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.Defs
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.Endpoint
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.ExactConcavity
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.ExactScore
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.ExactShape
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.FinalScore.Angles
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.FinalScore.Basic
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.FinalScore.Displacement
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.FinalScore.Pair
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.FinalScore.RConcavity
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.FinalScore.RConcavity.Anisotropy
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.FinalScore.RConcavity.Basic
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.FinalScore.RConcavity.Pair
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.FinalScore.RConcavity.Shear
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.RationalKernel
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.VarianceFloor
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Displacement
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Displacement.CentralFace
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Displacement.CentralFace.Endpoint
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Displacement.CentralFace.ShapeDerivative
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Displacement.Faces
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Displacement.OuterFace
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Displacement.OuterFace.Convexity
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Displacement.OuterFace.Decomposition
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Displacement.OuterFace.LowerCurveSigns
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Displacement.OuterFace.LowerCurves
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Displacement.OuterFace.LowerShape
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Displacement.OuterFace.MiddleShape
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Displacement.OuterFace.UpperShape
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Displacement.TauTwo
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Displacement.ZeroScale
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Envelope
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Envelope.Cap
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Envelope.CapData
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Envelope.CasimirScale
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Envelope.NormEndpoint
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.FaceValue
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Interface
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Jets
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.CentralFace
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.CentralFace.LowerFace
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.CentralFace.MaxDuration1
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.CentralFace.MaxDuration2
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.CentralFace.NearMaxDuration1
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.CentralFace.NearMaxDuration2
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.CentralFace.TauTwo1
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.CentralFace.TauTwo2
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.CentralFace.Tests
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.FaceSigns
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.OuterFace
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.OuterFace.LargeShape
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.OuterFace.MaxDuration1
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.OuterFace.MaxDuration2
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.OuterFace.NearMaxDuration1
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.OuterFace.NearMaxDuration2
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.OuterFace.Strip
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.OuterFace.TauTwo1
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.OuterFace.TauTwo2
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.SignTools
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.CentralFace
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.CentralFace.Beta
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.CentralFace.LowRatio
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.CentralFace.MonotonicityBounds
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.CentralFace.NormBeta
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.CentralFace.Partials
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.CentralFace.PathDerivative
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.CentralFace.Shape1
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.CentralFace.Shape2
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.CentralFace.Shape3
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.DerivativeRatio
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.FaceFunctions
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.OuterFace
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.OuterFace.BetaSum
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.OuterFace.Functions
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.OuterFace.LargeShape.TestOne
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.OuterFace.LargeShape.TestZero
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.OuterFace.PathDerivative
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.OuterFace.RationalForms
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.OuterFace.ReciprocalShape
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.OuterFace.Shapes
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.OuterFace.SmallRatio
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.OuterFace.SmallRatio.NormBeta
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.OuterFace.SmallShape.TestOne
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.OuterFace.SmallShape.TestZero1
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.OuterFace.SmallShape.TestZero2
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.OuterFace.SmallShape.TestZero3
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.OuterFace.SmallShape.TestZeroSigns
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.Tools
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Order
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Order.Barrier
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Order.Contacts
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Order.Quadratic
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Order.SmallUpper
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Order.Strong
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Order.Upper
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Point
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.ReverseScale
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Shear
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Shear.Duration
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Shear.Geometry
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Shear.Residual
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Shear.Shape
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Shear.Shape.Defs
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Shear.Shape.J
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Shear.Shape.TConcavity
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Shear.Shape.TEndpoint
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Shear.Sign
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.UpperRatio
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.UpperRatio.CentralFace
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.UpperRatio.CentralFace.Beta
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.UpperRatio.CentralFace.Beta.BaseFace
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.UpperRatio.CentralFace.Beta.Coefficients
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.UpperRatio.CentralFace.Beta.PartialFractions
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.UpperRatio.CentralFace.Defs
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.UpperRatio.CentralFace.Ratio
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.UpperRatio.CentralFace.Ratio.ChainRule
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.UpperRatio.CentralFace.Ratio.Defs
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.UpperRatio.CentralFace.Ratio.Norm
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.UpperRatio.CentralFace.Ratio.Signs
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.UpperRatio.CentralFace.Terminal
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.UpperRatio.CentralFace.Terminal.Numerators
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.UpperRatio.Defs
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.UpperRatio.OuterFace.LargeShape
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.UpperRatio.OuterFace.LowerTerminal
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.UpperRatio.OuterFace.LowerTerminal.Components
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.UpperRatio.OuterFace.LowerTerminal.Defs
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.UpperRatio.OuterFace.Reciprocal
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.UpperRatio.OuterFace.Reciprocal.Defs
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.UpperRatio.OuterFace.Reciprocal.Polynomials
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.UpperRatio.OuterFace.SmallShape
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.UpperRatio.OuterFace.SmallShape.Norm
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.UpperRatio.OuterFace.SmallShape.Terminal
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.UpperRatio.Reductions
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Window.Ceiling
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Window.Centre
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Window.Covector
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Window.Cover
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Window.Gap
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Window.LogSecant
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Window.Mean
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Window.Order
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Window.Residual
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort.Window.Secant
import all SmoothedOctagon.Exclusion.Mixed.TurnSecant
import all SmoothedOctagon.Exclusion.Mixed.WeightedLog
import all SmoothedOctagon.Exclusion.Mixed.Window
import all SmoothedOctagon.Exclusion.Mixed.WindowData
import all SmoothedOctagon.Exclusion.Mixed.Wire
import all SmoothedOctagon.Exclusion.Reverse
import all SmoothedOctagon.Exclusion.Reverse.Four
import all SmoothedOctagon.Exclusion.ShortRuns
import all SmoothedOctagon.Exclusion.ShortRuns.Centre
import all SmoothedOctagon.Exclusion.ShortRuns.Gap.Core
import all SmoothedOctagon.Exclusion.ShortRuns.Gap.Log
import all SmoothedOctagon.Exclusion.ShortRuns.Gap.SymmetricRoot
import all SmoothedOctagon.Exclusion.ShortRuns.Pattern
import all SmoothedOctagon.Exclusion.ShortRuns.Scalar
import all SmoothedOctagon.Exclusion.ShortRuns.TwoCentre
import all SmoothedOctagon.Exclusion.ShortRuns.Wind.Angle
import all SmoothedOctagon.Exclusion.ShortRuns.Wind.Frame
import all SmoothedOctagon.Exclusion.ShortRuns.Wind.Kappa
import all SmoothedOctagon.Exclusion.ShortRuns.Wind.Main
import all SmoothedOctagon.Exclusion.ShortRuns.Wind.Polar
import all SmoothedOctagon.Exclusion.ShortRuns.Winding
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
import all SmoothedOctagon.Foundations.IntervalBounds
import all SmoothedOctagon.Foundations.LowCostWinding
import all SmoothedOctagon.Foundations.Normalization
import all SmoothedOctagon.Foundations.Problem
import all SmoothedOctagon.Foundations.RadialRegularity
import all SmoothedOctagon.Foundations.ReciprocalMidpoint
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
import all SmoothedOctagon.Period.OctagonCost
import all SmoothedOctagon.Period.OctagonCost.LogMoment
import all SmoothedOctagon.Period.OctagonCost.PiMoment
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
import all SmoothedOctagon.Tactic.Deriv
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
