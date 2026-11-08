module

public meta import Lean.Elab.Command
import all Cited.HalesVajjha.CompactDomain
import all SmoothedOctagon
import all SmoothedOctagon.Bridge.Density
import all SmoothedOctagon.Bridge.Octagon
import all SmoothedOctagon.Certificates.Covers
import all SmoothedOctagon.Certificates.Nonshort
import all SmoothedOctagon.Certificates.SmallerShort
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
import all SmoothedOctagon.Exclusion.Mixed.Chart
import all SmoothedOctagon.Exclusion.Mixed.ChartAux.Gap
import all SmoothedOctagon.Exclusion.Mixed.ChartAux.Phi
import all SmoothedOctagon.Exclusion.Mixed.ChartAux.Point
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
import all SmoothedOctagon.Exclusion.Mixed.ForwardEndpoint
import all SmoothedOctagon.Exclusion.Mixed.ForwardHand
import all SmoothedOctagon.Exclusion.Mixed.Frames
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.Basic
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.Bern
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.Bern2
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.Casimir
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.CertChi
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.CertEn
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.CertLGa
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.CertLGa.Part1
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.CertLGa.Part2
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.CertLGa.Part3
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.CertLGa.Part4
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.CertLGa.Part5
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.CertLGb
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.CertLGb.Part1
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.CertLGb.Part2
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.CertLGc
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.CertLGc.Part1
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.CertLGd
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.CertLGd.Part1
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.CertLRa
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.CertLRa.Part1
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.CertLRa.Part2
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.CertLRa.Part3
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.CertLRb
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.CertPn
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.CertQC
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.CertQD
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.Chi
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.Clear
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.Coef
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.Envelope
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.LargeGap
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.LargeGapLink
import all SmoothedOctagon.Exclusion.Mixed.FwdHand.LowRatio
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
import all SmoothedOctagon.Exclusion.Mixed.SmallForwardMinimum
import all SmoothedOctagon.Exclusion.Mixed.SmallMin.Scalar
import all SmoothedOctagon.Exclusion.Mixed.SmallMin.Window
import all SmoothedOctagon.Exclusion.Mixed.SmallerShort
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
import all SmoothedOctagon.Interval.Check
import all SmoothedOctagon.Interval.Expr
import all SmoothedOctagon.Interval.Ival
import all SmoothedOctagon.Interval.SmallerShort
import all SmoothedOctagon.Interval.SmallerShort.C000
import all SmoothedOctagon.Interval.SmallerShort.C001
import all SmoothedOctagon.Interval.SmallerShort.C002
import all SmoothedOctagon.Interval.SmallerShort.C003
import all SmoothedOctagon.Interval.SmallerShort.C004
import all SmoothedOctagon.Interval.SmallerShort.C005
import all SmoothedOctagon.Interval.SmallerShort.C006
import all SmoothedOctagon.Interval.SmallerShort.C007
import all SmoothedOctagon.Interval.SmallerShort.C008
import all SmoothedOctagon.Interval.SmallerShort.C009
import all SmoothedOctagon.Interval.SmallerShort.C010
import all SmoothedOctagon.Interval.SmallerShort.C011
import all SmoothedOctagon.Interval.SmallerShort.C012
import all SmoothedOctagon.Interval.SmallerShort.C013
import all SmoothedOctagon.Interval.SmallerShort.C014
import all SmoothedOctagon.Interval.SmallerShort.C015
import all SmoothedOctagon.Interval.SmallerShort.C016
import all SmoothedOctagon.Interval.SmallerShort.C017
import all SmoothedOctagon.Interval.SmallerShort.C018
import all SmoothedOctagon.Interval.SmallerShort.C019
import all SmoothedOctagon.Interval.SmallerShort.C020
import all SmoothedOctagon.Interval.SmallerShort.C021
import all SmoothedOctagon.Interval.SmallerShort.C022
import all SmoothedOctagon.Interval.SmallerShort.C023
import all SmoothedOctagon.Interval.SmallerShort.C024
import all SmoothedOctagon.Interval.SmallerShort.C025
import all SmoothedOctagon.Interval.SmallerShort.C026
import all SmoothedOctagon.Interval.SmallerShort.C027
import all SmoothedOctagon.Interval.SmallerShort.C028
import all SmoothedOctagon.Interval.SmallerShort.C029
import all SmoothedOctagon.Interval.SmallerShort.C030
import all SmoothedOctagon.Interval.SmallerShort.C031
import all SmoothedOctagon.Interval.SmallerShort.C032
import all SmoothedOctagon.Interval.SmallerShort.C033
import all SmoothedOctagon.Interval.SmallerShort.C034
import all SmoothedOctagon.Interval.SmallerShort.C035
import all SmoothedOctagon.Interval.SmallerShort.C036
import all SmoothedOctagon.Interval.SmallerShort.C037
import all SmoothedOctagon.Interval.SmallerShort.C038
import all SmoothedOctagon.Interval.SmallerShort.C039
import all SmoothedOctagon.Interval.SmallerShort.C040
import all SmoothedOctagon.Interval.SmallerShort.C041
import all SmoothedOctagon.Interval.SmallerShort.C042
import all SmoothedOctagon.Interval.SmallerShort.C043
import all SmoothedOctagon.Interval.SmallerShort.C044
import all SmoothedOctagon.Interval.SmallerShort.C045
import all SmoothedOctagon.Interval.SmallerShort.C046
import all SmoothedOctagon.Interval.SmallerShort.C047
import all SmoothedOctagon.Interval.SmallerShort.C048
import all SmoothedOctagon.Interval.SmallerShort.C049
import all SmoothedOctagon.Interval.SmallerShort.C050
import all SmoothedOctagon.Interval.SmallerShort.C051
import all SmoothedOctagon.Interval.SmallerShort.C052
import all SmoothedOctagon.Interval.SmallerShort.C053
import all SmoothedOctagon.Interval.SmallerShort.C054
import all SmoothedOctagon.Interval.SmallerShort.C055
import all SmoothedOctagon.Interval.SmallerShort.C056
import all SmoothedOctagon.Interval.SmallerShort.C057
import all SmoothedOctagon.Interval.SmallerShort.C058
import all SmoothedOctagon.Interval.SmallerShort.C059
import all SmoothedOctagon.Interval.SmallerShort.C060
import all SmoothedOctagon.Interval.SmallerShort.C061
import all SmoothedOctagon.Interval.SmallerShort.C062
import all SmoothedOctagon.Interval.SmallerShort.C063
import all SmoothedOctagon.Interval.SmallerShort.C064
import all SmoothedOctagon.Interval.SmallerShort.C065
import all SmoothedOctagon.Interval.SmallerShort.C066
import all SmoothedOctagon.Interval.SmallerShort.C067
import all SmoothedOctagon.Interval.SmallerShort.C068
import all SmoothedOctagon.Interval.SmallerShort.C069
import all SmoothedOctagon.Interval.SmallerShort.C070
import all SmoothedOctagon.Interval.SmallerShort.C071
import all SmoothedOctagon.Interval.SmallerShort.C072
import all SmoothedOctagon.Interval.SmallerShort.C073
import all SmoothedOctagon.Interval.SmallerShort.C074
import all SmoothedOctagon.Interval.SmallerShort.C075
import all SmoothedOctagon.Interval.SmallerShort.C076
import all SmoothedOctagon.Interval.SmallerShort.C077
import all SmoothedOctagon.Interval.SmallerShort.C078
import all SmoothedOctagon.Interval.SmallerShort.C079
import all SmoothedOctagon.Interval.SmallerShort.C080
import all SmoothedOctagon.Interval.SmallerShort.C081
import all SmoothedOctagon.Interval.SmallerShort.C082
import all SmoothedOctagon.Interval.SmallerShort.C083
import all SmoothedOctagon.Interval.SmallerShort.C084
import all SmoothedOctagon.Interval.SmallerShort.C085
import all SmoothedOctagon.Interval.SmallerShort.C086
import all SmoothedOctagon.Interval.SmallerShort.C087
import all SmoothedOctagon.Interval.SmallerShort.C088
import all SmoothedOctagon.Interval.SmallerShort.C089
import all SmoothedOctagon.Interval.SmallerShort.C090
import all SmoothedOctagon.Interval.SmallerShort.C091
import all SmoothedOctagon.Interval.SmallerShort.C092
import all SmoothedOctagon.Interval.SmallerShort.C093
import all SmoothedOctagon.Interval.SmallerShort.C094
import all SmoothedOctagon.Interval.SmallerShort.C095
import all SmoothedOctagon.Interval.SmallerShort.C096
import all SmoothedOctagon.Interval.SmallerShort.C097
import all SmoothedOctagon.Interval.SmallerShort.C098
import all SmoothedOctagon.Interval.SmallerShort.C099
import all SmoothedOctagon.Interval.SmallerShort.C100
import all SmoothedOctagon.Interval.SmallerShort.C101
import all SmoothedOctagon.Interval.SmallerShort.C102
import all SmoothedOctagon.Interval.SmallerShort.C103
import all SmoothedOctagon.Interval.SmallerShort.C104
import all SmoothedOctagon.Interval.SmallerShort.C105
import all SmoothedOctagon.Interval.SmallerShort.C106
import all SmoothedOctagon.Interval.SmallerShort.C107
import all SmoothedOctagon.Interval.SmallerShort.C108
import all SmoothedOctagon.Interval.SmallerShort.C109
import all SmoothedOctagon.Interval.SmallerShort.C110
import all SmoothedOctagon.Interval.SmallerShort.C111
import all SmoothedOctagon.Interval.SmallerShort.C112
import all SmoothedOctagon.Interval.SmallerShort.C113
import all SmoothedOctagon.Interval.SmallerShort.C114
import all SmoothedOctagon.Interval.SmallerShort.C115
import all SmoothedOctagon.Interval.SmallerShort.C116
import all SmoothedOctagon.Interval.SmallerShort.C117
import all SmoothedOctagon.Interval.SmallerShort.C118
import all SmoothedOctagon.Interval.SmallerShort.C119
import all SmoothedOctagon.Interval.SmallerShort.C120
import all SmoothedOctagon.Interval.SmallerShort.C121
import all SmoothedOctagon.Interval.SmallerShort.C122
import all SmoothedOctagon.Interval.SmallerShort.C123
import all SmoothedOctagon.Interval.SmallerShort.C124
import all SmoothedOctagon.Interval.SmallerShort.C125
import all SmoothedOctagon.Interval.SmallerShort.C126
import all SmoothedOctagon.Interval.SmallerShort.C127
import all SmoothedOctagon.Interval.SmallerShort.C128
import all SmoothedOctagon.Interval.SmallerShort.C129
import all SmoothedOctagon.Interval.SmallerShort.C130
import all SmoothedOctagon.Interval.SmallerShort.C131
import all SmoothedOctagon.Interval.SmallerShort.C132
import all SmoothedOctagon.Interval.SmallerShort.C133
import all SmoothedOctagon.Interval.SmallerShort.C134
import all SmoothedOctagon.Interval.SmallerShort.C135
import all SmoothedOctagon.Interval.SmallerShort.C136
import all SmoothedOctagon.Interval.SmallerShort.C137
import all SmoothedOctagon.Interval.SmallerShort.C138
import all SmoothedOctagon.Interval.SmallerShort.C139
import all SmoothedOctagon.Interval.SmallerShort.C140
import all SmoothedOctagon.Interval.SmallerShort.C141
import all SmoothedOctagon.Interval.SmallerShort.C142
import all SmoothedOctagon.Interval.SmallerShort.C143
import all SmoothedOctagon.Interval.SmallerShort.C144
import all SmoothedOctagon.Interval.SmallerShort.C145
import all SmoothedOctagon.Interval.SmallerShort.C146
import all SmoothedOctagon.Interval.SmallerShort.C147
import all SmoothedOctagon.Interval.SmallerShort.C148
import all SmoothedOctagon.Interval.SmallerShort.C149
import all SmoothedOctagon.Interval.SmallerShort.C150
import all SmoothedOctagon.Interval.SmallerShort.C151
import all SmoothedOctagon.Interval.SmallerShort.C152
import all SmoothedOctagon.Interval.SmallerShort.C153
import all SmoothedOctagon.Interval.SmallerShort.C154
import all SmoothedOctagon.Interval.SmallerShort.C155
import all SmoothedOctagon.Interval.SmallerShort.C156
import all SmoothedOctagon.Interval.SmallerShort.C157
import all SmoothedOctagon.Interval.SmallerShort.C158
import all SmoothedOctagon.Interval.SmallerShort.C159
import all SmoothedOctagon.Interval.SmallerShort.C160
import all SmoothedOctagon.Interval.SmallerShort.C161
import all SmoothedOctagon.Interval.SmallerShort.C162
import all SmoothedOctagon.Interval.SmallerShort.C163
import all SmoothedOctagon.Interval.SmallerShort.C164
import all SmoothedOctagon.Interval.SmallerShort.C165
import all SmoothedOctagon.Interval.SmallerShort.C166
import all SmoothedOctagon.Interval.SmallerShort.C167
import all SmoothedOctagon.Interval.SmallerShort.C168
import all SmoothedOctagon.Interval.SmallerShort.C169
import all SmoothedOctagon.Interval.SmallerShort.C170
import all SmoothedOctagon.Interval.SmallerShort.C171
import all SmoothedOctagon.Interval.SmallerShort.C172
import all SmoothedOctagon.Interval.SmallerShort.C173
import all SmoothedOctagon.Interval.SmallerShort.C174
import all SmoothedOctagon.Interval.SmallerShort.C175
import all SmoothedOctagon.Interval.SmallerShort.C176
import all SmoothedOctagon.Interval.SmallerShort.C177
import all SmoothedOctagon.Interval.SmallerShort.C178
import all SmoothedOctagon.Interval.SmallerShort.C179
import all SmoothedOctagon.Interval.SmallerShort.C180
import all SmoothedOctagon.Interval.SmallerShort.C181
import all SmoothedOctagon.Interval.SmallerShort.C182
import all SmoothedOctagon.Interval.SmallerShort.C183
import all SmoothedOctagon.Interval.SmallerShort.C184
import all SmoothedOctagon.Interval.SmallerShort.C185
import all SmoothedOctagon.Interval.SmallerShort.C186
import all SmoothedOctagon.Interval.SmallerShort.C187
import all SmoothedOctagon.Interval.SmallerShort.C188
import all SmoothedOctagon.Interval.SmallerShort.C189
import all SmoothedOctagon.Interval.SmallerShort.C190
import all SmoothedOctagon.Interval.SmallerShort.C191
import all SmoothedOctagon.Interval.SmallerShort.C192
import all SmoothedOctagon.Interval.SmallerShort.C193
import all SmoothedOctagon.Interval.SmallerShort.C194
import all SmoothedOctagon.Interval.SmallerShort.C195
import all SmoothedOctagon.Interval.SmallerShort.C196
import all SmoothedOctagon.Interval.SmallerShort.C197
import all SmoothedOctagon.Interval.SmallerShort.C198
import all SmoothedOctagon.Interval.SmallerShort.C199
import all SmoothedOctagon.Interval.SmallerShort.C200
import all SmoothedOctagon.Interval.SmallerShort.C201
import all SmoothedOctagon.Interval.SmallerShort.C202
import all SmoothedOctagon.Interval.SmallerShort.C203
import all SmoothedOctagon.Interval.SmallerShort.C204
import all SmoothedOctagon.Interval.SmallerShort.C205
import all SmoothedOctagon.Interval.SmallerShort.C206
import all SmoothedOctagon.Interval.SmallerShort.C207
import all SmoothedOctagon.Interval.SmallerShort.C208
import all SmoothedOctagon.Interval.SmallerShort.C209
import all SmoothedOctagon.Interval.SmallerShort.C210
import all SmoothedOctagon.Interval.SmallerShort.C211
import all SmoothedOctagon.Interval.SmallerShort.C212
import all SmoothedOctagon.Interval.SmallerShort.C213
import all SmoothedOctagon.Interval.SmallerShort.C214
import all SmoothedOctagon.Interval.SmallerShort.C215
import all SmoothedOctagon.Interval.SmallerShort.C216
import all SmoothedOctagon.Interval.SmallerShort.C217
import all SmoothedOctagon.Interval.SmallerShort.C218
import all SmoothedOctagon.Interval.SmallerShort.C219
import all SmoothedOctagon.Interval.SmallerShort.C220
import all SmoothedOctagon.Interval.SmallerShort.C221
import all SmoothedOctagon.Interval.SmallerShort.C222
import all SmoothedOctagon.Interval.SmallerShort.C223
import all SmoothedOctagon.Interval.SmallerShort.C224
import all SmoothedOctagon.Interval.SmallerShort.C225
import all SmoothedOctagon.Interval.SmallerShort.C226
import all SmoothedOctagon.Interval.SmallerShort.C227
import all SmoothedOctagon.Interval.SmallerShort.C228
import all SmoothedOctagon.Interval.SmallerShort.C229
import all SmoothedOctagon.Interval.SmallerShort.C230
import all SmoothedOctagon.Interval.SmallerShort.C231
import all SmoothedOctagon.Interval.SmallerShort.C232
import all SmoothedOctagon.Interval.SmallerShort.C233
import all SmoothedOctagon.Interval.SmallerShort.C234
import all SmoothedOctagon.Interval.SmallerShort.C235
import all SmoothedOctagon.Interval.SmallerShort.C236
import all SmoothedOctagon.Interval.SmallerShort.C237
import all SmoothedOctagon.Interval.SmallerShort.C238
import all SmoothedOctagon.Interval.SmallerShort.C239
import all SmoothedOctagon.Interval.SmallerShort.C240
import all SmoothedOctagon.Interval.SmallerShort.C241
import all SmoothedOctagon.Interval.SmallerShort.C242
import all SmoothedOctagon.Interval.SmallerShort.C243
import all SmoothedOctagon.Interval.SmallerShort.C244
import all SmoothedOctagon.Interval.SmallerShort.C245
import all SmoothedOctagon.Interval.SmallerShort.C246
import all SmoothedOctagon.Interval.SmallerShort.C247
import all SmoothedOctagon.Interval.SmallerShort.C248
import all SmoothedOctagon.Interval.SmallerShort.C249
import all SmoothedOctagon.Interval.SmallerShort.C250
import all SmoothedOctagon.Interval.SmallerShort.C251
import all SmoothedOctagon.Interval.SmallerShort.Res
import all SmoothedOctagon.Interval.Special
import all SmoothedOctagon.Interval.Trig
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
  [``ReinhardtChallenge.reinhardt, ``ReinhardtChallenge.reinhardt_equality,
   ``ReinhardtChallenge.reinhardt_cost, ``ReinhardtChallenge.octagon_area]

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
