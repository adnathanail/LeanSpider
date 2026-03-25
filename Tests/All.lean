import Tests.SpiderFusion
import Tests.IdentityRemoval
import Tests.PiCopy
import Tests.HadamardHadamard
import Tests.ColourChange
import Tests.Normalization

open LSpec

#lspec spiderFusionTests ++ identityRemovalTests ++ piCopyTests ++ hadamardHadamardTests ++ colourChangeTests ++ normalizationTests
