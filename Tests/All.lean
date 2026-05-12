import Tests.SpiderFusion
import Tests.SpiderUnfusion
import Tests.IdentityRemoval
import Tests.PiCopy
import Tests.HadamardHadamard
import Tests.ColourChange
import Tests.Normalization
import Tests.StrongComp
import Tests.IdentityInsertion
import Tests.PhaseLabel

open LSpec LeanSpider.Tests.PhaseLabel

#lspec spiderFusionTests ++ spiderUnfusionTests ++ identityRemovalTests ++ identityInsertionTests ++ piCopyTests ++ hadamardHadamardTests ++ colourChangeTests ++ normalizationTests ++ strongCompTests ++ phaseLabelTests
