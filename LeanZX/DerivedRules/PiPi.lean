import LeanZX.Rules.SpiderFusion
import LeanZX.Rules.IdentityRemoval

/-- Fuse two connected same-color π-spiders and remove the resulting identity.
    Usage: `zx_pipi n` where `n` is one of the two spider node IDs. -/
macro "zx_pipi" a:num : tactic =>
  `(tactic| (zx_sp $a; zx_id $a))
