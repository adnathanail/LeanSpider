-- This module serves as the root of the `SpLean` library.
-- Import modules here that should be built as part of the library.

-- Shared by both representations: generic helpers, the zxcc wire format and
-- the widget that eats it, and the InfoView entry points that dispatch on
-- which representation a term belongs to. Nothing else is shared.
import SpLean.Utils
import SpLean.Widget
import SpLean.Panel
-- The hypergraph both representations lower into for equivalence checking.
import SpLean.Hypergraph
-- The two ZX representations.
import SpLean.Axiomatic
import SpLean.Algebraic
