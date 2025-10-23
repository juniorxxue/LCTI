module Implicit.README where

-- Note: the variant uses the old notion of "counters"
-- with the isomorphism proved in core calculus
-- it would be straightforward to derive a "mask" system

import Implicit.Decl.Properties.Trans using (s-refl'; s-trans')

import Implicit.Decl2Interm.Main using (complete-; complete+; complete0)

import Implicit.Interm2Decl.Main using (sound)
