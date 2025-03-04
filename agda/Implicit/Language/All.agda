module Implicit.Language.All where

open import Implicit.Language.Prelude public
open import Implicit.Language.Base public

open import Implicit.Language.Shift.All public
open import Implicit.Language.Subst.All public

open import Implicit.Language.Lookup.Base public
open import Implicit.Language.Occur.Base public

open import Implicit.Language.Find public

open import Implicit.Language.Regular.Base public

-- two files below are entangled
open import Implicit.Language.Norm.Base public
open import Implicit.Language.OpenClose.Base public
open import Implicit.Language.EnvOps.Base public

-- open import Implicit.Language.Extension.All public
open import Implicit.Language.Extension.Base public

-- open import Implicit.Language.Ground.All public
open import Implicit.Language.Ground.Base public
