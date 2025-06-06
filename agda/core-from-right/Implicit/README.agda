module Implicit.README where

open import Implicit.Language.All
import Implicit.Decl.All
open import Implicit.Decl.Typing renaming (_⊢_#_⦂_ to _⊢d_#_⦂_)
import Implicit.Interm.All
open import Implicit.Algo.All

-- (interm. <----> algo.) completeness
import Implicit.Algo2Interm.Main
open import Implicit.Algo2Interm.Corollaries renaming (sound0 to a→i0; sound∞ to a→i∞)

-- (interm. <----> algo.) soundness
open import Implicit.Interm2Algo.Main renaming (complete-0 to i→a0; complete-∞ to i→a∞)

-- (decl. <----> interm.) completeness
import Implicit.Decl2Interm.Main
open import Implicit.Decl2Interm.Corollaries renaming (⊢complete to d→i)

-- (decl. <----> interm.) soundness
import Implicit.Interm2Decl.Main
open import Implicit.Interm2Decl.Corollaries renaming (⊢sound to i→d)


d→a0 : Γ ⊢d Z # e ⦂ A
     → Γ ⊢ □ ⇒ e ⇒ A
d→a0 ⊢e = i→a0 (d→i ⊢e)


d→a∞ : Γ ⊢d ∞ # e ⦂ A
     → Γ ⊢ τ A ⇒ e ⇒ A
d→a∞ ⊢e = i→a∞ (d→i ⊢e)


a→d0 : Γ ⊢ □ ⇒ e ⇒ A
     → Γ ⊢d Z # e ⦂ A
a→d0 ⊢e = i→d (a→i0 ⊢e)

a→d∞ : Γ ⊢ τ A ⇒ e ⇒ A
     → Γ ⊢d ∞ # e ⦂ A
a→d∞ ⊢e = i→d (a→i∞ ⊢e)
