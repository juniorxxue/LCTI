module Implicit.Algo.Properties where

open import Implicit.Common
open import Implicit.Properties
open import Implicit.Algo
open import Implicit.Algo.Extension

----------------------------------------------------------------------
--+                   when context is full type                    +--
----------------------------------------------------------------------

postulate
  spl-weaken-ty : ∀ {Σ : Context n m} {B Bs A' es T}
    → ⟦ Σ , B ⟧→⟦ es , τ T , Bs , A' ⟧
    → ⟦ ↑tyΣ0 Σ , ↑ty0 B ⟧→⟦ upty0 es , τ ↑ty0 T , uptyT0 Bs , ↑ty0 A' ⟧

#S-pred : ∀ {x y : Fin m}
  → #S x ≡ #S y
  → x ≡ y
#S-pred refl = refl

tvar-pred : ∀ {x y : Fin m}
  → ‶ x ≡ ‶ y
  → x ≡ y
tvar-pred refl = refl

punchIn-pred : ∀ {k : Fin (1 + m)} {x y}
  → punchIn k x ≡ punchIn k y
  → x ≡ y
punchIn-pred {k = #0} {x = x} {.x} refl = refl
punchIn-pred {k = #S k} {x = #0} {#0} eq = refl
punchIn-pred {k = #S k} {x = #S x} {#S y} eq = cong #S (punchIn-pred (#S-pred eq))

arr-pred : ∀ {A B C D : Type m}
  → A `→ B ≡ C `→ D
  → A ≡ C × B ≡ D
arr-pred refl = ⟨ refl , refl ⟩

∀-pred : ∀ {A B : Type (1 + m)}
  → `∀ A ≡ `∀ B
  → A ≡ B
∀-pred refl = refl  
    
↑ty-pred : ∀ {k : Fin (1 + m)} {A B}
  → ↑ty k A ≡ ↑ty k B
  → A ≡ B
↑ty-pred {A = Int} {Int} eq = refl
↑ty-pred {A = ‶ X} {‶ Y} eq = cong ‶_ (punchIn-pred (tvar-pred eq))
↑ty-pred {A = A `→ A₁} {B `→ B₁} eq with arr-pred eq
... | ⟨ eq1 , eq2 ⟩ rewrite ↑ty-pred {A = A} {B} eq1 | ↑ty-pred {A = A₁} {B₁} eq2 = refl
↑ty-pred {A = `∀ A} {`∀ B} eq = cong `∀_ (↑ty-pred (∀-pred eq))
