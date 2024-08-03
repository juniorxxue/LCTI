module Poly.Basic where

open import Poly.Common

_/ˣ_ : Env (1 + n) m → Fin (1 + n) → Env n m
(Γ , A) /ˣ #0 = Γ
_/ˣ_ {suc n} (Γ , A) (#S k) = (Γ /ˣ k) , A
(Γ ,∙) /ˣ k = (Γ /ˣ k) ,∙

∈-weaken : ∀ {Γ : Env (1 + n) m} {k x A}
  → (Γ /ˣ k) ∋ x ⦂ A
  → Γ ∋ (punchIn k x) ⦂ A
∈-weaken {Γ = Γ , A} {#0} ∈Γ = S, ∈Γ
∈-weaken {m = zero} {Γ = Γ , A} {#S k} Z = Z
∈-weaken {m = zero} {Γ = Γ , A} {#S k} (S, ∈Γ) = S, (∈-weaken ∈Γ)
∈-weaken {suc n} {m = suc m} {Γ = Γ , A} {#S k} Z = Z
∈-weaken {suc n} {m = suc m} {Γ = Γ , A} {#S k} (S, ∈Γ) = S, (∈-weaken ∈Γ)
∈-weaken {Γ = Γ ,∙} (S∙ ∈Γ x) = S∙ (∈-weaken ∈Γ) x 

punchIn-comm : ∀ {x : Fin n} {j k} 
   → j F≤ k
   → punchIn (inject₁ j) (punchIn k x) ≡
      punchIn (#S k) (punchIn j x)
punchIn-comm {x = #0} {#0} j≤k = refl
punchIn-comm {x = #0} {#S j} {#S k} j≤k = refl
punchIn-comm {x = #S x} {#0} j≤k = refl
punchIn-comm {x = #S x} {#S j} {#S k} (s≤s j≤k) = cong #S (punchIn-comm j≤k)

↑tm-comm : ∀ {e : Term n m} {j k}
  → j F≤ k
  → ↑tm (inject₁ j) (↑tm k e) ≡ ↑tm (#S k) (↑tm j e)
↑tm-comm {e = lit i} j≤k = refl
↑tm-comm {e = ` x} j≤k = cong `_ (punchIn-comm j≤k)
↑tm-comm {e = ƛ e} j≤k = cong ƛ_ (↑tm-comm (s≤s j≤k))
↑tm-comm {e = e · e₁} j≤k = cong₂ _·_ (↑tm-comm j≤k) (↑tm-comm j≤k)
↑tm-comm {e = e ⦂ A} j≤k = cong (_⦂ A) (↑tm-comm j≤k)
↑tm-comm {e = Λ e} j≤k = cong Λ_ (↑tm-comm j≤k)
↑tm-comm {e = e [ A ]} j≤k = cong (_[ A ]) (↑tm-comm j≤k)
 
 