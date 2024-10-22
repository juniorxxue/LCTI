module Implicit.Decl.Properties where

open import Implicit.Common
open import Implicit.Decl


⊢sub' : ∀ {Γ : Env n m} {e A B j}
  → Γ ⊢ Z # e ⦂ B
  → Γ ⊢ j # B ≤ A
  → Γ ⊢ j # e ⦂ A
⊢sub' {j = Z} ⊢e s-refl = ⊢e
⊢sub' {j = ∞} ⊢e s = ⊢sub ⊢e s nz-∞
⊢sub' {j = I j} ⊢e s = ⊢sub ⊢e s nz-I
⊢sub' {j = C j} ⊢e s = ⊢sub ⊢e s nz-C


-- the needed lemmas
-- will do later
postulate
  strengthen-0 : ∀ {Γ : Env n m} {j A B e}
    → Γ , A ⊢ j # ↑tm0 e ⦂ B
    → Γ ⊢ j # e ⦂ B

  -- s-strengthen-tm-0 : ∀ {Γ : Env n m} {A B C j}
  --   → Γ , A ⊢ j # B ≤ C
  --   → Γ ⊢ j # B ≤ C

----------------------------------------------------------------------
--+                           Weakening                            +--
----------------------------------------------------------------------


_/ˣ_ : Env (1 + n) m → Fin (1 + n) → Env n m
(Γ , A) /ˣ #0 = Γ
_/ˣ_ {suc n} (Γ , A) (#S k) = (Γ /ˣ k) , A
(Γ ,∙) /ˣ k = (Γ /ˣ k) ,∙
(Γ ,= A) /ˣ k = (Γ /ˣ k) ,= A

∈-weaken : ∀ {Γ : Env (1 + n) m} {k X B}
  → X := B ∈ (Γ /ˣ k)
  → X := B ∈ Γ
∈-weaken {m = suc m} {Γ = Γ , A} {#0} ∈Γ = S, ∈Γ
∈-weaken {suc n} {m = suc m} {Γ = Γ , A} {#S k} (S, ∈Γ) = S, (∈-weaken ∈Γ)
∈-weaken {Γ = _,∙ {m = zero} Γ} (S∙ {k = ()} ∈Γ)
∈-weaken {Γ = _,∙ {m = suc m} Γ} (S∙ ∈Γ) = S∙ (∈-weaken ∈Γ)
∈-weaken {Γ = Γ ,= A} {B = B} (S= ∈Γ) = S= (∈-weaken ∈Γ)
∈-weaken {m = suc m} {Γ ,= A} {X = #0} Z = Z

∈'-weaken : ∀ {Γ : Env (1 + n) m} {k X B}
  → X := B ∈' (Γ /ˣ k)
  → X := B ∈' Γ
∈'-weaken {n} {suc m} {Γ = Γ , A} {#0} ∈'Γ = k, ∈'Γ
∈'-weaken {suc n} {suc m} {Γ = Γ , A} {#S k} (k, ∈'Γ) = k, (∈'-weaken ∈'Γ) 
∈'-weaken {n} {.(1 + _)} {Γ = Γ ,∙} (S∙ ∈'Γ) = S∙ (∈'-weaken ∈'Γ)
∈'-weaken {n} {.(1 + _)} {Γ = Γ ,= .(↓ty0 B)} {B = B} Z = Z
∈'-weaken {n} {.(1 + _)} {Γ = Γ ,= A} {B = B} (S= ∈'Γ) = S= (∈'-weaken ∈'Γ)

lookup-weaken : ∀ {Γ : Env (1 + n) m} {k x}
  → lookup (Γ /ˣ k) x ≡ lookup Γ (punchIn k x)
lookup-weaken {Γ = Γ , A} {k = #0} {x = #0} = refl
lookup-weaken {Γ = Γ ,∙} {k = #0} {x = #0} = cong ↑ty0 (lookup-weaken {Γ = Γ})
lookup-weaken {Γ = Γ ,= A} {k = #0} {x = #0} = cong ↑ty0 (lookup-weaken {Γ = Γ})
lookup-weaken {Γ = Γ , A} {k = #S k} {x = #0} = refl
lookup-weaken {Γ = Γ ,∙} {k = #S k} {x = #0} = cong ↑ty0 (lookup-weaken {Γ = Γ})
lookup-weaken {Γ = Γ ,= A} {k = #S k} {x = #0} = cong ↑ty0 (lookup-weaken {Γ = Γ})
lookup-weaken {Γ = Γ , A} {k = #0} {x = #S x} = refl
lookup-weaken {Γ = Γ ,∙} {k = #0} {x = #S x} = cong ↑ty0 (lookup-weaken {Γ = Γ})
lookup-weaken {Γ = Γ ,= A} {k = #0} {x = #S x} = cong ↑ty0 (lookup-weaken {Γ = Γ})
lookup-weaken {Γ = Γ , A} {k = #S k} {x = #S x} = lookup-weaken {Γ = Γ} {k = k} {x = x}
lookup-weaken {Γ = Γ ,∙} {k = #S k} {x = #S x} = cong ↑ty0 (lookup-weaken {Γ = Γ})
lookup-weaken {Γ = Γ ,= A} {k = #S k} {x = #S x} = cong ↑ty0 (lookup-weaken {Γ = Γ})


slv-weaken : ∀ {Γ : Env (1 + n) m} {k A B}
  → (Γ /ˣ k) ⟦ A ⟧⟹ B
  → Γ ⟦ A ⟧⟹ B
slv-weaken {A = Int} {Int} ⟦A⟧⟹B = slv-int
slv-weaken {A = ‶ X} {B} (slv-var x a) = slv-var (∈'-weaken x) (slv-weaken a)
slv-weaken {A = A `→ A₁} {B `→ B₁} (slv-arr ⟦A⟧⟹B ⟦A⟧⟹B₁) = slv-arr (slv-weaken ⟦A⟧⟹B) (slv-weaken ⟦A⟧⟹B₁)
slv-weaken {A = `∀ A} {`∀ B} (slv-∀ ⟦A⟧⟹B) = slv-∀ (slv-weaken ⟦A⟧⟹B)

s-weaken : ∀ {Γ : Env (1 + n) m} {k j A B }
  → Γ /ˣ k ⊢ j # A ≤ B
  → Γ ⊢ j # A ≤ B
s-weaken (s-refl) = s-refl
s-weaken s-int = s-int
s-weaken s-var = s-var
s-weaken (s-arr₁ C≤A B≤D) = s-arr₁ (s-weaken C≤A) (s-weaken B≤D)
s-weaken (s-arr₂ C≤A B≤D) = s-arr₂ (s-weaken C≤A) (s-weaken B≤D)
s-weaken (s-arr₃ C≤A B≤D) = s-arr₃ (s-weaken C≤A) (s-weaken B≤D)
s-weaken (s-∀ A≤B) = s-∀ (s-weaken A≤B)
s-weaken (s-∀l A≤B fd st1 st2) = s-∀l (s-weaken A≤B) fd st1 st2
s-weaken (s-var-l x A≤B) = s-var-l (∈-weaken x) (s-weaken A≤B)
s-weaken (s-var-r x A≤B) = s-var-r (∈-weaken x) (s-weaken A≤B)

postulate
  weaken : ∀ {Γ : Env (1 + n) m} {k j e A}
    → Γ /ˣ k ⊢ j # e ⦂ A
    → Γ ⊢ j # ↑tm k e ⦂ A

  s-strengthen-tm-0 : ∀ {Γ : Env n m} {A B C j}
    → Γ , A ⊢ j # B ≤ C
    → Γ ⊢ j # B ≤ C
  
weaken-0 : ∀ {Γ : Env (1 + n) m} {j e A}
  → Γ ⊢ j # e ⦂ A
  → Γ , A ⊢ j # ↑tm0 e ⦂ A
weaken-0 {Γ = Γ} {A = A} ⊢e = weaken {Γ = Γ , A} {k = #0} ⊢e

----------------------------------------------------------------------
--+                           Subtyping                            +--
----------------------------------------------------------------------
{-
s-trans : ∀ {Γ : Env n m} {A B C j}
  → Γ ⊢ j # A ≤ B
  → Γ ⊢ j # B ≤ C
  → Γ ⊢ j # A ≤ C
s-trans {B = Int} (s-refl ap) s2 = {!!}
s-trans {B = Int} s-int s2 = {!!}
s-trans {B = Int} (s-∀l s1) s2 = {!!}
s-trans {B = Int} (s-∀lτ s1) s2 = {!!}
s-trans {B = Int} (s-var-l x s1) s2 = {!!}

s-trans {B = ‶ X} s1 s2 = {!!}
s-trans {B = B `→ B₁} s1 s2 = {!!}
s-trans {B = `∀ B} s1 s2 = {!!}
-}

s-refl-∞ : ∀ {Γ : Env n m} {A}
  → Γ ⊢ ∞ # A ≤ A
s-refl-∞ {A = Int} = s-int
s-refl-∞ {A = ‶ X} = s-var
s-refl-∞ {A = A `→ A₁} = s-arr₁ s-refl-∞ s-refl-∞
s-refl-∞ {A = `∀ A} = s-∀ s-refl-∞
