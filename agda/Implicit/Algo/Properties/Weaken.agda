module Implicit.Algo.Properties.Weaken where

open import Implicit.Language.All
open import Implicit.Algo.Base
{-
▶⨟-unique : Γ ⨟ Γ ▶ k , T ⇘ Γ' ⨟ Δ'
          → Γ' ≡ Δ'
▶⨟-unique (▶Z cloA cloA') = refl
▶⨟-unique (▶S, s) rewrite ▶⨟-unique s = refl
▶⨟-unique (▶S^ s x) rewrite ▶⨟-unique s = refl
▶⨟-unique (▶S∙ s x) rewrite ▶⨟-unique s = refl
▶⨟-unique (▶S= s x) rewrite ▶⨟-unique s = refl

▶⨟-▶-l : Γ ⨟ Δ ▶ k , T ⇘ Γ' ⨟ Δ'
       → Γ ▶ k , T ⇘ Γ'
▶⨟-▶-l (▶Z cloA cloA') = ▶Z cloA
▶⨟-▶-l (▶S, newΓ) = ▶S, (▶⨟-▶-l newΓ)
▶⨟-▶-l (▶S^ newΓ x) = ▶S^ (▶⨟-▶-l newΓ) x
▶⨟-▶-l (▶S∙ newΓ x) = ▶S∙ (▶⨟-▶-l newΓ) x
▶⨟-▶-l (▶S= newΓ x) = ▶S= (▶⨟-▶-l newΓ) x
▶⨟-▶-l (▶S^= newΓ x) = ▶S^ (▶⨟-▶-l newΓ) x

▶⨟-▶-r : Γ ⨟ Δ ▶ k , T ⇘ Γ' ⨟ Δ'
       → Δ ▶ k , T ⇘ Δ'
▶⨟-▶-r (▶Z cloA cloA') = ▶Z cloA'
▶⨟-▶-r (▶S, s) = ▶S, (▶⨟-▶-r s)
▶⨟-▶-r (▶S^ s x) = ▶S^ (▶⨟-▶-r s) x
▶⨟-▶-r (▶S∙ s x) = ▶S∙ (▶⨟-▶-r s) x
▶⨟-▶-r (▶S= s x) = ▶S= (▶⨟-▶-r s) x
▶⨟-▶-r (▶S^= s x) = ▶S= (▶⨟-▶-r s) x

▶⨟,-∋:=-l : Γ ⨟ Δ ▶ k , T ⇘ Γ' ⨟ Δ'
          → Γ ∋ X := A
          → Γ' ∋ X := A
▶⨟,-∋:=-l newΓ inΓ = ▶,-∋:= inΓ (▶⨟-▶-l newΓ)
-}
{-
inst-weaken, : [ B / X ] Γ ⟹ Δ
             → Γ ⨟ Δ ▶ k , T ⇘ Γ' ⨟ Δ'
             → [ B / X ] Γ' ⟹ Δ'
inst-weaken, (⟹^0 up) (▶Z cloA cloA') = ⟹,S (⟹^0 up)
inst-weaken, (⟹^0 up) (▶S^= newΓ x)
  with refl ← ▶⨟-unique newΓ = ⟹^0 up
inst-weaken, (⟹^S inst up1) (▶Z cloA cloA') = ⟹,S (⟹^S inst up1)
inst-weaken, (⟹^S inst up1) (▶S^ newΓ x) = ⟹^S (inst-weaken, inst newΓ) up1
inst-weaken, (⟹∙S inst up1) (▶Z cloA cloA') = ⟹,S (⟹∙S inst up1)
inst-weaken, (⟹∙S inst up1) (▶S∙ newΓ x) = ⟹∙S (inst-weaken, inst newΓ) up1
inst-weaken, (⟹,S inst) (▶Z cloA cloA') = ⟹,S (⟹,S inst)
inst-weaken, (⟹,S inst) (▶S, newΓ) = ⟹,S (inst-weaken, inst newΓ)
inst-weaken, (⟹=S inst up1) (▶Z cloA cloA') = ⟹,S (⟹=S inst up1)
inst-weaken, (⟹=S inst up1) (▶S= newΓ x) = ⟹=S (inst-weaken, inst newΓ) up1
-}


-- s-weaken, : Γ ⊢ A ⌞ ≤ ⌝ Σ ⊣ Δ ↪ B
--           → Γ ⨟ Δ ▶ k , T ⇘ Γ' ⨟ Δ'
--           → Σ ↑tmᶜ k ⇘ Σ'
--           → Γ' ⊢ A  ⌞ ≤ ⌝ Σ' ⊣ Δ' ↪ B
-- s-weaken, s-int new ↑tmᶜ-τ
--   with refl ← ▶⨟-unique new = s-int
-- s-weaken, (s-empty clo) new ↑tmᶜ-□
--   with refl ← ▶⨟-unique new = s-empty (⊢c-weaken, clo (▶⨟-▶-l new))
-- s-weaken, s-var new ↑tmᶜ-τ
--   with refl ← ▶⨟-unique new = s-var
-- s-weaken, (s-ex-l^ x-in inst) new ↑tmᶜ-τ = s-ex-l^ (▶,-∋^ x-in (▶⨟-▶-l new)) (inst-weaken, inst new)
-- s-weaken, (s-ex-l= x-in s) new ↑tmᶜ-τ = s-ex-l= (▶⨟,-∋:=-l new x-in) (s-weaken, s new ↑tmᶜ-τ)
-- s-weaken, (s-ex-r^ x-in inst) new ↑tmᶜ-τ = s-ex-r^ (▶,-∋^ x-in (▶⨟-▶-l new)) (inst-weaken, inst new)
-- s-weaken, (s-ex-r= x-in s) new ↑tmᶜ-τ = s-ex-r= (▶⨟,-∋:=-l new x-in) (s-weaken, s new ↑tmᶜ-τ)
-- s-weaken, (s-arr s s₁) new ↑tmᶜ-τ = s-arr (s-weaken, s {!!} ↑tmᶜ-τ) (s-weaken, s₁ {!!} ↑tmᶜ-τ)
-- s-weaken, (s-term-c ⊢e s) new upΣ = {!!}
-- s-weaken, (s-term-o opnA ⊢e s s₁) new upΣ = {!!}
-- s-weaken, (s-∀ s) new upΣ = {!!}
-- s-weaken, (s-∀l s upᶜ upᵉ st₁ st₂) new upΣ = {!!}

-- s-weaken,0 : Γ ⊢ A ⌞ ≤ ⌝ Σ ⊣ Δ ↪ B
--            → ↑tmᶜ0 Σ ⇘ Σ'
--            → Γ ⊢c T
--            → Δ ⊢c T
--            → Γ , T ⊢ A ⌞ ≤ ⌝ Σ' ⊣ Δ , T ↪ B
-- s-weaken,0 s upΣ cloT cloT' = s-weaken, s (▶Z cloT cloT') upΣ

postulate
  s-weaken,0 : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
             → ↑tmᶜ0 Σ ⇘ Σ'
             → Γ ⊢c T
             → Δ ⊢c T
             → Γ , T ⊢ A ≤⁺ Σ' ⊣ Δ , T ↪ B

  s-weaken^0 : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
             → ↑ty0 A ⇘ A'
             → ↑tyᶜ0 Σ ⇘ Σ'
             → ↑ty0 B ⇘ B'
             → Γ ,^ ⊢ A' ≤⁺ Σ' ⊣ Δ ,^ ↪ B'

  s-weaken=0 : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
             → ↑ty0 A ⇘ A'
             → ↑tyᶜ0 Σ ⇘ Σ'
             → ↑ty0 B ⇘ B'
             → Γ ,= T ⊢ A' ≤⁺ Σ' ⊣ Δ ,= T ↪ B'
