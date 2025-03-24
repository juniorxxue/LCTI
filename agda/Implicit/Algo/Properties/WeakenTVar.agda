module Implicit.Algo.Properties.WeakenTVar where

open import Implicit.Language.All
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Extension
open import Implicit.Algo.Properties.Shift
open import Implicit.Algo.Properties.Id

▶⨟,-unique : Γ ⨟ Γ ▶ k , T ⇘ Γ' ⨟ Δ'
           → Γ' ≡ Δ'
▶⨟,-unique (▶Z regA) = refl
▶⨟,-unique (▶S, new) rewrite ▶⨟,-unique new = refl
▶⨟,-unique (▶S^ new x) rewrite ▶⨟,-unique new = refl
▶⨟,-unique (▶S∙ new x) rewrite ▶⨟,-unique new = refl
▶⨟,-unique (▶S= new x) rewrite ▶⨟,-unique new = refl
▶⨟,-unique (▶S⋈ new) rewrite ▶⨟,-unique new = refl

▶⨟,-▶,-l : Γ ⨟ Δ ▶ k , T ⇘ Γ' ⨟ Δ'
         → Γ ▶ k , T ⇘ Γ'
▶⨟,-▶,-l (▶Z regA) = ▶Z regA
▶⨟,-▶,-l (▶S, new) = ▶S, (▶⨟,-▶,-l new)
▶⨟,-▶,-l (▶S^ new x) = ▶S^ (▶⨟,-▶,-l new) x
▶⨟,-▶,-l (▶S∙ new x) = ▶S∙ (▶⨟,-▶,-l new) x
▶⨟,-▶,-l (▶S= new x) = ▶S= (▶⨟,-▶,-l new) x
▶⨟,-▶,-l (▶S^= new x) = ▶S^ (▶⨟,-▶,-l new) x
▶⨟,-▶,-l (▶S⋈ new) = ▶S⋈ (▶⨟,-▶,-l new)

▶,-▶⨟, : Γ ▶ k , T ⇘ Γ'
       → Γ ⨟ Γ ▶ k , T ⇘ Γ' ⨟ Γ'
▶,-▶⨟, (▶Z regA) = ▶Z regA
▶,-▶⨟, (▶S, new) = ▶S, (▶,-▶⨟, new)
▶,-▶⨟, (▶S^ new x) = ▶S^ (▶,-▶⨟, new) x
▶,-▶⨟, (▶S∙ new x) = ▶S∙ (▶,-▶⨟, new) x
▶,-▶⨟, (▶S= new x) = ▶S= (▶,-▶⨟, new) x
▶,-▶⨟, (▶S⋈ new) = ▶S⋈ (▶,-▶⨟, new)

▶,-𝕣 : Γ ▶ k , T ⇘ Γ'
     → 𝕣 Γ ▶ k , T ⇘ 𝕣 Γ'
▶,-𝕣 (▶Z regA) = ▶Z (⊢r-𝕣' regA)
▶,-𝕣 (▶S, new) = ▶S, (▶,-𝕣 new)
▶,-𝕣 (▶S^ new x) = ▶S^ (▶,-𝕣 new) x
▶,-𝕣 (▶S∙ new x) = ▶S∙ (▶,-𝕣 new) x
▶,-𝕣 (▶S= new x) = ▶S= (▶,-𝕣 new) x
▶,-𝕣 (▶S⋈ new) = new


▶⨟,-Ω-exist : Γ ⨟ Δ ▶ k , T ⇘ Γ' ⨟ Δ'
            → Γ ⊆ Ω
            → Ω ⊆ Δ
            → ∃[ Ω' ](Γ ⨟ Ω ▶ k , T ⇘ Γ' ⨟ Ω' ×
                      Ω ⨟ Δ ▶ k , T ⇘ Ω' ⨟ Δ')
▶⨟,-Ω-exist {T = T} {Ω = Ω} (▶Z regA) ext1 ext2 = ⟨ (Ω , T) , ⟨ ▶Z regA , ▶Z (⊆-⊢r regA ext1) ⟩ ⟩
▶⨟,-Ω-exist (▶S^ new x) (evar ext1) (evar ext2) = ⟨ ▶⨟,-Ω-exist new ext1 ext2 .proj₁ ,^ ,
                                                   ⟨ ▶S^ (▶⨟,-Ω-exist new ext1 ext2 .proj₂ .proj₁) x ,
                                                   ▶S^ (▶⨟,-Ω-exist new ext1 ext2 .proj₂ .proj₂) x ⟩
                                                   ⟩
▶⨟,-Ω-exist (▶S∙ new x) (uvar ext1) (uvar ext2) = ⟨ ▶⨟,-Ω-exist new ext1 ext2 .proj₁ ,∙ ,
                                                   ⟨ ▶S∙ (▶⨟,-Ω-exist new ext1 ext2 .proj₂ .proj₁) x ,
                                                   ▶S∙ (▶⨟,-Ω-exist new ext1 ext2 .proj₂ .proj₂) x ⟩ ⟩
▶⨟,-Ω-exist (▶S= new x) (svar {A = A} ext1 regA) (svar ext2 regA₁) = ⟨ ▶⨟,-Ω-exist new ext1 ext2 .proj₁ ,= A ,
                                                              ⟨ ▶S= (▶⨟,-Ω-exist new ext1 ext2 .proj₂ .proj₁) x ,
                                                              ▶S= (▶⨟,-Ω-exist new ext1 ext2 .proj₂ .proj₂) x ⟩ ⟩
▶⨟,-Ω-exist (▶S^= new x) (evar ext1) (evar-sol ext2 regA) = ⟨ ▶⨟,-Ω-exist new ext1 ext2 .proj₁ ,^ ,
                                                             ⟨ ▶S^ (▶⨟,-Ω-exist new ext1 ext2 .proj₂ .proj₁) x ,
                                                             ▶S^= (▶⨟,-Ω-exist new ext1 ext2 .proj₂ .proj₂) x ⟩
                                                             ⟩
▶⨟,-Ω-exist (▶S^= new x) (evar-sol {A = A} ext1 regA) (svar ext2 regA₁) = ⟨ ▶⨟,-Ω-exist new ext1 ext2 .proj₁ ,= A ,
                                                                   ⟨ ▶S^= (▶⨟,-Ω-exist new ext1 ext2 .proj₂ .proj₁) x ,
                                                                   ▶S= (▶⨟,-Ω-exist new ext1 ext2 .proj₂ .proj₂) x ⟩ ⟩
▶⨟,-Ω-exist (▶S⋈ {Γ' = Γ'} new) (mark regΓ) (mark regΓ₁)
  with refl ← ▶⨟,-unique new = ⟨ Γ' ⋈ , ⟨ ▶S⋈ new , ▶S⋈ new ⟩ ⟩


ss-weaken, : Γ ⊢ A ⌞ ≤ ⌝ B ⊣ Δ
           → Γ ⨟ Δ ▶ k , T ⇘ Γ' ⨟ Δ'
           → Γ' ⊢ A ⌞ ≤ ⌝ B ⊣ Δ'
ss-weaken, (s-int regΓ) new with refl ← ▶⨟,-unique new = s-int (sregular-weaken, regΓ (▶⨟,-▶,-l new))
ss-weaken, (s-var-∙ regΓ x) new with refl ← ▶⨟,-unique new = s-var-∙ (sregular-weaken, regΓ (▶⨟,-▶,-l new)) (∋∙-weaken, x (▶⨟,-▶,-l new))
ss-weaken, (s-ex-l^ inst) new = s-ex-l^ (inst-weaken, inst new)
ss-weaken, (s-ex-r^ inst) new = s-ex-r^ (inst-weaken, inst new)
ss-weaken, (s-ex-l= regΓ x-in) new
  with refl ← ▶⨟,-unique new = s-ex-l= (sregular-weaken, regΓ (▶⨟,-▶,-l new)) (∋:=-weaken, x-in (▶⨟,-▶,-l new))
ss-weaken, (s-ex-r= regΓ x-in) new
  with refl ← ▶⨟,-unique new = s-ex-r= (sregular-weaken, regΓ (▶⨟,-▶,-l new)) (∋:=-weaken, x-in (▶⨟,-▶,-l new))
ss-weaken, (s-arr ss ss₁) new
  with ⟨ Ω' , ⟨ new1 , new2 ⟩ ⟩ ← ▶⨟,-Ω-exist new (ss-⊆ ss) (ss-⊆ ss₁)
  = s-arr (ss-weaken, ss new1) (ss-weaken, ss₁ new2)
ss-weaken, {T = T} (s-∀ ss) new
  with ⟨ T' , upT ⟩ ← ↑ty0-total T = s-∀ (ss-weaken, ss (▶S∙ new upT))


t-weaken, : Γ ⊢ Σ ⇒ e ⇒ A
          → Γ ▶ k , T ⇘ Γ'
          → Σ ↑tmᶜ k ⇘ Σ'
          → e ↑tm k ⇘ e'
          → Γ' ⊢ Σ' ⇒ e' ⇒ A

s-weaken, : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
          → Σ ↑tmᶜ k ⇘ Σ'
          → Γ ⨟ Δ ▶ k , T ⇘ Γ' ⨟ Δ'
          → Γ' ⊢ A ≤⁺ Σ' ⊣ Δ' ↪ B

t-weaken, (⊢lit regΓ) new ↑tmᶜ-□ ↑tm-lit = ⊢lit (tregular-weaken, regΓ new)
t-weaken, (⊢var regΓ x∈Γ) new ↑tmᶜ-□ ↑tm-var = ⊢var (tregular-weaken, regΓ new) (∋⦂-weaken, x∈Γ new)
t-weaken, (⊢ann ⊢e) new ↑tmᶜ-□ (↑tm-⦂ upe) = ⊢ann (t-weaken, ⊢e new ↑tmᶜ-τ upe)
t-weaken, (⊢app ⊢e) new upΣ (↑tm-app upe upe₁) = ⊢app (t-weaken, ⊢e new (↑tmᶜ-e upe₁ upΣ) upe)
t-weaken, (⊢lam₁ ⊢e) new ↑tmᶜ-τ (↑tm-ƛ upe) = ⊢lam₁ (t-weaken, ⊢e (▶S, new) ↑tmᶜ-τ upe)
t-weaken, (⊢lam₂ ⊢e up-c ⊢e₁) new (↑tmᶜ-e {Σ' = Σ'} up-e upΣ) (↑tm-ƛ upe)
  with ⟨ Σ″ , upΣ' ⟩ ← ↑tmᶜ0-total Σ' = ⊢lam₂ (t-weaken, ⊢e new ↑tmᶜ-□ up-e) upΣ' (t-weaken, ⊢e₁ (▶S, new) (↑tmᶜ-comm' z≤n upΣ upΣ' up-c) upe)
t-weaken, (⊢sub ⊢e ne gc s) new upΣ upe = ⊢sub (t-weaken, ⊢e new ↑tmᶜ-□ upe) (nonempty-↑tmᶜ ne upΣ) (↑tm-gc gc upe) (s-weaken, s upΣ (▶S⋈ (▶,-▶⨟, new)))
t-weaken, {T = T} (⊢tabs ⊢e) new ↑tmᶜ-□ (↑tm-Λ upe)
  with ⟨ T' , upT ⟩ ← ↑ty0-total T = ⊢tabs (t-weaken, ⊢e (▶S∙ new upT) ↑tmᶜ-□ upe)

s-weaken, (s-empty regΓ cloA grd) ↑tmᶜ-□ new
   with refl ← ▶⨟,-unique new = s-empty (sregular-weaken, regΓ (▶⨟,-▶,-l new)) (⊢c-weaken, cloA (▶⨟,-▶,-l new)) (≫-weaken, grd (▶⨟,-▶,-l new))
s-weaken, (s-type ss) ↑tmᶜ-τ new = s-type (ss-weaken, ss new)
s-weaken, (s-term-c cloA ap ⊢e s) (↑tmᶜ-e up-e upΣ) new = s-term-c (⊢c-weaken, cloA (▶⨟,-▶,-l new))
                                                                   (≫-weaken, ap (▶⨟,-▶,-l new))
                                                                   (t-weaken, ⊢e (▶,-𝕣 (▶⨟,-▶,-l new)) ↑tmᶜ-τ up-e)
                                                                   (s-weaken, s upΣ new)
s-weaken, (s-term-o opnA ⊢e ss s) (↑tmᶜ-e up-e upΣ) new
  with ⟨ Ω' , ⟨ new1 , new2 ⟩ ⟩ ← ▶⨟,-Ω-exist new (ss-⊆ ss) (s-⊆ s)
  = s-term-o (⊢o-weaken, opnA (▶⨟,-▶,-l new))
             (t-weaken, ⊢e (▶,-𝕣 (▶⨟,-▶,-l new)) ↑tmᶜ-□ up-e)
             (ss-weaken, ss new1)
             (s-weaken, s upΣ new2)
s-weaken, {T = T} (s-∀l s upᶜ upᵉ upC upD) (↑tmᶜ-e {e' = e'} {Σ' = Σ'} up-e upΣ) new
  with ⟨ T' , upT ⟩ ← ↑ty0-total T
  with ⟨ Σ″ , upΣ' ⟩ ← ↑tyᶜ0-total Σ'
  with ⟨ e″ , upe' ⟩ ← ↑tyᵉ0-total e'
  = s-∀l (s-weaken, s (↑tmᶜ-e (↑tm-↑tyᵉ-comm up-e upe' upᵉ) (↑tmᶜ-↑tyᶜ-comm upΣ upΣ' upᶜ)) (▶S^= new upT)) upΣ' upe' upC upD

s-weaken,0 : Γ ⋈ ⊢ A ≤⁺ Σ ⊣ Δ ⋈ ↪ B
           → ↑tmᶜ0 Σ ⇘ Σ'
           → Γ ⊢r T
           → Γ , T ⋈ ⊢ A ≤⁺ Σ' ⊣ Δ , T ⋈  ↪ B
s-weaken,0 s upΣ regT = s-weaken, s upΣ (▶S⋈ (▶Z regT))

t-weaken,0 : Γ ⊢ Σ ⇒ e ⇒ A
           → ↑tmᶜ0 Σ ⇘ Σ'
           → ↑tm0 e ⇘ e'
           → Γ ⊢r T
           → Γ , T ⊢ Σ' ⇒ e' ⇒ A
t-weaken,0 ⊢e upΣ upe regT = t-weaken, ⊢e (▶Z regT) upΣ upe
