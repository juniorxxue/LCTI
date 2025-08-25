{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --allow-incomplete-matches #-}
module Implicit.Algo.Properties.WeakenTVar where

open import Implicit.Language.All
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Extension
open import Implicit.Algo.Properties.Shift
open import Implicit.Algo.Properties.Id

▶s⨟,-Ω-exist : Γ ⨟ Δ ▶s k , T ⇘ Γ' ⨟ Δ'
            → Γ ⊆ Ω
            → Ω ⊆ Δ
            → ∃[ Ω' ](Γ ⨟ Ω ▶s k , T ⇘ Γ' ⨟ Ω' ×
                      Ω ⨟ Δ ▶s k , T ⇘ Ω' ⨟ Δ')
▶s⨟,-Ω-exist (▶sS^ new x) (evar ext1) (evar ext2) = ⟨ ▶s⨟,-Ω-exist new ext1 ext2 .proj₁ ,^ ,
                                                   ⟨ ▶sS^ (▶s⨟,-Ω-exist new ext1 ext2 .proj₂ .proj₁) x ,
                                                   ▶sS^ (▶s⨟,-Ω-exist new ext1 ext2 .proj₂ .proj₂) x ⟩
                                                   ⟩
▶s⨟,-Ω-exist (▶sS∙ new x) (uvar ext1) (uvar ext2) = ⟨ ▶s⨟,-Ω-exist new ext1 ext2 .proj₁ ,∙ ,
                                                   ⟨ ▶sS∙ (▶s⨟,-Ω-exist new ext1 ext2 .proj₂ .proj₁) x ,
                                                   ▶sS∙ (▶s⨟,-Ω-exist new ext1 ext2 .proj₂ .proj₂) x ⟩ ⟩
▶s⨟,-Ω-exist (▶sS= new x) (svar {A = A} ext1 regA) (svar ext2 regA₁) = ⟨ ▶s⨟,-Ω-exist new ext1 ext2 .proj₁ ,= A ,
                                                              ⟨ ▶sS= (▶s⨟,-Ω-exist new ext1 ext2 .proj₂ .proj₁) x ,
                                                              ▶sS= (▶s⨟,-Ω-exist new ext1 ext2 .proj₂ .proj₂) x ⟩ ⟩
▶s⨟,-Ω-exist (▶sS^= new x) (evar ext1) (evar-sol ext2 regA) = ⟨ ▶s⨟,-Ω-exist new ext1 ext2 .proj₁ ,^ ,
                                                             ⟨ ▶sS^ (▶s⨟,-Ω-exist new ext1 ext2 .proj₂ .proj₁) x ,
                                                             ▶sS^= (▶s⨟,-Ω-exist new ext1 ext2 .proj₂ .proj₂) x ⟩
                                                             ⟩
▶s⨟,-Ω-exist (▶sS^= new x) (evar-sol {A = A} ext1 regA) (svar ext2 regA₁) = ⟨ ▶s⨟,-Ω-exist new ext1 ext2 .proj₁ ,= A ,
                                                                   ⟨ ▶sS^= (▶s⨟,-Ω-exist new ext1 ext2 .proj₂ .proj₁) x ,
                                                                   ▶sS= (▶s⨟,-Ω-exist new ext1 ext2 .proj₂ .proj₂) x ⟩ ⟩
▶s⨟,-Ω-exist (▶sS⋈ {Γ' = Γ'} new) (mark regΓ) (mark regΓ₁)
  with refl ← ▶⨟,-unique new = ⟨ Γ' ⋈ , ⟨ ▶sS⋈ new , ▶sS⋈ new ⟩ ⟩


ss-weaken, : Γ ⊢ A ⌞ ≤ ⌝ B ⊣ Δ
           → Γ ⨟ Δ ▶s k , T ⇘ Γ' ⨟ Δ'
           → Γ' ⊢ A ⌞ ≤ ⌝ B ⊣ Δ'

ss-weaken, (s-int regΓ) new with refl ← ▶s⨟,-unique new = s-int (sregular-weaken,s regΓ (▶s⨟,-▶s,-l new))
ss-weaken, (s-var-∙ regΓ x) new with refl ← ▶s⨟,-unique new = s-var-∙ (sregular-weaken,s regΓ (▶s⨟,-▶s,-l new)) (∋∙-weaken,s x (▶s⨟,-▶s,-l new))
ss-weaken, (s-ex-l^ inst) new = s-ex-l^ (inst-weaken,s inst new)
ss-weaken, (s-ex-r^ inst) new = s-ex-r^ (inst-weaken,s inst new)
ss-weaken, (s-ex-l= regΓ x-in) new
  with refl ← ▶s⨟,-unique new = s-ex-l= (sregular-weaken,s regΓ (▶s⨟,-▶s,-l new)) (∋:=-weaken,s x-in (▶s⨟,-▶s,-l new))
ss-weaken, (s-ex-r= regΓ x-in) new
  with refl ← ▶s⨟,-unique new = s-ex-r= (sregular-weaken,s regΓ (▶s⨟,-▶s,-l new)) (∋:=-weaken,s x-in (▶s⨟,-▶s,-l new))
ss-weaken, (s-arr ss ss₁) new
  with ⟨ Ω' , ⟨ new1 , new2 ⟩ ⟩ ← ▶s⨟,-Ω-exist new (ss-⊆ ss) (ss-⊆ ss₁)
  = s-arr (ss-weaken, ss new1) (ss-weaken, ss₁ new2)
ss-weaken, {T = T} (s-∀ ss) new
  with ⟨ T' , upT ⟩ ← ↑ty0-total T = s-∀ (ss-weaken, ss (▶sS∙ new upT))

t-weaken, : Γ ⊢ Σ ⇒ e ⇒ A
          → Γ ▶ k , T ⇘ Γ'
          → Σ ↑tmᶜ k ⇘ Σ'
          → e ↑tm k ⇘ e'
          → Γ' ⊢ Σ' ⇒ e' ⇒ A

infs-weaken, : Γ ⊨ Σ ⟹ A
             → Γ ▶ k , T ⇘ Γ'
             → Σ ↑tmᶜ k ⇘ Σ'
             → Γ' ⊨ Σ' ⟹ A
infs-weaken, (infs-z regΓ regA) new ↑tmᶜ-τ = infs-z (tregular-weaken, regΓ new) (⊢r-weaken, regA new)
infs-weaken, (infs-s ⊢e infs) new (↑tmᶜ-e up-e upΣ) = infs-s (t-weaken, ⊢e new ↑tmᶜ-□ up-e) (infs-weaken, infs new upΣ)

s-weaken, : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
          → Σ ↑tmᶜ k ⇘ Σ'
          → Γ ⨟ Δ ▶s k , T ⇘ Γ' ⨟ Δ'
          → Γ' ⊢ A ≤⁺ Σ' ⊣ Δ' ↪ B

t-weaken, (⊢lit regΓ) new ↑tmᶜ-□ ↑tm-lit = ⊢lit (tregular-weaken, regΓ new)
t-weaken, (⊢var regΓ x∈Γ) new ↑tmᶜ-□ ↑tm-var = ⊢var (tregular-weaken, regΓ new) (∋⦂-weaken, x∈Γ new)
t-weaken, (⊢ann ⊢e) new ↑tmᶜ-□ (↑tm-⦂ upe) = ⊢ann (t-weaken, ⊢e new ↑tmᶜ-τ upe)
t-weaken, (⊢app ⊢e) new upΣ (↑tm-app upe upe₁) = ⊢app (t-weaken, ⊢e new (↑tmᶜ-e upe₁ upΣ) upe)
t-weaken, (⊢lam₁ ⊢e) new ↑tmᶜ-τ (↑tm-ƛ upe) = ⊢lam₁ (t-weaken, ⊢e (▶S, new) ↑tmᶜ-τ upe)
t-weaken, (⊢lam₂ ⊢e up-c ⊢e₁) new (↑tmᶜ-e {Σ' = Σ'} up-e upΣ) (↑tm-ƛ upe)
  with ⟨ Σ″ , upΣ' ⟩ ← ↑tmᶜ0-total Σ' = ⊢lam₂ (t-weaken, ⊢e new ↑tmᶜ-□ up-e) upΣ' (t-weaken, ⊢e₁ (▶S, new) (↑tmᶜ-comm' z≤n upΣ upΣ' up-c) upe)
t-weaken, (⊢sub ⊢e ne gc s) new upΣ upe = ⊢sub (t-weaken, ⊢e new ↑tmᶜ-□ upe) (nonempty-↑tmᶜ ne upΣ) (↑tm-gc gc upe) (s-weaken, s upΣ (▶sS⋈ (▶,-▶⨟, new)))
t-weaken, {T = T} (⊢tabs ⊢e) new ↑tmᶜ-□ (↑tm-Λ upe)
  with ⟨ T' , upT ⟩ ← ↑ty0-total T = ⊢tabs (t-weaken, ⊢e (▶S∙ new upT) ↑tmᶜ-□ upe)
t-weaken, {T = T} (⊢tabs-τ ⊢e) new ↑tmᶜ-τ (↑tm-Λ upe)
  with ⟨ T' , upT ⟩ ← ↑ty0-total T = ⊢tabs-τ (t-weaken, ⊢e (▶S∙ new upT) ↑tmᶜ-τ upe)
-- t-weaken, (⊢tapp ⊢e st) new upΣ (↑tm-⓪ upe) = ⊢tapp (t-weaken, ⊢e new (↑tmᶜ-⓪ upΣ) upe) st

s-weaken, (s-empty regΓ cloA grd) ↑tmᶜ-□ new
   with refl ← ▶s⨟,-unique new = s-empty (sregular-weaken,s regΓ (▶s⨟,-▶s,-l new)) (⊢c-weaken,s cloA (▶s⨟,-▶s,-l new)) (≫-weaken,s grd (▶s⨟,-▶s,-l new))
s-weaken, (s-type ss) ↑tmᶜ-τ new = s-type (ss-weaken, ss new)
s-weaken, (s-term-c cloA ap ⊢e s) (↑tmᶜ-e up-e upΣ) new = s-term-c (⊢c-weaken,s cloA (▶s⨟,-▶s,-l new))
                                                                   (≫-weaken,s ap (▶s⨟,-▶s,-l new))
                                                                   (t-weaken, ⊢e (▶,-▶s,-𝕣 (▶s⨟,-▶s,-l new)) ↑tmᶜ-τ up-e)
                                                                   (s-weaken, s upΣ new)
s-weaken, (s-term-o opnA ⊢e ss s) (↑tmᶜ-e up-e upΣ) new
  with ⟨ Ω' , ⟨ new1 , new2 ⟩ ⟩ ← ▶s⨟,-Ω-exist new (ss-⊆ ss) (s-⊆ s)
  = s-term-o (⊢o-weaken,s opnA (▶s⨟,-▶s,-l new))
             (t-weaken, ⊢e (▶,-▶s,-𝕣 (▶s⨟,-▶s,-l new)) ↑tmᶜ-□ up-e)
             (ss-weaken, ss new1)
             (s-weaken, s upΣ new2)
-- s-weaken, {T = T} (s-∀l s upᶜ upᵉ upC upD) (↑tmᶜ-e {e' = e'} {Σ' = Σ'} up-e upΣ) new
--   with ⟨ T' , upT ⟩ ← ↑ty0-total T
--   with ⟨ Σ″ , upΣ' ⟩ ← ↑tyᶜ0-total Σ'
--   with ⟨ e″ , upe' ⟩ ← ↑tyᵉ0-total e'
--   = s-∀l (s-weaken, s (↑tmᶜ-e (↑tm-↑tyᵉ-comm up-e upe' upᵉ) (↑tmᶜ-↑tyᶜ-comm upΣ upΣ' upᶜ)) (▶sS^= new upT)) upΣ' upe' upC upD
-- s-weaken, {T = T} (s-∀l-no s upᶜ upᵉ upC upD) (↑tmᶜ-e {e' = e'} {Σ' = Σ'} up-e upΣ) new
--   with ⟨ T' , upT ⟩ ← ↑ty0-total T
--   with ⟨ Σ″ , upΣ' ⟩ ← ↑tyᶜ0-total Σ'
--   with ⟨ e″ , upe' ⟩ ← ↑tyᵉ0-total e'
--   = s-∀l-no (s-weaken, s (↑tmᶜ-e (↑tm-↑tyᵉ-comm up-e upe' upᵉ) (↑tmᶜ-↑tyᶜ-comm upΣ upΣ' upᶜ)) (▶sS^ new upT)) upΣ' upe' upC upD
s-weaken, {T = T} (s-tapp s upᶜ) (↑tmᶜ-⓪ {Σ' = Σ'} upΣ) new
  with ⟨ Σ″ , upΣ″ ⟩ ← ↑tyᶜ0-total Σ'
  with ⟨ T' , upT ⟩ ← ↑ty0-total T = s-tapp (s-weaken, s (↑tmᶜ-↑tyᶜ-comm upΣ upΣ″ upᶜ) (▶sS= new upT)) upΣ″
s-weaken, (s-svar-term inΓ s) (↑tmᶜ-e up-e upΣ) new
  with refl ← ▶s⨟,-unique new = s-svar-term (∋:=-weaken,s inΓ (▶s⨟,-▶s,-l new)) (s-weaken, s (↑tmᶜ-e up-e upΣ) new)
s-weaken, (s-svar-tapp inΓ s) (↑tmᶜ-⓪ upΣ) new
  with refl ← ▶s⨟,-unique new = s-svar-tapp (∋:=-weaken,s inΓ (▶s⨟,-▶s,-l new)) (s-weaken, s (↑tmᶜ-⓪ upΣ) new)
s-weaken, (s-evar-infers infs inst) (↑tmᶜ-e up-e upΣ) new = s-evar-infers (infs-weaken, infs (▶,-▶s,-𝕣 (▶s⨟,-▶s,-l new)) (↑tmᶜ-e up-e upΣ)) (inst-weaken,s inst new)

s-weaken,0 : Γ ⋈ ⊢ A ≤⁺ Σ ⊣ Δ ⋈ ↪ B
           → ↑tmᶜ0 Σ ⇘ Σ'
           → Γ ⊢r T
           → Γ , T ⋈ ⊢ A ≤⁺ Σ' ⊣ Δ , T ⋈  ↪ B
s-weaken,0 s upΣ regT = s-weaken, s upΣ (▶sS⋈ (▶Z regT))

t-weaken,0 : Γ ⊢ Σ ⇒ e ⇒ A
           → ↑tmᶜ0 Σ ⇘ Σ'
           → ↑tm0 e ⇘ e'
           → Γ ⊢r T
           → Γ , T ⊢ Σ' ⇒ e' ⇒ A
t-weaken,0 ⊢e upΣ upe regT = t-weaken, ⊢e (▶Z regT) upΣ upe
