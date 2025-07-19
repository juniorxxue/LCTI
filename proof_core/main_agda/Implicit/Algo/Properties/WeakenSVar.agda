module Implicit.Algo.Properties.WeakenSVar where

open import Implicit.Language.All
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Extension
open import Implicit.Algo.Properties.Shift
open import Implicit.Algo.Properties.Id

▶⨟=-Ω-exist : Γ ⨟ Δ ▶ k ,= T ⇘ Γ' ⨟ Δ'
            → Γ ⊆ Ω
            → Ω ⊆ Δ
            → ∃[ Ω' ](Γ ⨟ Ω ▶ k ,= T ⇘ Γ' ⨟ Ω' ×
                      Ω ⨟ Δ ▶ k ,= T ⇘ Ω' ⨟ Δ')
▶⨟=-Ω-exist {T = T} {Ω = Ω} (▶Z regA) ext1 ext2 = ⟨ (Ω ,= T) , ⟨ (▶Z regA) , (▶Z (⊆-⊢r regA ext1)) ⟩ ⟩
▶⨟=-Ω-exist (▶S^ new x) (evar ext1) (evar ext2) = ⟨ ▶⨟=-Ω-exist new ext1 ext2 .proj₁ ,^ ,
                                                   ⟨ ▶S^ (▶⨟=-Ω-exist new ext1 ext2 .proj₂ .proj₁) x ,
                                                   ▶S^ (▶⨟=-Ω-exist new ext1 ext2 .proj₂ .proj₂) x ⟩ ⟩
▶⨟=-Ω-exist (▶S^= new x x₁) (evar ext1) (evar-sol ext2 regA) = ⟨ ▶⨟=-Ω-exist new ext1 ext2 .proj₁ ,^ ,
                                                                ⟨ ▶S^ (▶⨟=-Ω-exist new ext1 ext2 .proj₂ .proj₁) x ,
                                                                ▶S^= (▶⨟=-Ω-exist new ext1 ext2 .proj₂ .proj₂) x x₁ ⟩ ⟩
▶⨟=-Ω-exist (▶S^= {B' = B'} new x x₁) (evar-sol ext1 regA) (svar ext2 regA₁) = ⟨ ▶⨟=-Ω-exist new ext1 ext2 .proj₁ ,= B' ,
                                                                      ⟨ ▶S^= (▶⨟=-Ω-exist new ext1 ext2 .proj₂ .proj₁) x x₁ ,
                                                                      ▶S= (▶⨟=-Ω-exist new ext1 ext2 .proj₂ .proj₂) x x₁ ⟩ ⟩
▶⨟=-Ω-exist (▶S∙ new x) (uvar ext1) (uvar ext2) = ⟨ ▶⨟=-Ω-exist new ext1 ext2 .proj₁ ,∙ ,
                                                   ⟨ ▶S∙ (▶⨟=-Ω-exist new ext1 ext2 .proj₂ .proj₁) x ,
                                                   ▶S∙ (▶⨟=-Ω-exist new ext1 ext2 .proj₂ .proj₂) x ⟩ ⟩
▶⨟=-Ω-exist (▶S= {B' = B'} new x x₁) (svar ext1 regA) (svar ext2 regA₁) = ⟨ ▶⨟=-Ω-exist new ext1 ext2 .proj₁ ,= B' ,
                                                                 ⟨ ▶S= (▶⨟=-Ω-exist new ext1 ext2 .proj₂ .proj₁) x x₁ ,
                                                                 ▶S= (▶⨟=-Ω-exist new ext1 ext2 .proj₂ .proj₂) x x₁ ⟩ ⟩
▶⨟=-Ω-exist (▶S⋈ {Γ' = Γ'} new) (mark regΓ) (mark regΓ₁) with refl ← ▶⨟=-unique new = ⟨ Γ' ⋈ , ⟨ ▶S⋈ new , ▶S⋈ new ⟩ ⟩


ss-weaken= : Γ ⊢ A ⌞ ≤ ⌝ B ⊣ Δ
           → Γ ⨟ Δ ▶ k ,= T ⇘ Γ' ⨟ Δ'
           → A ↑ty k ⇘ A'
           → B ↑ty k ⇘ B'
           → Γ' ⊢ A' ⌞ ≤ ⌝ B' ⊣ Δ'
ss-weaken= (s-int regΓ) new ↑ty-int ↑ty-int with refl ← ▶⨟=-unique new = s-int (sregular-weaken= regΓ (▶⨟=-▶=-l new))
ss-weaken= (s-var-∙ regΓ x) new ↑ty-var ↑ty-var with refl ← ▶⨟=-unique new = s-var-∙ (sregular-weaken= regΓ (▶⨟=-▶=-l new)) (∋∙-weaken= x (▶⨟=-▶=-l new))
ss-weaken= (s-ex-l^ inst) new ↑ty-var upB = s-ex-l^ (inst-weaken= inst new upB)
ss-weaken= (s-ex-r^ inst) new upA ↑ty-var = s-ex-r^ (inst-weaken= inst new upA)
ss-weaken= (s-ex-l= regΓ x-in) new ↑ty-var upB with refl ← ▶⨟=-unique new = s-ex-l= (sregular-weaken= regΓ (▶⨟=-▶=-l new)) (∋:=-weaken= x-in (▶⨟=-▶=-l new) upB)
ss-weaken= (s-ex-r= regΓ x-in) new upA ↑ty-var with refl ← ▶⨟=-unique new = s-ex-r= (sregular-weaken= regΓ (▶⨟=-▶=-l new)) (∋:=-weaken= x-in (▶⨟=-▶=-l new) upA)
ss-weaken= (s-arr ss ss₁) new (↑ty-arr upA upA₁) (↑ty-arr upB upB₁)
  with ⟨ Ω' , ⟨ new1 , new2 ⟩ ⟩ ← ▶⨟=-Ω-exist new (ss-⊆ ss) (ss-⊆ ss₁)
  = s-arr (ss-weaken= ss new1 upB upA) (ss-weaken= ss₁ new2 upA₁ upB₁)
ss-weaken= {T = T} (s-∀ ss) new (↑ty-∀ upA) (↑ty-∀ upB)
  with ⟨ T' , upT ⟩ ← ↑ty0-total T = s-∀ (ss-weaken= ss (▶S∙ new upT) upA upB)

t-weaken= : Γ ⊢ Σ ⇒ e ⇒ A
          → Γ ▶ k ,= T ⇘ Γ'
          → Σ ↑tyᶜ k ⇘ Σ'
          → e ↑tyᵉ k ⇘ e'
          → A ↑ty k ⇘ A'
          → Γ' ⊢ Σ' ⇒ e' ⇒ A'

infs-weaken= : Γ ⊨ Σ ⟹ A
             → Γ ▶ k ,= T ⇘ Γ'
             → Σ ↑tyᶜ k ⇘ Σ'
             → A ↑ty k ⇘ A'
             → Γ' ⊨ Σ' ⟹ A'

infs-weaken= (infs-z regΓ regA) new (↑tyᶜ-τ up-t) upA
  with refl ← ↑ty-unique up-t upA = infs-z (tregular-weaken= regΓ new) (⊢r-weaken= regA new upA)
infs-weaken= (infs-s ⊢e infs) new (↑tyᶜ-e up-e upΣ) (↑ty-arr upA upA₁) = infs-s (t-weaken= ⊢e new ↑tyᶜ-□ up-e upA) (infs-weaken= infs new upΣ upA₁)

s-weaken= : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
          → Γ ⨟ Δ ▶ k ,= T ⇘ Γ' ⨟ Δ'
          → A ↑ty k ⇘ A'
          → Σ ↑tyᶜ k ⇘ Σ'
          → B ↑ty k ⇘ B'
          → Γ' ⊢ A' ≤⁺ Σ' ⊣ Δ' ↪ B'

t-weaken= (⊢lit regΓ) new ↑tyᶜ-□ ↑tyᵉ-lit ↑ty-int = ⊢lit (tregular-weaken= regΓ new)
t-weaken= (⊢var regΓ x∈Γ) new ↑tyᶜ-□ ↑tyᵉ-var upA = ⊢var (tregular-weaken= regΓ new) (∋⦂-weaken= x∈Γ new upA)
t-weaken= {k = k} (⊢ann {B = B} ⊢e) new ↑tyᶜ-□ (↑tyᵉ-⦂ upe up) upA
  with refl ← ↑ty-unique up upA
  with ⟨ B' , upB ⟩ ← ↑ty-total B k = ⊢ann (t-weaken= ⊢e new (↑tyᶜ-τ up) upe upB)
t-weaken= {k = k}  (⊢app {A = A} ⊢e) new upΣ (↑tyᵉ-app upe upe₁) upA
  with ⟨ A' , upA' ⟩ ← ↑ty-total A k = ⊢app (t-weaken= ⊢e new (↑tyᶜ-e upe₁ upΣ) upe (↑ty-arr upA' upA))
t-weaken= (⊢lam₁ ⊢e) new (↑tyᶜ-τ (↑ty-arr up-t up-t₁)) (↑tyᵉ-ƛ upe) (↑ty-arr upA upA₁)
  with refl ← ↑ty-unique up-t upA
  with refl ← ⊢id0 ⊢e
  with refl ← ↑ty-unique up-t₁ upA₁
  = ⊢lam₁ (t-weaken= ⊢e (▶S, new up-t) (↑tyᶜ-τ up-t₁) upe up-t₁)
t-weaken= (⊢lam₂  ⊢e up-c ⊢e₁) new (↑tyᶜ-e {Σ' = Σ'} up-e upΣ) (↑tyᵉ-ƛ upe) (↑ty-arr upA upA₁)
  with ⟨ Σ″ , upΣ' ⟩ ← ↑tmᶜ0-total Σ'
  = ⊢lam₂ (t-weaken= ⊢e new ↑tyᶜ-□ up-e upA) upΣ'
          (t-weaken= ⊢e₁ (▶S, new upA) (↑tmᶜ-↑tyᶜ-comm' up-c upΣ upΣ') upe upA₁)
t-weaken= {k = k} (⊢sub {A = A} ⊢e ne gc s) new upΣ upe upA
  with ⟨ A' , upA' ⟩ ← ↑ty-total A k = ⊢sub (t-weaken= ⊢e new ↑tyᶜ-□ upe upA') (nonempty-↑tyᶜ' ne upΣ) (gc-↑tyᵉ gc upe) (s-weaken= s (▶S⋈ (▶=-▶⨟= new)) upA' upΣ upA)
t-weaken= {T = T} (⊢tabs ⊢e) new ↑tyᶜ-□ (↑tyᵉ-Λ upe) (↑ty-∀ upA)
  with ⟨ T' , upT ⟩ ← ↑ty0-total T = ⊢tabs (t-weaken= ⊢e (▶S∙ new upT) ↑tyᶜ-□ upe upA)
t-weaken= {T = T} (⊢tabs-τ ⊢e) new (↑tyᶜ-τ (↑ty-∀ upA')) (↑tyᵉ-Λ upe) (↑ty-∀ upA)
  with ⟨ T' , upT ⟩ ← ↑ty0-total T
  = ⊢tabs-τ (t-weaken= ⊢e (▶S∙ new upT) (↑tyᶜ-τ upA') upe upA)
t-weaken= {k = k} (⊢tapp {B = B} ⊢e st) newΓ upΣ (↑tyᵉ-⓪ upe upA₁) upA
  with ⟨ B' , upB ⟩ ← ↑ty-total B (#S k) = ⊢tapp (t-weaken= ⊢e newΓ (↑tyᶜ-⓪ upA₁ upΣ) upe (↑ty-∀ upB)) (↑ty-st-comm0 st upA₁ upB upA)

s-weaken= (s-empty regΓ cloA grd) new upA ↑tyᶜ-□ upB
  with refl ← ▶⨟=-unique new = s-empty (sregular-weaken= regΓ (▶⨟=-▶=-l new)) (⊢c-weaken= cloA (▶⨟=-▶=-l new) upA) (≫-weaken= grd (▶⨟=-▶=-l new) upA upB)
s-weaken= (s-type ss) new upA (↑tyᶜ-τ up-t) upB
  with refl ← ↑ty-unique up-t upB = s-type (ss-weaken= ss new upA up-t)
s-weaken= (s-term-c cloA ap ⊢e s) new (↑ty-arr upA upA₁) (↑tyᶜ-e up-e upΣ) (↑ty-arr upB upB₁)
  with refl ← ⊢id0 ⊢e
  = s-term-c (⊢c-weaken= cloA (▶⨟=-▶=-l new) upA) (≫-weaken= ap (▶⨟=-▶=-l new) upA upB) (t-weaken= ⊢e (▶=-𝕣 (▶⨟=-▶=-l new)) (↑tyᶜ-τ upB) up-e upB) (s-weaken= s new upA₁ upΣ upB₁)
s-weaken= (s-term-o opnA ⊢e ss s) new (↑ty-arr upA upA₁) (↑tyᶜ-e up-e upΣ) (↑ty-arr upB upB₁)
  with ⟨ Ω' , ⟨ new1 , new2 ⟩ ⟩ ← ▶⨟=-Ω-exist new (ss-⊆ ss) (s-⊆ s)
  = s-term-o (⊢o-weaken= opnA (▶⨟=-▶=-l new) upA)
             (t-weaken= ⊢e (▶=-𝕣 (▶⨟=-▶=-l new)) ↑tyᶜ-□ up-e upB)
             (ss-weaken= ss new1 upB upA)
             (s-weaken= s new2 upA₁ upΣ upB₁)
s-weaken= {k = k} {T = T} (s-∀l {B = B} s upᶜ upᵉ upC upD) new (↑ty-∀ upA) (↑tyᶜ-e {e' = e'} {Σ' = Σ'} up-e upΣ) (↑ty-arr {A' = C'} {B' = D'} upC' upD')
  with ⟨ T' , upT ⟩ ← ↑ty0-total T
  with ⟨ B' , upB' ⟩ ← ↑ty-total B k
  with ⟨ C″ , upC″ ⟩ ← ↑ty0-total C'
  with ⟨ D″ , upD″ ⟩ ← ↑ty0-total D'
  with ⟨ e″ , upe″ ⟩ ← ↑tyᵉ0-total e'
  with ⟨ Σ″ , upΣ″ ⟩ ← ↑tyᶜ0-total Σ'
  = s-∀l (s-weaken= s (▶S^= new upT upB') upA
                      (↑tyᶜ-comm0' (↑tyᶜ-e up-e upΣ) (↑tyᶜ-e upe″ upΣ″) (↑tyᶜ-e upᵉ upᶜ))
                      (↑ty-arr (↑ty-comm0' upC' upC″ upC) (↑ty-comm0' upD' upD″ upD))) upΣ″ upe″ upC″ upD″
s-weaken= {k = k} {T = T} (s-∀l-no s upᶜ upᵉ upC upD) new (↑ty-∀ upA) (↑tyᶜ-e {e' = e'} {Σ' = Σ'} up-e upΣ) (↑ty-arr {A' = C'} {B' = D'} upC' upD')
  with ⟨ T' , upT ⟩ ← ↑ty0-total T
  with ⟨ C″ , upC″ ⟩ ← ↑ty0-total C'
  with ⟨ D″ , upD″ ⟩ ← ↑ty0-total D'
  with ⟨ e″ , upe″ ⟩ ← ↑tyᵉ0-total e'
  with ⟨ Σ″ , upΣ″ ⟩ ← ↑tyᶜ0-total Σ'
  = s-∀l-no (s-weaken= s (▶S^ new upT) upA
                      (↑tyᶜ-comm0' (↑tyᶜ-e up-e upΣ) (↑tyᶜ-e upe″ upΣ″) (↑tyᶜ-e upᵉ upᶜ))
                      (↑ty-arr (↑ty-comm0' upC' upC″ upC) (↑ty-comm0' upD' upD″ upD))) upΣ″ upe″ upC″ upD″
s-weaken= {T = T} (s-tapp s upᶜ) new (↑ty-∀ upA) (↑tyᶜ-⓪ {Σ' = Σ'} upA' upΣ) (↑ty-∀ upB)
  with ⟨ Σ″ , upΣ″ ⟩ ← ↑tyᶜ0-total Σ'
  with ⟨ T' , upT ⟩ ← ↑ty0-total T = s-tapp (s-weaken= s (▶S= new upT upA') upA (↑tyᶜ-comm0' upΣ upΣ″ upᶜ) upB) upΣ″
s-weaken= {k = k} (s-svar {A = A} inΓ s) new ↑ty-var upΣ upB
  with ⟨ A' , upA' ⟩ ← ↑ty-total A k
  with refl ← ▶⨟=-unique new
  = s-svar (∋:=-weaken= inΓ (▶⨟=-▶=-l new) upA') (s-weaken= s new upA' upΣ upB)
s-weaken= (s-evar-infers infs inst) new ↑ty-var (↑tyᶜ-e up-e upΣ) upB
  = s-evar-infers (infs-weaken= infs (▶=-𝕣 (▶⨟=-▶=-l new)) (↑tyᶜ-e up-e upΣ) upB) (inst-weaken= inst new upB)

s-weaken=0 : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
           → ↑ty0 A ⇘ A'
           → ↑tyᶜ0 Σ ⇘ Σ'
           → ↑ty0 B ⇘ B'
           → Γ ⊢r T
           → Γ ,= T ⊢ A' ≤⁺ Σ' ⊣ Δ ,= T ↪ B'
s-weaken=0 s upA upΣ upB regT = s-weaken= s (▶Z regT) upA upΣ upB
