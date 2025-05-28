module Implicit.Algo.Properties.WeakenEVar where

open import Implicit.Language.All
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Extension
open import Implicit.Algo.Properties.Shift
open import Implicit.Algo.Properties.Id

▶⨟^-Ω-exist : Γ ⨟ Δ ▶ k ,^⇘ Γ' ⨟ Δ'
            → Γ ⊆ Ω
            → Ω ⊆ Δ
            → ∃[ Ω' ](Γ ⨟ Ω ▶ k ,^⇘ Γ' ⨟ Ω' ×
               Ω ⨟ Δ ▶ k ,^⇘ Ω' ⨟ Δ')
▶⨟^-Ω-exist {Ω = Ω} ▶Z ext1 ext2 = ⟨ Ω ,^ , ⟨ ▶Z , ▶Z ⟩ ⟩
▶⨟^-Ω-exist (▶S^ new) (evar ext1) (evar ext2) = ⟨ ▶⨟^-Ω-exist new ext1 ext2 .proj₁ ,^ ,
                                                 ⟨ ▶S^ (▶⨟^-Ω-exist new ext1 ext2 .proj₂ .proj₁) ,
                                                 ▶S^ (▶⨟^-Ω-exist new ext1 ext2 .proj₂ .proj₂) ⟩ ⟩
▶⨟^-Ω-exist (▶S^= new upA) (evar ext1) (evar-sol ext2 regA) = ⟨ ▶⨟^-Ω-exist new ext1 ext2 .proj₁ ,^ ,
                                                               ⟨ ▶S^ (▶⨟^-Ω-exist new ext1 ext2 .proj₂ .proj₁) ,
                                                               ▶S^= (▶⨟^-Ω-exist new ext1 ext2 .proj₂ .proj₂) upA ⟩ ⟩
▶⨟^-Ω-exist (▶S^= {A' = A'} new upA) (evar-sol ext1 regA) (svar ext2 regA₁) = ⟨ ▶⨟^-Ω-exist new ext1 ext2 .proj₁ ,= A' ,
                                                                     ⟨ ▶S^= (▶⨟^-Ω-exist new ext1 ext2 .proj₂ .proj₁) upA ,
                                                                     ▶S= (▶⨟^-Ω-exist new ext1 ext2 .proj₂ .proj₂) upA ⟩ ⟩
▶⨟^-Ω-exist (▶S∙ new) (uvar ext1) (uvar ext2) = ⟨ ▶⨟^-Ω-exist new ext1 ext2 .proj₁ ,∙ ,
                                                 ⟨ ▶S∙ (▶⨟^-Ω-exist new ext1 ext2 .proj₂ .proj₁) ,
                                                 ▶S∙ (▶⨟^-Ω-exist new ext1 ext2 .proj₂ .proj₂) ⟩ ⟩
▶⨟^-Ω-exist (▶S= {A' = A'} new upA) (svar ext1 regA) (svar ext2 regA₁) = ⟨ ▶⨟^-Ω-exist new ext1 ext2 .proj₁ ,= A' ,
                                                                ⟨ ▶S= (▶⨟^-Ω-exist new ext1 ext2 .proj₂ .proj₁) upA ,
                                                                ▶S= (▶⨟^-Ω-exist new ext1 ext2 .proj₂ .proj₂) upA ⟩ ⟩
▶⨟^-Ω-exist (▶S⋈ {Γ' = Γ'} new) (mark regΓ) (mark regΓ₁)
  with refl ← ▶⨟^-unique new = ⟨ Γ' ⋈ , ⟨ ▶S⋈ new , ▶S⋈ new ⟩ ⟩

ss-weaken^ : Γ ⊢ A ⌞ ≤ ⌝ B ⊣ Δ
           → Γ ⨟ Δ ▶ k ,^⇘ Γ' ⨟ Δ'
           → A ↑ty k ⇘ A'
           → B ↑ty k ⇘ B'
           → Γ' ⊢ A' ⌞ ≤ ⌝ B' ⊣ Δ'
ss-weaken^ (s-int regΓ) new ↑ty-int ↑ty-int
  with refl ← ▶⨟^-unique new = s-int (sregular-weaken^ regΓ (▶⨟^-▶^-l new))
ss-weaken^ (s-var-∙ regΓ x) new ↑ty-var ↑ty-var
  with refl ← ▶⨟^-unique new = s-var-∙ (sregular-weaken^ regΓ (▶⨟^-▶^-l new)) (∋∙-weaken^ x (▶⨟^-▶^-l new))
ss-weaken^ (s-ex-l^ inst) new ↑ty-var upB = s-ex-l^ (inst-weaken^ inst new upB)
ss-weaken^ (s-ex-r^ inst) new upA ↑ty-var = s-ex-r^ (inst-weaken^ inst new upA)
ss-weaken^ (s-ex-l= regΓ x-in) new ↑ty-var upB
  with refl ← ▶⨟^-unique new = s-ex-l= (sregular-weaken^ regΓ (▶⨟^-▶^-l new)) (∋:=-weaken^ x-in upB (▶⨟^-▶^-l new))
ss-weaken^ (s-ex-r= regΓ x-in) new upA ↑ty-var
  with refl ← ▶⨟^-unique new = s-ex-r= (sregular-weaken^ regΓ (▶⨟^-▶^-l new)) (∋:=-weaken^ x-in upA (▶⨟^-▶^-l new))
ss-weaken^ (s-arr ss ss₁) new (↑ty-arr upA upA₁) (↑ty-arr upB upB₁)
  with ⟨ Ω' , ⟨ new1 , new2 ⟩ ⟩ ← ▶⨟^-Ω-exist new (ss-⊆ ss) (ss-⊆ ss₁)
  = s-arr (ss-weaken^ ss new1 upB upA) (ss-weaken^ ss₁ new2 upA₁ upB₁)
ss-weaken^ (s-∀ ss) new (↑ty-∀ upA) (↑ty-∀ upB) = s-∀ (ss-weaken^ ss (▶S∙ new) upA upB)

▶^-𝕣 : Γ ▶ k ,^⇘ Γ'
     → 𝕣 Γ ▶ k ,^⇘ 𝕣 Γ'
▶^-𝕣 ▶Z = ▶Z
▶^-𝕣 (▶S, new upA) = ▶S, (▶^-𝕣 new) upA
▶^-𝕣 (▶S^ new) = ▶S^ (▶^-𝕣 new)
▶^-𝕣 (▶S∙ new) = ▶S∙ (▶^-𝕣 new)
▶^-𝕣 (▶S= new upA) = ▶S= (▶^-𝕣 new) upA
▶^-𝕣 (▶S⋈ new) = new


t-weaken^ : Γ ⊢ Σ ⇒ e ⇒ A
          → Γ ▶ k ,^⇘ Γ'
          → Σ ↑tyᶜ k ⇘ Σ'
          → e ↑tyᵉ k ⇘ e'
          → A ↑ty k ⇘ A'
          → Γ' ⊢ Σ' ⇒ e' ⇒ A'

s-weaken^ : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
          → Γ ⨟ Δ ▶ k ,^⇘ Γ' ⨟ Δ'
          → A ↑ty k ⇘ A'
          → Σ ↑tyᶜ k ⇘ Σ'
          → B ↑ty k ⇘ B'
          → Γ' ⊢ A' ≤⁺ Σ' ⊣ Δ' ↪ B'
s-weaken^ (s-empty regΓ cloA x) new upA ↑tyᶜ-□ upB
  with refl ← ▶⨟^-unique new = s-empty (sregular-weaken^ regΓ (▶⨟^-▶^-l new)) (⊢c-weaken^ cloA (▶⨟^-▶^-l new) upA) (≫-weaken^ x (▶⨟^-▶^-l new) upA upB)
s-weaken^ (s-type ss) new upA (↑tyᶜ-τ up-t) upB
  with refl ← ↑ty-unique up-t upB = s-type (ss-weaken^ ss new upA up-t)
s-weaken^ (s-term-c cloA ap ⊢e s) new (↑ty-arr upA upA₁) (↑tyᶜ-e up-e upΣ) (↑ty-arr upB upB₁)
  with refl ← ⊢id0 ⊢e
  = s-term-c (⊢c-weaken^ cloA (▶⨟^-▶^-l new) upA) (≫-weaken^ ap (▶⨟^-▶^-l new) upA upB) (t-weaken^ ⊢e (▶^-𝕣 (▶⨟^-▶^-l new)) (↑tyᶜ-τ upB) up-e upB)
             (s-weaken^ s new upA₁ upΣ upB₁)
s-weaken^ (s-term-o opnA ⊢e ss s) new (↑ty-arr upA upA₁) (↑tyᶜ-e up-e upΣ) (↑ty-arr upB upB₁)
  with ⟨ Ω' , ⟨ new1 , new2 ⟩ ⟩ ← ▶⨟^-Ω-exist new (ss-⊆ ss) (s-⊆ s)
  = s-term-o (⊢o-weaken^ opnA (▶⨟^-▶^-l new) upA)
             (t-weaken^ ⊢e (▶^-𝕣 (▶⨟^-▶^-l new)) ↑tyᶜ-□ up-e upB)
             (ss-weaken^ ss new1 upB upA)
             (s-weaken^ s new2 upA₁ upΣ upB₁)
s-weaken^ {k = k} (s-∀l {B = B} s upᶜ upᵉ upC upD) new (↑ty-∀ upA) (↑tyᶜ-e {e' = e'} {Σ' = Σ'} up-e upΣ) (↑ty-arr {A' = C'} {B' = D'} upC' upD')
  with ⟨ B' , upB' ⟩ ← ↑ty-total B k
  with ⟨ C″ , upC″ ⟩ ← ↑ty0-total C'
  with ⟨ D″ , upD″ ⟩ ← ↑ty0-total D'
  with ⟨ e″ , upe″ ⟩ ← ↑tyᵉ0-total e'
  with ⟨ Σ″ , upΣ″ ⟩ ← ↑tyᶜ0-total Σ'
  = s-∀l (s-weaken^ s (▶S^= new upB') upA
         (↑tyᶜ-comm0' (↑tyᶜ-e up-e upΣ) (↑tyᶜ-e upe″ upΣ″) (↑tyᶜ-e upᵉ upᶜ))
         (↑ty-arr (↑ty-comm0' upC' upC″ upC) (↑ty-comm0' upD' upD″ upD)))
         upΣ″ upe″ upC″ upD″
s-weaken^ {k = k} (s-∀l-no s upᶜ upᵉ upC upD) new (↑ty-∀ upA) (↑tyᶜ-e {e' = e'} {Σ' = Σ'} up-e upΣ) (↑ty-arr {A' = C'} {B' = D'} upC' upD')
  with ⟨ C″ , upC″ ⟩ ← ↑ty0-total C'
  with ⟨ D″ , upD″ ⟩ ← ↑ty0-total D'
  with ⟨ e″ , upe″ ⟩ ← ↑tyᵉ0-total e'
  with ⟨ Σ″ , upΣ″ ⟩ ← ↑tyᶜ0-total Σ'
  = s-∀l-no (s-weaken^ s (▶S^ new) upA
         (↑tyᶜ-comm0' (↑tyᶜ-e up-e upΣ) (↑tyᶜ-e upe″ upΣ″) (↑tyᶜ-e upᵉ upᶜ))
         (↑ty-arr (↑ty-comm0' upC' upC″ upC) (↑ty-comm0' upD' upD″ upD)))
         upΣ″ upe″ upC″ upD″
s-weaken^ (s-tapp s upᶜ) new (↑ty-∀ upA) (↑tyᶜ-⓪ {Σ' = Σ'} upA' upΣ) (↑ty-∀ upB)
  with ⟨ Σ″ , upΣ″ ⟩ ← ↑tyᶜ0-total Σ' = s-tapp (s-weaken^ s (▶S= new upA') upA (↑tyᶜ-comm0' upΣ upΣ″ upᶜ) upB) upΣ″
s-weaken^ {k = k} (s-svar-term {A = A} inΓ s) new ↑ty-var (↑tyᶜ-e up-e upΣ) (↑ty-arr upB upB₁)
  with ⟨ A' , upA ⟩ ← ↑ty-total A k
  with refl ← ▶⨟^-unique new = s-svar-term (∋:=-weaken^ inΓ upA (▶⨟^-▶^-l new)) (s-weaken^ s new upA (↑tyᶜ-e up-e upΣ) (↑ty-arr upB upB₁))
s-weaken^ {k = k} (s-svar-tapp {A = A} inΓ s) new ↑ty-var (↑tyᶜ-⓪ upA upΣ) (↑ty-∀ upB)
  with ⟨ A' , upA' ⟩ ← ↑ty-total A k
  with refl ← ▶⨟^-unique new = s-svar-tapp (∋:=-weaken^ inΓ upA' (▶⨟^-▶^-l new)) (s-weaken^ s new upA' (↑tyᶜ-⓪ upA upΣ) (↑ty-∀ upB))

t-weaken^ (⊢lit regΓ) newΓ ↑tyᶜ-□ ↑tyᵉ-lit ↑ty-int = ⊢lit (tregular-weaken^ regΓ newΓ)
t-weaken^ (⊢var regΓ x∈Γ) newΓ ↑tyᶜ-□ ↑tyᵉ-var upA = ⊢var (tregular-weaken^ regΓ newΓ) (∋⦂-weaken^ x∈Γ newΓ upA)
t-weaken^ {k = k} (⊢ann {B = B} ⊢e) newΓ ↑tyᶜ-□ (↑tyᵉ-⦂ upe up) upA
  with refl ← ↑ty-unique up upA
  with ⟨ B' , upB ⟩ ← ↑ty-total B k
  = ⊢ann (t-weaken^ ⊢e newΓ (↑tyᶜ-τ up) upe upB)
t-weaken^ {k = k} (⊢app {A = A} ⊢e) newΓ upΣ (↑tyᵉ-app upe upe₁) upA
  with ⟨ A' , upA' ⟩ ← ↑ty-total A k
  = ⊢app (t-weaken^ ⊢e newΓ (↑tyᶜ-e upe₁ upΣ) upe (↑ty-arr upA' upA))
t-weaken^ (⊢lam₁ ⊢e) newΓ (↑tyᶜ-τ (↑ty-arr up-t up-t₁)) (↑tyᵉ-ƛ upe) (↑ty-arr upA upA₁)
  with refl ← ↑ty-unique up-t upA = ⊢lam₁ (t-weaken^ ⊢e (▶S, newΓ up-t) (↑tyᶜ-τ up-t₁) upe upA₁)
t-weaken^ (⊢lam₂ ⊢e up-c ⊢e₁) newΓ (↑tyᶜ-e {Σ' = Σ'} up-e upΣ) (↑tyᵉ-ƛ upe) (↑ty-arr upA upA₁)
  with ⟨ Σ″ , upΣ' ⟩ ← ↑tmᶜ0-total Σ'
  = ⊢lam₂ (t-weaken^ ⊢e newΓ ↑tyᶜ-□ up-e upA) upΣ' (t-weaken^ ⊢e₁ (▶S, newΓ upA) (↑tmᶜ-↑tyᶜ-comm' up-c upΣ upΣ') upe upA₁)
t-weaken^ {k = k} (⊢sub {A = A} ⊢e ne gc s) newΓ upΣ upe upA
  with ⟨ A' , upA' ⟩ ← ↑ty-total A k
  = ⊢sub (t-weaken^ ⊢e newΓ ↑tyᶜ-□ upe upA')
         (nonempty-↑tyᶜ' ne upΣ) (gc-↑tyᵉ gc upe) (s-weaken^ s (▶S⋈ (▶^-▶⨟^ newΓ)) upA' upΣ upA)
t-weaken^ (⊢tabs ⊢e) newΓ ↑tyᶜ-□ (↑tyᵉ-Λ upe) (↑ty-∀ upA) = ⊢tabs (t-weaken^ ⊢e (▶S∙ newΓ) ↑tyᶜ-□ upe upA)
t-weaken^ {k = k} (⊢tapp {B = B} ⊢e st) newΓ upΣ (↑tyᵉ-⓪ upe upA₁) upA
  with ⟨ B' , upB ⟩ ← ↑ty-total B (#S k) = ⊢tapp (t-weaken^ ⊢e newΓ (↑tyᶜ-⓪ upA₁ upΣ) upe (↑ty-∀ upB)) (↑ty-st-comm0 st upA₁ upB upA)

t-weaken^0 : Γ ⊢ Σ ⇒ e ⇒ A
           → ↑tyᶜ0 Σ ⇘ Σ'
           → ↑tyᵉ0 e ⇘ e'
           → ↑ty0 A ⇘ A'
           → Γ ,^ ⊢ Σ' ⇒ e' ⇒ A'
t-weaken^0 ⊢e upΣ upe upA = t-weaken^ ⊢e ▶Z upΣ upe upA

s-weaken^0 : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
           → ↑ty0 A ⇘ A'
           → ↑tyᶜ0 Σ ⇘ Σ'
           → ↑ty0 B ⇘ B'
           → Γ ,^ ⊢ A' ≤⁺ Σ' ⊣ Δ ,^ ↪ B'
s-weaken^0 s upA upΣ upB = s-weaken^ s ▶Z upA upΣ upB
