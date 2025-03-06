module Implicit.Algo.Properties.Irrelevance where

open import Implicit.Language.All
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Extension

-- the logic looks good,
-- will come back later to fill in the holes
-- 2025-03-06

infix 3 _⇌_
data _⇌_ : Env n m → Env n m → Set where
  empty : ∅ ⇌ ∅
  var : Γ ⇌ Δ
      → Γ , A ⇌ Δ , A
  uvar :
      Γ ⇌ Δ
    → Γ ,∙ ⇌ Δ ,∙
  evar :
      Γ ⇌ Δ
    → Γ ,^ ⇌ Δ ,^
  svar :
      Γ ⇌ Δ
    → Γ ,= A ⇌ Δ ,= A
  evar-changed :
      Γ ⇌ Δ
    → (regA : Γ ⊢r A)
    → Γ ,^ ⇌ Δ ,= A
  sol-changed :
      Γ ⇌ Δ
    → Γ ,= A ⇌ Δ ,^

-- this is total on (Γ ⊆ Δ) and unique
infix 3 _&_⇌s_&_
data _&_⇌s_&_ : Env n m → Env n m → Env n m → Env n m → Set where
  uvar : Γ & Δ ⇌s Γ' & Δ'
      → Γ ,∙ & Δ ,∙ ⇌s Γ' ,∙ & Δ' ,∙
  evar :
      Γ & Δ ⇌s Γ' & Δ'
    → Γ ,^ & Δ ,^ ⇌s Γ' ,^ & Δ' ,^
  evar-sol :
      Γ & Δ ⇌s Γ' & Δ'
    → Γ ,^ & Δ ,= A ⇌s Γ' ,^ & Δ' ,= A
  svar :
      Γ & Δ ⇌s Γ' & Δ'
    → Γ ,= A & Δ ,= A ⇌s Γ' ,= A & Δ' ,= A
  mark : Γ ⇌ Δ
       → Γ ⋈ & Γ ⋈ ⇌s Δ ⋈ & Δ ⋈

⇌s-eq : Γ & Γ ⇌s Γ' & Δ'
        → Γ' ≡ Δ'
⇌s-eq (uvar tf) rewrite ⇌s-eq tf = refl
⇌s-eq (evar tf) rewrite ⇌s-eq tf = refl
⇌s-eq (svar tf) rewrite ⇌s-eq tf = refl
⇌s-eq (mark x) = refl

⇌s-Ω : Γ ⊆ Ω
     → Γ & Δ ⇌s Γ' & Δ'
     → ∃[ Ω' ](Γ & Ω ⇌s Γ' & Ω')
⇌s-Ω (uvar ext) (uvar tf) = ⟨ ⇌s-Ω ext tf .proj₁ ,∙ , uvar (⇌s-Ω ext tf .proj₂) ⟩
⇌s-Ω (evar ext) (evar tf) = ⟨ ⇌s-Ω ext tf .proj₁ ,^ , evar (⇌s-Ω ext tf .proj₂) ⟩
⇌s-Ω (evar ext) (evar-sol tf) = ⟨ ⇌s-Ω ext tf .proj₁ ,^ , evar (⇌s-Ω ext tf .proj₂) ⟩
⇌s-Ω (evar-sol {A = A} ext regA) (evar tf) = ⟨ ⇌s-Ω ext tf .proj₁ ,= A , evar-sol (⇌s-Ω ext tf .proj₂) ⟩
⇌s-Ω (evar-sol {A = A} ext regA) (evar-sol tf) = ⟨ ⇌s-Ω ext tf .proj₁ ,= A , evar-sol (⇌s-Ω ext tf .proj₂) ⟩
⇌s-Ω (svar {A = A} ext regA) (svar tf) = ⟨ ⇌s-Ω ext tf .proj₁ ,= A , svar (⇌s-Ω ext tf .proj₂) ⟩
⇌s-Ω (mark x) (mark {Δ = Δ} x₁) = ⟨ Δ ⋈ , mark x₁ ⟩

⇌s-arr : Γ & Δ ⇌s Γ' & Δ'
       → Γ & Ω ⇌s Γ' & Ω'
       → Ω ⊆ Δ
       → Ω & Δ ⇌s Ω' & Δ'
⇌s-arr (uvar tf1) (uvar tf2) (uvar ext) = uvar (⇌s-arr tf1 tf2 ext)
⇌s-arr (evar tf1) (evar tf2) (evar ext) = evar (⇌s-arr tf1 tf2 ext)
⇌s-arr (evar-sol tf1) (evar tf2) (evar-sol ext regA) = evar-sol (⇌s-arr tf1 tf2 ext)
⇌s-arr (evar-sol tf1) (evar-sol tf2) (svar ext regA) = svar (⇌s-arr tf1 tf2 ext)
⇌s-arr (svar tf1) (svar tf2) (svar ext regA) = svar (⇌s-arr tf1 tf2 ext)
⇌s-arr (mark x) (mark x₁) (mark x₂) = mark x

⇌-∋∙ : Γ ∋∙ X
     → Γ ⇌ Δ
     → Δ ∋∙ X
⇌-∋∙ Z (uvar tf) = Z
⇌-∋∙ (S, inΓ) (var s) = S, (⇌-∋∙ inΓ s)
⇌-∋∙ (S∙ inΓ) (uvar tf) = S∙ (⇌-∋∙ inΓ tf)
⇌-∋∙ (S= inΓ) (svar tf) = S= (⇌-∋∙ inΓ tf)
⇌-∋∙ (S= inΓ) (sol-changed tf) = S^ (⇌-∋∙ inΓ tf)
⇌-∋∙ (S^ inΓ) (evar tf) = S^ (⇌-∋∙ inΓ tf)
⇌-∋∙ (S^ inΓ) (evar-changed tf regA) = S= (⇌-∋∙ inΓ tf)

⇌-⊢r : Γ ⊢r A
     → Γ ⇌ Δ
     → Δ ⊢r A
⇌-⊢r ⊢r-int tf = ⊢r-int
⇌-⊢r (⊢r-var-∙ inΓ) tf = ⊢r-var-∙ (⇌-∋∙ inΓ tf)
⇌-⊢r (⊢r-arr regA regA₁) tf = ⊢r-arr (⇌-⊢r regA tf) (⇌-⊢r regA₁ tf)
⇌-⊢r (⊢r-∀ regA) tf = ⊢r-∀ (⇌-⊢r regA (uvar tf))

⇌-tregular : TRegular Γ
           → Γ ⇌ Δ
           → TRegular Δ
⇌-tregular reg-Z empty = reg-Z
⇌-tregular (reg-S, regA regΓ) (var s) = reg-S, (⇌-tregular regA s) (⇌-⊢r regΓ s)
⇌-tregular (reg-S∙ regΓ) (uvar tf) = reg-S∙ (⇌-tregular regΓ tf)
⇌-tregular (reg-S^ regΓ) (evar tf) = reg-S^ (⇌-tregular regΓ tf)
⇌-tregular (reg-S^ regΓ) (evar-changed tf regA) = reg-S= (⇌-tregular regΓ tf) (⇌-⊢r regA tf)
⇌-tregular (reg-S= regΓ regA) (svar tf) = reg-S= (⇌-tregular regΓ tf) (⇌-⊢r regA tf)
⇌-tregular (reg-S= regΓ regA) (sol-changed tf) = reg-S^ (⇌-tregular regΓ tf)

ss-irrev : Γ ⊢ A ⌞ ≤ ⌝ B ⊣ Δ
         → Γ & Δ ⇌s Γ' & Δ'
         → Γ' ⊢ A ⌞ ≤ ⌝ B ⊣ Δ'
ss-irrev (s-int regΓ) tf with refl ← ⇌s-eq tf = s-int {!!}
ss-irrev (s-var-∙ regΓ x) tf with refl ← ⇌s-eq tf = s-var-∙ {!!} {!!}
ss-irrev (s-ex-l^ inst) tf = s-ex-l^ {!!}
ss-irrev (s-ex-r^ inst) tf = s-ex-r^ {!!}
ss-irrev (s-ex-l= regΓ x-in) tf with refl ← ⇌s-eq tf = s-ex-l= {!!} {!!}
ss-irrev (s-ex-r= regΓ x-in) tf with refl ← ⇌s-eq tf = s-ex-r= {!!} {!!}
ss-irrev (s-arr s s₁) tf with ⇌s-Ω (ss-⊆ s) tf
... | ⟨ Ω' , tf' ⟩ = s-arr (ss-irrev s tf') (ss-irrev s₁ (⇌s-arr tf tf' (ss-⊆ s₁)))
ss-irrev (s-∀ s) tf = s-∀ (ss-irrev s (uvar tf))


t-irrev : Γ ⊢ Σ ⇒ e ⇒ A
        → Γ ⇌ Δ
        → Δ ⊢ Σ ⇒ e ⇒ A

s-irrev : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
        → Γ & Δ ⇌s Γ' & Δ'
        → Γ' ⊢ A ≤⁺ Σ ⊣ Δ' ↪ B

t-irrev (⊢lit regΓ) tf = ⊢lit (⇌-tregular regΓ tf)
t-irrev (⊢var regΓ x∈Γ) tf = {!!}
t-irrev (⊢ann ⊢e) tf = ⊢ann (t-irrev ⊢e tf)
t-irrev (⊢app ⊢e) tf = ⊢app (t-irrev ⊢e tf)
t-irrev (⊢lam₁ ⊢e) tf = ⊢lam₁ (t-irrev ⊢e (var tf))
t-irrev (⊢lam₂ ⊢e up-c ⊢e₁) tf = ⊢lam₂ (t-irrev ⊢e tf) up-c (t-irrev ⊢e₁ (var tf))
t-irrev (⊢sub ⊢e ne gc s) tf = ⊢sub (t-irrev ⊢e tf) ne gc (s-irrev s (mark tf))
t-irrev (⊢tabs ⊢e) tf = ⊢tabs (t-irrev ⊢e (uvar tf))

s-irrev (s-empty regΓ cloA x) tf = {!!}
s-irrev (s-type ss) tf = s-type {!!}
s-irrev (s-term-c cloA ap ⊢e s) tf = s-term-c {!!} {!!} (t-irrev ⊢e {!!}) (s-irrev s tf)
s-irrev (s-term-o opnA ⊢e ss s) tf = s-term-o {!!} (t-irrev ⊢e {!!}) {!!} (s-irrev s {!!})
s-irrev (s-∀l s upᶜ upᵉ upC upD) tf = s-∀l (s-irrev s (evar-sol tf)) upᶜ upᵉ upC upD

----------------------------------------------------------------------
--+                           corollary                            +--
----------------------------------------------------------------------

⇌-refl : TRegular Γ
       → Γ ⇌ Γ
⇌-refl reg-Z = empty
⇌-refl (reg-S, regΓ regA) = var (⇌-refl regΓ)
⇌-refl (reg-S∙ regΓ) = uvar (⇌-refl regΓ)
⇌-refl (reg-S^ regΓ) = evar (⇌-refl regΓ)
⇌-refl (reg-S= regΓ regA) = svar (⇌-refl regΓ)

⊆-⇌ : Γ ⊆ Δ
    → 𝕣 Γ ⇌ 𝕣 Δ
⊆-⇌ (uvar ext) = uvar (⊆-⇌ ext)
⊆-⇌ (evar ext) = evar (⊆-⇌ ext)
⊆-⇌ (evar-sol ext regA) = evar-changed (⊆-⇌ ext) (⊢r-𝕣' (⊆-⊢r' regA ext))
⊆-⇌ (svar ext regA) = svar (⊆-⇌ ext)
⊆-⇌ (mark x) = ⇌-refl x

t-irrev-⊆ : 𝕣 Γ ⊢ Σ ⇒ e ⇒ A
          → Γ ⊆ Δ
          → 𝕣 Δ ⊢ Σ ⇒ e ⇒ A
t-irrev-⊆ ⊢e ext = t-irrev ⊢e (⊆-⇌ ext)
