{-# OPTIONS --allow-unsolved-metas #-}
module Implicit.Algo.Properties.Irrelevance where

-- the irrelevance in altering (solutions and ex-vars in) typing environments

open import Implicit.Language.All
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Extension

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
    → (regA : Γ ⊢r A)
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
⇌-∋∙ (S= inΓ) (sol-changed tf regA) = S^ (⇌-∋∙ inΓ tf)
⇌-∋∙ (S^ inΓ) (evar tf) = S^ (⇌-∋∙ inΓ tf)
⇌-∋∙ (S^ inΓ) (evar-changed tf regA) = S= (⇌-∋∙ inΓ tf)

⇌-∋⦂ : Γ ∋ x ⦂ A
     → Γ ⇌ Δ
     → Δ ∋ x ⦂ A
⇌-∋⦂ Z (var tf) = Z
⇌-∋⦂ (S, inΓ) (var tf) = S, (⇌-∋⦂ inΓ tf)
⇌-∋⦂ (S∙ inΓ up) (uvar tf) = S∙ (⇌-∋⦂ inΓ tf) up
⇌-∋⦂ (S^ inΓ up) (evar tf) = S^ (⇌-∋⦂ inΓ tf) up
⇌-∋⦂ (S^ inΓ up) (evar-changed tf regA) = S= (⇌-∋⦂ inΓ tf) up
⇌-∋⦂ (S= inΓ up) (svar tf) = S= (⇌-∋⦂ inΓ tf) up
⇌-∋⦂ (S= inΓ up) (sol-changed tf regA) = S^ (⇌-∋⦂ inΓ tf) up


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
⇌-tregular (reg-S= regΓ regA) (sol-changed tf regA') = reg-S^ (⇌-tregular regΓ tf)

⇌s-∋∙-l : Γ ∋∙ X
        → Γ & Δ ⇌s Γ' & Δ'
        → Γ' ∋∙ X
⇌s-∋∙-l Z (uvar tf) = Z
⇌s-∋∙-l (S∙ inΓ) (uvar tf) = S∙ (⇌s-∋∙-l inΓ tf)
⇌s-∋∙-l (S= inΓ) (svar tf) = S= (⇌s-∋∙-l inΓ tf)
⇌s-∋∙-l (S^ inΓ) (evar tf) = S^ (⇌s-∋∙-l inΓ tf)
⇌s-∋∙-l (S^ inΓ) (evar-sol tf) = S^ (⇌s-∋∙-l inΓ tf)
⇌s-∋∙-l (S⋈ inΓ) (mark x) = S⋈ (⇌-∋∙ inΓ x)

⇌s-∋=-l : Γ ∋= X
        → Γ & Δ ⇌s Γ' & Δ'
        → Γ' ∋= X
⇌s-∋=-l Z (svar tf) = Z
⇌s-∋=-l (S∙ inΓ) (uvar tf) = S∙ (⇌s-∋=-l inΓ tf)
⇌s-∋=-l (S^ inΓ) (evar tf) = S^ (⇌s-∋=-l inΓ tf)
⇌s-∋=-l (S^ inΓ) (evar-sol tf) = S^ (⇌s-∋=-l inΓ tf)
⇌s-∋=-l (S= inΓ) (svar tf) = S= (⇌s-∋=-l inΓ tf)

⇌s-∋^-l : Γ ∋^ X
        → Γ & Δ ⇌s Γ' & Δ'
        → Γ' ∋^ X
⇌s-∋^-l Z (evar tf) = Z
⇌s-∋^-l Z (evar-sol tf) = Z
⇌s-∋^-l (S∙ inΓ) (uvar tf) = S∙ (⇌s-∋^-l inΓ tf)
⇌s-∋^-l (S= inΓ) (svar tf) = S= (⇌s-∋^-l inΓ tf)
⇌s-∋^-l (S^ inΓ) (evar tf) = S^ (⇌s-∋^-l inΓ tf)
⇌s-∋^-l (S^ inΓ) (evar-sol tf) = S^ (⇌s-∋^-l inΓ tf)


⇌s-∋:=-l : Γ ∋ X := A
        → Γ & Δ ⇌s Γ' & Δ'
        → Γ' ∋ X := A
⇌s-∋:=-l (Z up) (svar tf) = Z up
⇌s-∋:=-l (S∙ inΓ up) (uvar tf) = S∙ (⇌s-∋:=-l inΓ tf) up
⇌s-∋:=-l (S^ inΓ up) (evar tf) = S^ (⇌s-∋:=-l inΓ tf) up
⇌s-∋:=-l (S^ inΓ up) (evar-sol tf) = S^ (⇌s-∋:=-l inΓ tf) up
⇌s-∋:=-l (S= inΓ up) (svar tf) = S= (⇌s-∋:=-l inΓ tf) up


⇌s-⊢r-l : Γ ⊢r A
        → Γ & Δ ⇌s Γ' & Δ'
        → Γ' ⊢r A
⇌s-⊢r-l ⊢r-int tf = ⊢r-int
⇌s-⊢r-l (⊢r-var-∙ inΓ) tf = ⊢r-var-∙ (⇌s-∋∙-l inΓ tf)
⇌s-⊢r-l (⊢r-arr regA regA₁) tf = ⊢r-arr (⇌s-⊢r-l regA tf) (⇌s-⊢r-l regA₁ tf)
⇌s-⊢r-l (⊢r-∀ regA) tf = ⊢r-∀ (⇌s-⊢r-l regA (uvar tf))

⇌s-⊢c-l : Γ ⊢c A
        → Γ & Δ ⇌s Γ' & Δ'
        → Γ' ⊢c A
⇌s-⊢c-l ⊢c-int tf = ⊢c-int
⇌s-⊢c-l (⊢c-var-∙ inΔ) tf = ⊢c-var-∙ (⇌s-∋∙-l inΔ tf)
⇌s-⊢c-l (⊢c-var-= inΔ) tf = ⊢c-var-= (⇌s-∋=-l inΔ tf)
⇌s-⊢c-l (⊢c-arr cloA cloA₁) tf = ⊢c-arr (⇌s-⊢c-l cloA tf) (⇌s-⊢c-l cloA₁ tf)
⇌s-⊢c-l (⊢c-∀ cloA) tf = ⊢c-∀ (⇌s-⊢c-l cloA (uvar tf))

⇌s-⊢o-l : Γ ⊢o A
        → Γ & Δ ⇌s Γ' & Δ'
        → Γ' ⊢o A
⇌s-⊢o-l (⊢o-var-^ x) tf = ⊢o-var-^ (⇌s-∋^-l x tf)
⇌s-⊢o-l (⊢o-arr-l opn) tf = ⊢o-arr-l (⇌s-⊢o-l opn tf)
⇌s-⊢o-l (⊢o-arr-r opn) tf = ⊢o-arr-r (⇌s-⊢o-l opn tf)
⇌s-⊢o-l (⊢o-∀ opn) tf = ⊢o-∀ (⇌s-⊢o-l opn (uvar tf))


⇌s-sregular-l : SRegular Γ
              → Γ & Δ ⇌s Γ' & Δ'
              → SRegular Γ'
⇌s-sregular-l (reg-Z regΓ) (mark x) = reg-Z (⇌-tregular regΓ x)
⇌s-sregular-l (reg-S∙ regΓ) (uvar tf) = reg-S∙ (⇌s-sregular-l regΓ tf)
⇌s-sregular-l (reg-S^ regΓ) (evar tf) = reg-S^ (⇌s-sregular-l regΓ tf)
⇌s-sregular-l (reg-S^ regΓ) (evar-sol tf) = reg-S^ (⇌s-sregular-l regΓ tf)
⇌s-sregular-l (reg-S= regΓ regA) (svar tf) = reg-S= (⇌s-sregular-l regΓ tf) (⇌s-⊢r-l regA tf)

⇌s-≫-l : Γ ≫ A ⇘ B
       → Γ & Δ ⇌s Γ' & Δ'
       → Γ' ≫ A ⇘ B
⇌s-≫-l grd-int tf = grd-int
⇌s-≫-l (grd-var= x) tf = grd-var= (⇌s-∋:=-l x tf)
⇌s-≫-l (grd-var∙ x) tf = grd-var∙ (⇌s-∋∙-l x tf)
⇌s-≫-l (grd-arr grd grd₁) tf = grd-arr (⇌s-≫-l grd tf) (⇌s-≫-l grd₁ tf)
⇌s-≫-l (grd-∀ grd) tf = grd-∀ (⇌s-≫-l grd (uvar tf))

⇌s-⇌-l : Γ & Δ ⇌s Γ' & Δ'
       → 𝕣 Γ ⇌ 𝕣 Γ'
⇌s-⇌-l (uvar tf) = uvar (⇌s-⇌-l tf)
⇌s-⇌-l (evar tf) = evar (⇌s-⇌-l tf)
⇌s-⇌-l (evar-sol tf) = evar (⇌s-⇌-l tf)
⇌s-⇌-l (svar tf) = svar (⇌s-⇌-l tf)
⇌s-⇌-l (mark x) = x


----------------------------------------------------------------------
--+                           main logic                           +--
----------------------------------------------------------------------

⇌s-inst : Γ & Δ ⇌s Γ' & Δ'
        → [ B / X ] Γ ⟹ Δ
        → [ B / X ] Γ' ⟹ Δ'
⇌s-inst (evar-sol tf) (⟹^0 up regA env) with refl ← ⇌s-eq tf = ⟹^0 up (⇌s-⊢r-l regA tf) (⇌s-sregular-l env tf)
⇌s-inst (evar tf) (⟹^S inst up1) = ⟹^S (⇌s-inst tf inst) up1
⇌s-inst (uvar tf) (⟹∙S inst up1) = ⟹∙S (⇌s-inst tf inst) up1
⇌s-inst (svar tf) (⟹=S inst up1 regB) = ⟹=S (⇌s-inst tf inst) up1 (⇌s-⊢r-l regB tf)

ss-irrev : Γ ⊢ A ⌞ ≤ ⌝ B ⊣ Δ
         → Γ & Δ ⇌s Γ' & Δ'
         → Γ' ⊢ A ⌞ ≤ ⌝ B ⊣ Δ'
ss-irrev (s-int regΓ) tf with refl ← ⇌s-eq tf = s-int (⇌s-sregular-l regΓ tf)
ss-irrev (s-var-∙ regΓ x) tf with refl ← ⇌s-eq tf = s-var-∙ (⇌s-sregular-l regΓ tf) (⇌s-∋∙-l x tf)
ss-irrev (s-ex-l^ inst) tf = s-ex-l^ (⇌s-inst tf inst)
ss-irrev (s-ex-r^ inst) tf = s-ex-r^ (⇌s-inst tf inst)
ss-irrev (s-ex-l= regΓ x-in) tf with refl ← ⇌s-eq tf = s-ex-l= (⇌s-sregular-l regΓ tf) (⇌s-∋:=-l x-in tf)
ss-irrev (s-ex-r= regΓ x-in) tf with refl ← ⇌s-eq tf = s-ex-r= (⇌s-sregular-l regΓ tf) (⇌s-∋:=-l x-in tf)
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
t-irrev (⊢var regΓ x∈Γ) tf = ⊢var (⇌-tregular regΓ tf) (⇌-∋⦂ x∈Γ tf)
t-irrev (⊢ann ⊢e) tf = ⊢ann (t-irrev ⊢e tf)
t-irrev (⊢app ⊢e) tf = ⊢app (t-irrev ⊢e tf)
t-irrev (⊢lam₁ ⊢e) tf = ⊢lam₁ (t-irrev ⊢e (var tf))
t-irrev (⊢lam₂ ⊢e up-c ⊢e₁) tf = ⊢lam₂ (t-irrev ⊢e tf) up-c (t-irrev ⊢e₁ (var tf))
t-irrev (⊢lam₃ ⊢e) tf = ⊢lam₃ (t-irrev ⊢e (var tf))
t-irrev (⊢sub ⊢e ne gc s) tf = ⊢sub (t-irrev ⊢e tf) ne gc (s-irrev s (mark tf))
t-irrev (⊢tabs ⊢e) tf = ⊢tabs (t-irrev ⊢e (uvar tf))
t-irrev (⊢tapp ⊢e st) tf = ⊢tapp (t-irrev ⊢e tf) st

s-irrev (s-empty regΓ cloA x) tf with refl ← ⇌s-eq tf = s-empty (⇌s-sregular-l regΓ tf) (⇌s-⊢c-l cloA tf) (⇌s-≫-l x tf)
s-irrev (s-type ss) tf = s-type (ss-irrev ss tf)
s-irrev (s-term-c cloA ap ⊢e s) tf = s-term-c (⇌s-⊢c-l cloA tf) (⇌s-≫-l ap tf) (t-irrev ⊢e (⇌s-⇌-l tf)) (s-irrev s tf)
s-irrev (s-term-o opnA conv ⊢e ss s) tf with ⇌s-Ω (ss-⊆ ss) tf
... | ⟨ Ω' , tf' ⟩ = s-term-o (⇌s-⊢o-l opnA tf) {!!} (t-irrev ⊢e (⇌s-⇌-l tf)) (ss-irrev ss tf') (s-irrev s (⇌s-arr tf tf' (s-⊆ s)))
s-irrev (s-∀l s upᶜ upᵉ upC upD) tf = s-∀l (s-irrev s (evar-sol tf)) upᶜ upᵉ upC upD
s-irrev (s-tapp s upᶜ) tf = s-tapp (s-irrev s (svar tf)) upᶜ
s-irrev (s-term-p ss s) tf with ⇌s-Ω (ss-⊆ ss) tf
... | ⟨ Ω' , tf' ⟩ = s-term-p (ss-irrev ss tf') (s-irrev s (⇌s-arr tf tf' (s-⊆ s)))

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

⇌-symm : Γ ⇌ Δ
       → Δ ⇌ Γ
⇌-symm empty = empty
⇌-symm (var ext) = var (⇌-symm ext)
⇌-symm (uvar ext) = uvar (⇌-symm ext)
⇌-symm (evar ext) = evar (⇌-symm ext)
⇌-symm (svar ext) = svar (⇌-symm ext)
⇌-symm (evar-changed ext regA) = sol-changed (⇌-symm ext) (⇌-⊢r regA ext)
⇌-symm (sol-changed ext regA) = evar-changed (⇌-symm ext) (⇌-⊢r regA ext)

t-irrev-⊆ : 𝕣 Γ ⊢ Σ ⇒ e ⇒ A
          → Γ ⊆ Δ
          → 𝕣 Δ ⊢ Σ ⇒ e ⇒ A
t-irrev-⊆ ⊢e ext = t-irrev ⊢e (⊆-⇌ ext)

t-irrev-⊆' : 𝕣 Δ ⊢ Σ ⇒ e ⇒ A
           → Γ ⊆ Δ
           → 𝕣 Γ ⊢ Σ ⇒ e ⇒ A
t-irrev-⊆' ⊢e ext = t-irrev ⊢e (⇌-symm (⊆-⇌ ext))
