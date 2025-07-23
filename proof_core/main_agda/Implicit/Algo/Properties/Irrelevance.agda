module Implicit.Algo.Properties.Irrelevance where

-- the irrelevance in altering (solutions and ex-vars in) typing environments

open import Implicit.Language.All
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Extension
open import Implicit.Algo.Properties.OpenK
open import Implicit.Algo.Properties.Regularity

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
  ⇌⋈ : Γ ⇌ Δ
     → Γ ⋈ ⇌ Δ ⋈

-- stays the same between [0 .. k]
-- change from Γ to Δ from k + 1
infix 3 _⇌_∣_⇌_by_
data _⇌_∣_⇌_by_ : Env n m → Env n m → Env n m → Env n m → Fin (1 + m) → Set where

  ⇌⇌-Z : (ext : Γ ⇌ Δ)
       → Γ ⇌ Δ ∣ Γ ⇌ Δ by #0
{-
  ⇌⇌-S, : Γ₁ ⇌ Δ₁ ∣ Γ₂ ⇌ Δ₂ by k
        → Γ₁ , A ⇌ Δ₁ , A ∣ Γ₂ , A ⇌ Δ₂ , A by k
-}
  ⇌-S^^  : Γ₁ ⇌ Δ₁ ∣ Γ₂ ⇌ Δ₂ by k
        → Γ₁ ,^ ⇌ Δ₁ ,^ ∣ Γ₂ ,^ ⇌ Δ₂ ,^ by #S k
  ⇌-S∙∙  : Γ₁ ⇌ Δ₁ ∣ Γ₂ ⇌ Δ₂ by k
        → Γ₁ ,∙ ⇌ Δ₁ ,∙ ∣ Γ₂ ,∙ ⇌ Δ₂ ,∙ by #S k
  ⇌-S==  : Γ₁ ⇌ Δ₁ ∣ Γ₂ ⇌ Δ₂ by k
         → (regA : Γ₁ ⊢r A)
         → Γ₁ ,= A ⇌ Δ₁ ,= A ∣ Γ₂ ,= A ⇌ Δ₂ ,= A by #S k
  ⇌-S^=  : Γ₁ ⇌ Δ₁ ∣ Γ₂ ⇌ Δ₂ by k
         → (regA : Γ₁ ⊢r A)
         → Γ₁ ,^ ⇌ Δ₁ ,^ ∣ Γ₂ ,= A ⇌ Δ₂ ,= A by #S k


ss+-irrev : Γ₁ ⊢ A ⌞ ≤⁺ ⌝ B ⊣ Γ₂
          → Γ₁ ∤ k ⊢o A
          → Γ₁ ⇌ Δ₁ ∣ Γ₂ ⇌ Δ₂ by k
          → Δ₁ ⊢ A ⌞ ≤⁺ ⌝ B ⊣ Δ₂

ss--irrev : Γ₁ ⊢ A ⌞ ≤⁻ ⌝ B ⊣ Γ₂
          → Γ₁ ∤ k ⊢o B
          → Γ₁ ⇌ Δ₁ ∣ Γ₂ ⇌ Δ₂ by k
          → Δ₁ ⊢ A ⌞ ≤⁻ ⌝ B ⊣ Δ₂

s-irrev : Γ₁ ⊢ A ≤⁺ Σ ⊣ Γ₂ ↪ B
        → Γ₁ ∤ k ⊢o A
        → Γ₁ ⇌ Δ₁ ∣ Γ₂ ⇌ Δ₂ by k
        → Δ₁ ⊢ A ≤⁺ Σ ⊣ Δ₂ ↪ B

s-irrev0 : Γ ⊢ A ≤⁺ Σ ⊣ Γ ↪ B
         → Γ ⇌ Δ
         → Δ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
s-irrev0 s tf = s-irrev s (⊢c-⊢ok (s-⊢c s)) (⇌⇌-Z tf)

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
⇌-∋∙ (S⋈ inΓ) (⇌⋈ tf) = S⋈ (⇌-∋∙ inΓ tf)

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


t-irrev : Γ ⊢ Σ ⇒ e ⇒ A
        → Γ ⇌ Δ
        → Δ ⊢ Σ ⇒ e ⇒ A

infs-irrev : Γ ⊨ Σ ⟹ A
           → Γ ⇌ Δ
           → Δ ⊨ Σ ⟹ A

t-irrev (⊢lit regΓ) tf = ⊢lit (⇌-tregular regΓ tf)
t-irrev (⊢var regΓ x∈Γ) tf = ⊢var (⇌-tregular regΓ tf) (⇌-∋⦂ x∈Γ tf)
t-irrev (⊢ann ⊢e) tf = ⊢ann (t-irrev ⊢e tf)
t-irrev (⊢app ⊢e) tf = ⊢app (t-irrev ⊢e tf)
t-irrev (⊢lam₁ ⊢e) tf = ⊢lam₁ (t-irrev ⊢e (var tf))
t-irrev (⊢lam₂ ⊢e up-c ⊢e₁) tf = ⊢lam₂ (t-irrev ⊢e tf) up-c (t-irrev ⊢e₁ (var tf))
t-irrev (⊢sub ⊢e ne gc s) tf = ⊢sub (t-irrev ⊢e tf) ne gc (s-irrev0 s (⇌⋈ tf))
t-irrev (⊢tabs ⊢e) tf = ⊢tabs (t-irrev ⊢e (uvar tf))
t-irrev {e = Λ e} (⊢tabs-τ x₁) x = ⊢tabs-τ (t-irrev x₁ (uvar x))
t-irrev (⊢tapp ⊢e st) tf = ⊢tapp (t-irrev ⊢e tf) st

infs-irrev (infs-z regΓ regA) tf = infs-z (⇌-tregular regΓ tf) (⇌-⊢r regA tf)
infs-irrev (infs-s x infs) tf = infs-s (t-irrev x tf) (infs-irrev infs tf)

⇌-refl : TRegular Γ
       → Γ ⇌ Γ
⇌-refl reg-Z = empty
⇌-refl (reg-S, regΓ regA) = var (⇌-refl regΓ)
⇌-refl (reg-S∙ regΓ) = uvar (⇌-refl regΓ)
⇌-refl (reg-S^ regΓ) = evar (⇌-refl regΓ)
⇌-refl (reg-S= regΓ regA) = svar (⇌-refl regΓ)

⇌-symm : Γ ⇌ Δ
       → Δ ⇌ Γ
⇌-symm empty = empty
⇌-symm (var ext) = var (⇌-symm ext)
⇌-symm (uvar ext) = uvar (⇌-symm ext)
⇌-symm (evar ext) = evar (⇌-symm ext)
⇌-symm (svar ext) = svar (⇌-symm ext)
⇌-symm (evar-changed ext regA) = sol-changed (⇌-symm ext) (⇌-⊢r regA ext)
⇌-symm (sol-changed ext regA) = evar-changed (⇌-symm ext) (⇌-⊢r regA ext)
⇌-symm (⇌⋈ tf) = ⇌⋈ (⇌-symm tf)
