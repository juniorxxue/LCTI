module Implicit.SoundIntermAux where

open import Implicit.Language hiding (_≤_)

apx-var-∙ : Γ ∋∙ X
          → Γ ≫ˣ X ⇘ ‶ X
apx-var-∙ Z = Z∙
apx-var-∙ (S, inΓ) = S, (apx-var-∙ inΓ)
apx-var-∙ (S∙ inΓ) = S∙ (apx-var-∙ inΓ) ↑ty-var
apx-var-∙ (S= inΓ) = S= (apx-var-∙ inΓ) ↑ty-var
apx-var-∙ (S^ inΓ) = S^ (apx-var-∙ inΓ) ↑ty-var



apx-total : Γ ∋= X
          → ∃[ A% ](Γ ≫ˣ X ⇘ A%)

ap-total : Γ ⊢c A
         → ∃[ A% ](Γ ≫ A ⇘ A%)

apx-total (Z {A = A}) = let ⟨ A' , up ⟩ = ↑ty0-total A in ⟨ A' , Z= {!!} {!!} ⟩
apx-total (S, inΓ) = ⟨ apx-total inΓ .proj₁ , S, (apx-total inΓ .proj₂) ⟩
apx-total (S∙ inΓ) with apx-total inΓ
... | ⟨ A% , apA ⟩ = let ⟨ A%' , upA% ⟩ = ↑ty0-total A% in ⟨ A%' , (S∙ apA upA%) ⟩
apx-total (S^ inΓ) with apx-total inΓ
... | ⟨ A% , apA ⟩ = let ⟨ A%' , upA% ⟩ = ↑ty0-total A% in ⟨ A%' , (S^ apA upA%) ⟩
apx-total (S= inΓ) with apx-total inΓ
... | ⟨ A% , apA ⟩ = let ⟨ A%' , upA% ⟩ = ↑ty0-total A% in ⟨ A%' , (S= apA upA%) ⟩

ap-total ⊢c-int = ⟨ Int , ap-int ⟩
ap-total (⊢c-var-∙ {X = X} inΓ) = ⟨ ‶ X , (ap-var (apx-var-∙ inΓ)) ⟩
ap-total (⊢c-var-= inΓ) with apx-total inΓ
... | ⟨ A% , apA ⟩ = ⟨ A% , (ap-var apA) ⟩
ap-total (⊢c-arr cloA cloA₁) = ⟨ ap-total cloA .proj₁ `→ ap-total cloA₁ .proj₁ ,
                                ap-arr (ap-total cloA .proj₂) (ap-total cloA₁ .proj₂) ⟩
ap-total (⊢c-∀ cloA) = ⟨ `∀ ap-total cloA .proj₁ , ap-∀ (ap-total cloA .proj₂) ⟩
