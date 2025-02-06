module Implicit.SoundIntermAux where

open import Implicit.Language hiding (_≤_)

∋:=-total : Γ ∋= X
          → ∃[ A ](Γ ∋ X := A)
∋:=-total (Z {A = A}) with ↑ty0-total A
... | ⟨ A' , upA ⟩ = ⟨ A' , Z upA ⟩
∋:=-total (S, inΓ) = ⟨ ∋:=-total inΓ .proj₁ , S, (∋:=-total inΓ .proj₂) ⟩
∋:=-total (S∙ inΓ) with ∋:=-total inΓ
... | ⟨ A , AinΓ ⟩ = let ⟨ A' , upA ⟩ = ↑ty0-total A in ⟨ A' , S∙ AinΓ upA ⟩
∋:=-total (S^ inΓ) with ∋:=-total inΓ
... | ⟨ A , AinΓ ⟩ = let ⟨ A' , upA ⟩ = ↑ty0-total A in ⟨ A' , S^ AinΓ upA ⟩
∋:=-total (S= inΓ) with ∋:=-total inΓ
... | ⟨ A , AinΓ ⟩ = let ⟨ A' , upA ⟩ = ↑ty0-total A in ⟨ A' , S= AinΓ upA ⟩


ap-total : Γ ⊢c A
         → ∃[ A% ](Γ ≫ A ⇘ A%)
ap-total ⊢c-int = ⟨ Int , ap-int ⟩
ap-total (⊢c-var-∙ {X = X} inΓ) = ⟨ ‶ X , ap-var∙ inΓ ⟩
ap-total (⊢c-var-= inΓ) with ∋:=-total inΓ
... | ⟨ A , AinΓ ⟩ = ⟨ A , ap-var= AinΓ ⟩
ap-total (⊢c-arr cloA cloA₁) = ⟨ ap-total cloA .proj₁ `→ ap-total cloA₁ .proj₁ ,
                                   ap-arr (ap-total cloA .proj₂) (ap-total cloA₁ .proj₂) ⟩
ap-total (⊢c-∀ cloA) = ⟨ `∀ ap-total cloA .proj₁ ,
                           ap-∀ (ap-total cloA .proj₂) ⟩

ap-unique : Γ ≫ A ⇘ A%
          → Γ ≫ A ⇘ B%
          → A% ≡ B%
ap-unique ap-int ap-int = refl
ap-unique (ap-var= x) (ap-var= x₁) = ∋:=-unique x x₁
ap-unique (ap-var= x) (ap-var∙ x₁) = ⊥-elim (∙∈-:=∈-false x₁ x)
ap-unique (ap-var∙ x) (ap-var= x₁) = ⊥-elim (∙∈-:=∈-false x x₁)
ap-unique (ap-var∙ x) (ap-var∙ x₁) = refl
ap-unique (ap-arr apA apA₁) (ap-arr apB apB₁) with ap-unique apA apB | ap-unique apA₁ apB₁
... | refl | refl = refl
ap-unique (ap-∀ apA) (ap-∀ apB) with ap-unique apA apB
... | refl = refl

postulate
  ⊢n-weaken,0 : Γ ⊢n A
              → Γ ⊢n T
              → Γ , T ⊢n A

  ⊢n-weaken∙0 : Γ ⊢n A
              → ↑ty0 A ⇘ A'
              → Γ ,∙ ⊢n A'

  ⊢n-weaken^0 : Γ ⊢n A
              → ↑ty0 A ⇘ A'
              → Γ ,^ ⊢n A'

  ⊢n-weaken=0 : Γ ⊢n A
              → ↑ty0 A ⇘ A'
              → Γ ⊢n T
              → Γ ,= T ⊢n A'

∋:=-norm : Norm Γ
         → Γ ∋ X := A
         → Γ ⊢n A
∋:=-norm (nom-S, nΓ nrmA) (S, inΓ) = ⊢n-weaken,0 (∋:=-norm nΓ inΓ) nrmA
∋:=-norm (nom-S∙ nΓ) (S∙ inΓ up) = ⊢n-weaken∙0 (∋:=-norm nΓ inΓ) up
∋:=-norm (nom-S^ nΓ) (S^ inΓ up) = ⊢n-weaken^0 (∋:=-norm nΓ inΓ) up
∋:=-norm (nom-S= nΓ nomA) (Z up) = ⊢n-weaken=0 nomA up nomA
∋:=-norm (nom-S= nΓ nomA) (S= inΓ up) = ⊢n-weaken=0 (∋:=-norm nΓ inΓ) up nomA

ap-∋∙ : Γ ∋∙ X
      → Γ ≫ᵍ Γ%
      → Γ% ∋∙ X
ap-∋∙ Z (ap-S∙ apΓ) = Z
ap-∋∙ (S, inΓ) (ap-S, apΓ apA) = S, (ap-∋∙ inΓ apΓ)
ap-∋∙ (S∙ inΓ) (ap-S∙ apΓ) = S∙ (ap-∋∙ inΓ apΓ)
ap-∋∙ (S= inΓ) (ap-S= apΓ x) = S= (ap-∋∙ inΓ apΓ)
ap-∋∙ (S^ inΓ) (ap-S^ apΓ) = S^ (ap-∋∙ inΓ apΓ)

ap-∋∙-rev : Γ% ∋∙ X
          → Γ ≫ᵍ Γ%
          → Γ ∋∙ X
ap-∋∙-rev Z (ap-S∙ apΓ) = Z
ap-∋∙-rev (S, inΓ%) (ap-S, apΓ apA) = S, (ap-∋∙-rev inΓ% apΓ)
ap-∋∙-rev (S∙ inΓ%) (ap-S∙ apΓ) = S∙ (ap-∋∙-rev inΓ% apΓ)
ap-∋∙-rev (S= inΓ%) (ap-S= apΓ x) = S= (ap-∋∙-rev inΓ% apΓ)
ap-∋∙-rev (S^ inΓ%) (ap-S^ apΓ) = S^ (ap-∋∙-rev inΓ% apΓ)

ap-∋= : Γ ∋= X
      → Γ ≫ᵍ Γ%
      → Γ% ∋= X
ap-∋= Z (ap-S= apΓ x) = Z
ap-∋= (S, inΓ) (ap-S, apΓ apA) = S, (ap-∋= inΓ apΓ)
ap-∋= (S∙ inΓ) (ap-S∙ apΓ) = S∙ (ap-∋= inΓ apΓ)
ap-∋= (S= inΓ) (ap-S= apΓ x) = S= (ap-∋= inΓ apΓ)
ap-∋= (S^ inΓ) (ap-S^ apΓ) = S^ (ap-∋= inΓ apΓ)

ap-closeA : Γ ⊢c A
          → Γ ≫ᵍ Γ%
          → Norm Γ%
          → Γ% ≫ A ⇘ A%
          → Γ% ⊢n A%
ap-closeA ⊢c-int cloΓ apΓ ap-int = ⊢n-int
ap-closeA (⊢c-var-∙ inΓ) cloΓ apΓ (ap-var= x) = ⊥-elim (∙∈-:=∈-false (ap-∋∙ inΓ cloΓ) x)
ap-closeA (⊢c-var-∙ inΓ) cloΓ apΓ (ap-var∙ x) = ⊢n-var-∙ x
ap-closeA (⊢c-var-= inΓ) cloΓ apΓ (ap-var= x) = ∋:=-norm apΓ x
ap-closeA (⊢c-var-= inΓ) cloΓ apΓ (ap-var∙ x) = ⊥-elim (∙∈-=∈-false x (ap-∋= inΓ cloΓ))
ap-closeA (⊢c-arr cloA cloA₁) cloΓ apΓ (ap-arr apA apA₁) = ⊢n-arr (ap-closeA cloA cloΓ apΓ apA)
                                                                  (ap-closeA cloA₁ cloΓ apΓ apA₁)
ap-closeA (⊢c-∀ cloA) cloΓ apΓ (ap-∀ apA) = ⊢n-∀ (ap-closeA cloA (ap-S∙ cloΓ) (nom-S∙ apΓ) apA)

ap-closed : Closed Γ
          → Γ ≫ᵍ Γ%
          → Norm Γ%
ap-closed clo-Z ap-Z = nom-Z
ap-closed (clo-S, cloΓ cloA) (ap-S, apΓ apA) = nom-S, (ap-closed cloΓ apΓ) (ap-closeA cloA apΓ (ap-closed cloΓ apΓ) apA)
ap-closed (clo-S∙ cloΓ) (ap-S∙ apΓ) = nom-S∙ (ap-closed cloΓ apΓ)
ap-closed (clo-S^ cloΓ) (ap-S^ apΓ) = nom-S^ (ap-closed cloΓ apΓ)
ap-closed (clo-S= cloΓ cloA) (ap-S= apΓ x) = nom-S= (ap-closed cloΓ apΓ) (ap-closeA cloA apΓ (ap-closed cloΓ apΓ) x)

postulate
  ap-weaken=0 : Γ ≫ A ⇘ A%
              → ↑ty0 A ⇘ A'
              → ↑ty0 A% ⇘ A%'
              → Γ ,= T ≫ A' ⇘ A%'

  ap-weaken∙0 : Γ ≫ A ⇘ A%
              → ↑ty0 A ⇘ A'
              → ↑ty0 A% ⇘ A%'
              → Γ ,∙ ≫ A' ⇘ A%'

  ap-weaken^0 : Γ ≫ A ⇘ A%
              → ↑ty0 A ⇘ A'
              → ↑ty0 A% ⇘ A%'
              → Γ ,^ ≫ A' ⇘ A%'

  ap-weaken,0 : Γ ≫ A ⇘ A%
              → Γ , T ≫ A ⇘ A%

ap-var=-ap : Γ ∋ X := A
           → Γ ≫ᵍ Γ%
           → Γ% ∋ X := A%
           → Γ% ≫ A ⇘ A%
ap-var=-ap (Z up) (ap-S= apΓ x) (Z up₁) = ap-weaken=0 x up up₁
ap-var=-ap (S, inΓ) (ap-S, apΓ apA) (S, inΓ%) = ap-weaken,0 (ap-var=-ap inΓ apΓ inΓ%)
ap-var=-ap (S∙ inΓ up) (ap-S∙ apΓ) (S∙ inΓ% up₁) = ap-weaken∙0 (ap-var=-ap inΓ apΓ inΓ%) up up₁
ap-var=-ap (S^ inΓ up) (ap-S^ apΓ) (S^ inΓ% up₁) = ap-weaken^0 (ap-var=-ap inΓ apΓ inΓ%) up up₁
ap-var=-ap (S= inΓ up) (ap-S= apΓ x) (S= inΓ% up₁) = ap-weaken=0 (ap-var=-ap inΓ apΓ inΓ%) up up₁

◀∙-∋:=' : Γ ∋ punchIn k X := A'
        → Γ ◀ k ∙⇘ Γ'
        → Γ' ∋ X := A
        → A ↑ty k ⇘ A'
◀∙-∋:=' {k = #0} {#0} (S, inΓ) (◀S, newΓ x) (S, inΓ') = ◀∙-∋:=' inΓ newΓ inΓ'
◀∙-∋:=' {k = #0} {#0} (S∙ (Z up₂) up) ◀Z (Z up₁) with ↑ty-unique up₁ up₂
... | refl = up
◀∙-∋:=' {k = #0} {#0} (S∙ (S, inΓ) up) ◀Z (S, inΓ') with ∋:=-unique inΓ inΓ'
... | refl = up
◀∙-∋:=' {k = #0} {#S X} (S, inΓ) (◀S, newΓ x) (S, inΓ') = ◀∙-∋:=' inΓ newΓ inΓ'
◀∙-∋:=' {k = #0} {#S X} (S∙ inΓ up) ◀Z inΓ' with ∋:=-unique inΓ inΓ'
... | refl = up
◀∙-∋:=' {k = #S k} {#0} (Z up) (◀S= newΓ x) (Z up₁) = ↑ty-comm' z≤n x up up₁
◀∙-∋:=' {k = #S k} {#0} (S, inΓ) (◀S, newΓ x) (S, inΓ') = ◀∙-∋:=' inΓ newΓ inΓ'
◀∙-∋:=' {k = #S k} {#S X} (S, inΓ) (◀S, newΓ x) (S, inΓ') = ◀∙-∋:=' inΓ newΓ inΓ'
◀∙-∋:=' {k = #S k} {#S X} (S∙ inΓ up) (◀S∙ newΓ) (S∙ inΓ' up₁) = ↑ty-comm' z≤n (◀∙-∋:=' inΓ newΓ inΓ') up up₁
◀∙-∋:=' {k = #S k} {#S X} (S^ inΓ up) (◀S^ newΓ) (S^ inΓ' up₁) = ↑ty-comm' z≤n (◀∙-∋:=' inΓ newΓ inΓ') up up₁
◀∙-∋:=' {k = #S k} {#S X} (S= inΓ up) (◀S= newΓ x) (S= inΓ' up₁) = ↑ty-comm' z≤n (◀∙-∋:=' inΓ newΓ inΓ') up up₁

ap-↑ty : Γ ≫ A' ⇘ A%'
       → Γ ◀ k ∙⇘ Γ'
       → A ↑ty k ⇘ A'
       → Γ' ≫ A ⇘ A%
       → A% ↑ty k ⇘ A%'
ap-↑ty ap-int newΓ ↑ty-int ap-int = ↑ty-int
ap-↑ty (ap-var= x) newΓ ↑ty-var (ap-var= x₁) = ◀∙-∋:=' x newΓ x₁
ap-↑ty (ap-var= x) newΓ ↑ty-var (ap-var∙ x₁) = {!!} -- false
ap-↑ty (ap-var∙ x) newΓ ↑ty-var (ap-var= x₁) = {!!} -- false
ap-↑ty (ap-var∙ x) newΓ ↑ty-var (ap-var∙ x₁) = ↑ty-var
ap-↑ty (ap-arr apA' apA'') newΓ (↑ty-arr upA upA₁) (ap-arr apA apA₁) = ↑ty-arr (ap-↑ty apA' newΓ upA apA) (ap-↑ty apA'' newΓ upA₁ apA₁)
ap-↑ty (ap-∀ apA') newΓ (↑ty-∀ upA) (ap-∀ apA) = ↑ty-∀ (ap-↑ty apA' (◀S∙ newΓ) upA apA)

ap-∋⦂' : Γ ∋ x ⦂ A
       → Closed Γ
       → Γ ≫ᵍ Γ%
       → Γ% ≫ A ⇘ A%
       → Γ% ∋ x ⦂ A%
ap-∋⦂' Z cloΓ apΓ apA = {!!}
ap-∋⦂' (S, inΓ) cloΓ apΓ apA = {!!}
ap-∋⦂' (S∙ inΓ up) (clo-S∙ cloΓ) (ap-S∙ apΓ) apA with ap-total {!!}
... | ⟨ A% , apA' ⟩ = S∙ (ap-∋⦂' inΓ cloΓ apΓ apA') (ap-↑ty apA ◀Z up apA')
ap-∋⦂' (S^ inΓ up) cloΓ apΓ apA = {!!}
ap-∋⦂' (S= inΓ up) cloΓ apΓ apA = {!!}
