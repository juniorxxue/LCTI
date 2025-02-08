module Implicit.SoundIntermAux3 where

open import Implicit.Language hiding (_≤_)
open import Implicit.SoundIntermAux
open import Implicit.SoundIntermAux2

-- different to original insertion, when insert a type, we apply the environment to the operand
infix 3 _▶%_,=_⇘_
data _▶%_,=_⇘_ : Env n m → Fin (1 + m) → Type m → Env n (1 + m) → Set where
  ▶%Z  : Γ ≫ A ⇘ A%
       → Γ ▶% #0 ,= A ⇘ Γ ,= A%
  ▶%S, : Γ ▶% k ,= A ⇘ Γ'
       → (up : B ↑ty k ⇘ B')
       → Γ , B ▶% k ,= A ⇘ Γ' , B'
  ▶%S^ : Γ ▶% k ,= A ⇘ Γ'
       → ↑ty0 A ⇘ A'
       → Γ ,^ ▶% #S k ,= A' ⇘ Γ' ,^
  ▶%S∙ : Γ ▶% k ,= A ⇘ Γ'
       → ↑ty0 A ⇘ A'
       → Γ ,∙ ▶% #S k ,= A' ⇘ Γ' ,∙
  ▶%S= : Γ ▶% k ,= A ⇘ Γ'
       → ↑ty0 A ⇘ A'
       → B ↑ty k ⇘ B'
       → Γ ,= B ▶% #S k ,= A' ⇘ Γ' ,= B'

▶%-punchOut-∋= : ∀ {m} {Γ : Env n m} {k X B Γ'}
       → (¬p : k ≢ X)
       → Γ ∋= punchOut ¬p
       → Γ ▶% k ,= B ⇘ Γ'
       → Γ' ∋= X
▶%-punchOut-∋= {m = m} {k = #0} {X = #0} ¬p inΓ (▶%Z x) = Z
▶%-punchOut-∋= {m = m} {k = k} {X = #S X} ¬p inΓ (▶%Z x) = S= inΓ
▶%-punchOut-∋= {m = m} {k = k} {X = X} ¬p (S, inΓ) (▶%S, newΓ up) = S, (▶%-punchOut-∋= ¬p inΓ newΓ)
▶%-punchOut-∋= {m = suc m} {k = #S k} {X = #S X} ¬p (S^ inΓ) (▶%S^ newΓ x) = S^ (▶%-punchOut-∋= (≢-pred ¬p) inΓ newΓ)
▶%-punchOut-∋= {m = suc m} {k = #S k} {X = #S X} ¬p (S∙ inΓ) (▶%S∙ newΓ x) = S∙ (▶%-punchOut-∋= (≢-pred ¬p) inΓ newΓ)
▶%-punchOut-∋= {m = m} {k = #S k} {X = #0} ¬p Z (▶%S= newΓ x x₁) = Z
▶%-punchOut-∋= {m = m} {k = #S k} {X = #S X} ¬p (S= inΓ) (▶%S= newΓ x x₁) = S= (▶%-punchOut-∋= (≢-pred ¬p) inΓ newΓ)

▶%-punchOut-∋∙ : ∀ {m} {Γ : Env n m} {k X B Γ'}
       → (¬p : k ≢ X)
       → Γ ∋∙ punchOut ¬p
       → Γ ▶% k ,= B ⇘ Γ'
       → Γ' ∋∙ X
▶%-punchOut-∋∙ {m = m} {k = #0} {X = #0} ¬p inΓ (▶%Z x) = ⊥-elim (¬p refl)
▶%-punchOut-∋∙ {m = m} {k = k} {X = #S X} ¬p inΓ (▶%Z x) = S= inΓ
▶%-punchOut-∋∙ {m = m} {k = k} {X = X} ¬p (S, inΓ) (▶%S, newΓ up) = S, (▶%-punchOut-∋∙ ¬p inΓ newΓ)
▶%-punchOut-∋∙ {m = suc m} {k = #S k} {X = #S X} ¬p (S^ inΓ) (▶%S^ newΓ x) = S^ (▶%-punchOut-∋∙ (≢-pred ¬p) inΓ newΓ)
▶%-punchOut-∋∙ {m = suc m} {k = #S k} {X = #S X} ¬p (S∙ inΓ) (▶%S∙ newΓ x) = S∙ (▶%-punchOut-∋∙ (≢-pred ¬p) inΓ newΓ)
▶%-punchOut-∋∙ {m = m} {k = #S k} {X = #0} ¬p Z (▶%S∙ newΓ x) = Z
▶%-punchOut-∋∙ {m = m} {k = #S k} {X = #S X} ¬p (S= inΓ) (▶%S= newΓ x x₁) = S= (▶%-punchOut-∋∙ (≢-pred ¬p) inΓ newΓ)

▶%-∋= : Γ ▶% k ,= B ⇘ Γ'
      → Γ' ∋= k
▶%-∋= (▶%Z x) = Z
▶%-∋= (▶%S, newΓ up) = S, (▶%-∋= newΓ)
▶%-∋= (▶%S^ newΓ x) = S^ (▶%-∋= newΓ)
▶%-∋= (▶%S∙ newΓ x) = S∙ (▶%-∋= newΓ)
▶%-∋= (▶%S= newΓ x x₁) = S= (▶%-∋= newΓ)

ap-↑ty : Γ ≫ A ⇘ A%
       → k ¬εᵍ Γ
       → Shifted A k
       → Shifted A% k
ap-↑ty ap-int ninΓ sfd-int = sfd-int
ap-↑ty (ap-var= x) ninΓ (sfd-var x₁) = εᵍ-shifted ninΓ x
ap-↑ty (ap-var∙ x) ninΓ (sfd-var x₁) = sfd-var x₁
ap-↑ty (ap-arr apA apA₁) ninΓ (sfd-arr st st₁) = sfd-arr (ap-↑ty apA ninΓ st) (ap-↑ty apA₁ ninΓ st₁)
ap-↑ty (ap-∀ apA) ninΓ (sfd-∀ st) = sfd-∀ (ap-↑ty apA (S∙ ninΓ) st)

shifted-↑ty : Shifted A' k
            → ∃[ A ](A ↑ty k ⇘ A')
shifted-↑ty sfd-int = ⟨ Int , ↑ty-int ⟩
shifted-↑ty (sfd-var x) = ⟨ (‶ punchOut (≢-sym x)) , ↑ty-punchOut (≢-sym x) ⟩
shifted-↑ty (sfd-arr sf sf₁) = ⟨ shifted-↑ty sf .proj₁ `→ shifted-↑ty sf₁ .proj₁ ,
                                ↑ty-arr (shifted-↑ty sf .proj₂) (shifted-↑ty sf₁ .proj₂) ⟩
shifted-↑ty (sfd-∀ sf) = ⟨ `∀ shifted-↑ty sf .proj₁ , ↑ty-∀ (shifted-↑ty sf .proj₂) ⟩

▶%-∋:=-ap : Γ ▶% k ,= A ⇘ Γ'
          → k ¬εᵍ Γ
          → Γ' ∋ k := A%'
          → Γ ≫ A ⇘ A%
          → A% ↑ty k ⇘ A%'
▶%-∋:=-ap (▶%Z x) ninΓ (Z up) apA = {!!}
▶%-∋:=-ap (▶%S, newΓ up) ninΓ (S, inΓ) apA = ▶%-∋:=-ap newΓ {!!} inΓ (ap-strengthen,0 apA)
▶%-∋:=-ap (▶%S^ newΓ x) ninΓ (S^ inΓ up) apA with ▶%-∋:=-ap newΓ {!!} inΓ (ap-strengthen^0 apA x {!!})
... | ih = ↑ty-comm' z≤n ih up {!!}
▶%-∋:=-ap (▶%S∙ newΓ x) ninΓ (S∙ inΓ up) apA with ▶%-∋:=-ap newΓ {!!} inΓ (ap-strengthen∙0 apA x {!!})
... | ih = ↑ty-comm' z≤n ih up {!!}
▶%-∋:=-ap (▶%S= newΓ x x₁) ninΓ (S= inΓ up) apA with ▶%-∋:=-ap newΓ {!!} inΓ (ap-strengthen=0 apA x {!!})
... | ih = ↑ty-comm' z≤n ih up {!!}

late-ap-v2-gen : ∀ {A*% Γ'}
               → ⟦ k / B ⟧ A ⇘ A*
               → Γ ≫ A*      ⇘ A*%
               → Γ ▶% k ,= B ⇘ Γ'
               → Γ' ≫ A      ⇘ A%'
               → A*% ↑ty k   ⇘ A%'
late-ap-v2-gen st-int ap-int newΓ ap-int = ↑ty-int
late-ap-v2-gen (st-var stx-eq) apA* newΓ (ap-var= x) = ▶%-∋:=-ap newΓ {!!} x apA*
late-ap-v2-gen (st-var (stx-neq ¬p)) (ap-var= x₁) newΓ (ap-var= x) = {!!}
late-ap-v2-gen (st-var (stx-neq ¬p)) (ap-var∙ x₁) newΓ (ap-var= x) = ⊥-elim (∙∈-:=∈-false (▶%-punchOut-∋∙ ¬p x₁ newΓ) x)
late-ap-v2-gen (st-var stx-eq) apA* newΓ (ap-var∙ x) = ⊥-elim (∙∈-=∈-false x (▶%-∋= newΓ))
late-ap-v2-gen (st-var (stx-neq ¬p)) (ap-var= x₁) newΓ (ap-var∙ x) = ⊥-elim (∙∈-=∈-false x (▶%-punchOut-∋= ¬p (:=to= x₁) newΓ))
late-ap-v2-gen (st-var (stx-neq ¬p)) (ap-var∙ x₁) newΓ (ap-var∙ x) = ↑ty-punchOut ¬p
late-ap-v2-gen (st-arr stA stA₁) (ap-arr apA* apA*₁) newΓ (ap-arr apA' apA'') = ↑ty-arr (late-ap-v2-gen stA apA* newΓ apA')
                                                                                        (late-ap-v2-gen stA₁ apA*₁ newΓ apA'')
late-ap-v2-gen (st-∀ up stA) (ap-∀ apA*) newΓ (ap-∀ apA') = ↑ty-∀ (late-ap-v2-gen stA apA* (▶%S∙ newΓ up) apA')


late-ap-v2 : ∀ {C*%}
           → ⟦ B ⟧ C ⇘ C*
           → Γ% ≫ C* ⇘ C*%
           → Γ% ≫ B ⇘ B%
           → Γ% ,= B% ≫ C ⇘ C%'
           → ↑ty0 C*% ⇘ C%'
late-ap-v2 st apC* apB apC = late-ap-v2-gen st apC* (▶%Z apB) apC
