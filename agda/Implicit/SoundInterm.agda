module Implicit.SoundInterm where

open import Implicit.Language.All hiding (_≤_)
open import Implicit.Decl.All renaming (_⊢_#_⦂_ to _⊢d_#_⦂_; _⊢_#_≤_ to _⊢d_#_≤_; s-refl-∞ to sd-refl-∞)
open import Implicit.Interm.All renaming (_⊢_#_⦂_ to _⊢i_#_⦂_; _⊢_#_≤_ to _⊢i_#_≤_)

postulate

  sd-strengthen=0 : Γ ,= T ⊢d j # A' ≤ B'
              → ↑ty0 A ⇘ A'
              → ↑ty0 B ⇘ B'
              → Γ ⊢d j # A ≤ B

late-grd-gen : ∀ {A%* A%*'}
             → Γ ≫ A ⇘ A%
             → k ¬εᵍ Γ -- if we model ∙⟹, as two insertions, we could have this property implicitly.
             → ⟦ k / B ⟧ A% ⇘ A%*
             → B ↑ty k ⇘ B'
             → [ B' / k ] Γ ∙⟹ Γ'
             → Γ' ≫ A ⇘ A%*'
             → A%* ↑ty k ⇘ A%*'
late-grd-gen grd-int ninΓ st-int upB newΓ grd-int = ↑ty-int
late-grd-gen (grd-var= x) ninΓ stA% upB newΓ (grd-var= x₁) with ∙⟹-:=-eq x newΓ x₁
... | refl = st-↑ty (εᵍ-:=-¬ε ninΓ x) stA%
late-grd-gen (grd-var= x) ninΓ stA% upB newΓ (grd-var∙ x₁) = ⊥-elim (∙⟹-:=-∙-false x newΓ x₁)
late-grd-gen (grd-var∙ x) ninΓ (st-var stx-eq) upB newΓ (grd-var= x₁) with ∙⟹-∙-:=-eq x newΓ x₁
... | refl = upB
late-grd-gen (grd-var∙ x) ninΓ (st-var (stx-neq ¬p)) upB newΓ (grd-var= x₁) = ⊥-elim (∙⟹-∙-:=-neq-false x newΓ x₁ ¬p)
late-grd-gen (grd-var∙ x) ninΓ (st-var stx-eq) upB newΓ (grd-var∙ x₁) = ⊥-elim (∙⟹-∙-eq-false x newΓ x₁)
late-grd-gen (grd-var∙ x) ninΓ (st-var (stx-neq ¬p)) upB newΓ (grd-var∙ x₁) = ↑ty-punchOut ¬p
late-grd-gen (grd-arr apA apA₁) ninΓ (st-arr stA% stA%₁) upB newΓ (grd-arr apA' apA'') = ↑ty-arr (late-grd-gen apA ninΓ stA% upB newΓ apA')
                                                                                               (late-grd-gen apA₁ ninΓ stA%₁ upB newΓ apA'')
late-grd-gen {B' = B'} (grd-∀ apA) ninΓ (st-∀ up stA%) upB newΓ (grd-∀ apA') =
   let ⟨ B'' , upB' ⟩ = ↑ty0-total B' in ↑ty-∀ (late-grd-gen apA (S∙ ninΓ) stA% (↑ty-comm' z≤n upB upB' up) (∙⟹∙S newΓ upB') apA')

late-grd : ∀ {A%* A%*'}
        → Γ ,∙ ≫ A ⇘ A%
        → ⟦ B ⟧ A% ⇘ A%*
        → Γ ,= B ≫ A ⇘ A%*'
        → ↑ty0 A%* ⇘ A%*'
late-grd {B = B} apA stA% apA' =
  let ⟨ B' , upB ⟩ = ↑ty0-total B
  in late-grd-gen apA Z∙ stA% upB (∙⟹^0 upB) apA'

late-grd-v2-gen : ∀ {A*% Γ'}
               → ⟦ k / B ⟧ A ⇘ A*
               → Γ ≫ A*      ⇘ A*%
               → Γ ▶% k ,= B ⇘ Γ'
               → Γ' ≫ A      ⇘ A%'
               → A*% ↑ty k   ⇘ A%'
late-grd-v2-gen st-int grd-int newΓ grd-int = ↑ty-int
late-grd-v2-gen (st-var stx-eq) apA* newΓ (grd-var= x) = ▶%-∋:=-ap newΓ x apA*
late-grd-v2-gen (st-var (stx-neq ¬p)) (grd-var= x₁) newΓ (grd-var= x) = ▶%-punchOut-∋:= ¬p x₁ newΓ x
late-grd-v2-gen (st-var (stx-neq ¬p)) (grd-var∙ x₁) newΓ (grd-var= x) = ⊥-elim (∋∙-∋:=-false (▶%-punchOut-∋∙ ¬p x₁ newΓ) x)
late-grd-v2-gen (st-var stx-eq) apA* newΓ (grd-var∙ x) = ⊥-elim (∋∙-∋=-false x (▶%-∋= newΓ))
late-grd-v2-gen (st-var (stx-neq ¬p)) (grd-var= x₁) newΓ (grd-var∙ x) = ⊥-elim (∋∙-∋=-false x (▶%-punchOut-∋= ¬p (∋:=to∋= x₁) newΓ))
late-grd-v2-gen (st-var (stx-neq ¬p)) (grd-var∙ x₁) newΓ (grd-var∙ x) = ↑ty-punchOut ¬p
late-grd-v2-gen (st-arr stA stA₁) (grd-arr apA* apA*₁) newΓ (grd-arr apA' apA'') = ↑ty-arr (late-grd-v2-gen stA apA* newΓ apA')
                                                                                           (late-grd-v2-gen stA₁ apA*₁ newΓ apA'')
late-grd-v2-gen (st-∀ up stA) (grd-∀ apA*) newΓ (grd-∀ apA') = ↑ty-∀ (late-grd-v2-gen stA apA* (▶%S∙ newΓ up) apA')


late-grd-v2 : ∀ {C*%}
           → ⟦ B ⟧ C ⇘ C*
           → Γ% ≫ C* ⇘ C*%
           → Γ% ≫ B ⇘ B%
           → Γ% ,= B% ≫ C ⇘ C%'
           → ↑ty0 C*% ⇘ C%'
late-grd-v2 st apC* apB apC = late-grd-v2-gen st apC* (▶%Z apB) apC


sound-s : Γ ⊢i j # A ≤ B
        → Γ ≫ᵍ Γ%
        → Γ% ≫ A ⇘ A%
        → Γ% ≫ B ⇘ B%
        → Γ% ⊢d j # A% ≤ B%
sound-s (s-refl cloΓ cloA) apΓ apA apB with grd-unique apA apB
... | refl = s-refl (grd-closed cloΓ apΓ) (grd-closeA cloA apΓ (grd-closed cloΓ apΓ) apB)
sound-s (s-int cloΓ) apΓ grd-int grd-int = s-int (grd-closed cloΓ apΓ)
sound-s (s-var-∙ cloΓ inΓ) apΓ apA apB with grd-unique apA apB
... | refl = sd-refl-∞ (grd-closed cloΓ apΓ) (grd-closeA (⊢c-var-∙ inΓ) apΓ (grd-closed cloΓ apΓ) apA)
sound-s (s-var-= cloΓ inΓ) apΓ apA apB with grd-unique apA apB
... | refl = sd-refl-∞ (grd-closed cloΓ apΓ) (grd-closeA (⊢c-var-= inΓ) apΓ (grd-closed cloΓ apΓ) apA)
sound-s (s-arr₁ s s₁) apΓ (grd-arr apA apA₁) (grd-arr apB apB₁) = s-arr₁ (sound-s s apΓ apB apA) (sound-s s₁ apΓ apA₁ apB₁)
sound-s (s-arr₂ s s₁) apΓ (grd-arr apA apA₁) (grd-arr apB apB₁) = s-arr₂ (sound-s s apΓ apB apA) (sound-s s₁ apΓ apA₁ apB₁)
sound-s (s-arr₃ cloA s) apΓ (grd-arr apA apA₁) (grd-arr apB apB₁) with grd-unique apA apB
... | refl = s-arr₃ (grd-closeA cloA apΓ (grd-closed (s-closed s) apΓ) apB) (sound-s s apΓ apA₁ apB₁)
sound-s (s-∀ s) apΓ (grd-∀ apA) (grd-∀ apB) = s-∀ (sound-s s (grd-S∙ apΓ) apA apB)
sound-s (s-∀l {B = B} s ic fd stC stD) apΓ (grd-∀ {A% = A%} apA) (grd-arr apC apD) with s-closed s | s-close-r s
... | clo-S= r cloA | ⊢c-arr cloC cloD =
  let ⟨ B%  , apB% ⟩ = grd-total (grd-close-prv cloA apΓ)
      ⟨ A%* , stA% ⟩ = st0-total B% A%
      ⟨ A%*' , apA% ⟩ = grd-total (grd-close-prv (s-close-l s) (grd-S= apΓ apB%))
      ⟨ C%' , apC% ⟩ = grd-total (grd-close-prv cloC (grd-S= apΓ apB%))
      ⟨ D%' , apD% ⟩ = grd-total (grd-close-prv cloD (grd-S= apΓ apB%))
  in s-∀l {B = B%} stA% (sd-strengthen=0 (sound-s s (grd-S= apΓ apB%)
    apA% (grd-arr apC% apD%))
    (late-grd apA stA% apA%) (↑ty-arr (late-grd-v2 stC apC apB% apC%)
                                     (late-grd-v2 stD apD apB% apD%)))
                                     ic
                                     (grd-find0 fd apA)
sound-s (s-var-l inΓ s) apΓ (grd-var= x) apB = sound-s s apΓ (grd-var=-ap inΓ apΓ x) apB
sound-s (s-var-l inΓ s) apΓ (grd-var∙ x) apB = ⊥-elim (∋∙-∋:=-false (grd-∋∙-rev x apΓ) inΓ)
sound-s (s-var-r inΓ s) apΓ apA (grd-var= x) = sound-s s apΓ apA (grd-var=-ap inΓ apΓ x)
sound-s (s-var-r inΓ s) apΓ apA (grd-var∙ x) = ⊥-elim (∋∙-∋:=-false (grd-∋∙-rev x apΓ) inΓ)

sound : Γ ⊢i j # e ⦂ A
      → Γ ≫ᵍ Γ%
      → Γ% ≫ A ⇘ A%
      → Γ% ≫ᵉ e ⇘ e%
      → Γ% ⊢d j # e% ⦂ A%
sound (⊢lit cloΣ) apΓ grd-int grd-lit = ⊢lit (grd-closed cloΣ apΓ)
sound (⊢var cloΣ x∈Γ) apΓ apA grd-var = ⊢var (grd-closed cloΣ apΓ) (grd-∋⦂ x∈Γ cloΣ apΓ apA)
sound (⊢ann ⊢e) apΓ apA (grd-ann apA₁ ape) with grd-unique apA apA₁
... | refl = ⊢ann (sound ⊢e apΓ apA ape)
sound (⊢lam₁ ⊢e) apΓ (grd-arr apA apA₁) (grd-lam ape) =
  ⊢lam₁ (sound ⊢e (grd-S, apΓ apA) (grd-weaken,0 apA₁) (grde-invar,0 ape))
sound (⊢lam₂ ⊢e) apΓ (grd-arr apA apA₁) (grd-lam ape) =
  ⊢lam₂ (sound ⊢e (grd-S, apΓ apA) (grd-weaken,0 apA₁) (grde-invar,0 ape))
sound (⊢app₁ ⊢e ⊢e₁) apΓ apA (grd-app ape ape₁) with grd-total (grd-close-prv (t-close ⊢e₁) apΓ)
... | ⟨ A%' , ap' ⟩ = ⊢app₁ (sound ⊢e apΓ (grd-arr ap' apA) ape) (sound ⊢e₁ apΓ ap' ape₁)
sound (⊢app₂ ⊢e ⊢e₁) apΓ apA (grd-app ape ape₁)  with grd-total (grd-close-prv (t-close ⊢e₁) apΓ)
... | ⟨ A%' , ap' ⟩ = ⊢app₂ (sound ⊢e apΓ (grd-arr ap' apA) ape) (sound ⊢e₁ apΓ ap' ape₁)
sound (⊢sub ⊢e B≤A j≢Z) apΓ apA ape with grd-total (grd-close-prv (t-close ⊢e) apΓ)
... | ⟨ A% , ap ⟩ = ⊢sub (sound ⊢e apΓ ap ape) (sound-s B≤A apΓ ap apA) j≢Z
sound (⊢tabs ⊢e) apΓ (grd-∀ apA) (grd-tlam ape) = ⊢tabs (sound ⊢e (grd-S∙ apΓ) apA ape)
