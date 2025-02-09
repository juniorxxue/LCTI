module Implicit.SoundCounterAux where

open import Implicit.Language hiding (_≤_)
open import Implicit.Interm
open import Implicit.Algo
open import Implicit.Algo.BaseCounter

-- counter based is sound
tc-sound : Γ ⊢ Σ ⇒ e ⇒ A ↡ j
         → Γ ⊢ Σ ⇒ e ⇒ A

sc-sound : Γ ⊢ A ⌞ ≤ ⌝ Σ ⊣ Δ ↪ B ↡ j
         → Γ ⊢ A ⌞ ≤ ⌝ Σ ⊣ Δ ↪ B

tc-sound (⊢lit cloΓ) = ⊢lit cloΓ
tc-sound (⊢var cloΓ x∈Γ) = ⊢var cloΓ x∈Γ
tc-sound (⊢ann ⊢e) = ⊢ann (tc-sound ⊢e)
tc-sound (⊢app ⊢e) = ⊢app (tc-sound ⊢e)
tc-sound (⊢lam₁ ⊢e) = ⊢lam₁ (tc-sound ⊢e)
tc-sound (⊢lam₂ ⊢e up-c ⊢e₁) = ⊢lam₂ (tc-sound ⊢e) up-c (tc-sound ⊢e₁)
tc-sound (⊢sub ⊢e ne gc cloΣ s) = ⊢sub (tc-sound ⊢e) ne gc cloΣ (sc-sound s)
tc-sound (⊢tabs ⊢e) = ⊢tabs (tc-sound ⊢e)

sc-sound s-int = s-int
sc-sound (s-empty clo) = s-empty clo
sc-sound s-var = s-var
sc-sound (s-ex-l^ x-in inst) = s-ex-l^ x-in inst
sc-sound (s-ex-l= x-in s) = s-ex-l= x-in (sc-sound s)
sc-sound (s-ex-r^ x-in inst) = s-ex-r^ x-in inst
sc-sound (s-ex-r= x-in s) = s-ex-r= x-in (sc-sound s)
sc-sound (s-arr s s₁) = s-arr (sc-sound s) (sc-sound s₁)
sc-sound (s-term-c ⊢e s) = s-term-c (tc-sound ⊢e) (sc-sound s)
sc-sound (s-term-o opnA ⊢e s s₁) = s-term-o opnA (tc-sound ⊢e) (sc-sound s) (sc-sound s₁)
sc-sound (s-∀ s) = s-∀ (sc-sound s)
sc-sound (s-∀l s upᶜ upᵉ st₁ st₂) = s-∀l (sc-sound s) upᶜ upᵉ st₁ st₂

infix 3 _⊢_~_
data _⊢_~_ : Env n m → Counter × Type m → Context n m → Set where

  ~Z : ∀ {Γ : Env n m} {A}
    → Γ ⊢ ⟨ Z , A ⟩ ~ □

  ~∞ : ∀ {Γ : Env n m} {A }
    → Γ ⊢ ⟨ ∞ , A ⟩ ~ τ A

  ~I : ∀ {Γ : Env n m} {j A B Σ e}
    → (⊢e : Γ ⊢ Z # e ⦂ A)
    → Γ ⊢ ⟨ j , B ⟩ ~ Σ
    → Γ ⊢ ⟨ 𝕚 j , A `→ B ⟩ ~ ([ e ]↝ Σ)

  ~C : ∀ {Γ : Env n m} {j A B Σ e}
    (⊢e : Γ ⊢ ∞ # e ⦂ A)
    → Γ ⊢ ⟨ j , B ⟩ ~ Σ
    → Γ ⊢ ⟨ 𝕔 j , A `→ B ⟩ ~ ([ e ]↝ Σ)


NonEmpty-NonZ : NonEmpty Σ
              → Γ ⊢ ⟨ j , A ⟩ ~ Σ
              → NonZ j
NonEmpty-NonZ ne-τ ~∞ = nz-∞
NonEmpty-NonZ ne-app (~I ⊢e j~Σ) = nz-I
NonEmpty-NonZ ne-app (~C ⊢e j~Σ) = nz-C

~subst0 : (Γ ,= B) ⊢ ⟨ j , A ⟩ ~ Σ
        → ⟦ B ⟧ᶜ Σ ⇘ Σ*
        → ⟦ B ⟧ A ⇘ A*
        → Γ ⊢ ⟨ j , A* ⟩ ~ Σ*
~subst0 ~Z empty st2 = ~Z
~subst0 ~∞ (fulltype st) st2 rewrite st-unique st st2 = ~∞
~subst0 (~I ⊢e j~Σ) (term st1 ste) (st-arr st2 st3) = ~I (t-subst0 ⊢e ste st2) (~subst0 j~Σ st1 st3)
~subst0 (~C ⊢e j~Σ) (term st1 ste) (st-arr st2 st3) = ~C (t-subst0 ⊢e ste st2) (~subst0 j~Σ st1 st3)

~strengthen,0 : Γ , A ⊢ ⟨ j , B ⟩ ~ Σ'
              → ↑tmᶜ0 Σ ⇘ Σ'
              → Γ ⊢ ⟨ j , B ⟩ ~ Σ
~strengthen,0 ~Z ↑tmᶜ-□ = ~Z
~strengthen,0 ~∞ ↑tmᶜ-τ = ~∞
~strengthen,0 (~I ⊢e j~Σ) (↑tmᶜ-e up-e up) = ~I (t-strengthen,0 ⊢e up-e) (~strengthen,0 j~Σ up)
~strengthen,0 (~C ⊢e j~Σ) (↑tmᶜ-e up-e up) = ~C (t-strengthen,0 ⊢e up-e) (~strengthen,0 j~Σ up)

inst-affect-one : [ A / X ] Γ ⟹ Δ
                → Γ ∋^ k
                → Δ ∋= k
                → k ≡ X
inst-affect-one (⟹^0 up) Z inΔ = refl
inst-affect-one (⟹^0 up) (S^ inΓ) (S= inΔ) = ⊥-elim (∋^-∋=-false inΓ inΔ)
inst-affect-one (⟹^S inst up1) (S^ inΓ) (S^ inΔ) = cong #S (inst-affect-one inst inΓ inΔ)
inst-affect-one (⟹∙S inst up1) (S∙ inΓ) (S∙ inΔ) = cong #S (inst-affect-one inst inΓ inΔ)
inst-affect-one (⟹,S inst) (S, inΓ) (S, inΔ) = inst-affect-one inst inΓ inΔ
inst-affect-one (⟹=S inst up1) (S= inΓ) (S= inΔ) = cong #S (inst-affect-one inst inΓ inΔ)

data ExSol (Γ : Env n m) (k : Fin m) : Set where
  is-ex  : (inΓ : Γ ∋^ k) → ExSol Γ k
  is-sol : (inΓ : Γ ∋= k) → ExSol Γ k

s-⊆-exsol : Γ ⊆ Δ
          → Γ ∋^ k
          → ExSol Δ k
s-⊆-exsol (uvar ext) (S∙ inΓ) with s-⊆-exsol ext inΓ
... | is-ex x = is-ex (S∙ x)
... | is-sol x = is-sol (S∙ x)
s-⊆-exsol (var ext) (S, inΓ) with s-⊆-exsol ext inΓ
... | is-ex x = is-ex (S, x)
... | is-sol x = is-sol (S, x)
s-⊆-exsol (evar ext) Z = is-ex Z
s-⊆-exsol (evar ext) (S^ inΓ) with s-⊆-exsol ext inΓ
... | is-ex x = is-ex (S^ x)
... | is-sol x = is-sol (S^ x)
s-⊆-exsol (evar-sol ext cloA) Z = is-sol Z
s-⊆-exsol (evar-sol ext cloA) (S^ inΓ) with s-⊆-exsol ext inΓ
... | is-ex x = is-ex (S= x)
... | is-sol x = is-sol (S= x)
s-⊆-exsol (svar ext) (S= inΓ) with s-⊆-exsol ext inΓ
... | is-ex x = is-ex (S= x)
... | is-sol x = is-sol (S= x)


find-ε : find A k ∞
       → k ε A
find-ε (f-∞ x) = x
find-ε (f-∀ fd) = ε-∀ (find-ε fd)

find-arr-r : find B k ∞
         → find (A `→ B) k ∞
find-arr-r fd = f-∞ (ε-arr-r (find-ε fd))

find-arr-l : find A k ∞
           → find (A `→ B) k ∞
find-arr-l fd = f-∞ (ε-arr-l (find-ε fd))

⊢c-¬ε : Γ ⊢c A
      → Γ ∋^ k
      → k ε A
      → ⊥
⊢c-¬ε (⊢c-var-∙ inΓ₁) inΓ ε-var = ∋^-∋∙-false inΓ inΓ₁
⊢c-¬ε (⊢c-var-= inΓ₁) inΓ ε-var = ∋^-∋=-false inΓ inΓ₁
⊢c-¬ε (⊢c-arr cloA cloA₁) inΓ (ε-arr-l inA) = ⊢c-¬ε cloA inΓ inA
⊢c-¬ε (⊢c-arr cloA cloA₁) inΓ (ε-arr-r inA) = ⊢c-¬ε cloA₁ inΓ inA
⊢c-¬ε (⊢c-∀ cloA) inΓ (ε-∀ inA) = ⊢c-¬ε cloA (S∙ inΓ) inA

-- a more restricted extending

infix 3 _⊆_w/v_
data _⊆_w/v_ : Env n m → Env n m → Fin m → Set where
  ext-Z^ : (cloA : Γ ⊢c A)
         → Γ ,^ ⊆ Γ ,= A w/v #0
  ext-Z∙ : Γ ,∙ ⊆ Γ ,∙ w/v #0
  ext-Z= : Γ ,= A ⊆ Γ ,= A w/v #0
  ext-S, : Γ ⊆ Δ w/v k
         → Γ , A ⊆ Δ , A w/v k
  ext-S^ : Γ ⊆ Δ w/v k
         → Γ ,^ ⊆ Δ ,^ w/v #S k
  ext-S∙ : Γ ⊆ Δ w/v k
         → Γ ,∙ ⊆ Δ ,∙ w/v #S k
  ext-S= : Γ ⊆ Δ w/v k
         → Γ ,= A ⊆ Δ ,= A w/v #S k

data Merge : Env n m → Env n m → Env n m → Set where
  mrg-∅    : Merge ∅ ∅ ∅
  mrg-S,   : Merge (Γ , A) (Γ , A) (Γ , A)
  mrg-S∙   : Merge (Γ ,∙) (Γ ,∙) (Γ ,∙)
  mrg-S^   : Merge (Γ ,^) (Γ ,^) (Γ ,^)
  mrg-S=   : Merge (Γ ,= A) (Γ ,= A) (Γ ,= A)
  mrg-S^-l : Merge (Γ ,^) (Γ ,= A) (Γ ,= A)
  mrg-S^-r : Merge (Γ ,= A) (Γ ,^) (Γ ,= A)

infix 3 _⊆_w/t_
data _⊆_w/t_ : Env n m → Env n m → Type m → Set where
  ext-int : Γ ⊆ Γ w/t Int
  ext-var : Γ ⊆ Δ w/v X
          → Γ ⊆ Δ w/t ‶ X
  ext-arr : Γ ⊆ Ω w/t A
          → Ω ⊆ Δ w/t B
          → Γ ⊆ Δ w/t A `→ B
  ext-∀   : Γ ,∙ ⊆ Δ ,∙ w/t A
          → Γ ⊆ Δ w/t `∀ A
{-
  ext-∀l   : Γ ,^ ⊆ Δ ,= T w/t A
           → Γ ⊆ Δ w/t `∀ A
-}

extv-∙-eq : Γ ∋∙ X
          → Γ ⊆ Δ w/v X
          → Γ ≡ Δ
extv-∙-eq Z ext-Z∙ = refl
extv-∙-eq (S, inΓ) (ext-S, ext) rewrite extv-∙-eq inΓ ext = refl
extv-∙-eq (S∙ inΓ) (ext-S∙ ext) rewrite extv-∙-eq inΓ ext = refl
extv-∙-eq (S= inΓ) (ext-S= ext) rewrite extv-∙-eq inΓ ext = refl
extv-∙-eq (S^ inΓ) (ext-S^ ext) rewrite extv-∙-eq inΓ ext = refl

extv-∙ : Γ ∋∙ X
       → Γ ⊆ Γ w/v X
extv-∙ Z = ext-Z∙
extv-∙ (S, inΓ) = ext-S, (extv-∙ inΓ)
extv-∙ (S∙ inΓ) = ext-S∙ (extv-∙ inΓ)
extv-∙ (S= inΓ) = ext-S= (extv-∙ inΓ)
extv-∙ (S^ inΓ) = ext-S^ (extv-∙ inΓ)

extv-=-eq : Γ ∋= X
          → Γ ⊆ Δ w/v X
          → Γ ≡ Δ
extv-=-eq Z ext-Z= = refl
extv-=-eq (S, inΓ) (ext-S, ext) rewrite extv-=-eq inΓ ext = refl
extv-=-eq (S∙ inΓ) (ext-S∙ ext) rewrite extv-=-eq inΓ ext = refl
extv-=-eq (S= inΓ) (ext-S= ext) rewrite extv-=-eq inΓ ext = refl
extv-=-eq (S^ inΓ) (ext-S^ ext) rewrite extv-=-eq inΓ ext = refl

extv-= : Γ ∋= X
       → Γ ⊆ Γ w/v X
extv-= Z = ext-Z=
extv-= (S, inΓ) = ext-S, (extv-= inΓ)
extv-= (S∙ inΓ) = ext-S∙ (extv-= inΓ)
extv-= (S^ inΓ) = ext-S^ (extv-= inΓ)
extv-= (S= inΓ) = ext-S= (extv-= inΓ)

ext-close-eq : Γ ⊢c A
             → Γ ⊆ Δ w/t A
             → Γ ≡ Δ
ext-close-eq ⊢c-int ext-int = refl
ext-close-eq (⊢c-var-∙ inΓ) (ext-var x) = extv-∙-eq inΓ x
ext-close-eq (⊢c-var-= inΓ) (ext-var x) = extv-=-eq inΓ x
ext-close-eq (⊢c-arr cloA cloA₁) (ext-arr ext ext₁) with ext-close-eq cloA ext
... | refl = ext-close-eq cloA₁ ext₁
ext-close-eq (⊢c-∀ cloA) (ext-∀ ext) with ext-close-eq cloA ext
... | refl = refl

ext-close : Γ ⊢c A
           → Γ ⊆ Γ w/t A
ext-close ⊢c-int = ext-int
ext-close (⊢c-var-∙ inΓ) = ext-var (extv-∙ inΓ)
ext-close (⊢c-var-= inΓ) = ext-var (extv-= inΓ)
ext-close (⊢c-arr cloA cloA₁) = ext-arr (ext-close cloA) (ext-close cloA₁)
ext-close (⊢c-∀ cloA) = ext-∀ (ext-close cloA)

inst-extv : [ A / X ] Γ ⟹ Δ
         → Γ ⊢c A
         → Γ ⊆ Δ w/v X
inst-extv (⟹^0 up) cloA = ext-Z^ (⊢c-strengthen^0 cloA up)
inst-extv (⟹^S inst up1) cloA = ext-S^ (inst-extv inst (⊢c-strengthen^0 cloA up1))
inst-extv (⟹∙S inst up1) cloA = ext-S∙ (inst-extv inst (⊢c-strengthen∙0 cloA up1))
inst-extv (⟹,S inst) cloA = ext-S, (inst-extv inst (⊢c-strengthen,0 cloA))
inst-extv (⟹=S inst up1) cloA = ext-S= (inst-extv inst (⊢c-strengthen=0 cloA up1))

s-extend-l : Γ ⊢ A ⌞ ≤⁺ ⌝ Σ ⊣ Δ ↪ B
           → Closed Γ
           → Γ ⊢cᶜ Σ
           → Γ ⊆ Δ w/t A

s-extend-r : Γ ⊢ A ⌞ ≤⁻ ⌝ (τ B) ⊣ Δ ↪ C
           → Closed Γ
           → Γ ⊢c A
           → Γ ⊆ Δ w/t B

s-all-closed : Γ ⊢ A ⌞ ≤ ⌝ Σ ⊣ Δ ↪ B
             → Closed Γ
             → Γ ⊢c A
             → Γ ⊢cᶜ Σ
             → Γ ≡ Δ
s-all-closed {≤ = ≤⁺} s cloΓ cloA cloΣ with s-extend-l s cloΓ cloΣ
... | ext = ext-close-eq cloA ext
s-all-closed {≤ = ≤⁻} {τ A} s cloΓ cloA (⊢c-τ cloA₁) with s-extend-r s cloΓ cloA
... | ext = ext-close-eq cloA₁ ext

s-extend-l s-int cloΓ cloΣ = ext-int
s-extend-l (s-empty clo) cloΓ cloΣ = ext-close clo
s-extend-l s-var cloΓ (⊢c-τ cloA) = ext-close cloA
s-extend-l (s-ex-l^ x-in inst) cloΓ (⊢c-τ cloA) = ext-var (inst-extv inst cloA)
s-extend-l (s-ex-l= x-in s) cloΓ cloΣ with s-all-closed s cloΓ (∋=-closed cloΓ x-in) cloΣ
... | refl = ext-var (extv-= (∋:=to∋= x-in))
s-extend-l (s-ex-r= x-in s) cloΓ (⊢c-τ cloA) = s-extend-l s cloΓ (⊢c-τ (∋=-closed cloΓ x-in))
s-extend-l (s-arr s s₁) cloΓ (⊢c-τ (⊢c-arr cloA cloA₁)) with s-extend-r s cloΓ cloA
                        | s-extend-l s₁ (s-closed-env s (polar-l cloΓ cloA)) (⊢c-τ (⊆-cloA cloA₁ (s-⊆ s (polar-l cloΓ cloA))))
... | r1 | r2 = ext-arr r1 r2
s-extend-l (s-term-c ⊢e s) cloΓ (⊢c-term cloe cloΣ) = ext-arr (ext-close (⊢close-τ ⊢e)) (s-extend-l s cloΓ cloΣ)
s-extend-l (s-term-o opnA ⊢e s s₁) cloΓ (⊢c-term cloe cloΣ) = let cloC = ⊢closeA ⊢e
                                                                  ext = s-⊆ s (polar-l cloΓ cloC)
  in ext-arr (s-extend-r s cloΓ cloC) (s-extend-l s₁ (s-closed-env s (polar-l cloΓ cloC)) (⊆-cloAᶜ cloΣ ext))
s-extend-l (s-∀ s) cloΓ (⊢c-τ (⊢c-∀ cloA)) = ext-∀ (s-extend-l s (clo-S∙ cloΓ) (⊢c-τ cloA))
s-extend-l (s-∀l s upᶜ upᵉ st₁ st₂) cloΓ cloΣ with s-extend-l s (clo-S^ cloΓ) (⊢cᶜ-weaken^0 cloΣ (↑tyᶜ-e upᵉ upᶜ))
... | r = ext-∀ (helper r)
  where postulate
    helper : Γ ,^ ⊆ Δ ,= B w/t A → Γ ,∙ ⊆ Δ ,∙ w/t A

s-extend-r s-int cloΓ cloA = ext-int
s-extend-r s-var cloΓ cloA = ext-close cloA
s-extend-r (s-ex-l= x-in s) cloΓ cloA = s-extend-r s cloΓ (∋=-closed cloΓ x-in)
s-extend-r (s-ex-r^ x-in inst) cloΓ cloA = ext-var (inst-extv inst cloA)
s-extend-r (s-ex-r= x-in s) cloΓ cloA with s-all-closed s cloΓ cloA (⊢c-τ (∋=-closed cloΓ x-in))
... | refl = ext-var (extv-= (∋:=to∋= x-in))
s-extend-r (s-arr s s₁) cloΓ (⊢c-arr cloA cloA₁) = ext-arr (s-extend-l s cloΓ (⊢c-τ cloA))
  (s-extend-r s₁ (s-closed-env s (polar-r cloΓ (⊢c-τ cloA))) (⊆-cloA cloA₁ (s-⊆ s (polar-r cloΓ (⊢c-τ cloA)))))
s-extend-r (s-∀ s) cloΓ (⊢c-∀ cloA) = ext-∀ (s-extend-r s (clo-S∙ cloΓ) cloA)

env-◆◇-false : Γ ◇ k ⇘ Γ₁
             → Γ ◆ k ⇘ Γ₂
             → ⊥
env-◆◇-false (◇S, newΓ1) (◆S, newΓ2) = env-◆◇-false newΓ1 newΓ2
env-◆◇-false (◇S∙ newΓ1) (◆S∙ newΓ2) = env-◆◇-false newΓ1 newΓ2
env-◆◇-false (◇S= newΓ1) (◆S= newΓ2) = env-◆◇-false newΓ1 newΓ2
env-◆◇-false (◇S^ newΓ1) (◆S^ newΓ2) = env-◆◇-false newΓ1 newΓ2

{-
-- let's try to take a merge approach
ext-◆◇ : Γ ⊆ Δ w/t A
       → Γ ◇ k ⇘ Γ'
       → Δ ◆ k ⇘ Δ' -- 3 above implies k ε A
       → Γ' ⊆ Δ' w/t A

ext-◇◇ : Γ ⊆ Δ w/t A
       → Γ ◇ k ⇘ Γ'
       → Δ ◇ k ⇘ Δ'
       → Γ' ⊆ Δ' w/t A

ext-◆◆ : Γ ⊆ Δ w/t A
       → Γ ◆ k ⇘ Γ'
       → Δ ◆ k ⇘ Δ'
       → Γ' ⊆ Δ' w/t A

ext-◆◇ ext-int newΓ newΔ = ⊥-elim (env-◆◇-false newΓ newΔ)
ext-◆◇ (ext-var x) newΓ newΔ = ext-var {!!}
ext-◆◇ (ext-arr ext ext₁) newΓ newΔ = ext-arr (ext-◆◇ ext newΓ {!!}) (ext-◆◇ ext₁ {!!} {!!})
-- ext-arr (ext-◆◇ ext newΓ {!!}) (ext-◆◇ ext₁ {!!} newΔ)
ext-◆◇ (ext-∀ ext) newΓ newΔ = ext-∀ (ext-◆◇ ext (◇S∙ newΓ) (◆S∙ newΔ))
-}
