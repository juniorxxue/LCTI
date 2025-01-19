module Implicit.SoundCounterAux where

open import Implicit.Language hiding (_≤_)
open import Implicit.Decl renaming (find to d-find)
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


-- define this relation is doable, but the weakening and subst lemma rely the properties of algo system
infix 3 _⊢_∻_
data _⊢_∻_ : Env n m → Counter × Type m → Context n m → Set where

  ∻Z : ∀ {Γ : Env n m} {A}
    → Γ ⊢ ⟨ Z , A ⟩ ∻ □

  ∻∞ : ∀ {Γ : Env n m} {A }
    → Γ ⊢ ⟨ ∞ , A ⟩ ∻ τ A

  ∻I : ∀ {Γ : Env n m} {j A B Σ e}
    → (⊢e : Γ ⊢ □ ⇒ e ⇒ A)
    → Γ ⊢ ⟨ j , B ⟩ ∻ Σ
    → Γ ⊢ ⟨ 𝕚 j , A `→ B ⟩ ∻ ([ e ]↝ Σ)

  ∻C : ∀ {Γ : Env n m} {j A B Σ e}
    → (⊢e : Γ ⊢ τ A ⇒ e ⇒ A)
    → Γ ⊢ ⟨ j , B ⟩ ∻ Σ
    → Γ ⊢ ⟨ 𝕔 j , A `→ B ⟩ ∻ ([ e ]↝ Σ)

{-
tc-∻ : Γ ⊢ Σ ⇒ e ⇒ A ↡ j
     → Γ ⊢ ⟨ j , A ⟩ ∻ Σ
tc-∻ (⊢lit cloΓ) = ∻Z
tc-∻ (⊢var cloΓ x∈Γ) = ∻Z
tc-∻ (⊢ann ⊢e) = ∻Z
tc-∻ (⊢app ⊢e) with tc-∻ ⊢e
... | ∻I ⊢e₁ r = r
... | ∻C ⊢e₁ r = r
tc-∻ (⊢lam₁ ⊢e) with ⊢id0 (tc-sound ⊢e)
... | refl = ∻∞
tc-∻ (⊢lam₂ ⊢e up-c ⊢e₁) = ∻I (tc-sound ⊢e) {!g!}
tc-∻ (⊢sub ⊢e ne gc cloΣ s) = {!!}
tc-∻ (⊢tabs ⊢e) = ∻Z
-}



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


postulate
  ~subst0 : (Γ ,= B) ⊢ ⟨ j , A ⟩ ~ Σ
        → ⟦ B ⟧ᶜ Σ ⇘ Σ'
        → ⟦ B ⟧ A ⇘ A'
        → Γ ⊢ ⟨ j , A' ⟩ ~ Σ'


  ~weaken,0 : Γ , A ⊢ ⟨ j , B ⟩ ~ Σ'
          → ↑tmᶜ0 Σ ⇘ Σ'
          → Γ ⊢ ⟨ j , B ⟩ ~ Σ

{-
~subst0 ~Z empty st2 = ~Z
~subst0 ~∞ (fulltype st) st2 rewrite st-unique st st2 = ~∞
~subst0 (~I ⊢e j~Σ) (term st1 ste) (st-arr st2 st3) = ~I {!!} {!!}
~subst0 (~C ⊢e j~Σ) st1 st2 = {!!}
-}




{-
~weaken,0 ~Z ↑tmᶜ-□ = ~Z
~weaken,0 ~∞ ↑tmᶜ-τ = ~∞
~weaken,0 (~I ⊢e j~Σ) (↑tmᶜ-e up-e up) = ~I {!!} {!!}
~weaken,0 (~C ⊢e j~Σ) up = {!!}
-}


inst-affect-one : [ A / X ] Γ ⟹ Δ
                → Γ ∋^ k
                → Δ ∋= k
                → k ≡ X
inst-affect-one (⟹^0 up) Z inΔ = refl
inst-affect-one (⟹^0 up) (S^ inΓ) (S= inΔ) = ⊥-elim (^∈-=∈-false inΓ inΔ)
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


find-ε : d-find A k ∞
       → k ε A
find-ε (f-∞ x) = x
find-ε (f-∀ fd) = ε-∀ (find-ε fd)

find-arr-r : d-find B k ∞
         → d-find (A `→ B) k ∞
find-arr-r fd = f-∞ (ε-arr-r (find-ε fd))

find-arr-l : d-find A k ∞
           → d-find (A `→ B) k ∞
find-arr-l fd = f-∞ (ε-arr-l (find-ε fd))

⊢c-¬ε : Γ ⊢c A
      → Γ ∋^ k
      → k ε A
      → ⊥
⊢c-¬ε (⊢c-var-∙ inΓ₁) inΓ ε-var = ^∈-∙∈-false inΓ inΓ₁
⊢c-¬ε (⊢c-var-= inΓ₁) inΓ ε-var = ^∈-=∈-false inΓ inΓ₁
⊢c-¬ε (⊢c-arr cloA cloA₁) inΓ (ε-arr-l inA) = ⊢c-¬ε cloA inΓ inA
⊢c-¬ε (⊢c-arr cloA cloA₁) inΓ (ε-arr-r inA) = ⊢c-¬ε cloA₁ inΓ inA
⊢c-¬ε (⊢c-∀ cloA) inΓ (ε-∀ inA) = ⊢c-¬ε cloA (S∙ inΓ) inA


-- a more restricted extending

infix 3 _⊆_w/v_
data _⊆_w/v_ : Env n m → Env n m → Fin m → Set where
  ext-z : (cloA : Γ ⊢c A)
        → Γ ,^ ⊆ Γ ,= A w/v #0
  ext-S, : Γ ⊆ Δ w/v k
         → Γ , A ⊆ Δ , A w/v k
  ext-S^ : Γ ⊆ Δ w/v k
         → Γ ,^ ⊆ Δ ,^ w/v #S k
  ext-S∙ : Γ ⊆ Δ w/v k
         → Γ ,∙ ⊆ Δ ,∙ w/v #S k
  ext-S= : Γ ⊆ Δ w/v k
         → Γ ,∙ ⊆ Δ ,∙ w/v #S k

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
  ext-arr : Γ ⊆ Δ₁ w/t A
          → Γ ⊆ Δ₂ w/t B
          → Merge Δ₁ Δ₂ Δ
          → Γ ⊆ Δ w/t A `→ B
  ext-∀   : Γ ,∙ ⊆ Δ ,∙ w/t A
          → Γ ⊆ Δ w/t `∀ A

{-
data Extend : Env n m → Env n m → Type m → Set where
  base : Extend ∅ ∅ A
  uvar : Extend Γ Δ (`∀ A)
       → Extend (Γ ,∙) (Δ ,∙) A
  var : Extend Γ Δ A
      → Extend (Γ , B) (Δ , B) A
  evar : Extend Γ Δ (`∀ A)
       → Extend (Γ ,^) (Δ ,^) A
  evar-sol : Extend Γ Δ (`∀ A)
           → #0 ε A
           → Extend (Γ ,^) (Δ ,= B) A
  svar : Extend Γ Δ (`∀ A)
        → Extend (Γ ,= B) (Δ ,= B) A

extend-close : Extend Γ Δ A
             → Γ ⊢c A
             → Γ ≡ Δ
extend-close base cloA = refl
extend-close (uvar ext) cloA rewrite extend-close ext (⊢c-∀ cloA) = refl
extend-close (var ext) cloA rewrite extend-close ext (⊢c-strengthen,0 cloA) = refl
extend-close (evar ext) cloA rewrite extend-close ext (⊢c-∀ {!!}) = refl
extend-close (evar-sol ext x) cloA = {!!}
extend-close (svar ext) cloA = {!!}

extend-same : Γ ⊢c A
            → Extend Γ Γ A
extend-same {Γ = ∅} cloA = base
extend-same {Γ = Γ , A} cloA = var (extend-same {Γ = Γ} (⊢c-strengthen,0 cloA))
extend-same {Γ = Γ ,^} cloA = evar (extend-same {Γ = Γ} (⊢c-∀ {!!}))
extend-same {Γ = Γ ,∙} cloA = uvar (extend-same {Γ = Γ} (⊢c-∀ cloA))
extend-same {Γ = Γ ,= A} cloA = svar (extend-same {Γ = Γ} (⊢c-∀ {!!}))

extend-inst : [ B / X ] Γ ⟹ Δ
            → Extend Γ Δ (‶ X)
extend-inst (⟹^0 up) = evar-sol (extend-same (⊢c-∀ (⊢c-var-∙ Z))) ε-var
extend-inst (⟹^S inst up1) = evar {!extend-inst inst!}
extend-inst (⟹∙S inst up1) = {!!}
extend-inst (⟹,S inst) = {!!}
extend-inst (⟹=S inst up1) = {!!}
-}

merge-refl : Merge Γ Γ Δ
           → Γ ≡ Δ
merge-refl mrg-∅ = refl
merge-refl mrg-S, = refl
merge-refl mrg-S∙ = refl
merge-refl mrg-S^ = refl
merge-refl mrg-S= = refl

extv-∙ : Γ ∋∙ X
       → Γ ⊆ Δ w/v X
       → Γ ≡ Δ
extv-∙ (S, inΓ) (ext-S, ext) rewrite extv-∙ inΓ ext = refl
extv-∙ (S∙ inΓ) (ext-S∙ ext) rewrite extv-∙ inΓ ext = refl
extv-∙ (S∙ inΓ) (ext-S= ext) rewrite extv-∙ inΓ ext = refl
extv-∙ (S^ inΓ) (ext-S^ ext) rewrite extv-∙ inΓ ext = refl

extv-= : Γ ∋= X
       → Γ ⊆ Δ w/v X
       → Γ ≡ Δ
extv-= (S, inΓ) (ext-S, ext) rewrite extv-= inΓ ext = refl
extv-= (S∙ inΓ) (ext-S∙ ext) rewrite extv-= inΓ ext = refl
extv-= (S∙ inΓ) (ext-S= ext) rewrite extv-= inΓ ext = refl
extv-= (S^ inΓ) (ext-S^ ext) rewrite extv-= inΓ ext = refl

ext-close : Γ ⊢c A
          → Γ ⊆ Δ w/t A
          → Γ ≡ Δ
ext-close ⊢c-int ext-int = refl
ext-close (⊢c-var-∙ inΓ) (ext-var x) = extv-∙ inΓ x
ext-close (⊢c-var-= inΓ) (ext-var x) = extv-= inΓ x
ext-close (⊢c-arr cloA cloA₁) (ext-arr ext ext₁ x) with ext-close cloA ext | ext-close cloA₁ ext₁
... | refl | refl = merge-refl x
ext-close (⊢c-∀ cloA) (ext-∀ ext) with ext-close cloA ext
... | refl = refl

ext-close' : Γ ⊢c A
           → Γ ⊆ Γ w/t A
ext-close' ⊢c-int = ext-int
ext-close' (⊢c-var-∙ inΓ) = {!!}
ext-close' (⊢c-var-= inΓ) = {!!}
ext-close' (⊢c-arr cloA cloA₁) = {!!}
ext-close' (⊢c-∀ cloA) = ext-∀ (ext-close' cloA)

s-extend-l : Γ ⊢ A ⌞ ≤⁺ ⌝ Σ ⊣ Δ ↪ B
           → Closed Γ
           → Γ ⊢cᶜ Σ
           → Γ ⊆ Δ w/t A
s-extend-l s-int cloΓ cloΣ = ext-int
s-extend-l (s-empty clo) cloΓ cloΣ = {!!}
s-extend-l s-var cloΓ cloΣ = {!!}
s-extend-l (s-ex-l^ x-in inst) cloΓ cloΣ = {!!}
s-extend-l (s-ex-l= x-in s) cloΓ cloΣ = {!!}
s-extend-l (s-ex-r= x-in s) cloΓ cloΣ = {!!}
s-extend-l (s-arr s s₁) cloΓ cloΣ = {!!}
s-extend-l (s-term-c ⊢e s) cloΓ cloΣ = {!!}
s-extend-l (s-term-o opnA ⊢e s s₁) cloΓ cloΣ = {!!}
s-extend-l (s-∀ s) cloΓ cloΣ = {!!}
s-extend-l (s-∀l s upᶜ upᵉ st₁ st₂) cloΓ cloΣ with s-extend-l s (clo-S^ cloΓ) {!!}
... | r = ext-∀ {!!}



{-
s-extend-l : Γ ⊢ A ⌞ ≤⁺ ⌝ Σ ⊣ Δ ↪ B
           → Closed Γ
           → Γ ⊢cᶜ Σ
           → Extend Γ Δ A
s-extend-r : Γ ⊢ A ⌞ ≤⁻ ⌝ (τ B) ⊣ Δ ↪ C
           → Closed Γ
           → Γ ⊢c A
           → Extend Γ Δ B

s-extend-l s-int cloΓ cloΣ = extend-same ⊢c-int
s-extend-l (s-empty clo) cloΓ cloΣ = extend-same clo
s-extend-l s-var cloΓ (⊢c-τ cloA) = extend-same cloA
s-extend-l (s-ex-l^ x-in inst) cloΓ cloΣ = {!!}
s-extend-l (s-ex-l= x-in s) cloΓ cloΣ = {!!}
s-extend-l (s-ex-r= x-in s) cloΓ cloΣ = {!!}
s-extend-l (s-arr s s₁) cloΓ cloΣ = {!!}
s-extend-l (s-term-c ⊢e s) cloΓ cloΣ = {!!}
s-extend-l (s-term-o opnA ⊢e s s₁) cloΓ cloΣ = {!!}
s-extend-l (s-∀ s) cloΓ cloΣ = {!!}
-- with s-extend-l s (clo-S∙ cloΓ) (⊢c-τ {!cloΓ!})
s-extend-l (s-∀l s upᶜ upᵉ st₁ st₂) cloΓ cloΣ = {!!}

s-extend-r s cloΓ cloA = {!!}

-}

s-all-closed : Γ ⊢ A ⌞ ≤ ⌝ Σ ⊣ Δ ↪ B
             → Closed Γ
             → Γ ⊢c A
             → Γ ⊢cᶜ Σ
             → Γ ≡ Δ
s-all-closed {≤ = ≤⁺} s cloΓ cloA cloΣ with s-extend-l s cloΓ cloΣ
... | ext = ext-close cloA ext
