module Implicit.Algo.Subsumption where

open import Implicit.Common
open import Implicit.Algo
-- open import Implicit.Algo.Properties

infix 4 ⟦_⟧⇒⟦_,_⟧

data ⟦_⟧⇒⟦_,_⟧ : Context n m → Apps n m → Context n m → Set where

  none-□ :
      ⟦ (Context n m ∋⦂ □) ⟧⇒⟦ nil , □ ⟧

  none-τ : ∀ {A}
    → ⟦ (Context n m ∋⦂ τ A) ⟧⇒⟦ nil , τ A ⟧

  have-e : ∀ {Σ Σ' : Context n m} {e es}
    → ⟦ Σ ⟧⇒⟦ es , Σ' ⟧
    → ⟦ [ e ]↝ Σ ⟧⇒⟦ e ∷a es , Σ' ⟧

postulate
  Σsplit-weaken0 : ∀ {Σ : Context n m} {a̅ Σ'}
    → ⟦ Σ ⟧⇒⟦ a̅ , Σ' ⟧
    → ⟦ ↑Σ0 Σ ⟧⇒⟦ up0 a̅ , ↑Σ0 Σ' ⟧


infix 4 _⊕_:=_

data _⊕_:=_ : Apps n m → Context n m → Context n m → Set where

  ⊕nil : ∀ {Σ : Context n m}
    → nil ⊕ Σ := Σ

  ⊕cons-e : ∀ {Σ : Context n m} {e a̅ Σ'}
    → a̅ ⊕ Σ := Σ'
    → (e ∷a a̅) ⊕ Σ := [ e ]↝ Σ'
    
postulate

  ⊕-weaken0 : ∀ {Σ : Context n m} {es Σ'}
    → es ⊕ Σ' := Σ
    → (up0 es) ⊕ (↑Σ0 Σ') := ↑Σ0 Σ

  s-weaken0 : ∀ {Ψ Ψ' : SEnv n m} {Σ A B B'}
    → Ψ ⊢ B ≤ Σ ⊣ Ψ' ↪ B'
    → Ψ , A ⊢ B ≤ ↑Σ0 Σ ⊣ Ψ' , A ↪ B'

  s-strengthen0 : ∀ {Ψ Ψ' : SEnv n m} {Σ A B B'}
    → Ψ , A ⊢ B ≤ ↑Σ0 Σ ⊣ Ψ' , A ↪ B'
    → Ψ ⊢ B ≤ Σ ⊣ Ψ' ↪ B'

  s-closed-r : ∀ {Ψ : SEnv n m} {Γ A B Σ}
    → 𝕎 Γ ⊢ A ≤ Σ ⊣ Ψ ↪ B
    → 𝕎 Γ ⊢ A ≤ Σ ⊣ 𝕎 Γ ↪ B

  s-closed-l : ∀ {Ψ : SEnv n m} {Γ A B Σ}
    → Ψ ⊢ A ≤ Σ ⊣ 𝕎 Γ ↪ B
    → 𝕎 Γ ⊢ A ≤ Σ ⊣ 𝕎 Γ ↪ B

  𝕎-open : ∀ {Γ : Env n m} {A}
    → ¬ (𝕎 Γ ⊢o A)

{-
  ⊢id : ∀ {Γ : Env n m} {A B e}
    → Γ ⊢ τ A ⇒ e ⇒ B
    → A ≡ B

  s-id : ∀ {Ψ Ψ' : SEnv n m} {A A' B}
    → Ψ ⊢ A ≤ τ B ⊣ Ψ' ↪ A'
    → B ≡ A'
-}    

  ⊢a→⊢c : ∀ {Γ : Env n m} {Σ e A}
    → Γ ⊢ Σ ⇒ e ⇒ A
    → 𝕎 Γ ⊢c A

  ⊢a→⊢c-τ : ∀ {Γ : Env n m} {e A B}
    → Γ ⊢ τ B ⇒ e ⇒ A
    → 𝕎 Γ ⊢c B

  ⊢a→⊢c-weaken : ∀ {Γ : Env n m} {Σ e A B}
    → Γ , B ⊢ Σ ⇒ e ⇒ A
    → 𝕎 Γ ⊢c A

s-trans : ∀ {Ψ : SEnv n m} {A Σ Σ' Σ'' Ψ' Ψ'' A' a̅ A''}
  → Ψ ⊢ A ≤ Σ ⊣ Ψ' ↪ A'
  → ⟦ Σ ⟧⇒⟦ a̅ , □ ⟧  
  → a̅ ⊕ Σ'' := Σ'
  → Ψ ⊢ A' ≤ Σ' ⊣ Ψ'' ↪ A''
  → Ψ ⊢ A ≤ Σ' ⊣ Ψ'' ↪ A''
s-trans (s-empty p) none-□ ch s2 = s2
s-trans (s-term-c cloA cloB ⊢e s1) (have-e spl) (⊕cons-e ch) (s-term-c cloA₁ cloB₁ ⊢e₁ s2) = s-term-c cloA cloB {!!} (s-trans s1 spl ch s2) -- easy
s-trans (s-term-c cloA cloB ⊢e s1) (have-e spl) (⊕cons-e ch) (s-term-o op ⊢e₁ s2 s3) = {!!} -- false case
s-trans (s-term-o op ⊢e s1 s3) (have-e spl) (⊕cons-e ch) s2 = {!!}
s-trans (s-∀l-^ s1) spl ch s2 = {!!}
s-trans (s-∀l-eq s1 st₁ st₂) spl ch s2 = {!!}


s-refl : ∀ {Ψ : SEnv n m} {A}
  → Ψ ⊢ A ≤ τ A ⊣ Ψ ↪ A -- the output context shouldn't be affected
s-refl {A = Int} = s-int
s-refl {A = ‶ X} = s-var
s-refl {A = A `→ A₁} = s-arr (s-refl {A = A}) (s-refl {A = A₁})
s-refl {A = `∀ A} = s-∀ (s-refl {A = A})

m-w-eq : ∀ (Γ : Env n m)
  → 𝕄 (𝕎 Γ) ≡ Γ
m-w-eq ∅ = refl
m-w-eq (Γ , A) rewrite m-w-eq Γ = refl
m-w-eq (Γ ,∙) rewrite m-w-eq Γ = refl
m-w-eq (Γ ,= A) rewrite m-w-eq Γ = refl

⊢refined : ∀ {Γ : Env n m} {Σ e A A'}
  → Γ ⊢ Σ ⇒ e ⇒ A
  → Γ ⊢ τ A ⇒ e ⇒ A

s-refined : ∀ {Ψ Ψ' : SEnv n m} {Σ A B}
  → Ψ ⊢ A ≤ Σ ⊣ Ψ' ↪ B
  → Ψ' ⊢ B ≤ Σ ⊣ Ψ' ↪ B

⊢refined ⊢lit = {!!}
⊢refined (⊢var x∈Γ) = {!!}
⊢refined (⊢ann ⊢e) = {!!}
⊢refined (⊢app ⊢e) = ⊢app {!!}
⊢refined (⊢lam₁ ⊢e) = {!!}
⊢refined (⊢lam₂ ⊢e ⊢e₁) = {!!}
⊢refined (⊢sub ⊢e ne gc s) = {!!}
⊢refined (⊢tabs ⊢e) = {!!}

s-refined s-int = s-int
s-refined (s-empty p) = s-empty p
s-refined s-var = s-var
s-refined (s-ex-l^ clo x-in inst) = s-refl -- s-refl
s-refined s'@(s-ex-l= clo x-in s) = s-refl -- s-refl
s-refined (s-ex-r^ clo x-in inst) = s-refl
s-refined (s-ex-r= clo x-in s) = s-refl
s-refined (s-arr s s₁) = s-refl
s-refined (s-term-c cloA cloB ⊢e s) = s-term-c {!!} {!!} {!!} (s-refined s) -- easy
s-refined s'@(s-term-o op ⊢e s s₁) = s-term-c {!!} {!!} {!!} (s-refined s₁)

{-with s-id s
... | refl = s-term-c {!!} {!!} {!!} (s-refined s₁)
-}
s-refined (s-∀ s) = s-∀ (s-refined s)
s-refined (s-∀l-^ s) = {!s-refined s!}
s-refined (s-∀l-eq s st₁ st₂) = {!s-refined s!} -- substituition lemma
-- s-term-c {!!} {!!} {!!} {!!}

⊢a-m-w : ∀ {Γ : Env n m} {Σ e A}
  → Γ ⊢ Σ ⇒ e ⇒ A
  → 𝕄 (𝕎 Γ) ⊢ Σ ⇒ e ⇒ A
⊢a-m-w {Γ = Γ} ⊢e rewrite m-w-eq Γ = ⊢e  

⊢to≤ : ∀ {Γ : Env n m} {e Σ A}
  → Γ ⊢ Σ ⇒ e ⇒ A
  → 𝕎 Γ ⊢ A ≤ Σ ⊣ 𝕎 Γ ↪ A

subsumption : ∀ {Γ : Env n m} {Σ Σ' Σ'' Ψ e A A' a̅}
  → Γ ⊢ Σ ⇒ e ⇒ A
  → ⟦ Σ ⟧⇒⟦ a̅ , □ ⟧
  → a̅ ⊕ Σ'' := Σ'
  → 𝕎 Γ ⊢ A ≤ Σ' ⊣ Ψ ↪ A'
  → Γ ⊢ Σ' ⇒ e ⇒ A'

subsumption0 : ∀ {Γ : Env n m} {Ψ Σ e A A'}
  → Γ ⊢ □ ⇒ e ⇒ A
  → 𝕎 Γ ⊢ A ≤ Σ ⊣ Ψ ↪ A'
  → Γ ⊢ Σ ⇒ e ⇒ A'
subsumption0 ⊢e s = subsumption ⊢e none-□ ⊕nil s

⊢to≤ ⊢lit = s-empty ⊢c-int
⊢to≤ ⊢e@(⊢var x∈Γ) = s-empty (⊢a→⊢c ⊢e)
⊢to≤ (⊢ann ⊢e) = {!!}
⊢to≤ (⊢app ⊢e) with ⊢to≤ ⊢e
... | s-term-c x x₁ x₂ r = r
... | s-term-o x x₁ r r₁ = s-closed-l r₁
⊢to≤ (⊢lam₁ ⊢e) = {!!}
⊢to≤ {Γ = Γ} (⊢lam₂ ⊢e ⊢e₁) = s-term-c (⊢a→⊢c ⊢e) (⊢a→⊢c-weaken ⊢e₁) (⊢a-m-w (subsumption0 {Ψ = 𝕎 Γ} ⊢e s-refl)) (s-strengthen0 (⊢to≤ ⊢e₁))
⊢to≤ (⊢sub ⊢e x x₁ x₂) = {!!}
-- s-refined x₂
⊢to≤ (⊢tabs ⊢e) = s-empty (⊢c-∀ (⊢a→⊢c ⊢e))

subsumption {Σ' = □} ⊢e none-□ ⊕nil (s-empty p) = ⊢e

subsumption {Σ' = τ _} ⊢lit spl ⊕nil s = ⊢sub ⊢lit ne-τ gc-i (s-closed-r s)
subsumption {Σ' = τ _} (⊢var x∈Γ) none-□ ⊕nil s = ⊢sub (⊢var x∈Γ) ne-τ gc-var (s-closed-r s)
subsumption {Σ' = τ _} (⊢ann ⊢e) none-□ ⊕nil s = ⊢sub (⊢ann ⊢e) ne-τ gc-ann (s-closed-r s)
subsumption {Σ' = τ _} (⊢app ⊢e) none-□ ⊕nil s with ⊢to≤ ⊢e
... | s-term-c cloA cloB ⊢e₁ s₁ = ⊢app (subsumption ⊢e (have-e none-□) (⊕cons-e ⊕nil) (s-term-c cloA cloB ⊢e₁ s))
... | s-term-o op ⊢e₁ s₁ s₂ = ⊥-elim (𝕎-open op)
subsumption {Σ' = τ _} (⊢lam₂ ⊢e ⊢e₁) (have-e spl) () s
subsumption {Σ' = τ _} (⊢sub ⊢e ne gc (s-empty p)) none-□ ⊕nil s = ⊢sub ⊢e ne-τ gc (s-closed-r s)
-- subsumption {Σ' = τ _} (⊢sub ⊢e ne gc (s-ex-l= clo x-in s₁)) none-□ ⊕nil s = ?
subsumption {Σ' = τ _} (⊢tabs ⊢e) none-□ ⊕nil s = ⊢sub (⊢tabs ⊢e) ne-τ gc-tlam (s-closed-r s)

subsumption {Σ' = [ e ]↝ Σ'} (⊢var x∈Γ) spl ch s = ⊢sub (⊢var x∈Γ) ne-app gc-var (s-closed-r s)
subsumption {Σ' = [ e ]↝ Σ'} (⊢ann ⊢e) spl ch s = ⊢sub (⊢ann ⊢e) ne-app gc-ann (s-closed-r s)
subsumption {Σ' = [ e ]↝ Σ'} (⊢app ⊢e) spl ch s with ⊢to≤ ⊢e
... | s-term-c cloA cloB ⊢e₁ s₁ = ⊢app (subsumption ⊢e (have-e spl) (⊕cons-e ch) (s-term-c cloA cloB ⊢e₁ s))
... | s-term-o op ⊢e₁ s₁ s₂ = ⊥-elim (𝕎-open op)
subsumption {Σ' = [ e ]↝ Σ'} (⊢lam₂ ⊢e ⊢e₁) (have-e spl) (⊕cons-e ch) (s-term-c cloA cloB ⊢e₂ s) = {!!}
subsumption {Σ' = [ e ]↝ Σ'} (⊢lam₂ ⊢e ⊢e₁) (have-e spl) (⊕cons-e ch) (s-term-o op ⊢e₂ s s₁) = ⊥-elim (𝕎-open op)
subsumption {Σ' = [ e ]↝ Σ'} (⊢sub ⊢e ne gc s₁) spl ch s = ⊢sub ⊢e ne-app gc (s-trans s₁ spl ch (s-closed-r s))
subsumption {Σ' = [ e ]↝ Σ'} (⊢tabs ⊢e) none-□ ch s = ⊢sub (⊢tabs ⊢e) ne-app gc-tlam (s-closed-r s)


