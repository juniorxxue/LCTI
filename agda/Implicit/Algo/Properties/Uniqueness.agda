module Implicit.Algo.Properties.Uniqueness where

open import Implicit.Language
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.OpenClose

private variable
  Γ : Env n m
  Σ : Context n m
  A B A₁ A₂ : Type m
  e : Term n m
  Ψ Ψ₁ Ψ₂ : SEnv n m  

⊢unique :
    Γ ⊢ Σ ⇒ e ⇒ A
  → Γ ⊢ Σ ⇒ e ⇒ B
  → A ≡ B

≤unique-out :
    Ψ ⊢ A ≤ Σ ⊣ Ψ₁ ↪ A₁
  → Ψ ⊢ A ≤ Σ ⊣ Ψ₂ ↪ A₂
  → Ψ₁ ≡ Ψ₂

≤unique-type :
    Ψ ⊢ A ≤ Σ ⊣ Ψ₁ ↪ A₁
  → Ψ ⊢ A ≤ Σ ⊣ Ψ₂ ↪ A₂
  → A₁ ≡ A₂

≤unique-out s-int s-int = refl
≤unique-out (s-empty p) (s-empty p₁) = refl
≤unique-out (s-var clo) (s-var clo₁) = refl
≤unique-out (s-var clo) (s-ex-l^ clo₁ x-in inst) = {!!} -- false
≤unique-out (s-var clo) (s-ex-l= clo₁ x-in s2) = {!!} -- extra lemma:
≤unique-out (s-var clo) (s-ex-r^ clo₁ x-in inst) = {!!} -- fasle
≤unique-out (s-var clo) (s-ex-r= clo₁ x-in s2) = {!!} -- extra lemma
≤unique-out (s-ex-l^ clo x-in inst) (s-var clo₁) = {!!}
≤unique-out (s-ex-l^ clo x-in inst) (s-ex-l^ clo₁ x-in₁ inst₁) = {!!}
≤unique-out (s-ex-l^ clo x-in inst) (s-ex-l= clo₁ x-in₁ s2) = {!!}
≤unique-out (s-ex-l^ clo x-in inst) (s-ex-r^ clo₁ x-in₁ inst₁) = {!!}
≤unique-out (s-ex-l^ clo x-in inst) (s-ex-r= clo₁ x-in₁ s2) = {!!}
≤unique-out (s-ex-l= clo x-in s1) s2 = {!!}
≤unique-out (s-ex-r^ clo x-in inst) s2 = {!!}
≤unique-out (s-ex-r= clo x-in s1) s2 = {!!}
≤unique-out (s-arr s1 s3) (s-arr s2 s4) = {!!}
≤unique-out (s-term-c cloA ⊢e s1) (s-term-c cloA₁ ⊢e₁ s2) = ≤unique-out s1 s2
≤unique-out (s-term-c cloA ⊢e s1) (s-term-o opnA ⊢e₁ s2 s3) = {!!}
≤unique-out (s-term-o opnA ⊢e s1 s3) (s-term-c cloA ⊢e₁ s2) = {!!}
≤unique-out (s-term-o opnA ⊢e s1 s3) (s-term-o opnA₁ ⊢e₁ s2 s4) = {!!}
≤unique-out (s-∀ s1) (s-∀ s2) with ≤unique-out s1 s2
... | refl = refl
≤unique-out (s-∀l s1 upᶜ upᵉ st₁ st₂) (s-∀l s2 upᶜ₁ upᵉ₁ st₃ st₄) = {!!}

≤unique-type s-int s-int = refl
≤unique-type (s-empty p) (s-empty p₁) = refl
≤unique-type (s-var clo) (s-var clo₁) = refl
≤unique-type (s-var clo) (s-ex-l^ clo₁ x-in inst) = refl
≤unique-type (s-var clo) (s-ex-l= clo₁ x-in s2) = refl
≤unique-type (s-var clo) (s-ex-r^ clo₁ x-in inst) = refl
≤unique-type (s-var clo) (s-ex-r= clo₁ x-in s2) = refl
≤unique-type (s-ex-l^ clo x-in inst) (s-var clo₁) = refl
≤unique-type (s-ex-l^ clo x-in inst) (s-ex-l^ clo₁ x-in₁ inst₁) = refl
≤unique-type (s-ex-l^ clo x-in inst) (s-ex-l= clo₁ x-in₁ s2) = refl
≤unique-type (s-ex-l^ clo x-in inst) (s-ex-r^ clo₁ x-in₁ inst₁) = refl
≤unique-type (s-ex-l^ clo x-in inst) (s-ex-r= clo₁ x-in₁ s2) = refl
≤unique-type (s-ex-l= clo x-in s1) (s-var clo₁) = refl
≤unique-type (s-ex-l= clo x-in s1) (s-ex-l^ clo₁ x-in₁ inst) = refl
≤unique-type (s-ex-l= clo x-in s1) (s-ex-l= clo₁ x-in₁ s2) = refl
≤unique-type (s-ex-l= clo x-in s1) (s-ex-r^ clo₁ x-in₁ inst) = refl
≤unique-type (s-ex-l= clo x-in s1) (s-ex-r= clo₁ x-in₁ s2) = refl
≤unique-type (s-ex-r^ clo x-in inst) (s-var clo₁) = refl
≤unique-type (s-ex-r^ clo x-in inst) (s-ex-l^ clo₁ x-in₁ inst₁) = refl
≤unique-type (s-ex-r^ clo x-in inst) (s-ex-l= clo₁ x-in₁ s2) = refl
≤unique-type (s-ex-r^ clo x-in inst) (s-ex-r^ clo₁ x-in₁ inst₁) = refl
≤unique-type (s-ex-r^ clo x-in inst) (s-ex-r= clo₁ x-in₁ s2) = refl
≤unique-type (s-ex-r= clo x-in s1) (s-var clo₁) = refl
≤unique-type (s-ex-r= clo x-in s1) (s-ex-l^ clo₁ x-in₁ inst) = refl
≤unique-type (s-ex-r= clo x-in s1) (s-ex-l= clo₁ x-in₁ s2) = refl
≤unique-type (s-ex-r= clo x-in s1) (s-ex-r^ clo₁ x-in₁ inst) = refl
≤unique-type (s-ex-r= clo x-in s1) (s-ex-r= clo₁ x-in₁ s2) = refl
≤unique-type (s-arr s1 s3) (s-arr s2 s4) = refl
≤unique-type (s-term-c cloA ⊢e s1) (s-term-c cloA₁ ⊢e₁ s2) rewrite ⊢unique ⊢e ⊢e₁ | ≤unique-type s1 s2 = refl
≤unique-type (s-term-c cloA ⊢e s1) (s-term-o opnA ⊢e₁ s2 s3) = ⊥-elim (⊢c-⊢o-⊥ cloA opnA)
≤unique-type (s-term-o opnA ⊢e s1 s3) (s-term-c cloA ⊢e₁ s2) = ⊥-elim (⊢c-⊢o-⊥ cloA opnA)
≤unique-type (s-term-o opnA ⊢e s1 s3) (s-term-o opnA₁ ⊢e₁ s2 s4) rewrite ⊢unique ⊢e ⊢e₁
                                                                       | ≤unique-type s1 s2
                                                                       | ≤unique-out s1 s2
                                                                       | ≤unique-type s3 s4 = refl
≤unique-type (s-∀ s1) (s-∀ s2) = cong `∀_ (≤unique-type s1 s2)
≤unique-type (s-∀l s1 upᶜ upᵉ st₁ st₂) (s-∀l s2 upᶜ₁ upᵉ₁ st₃ st₄) = {!!}


⊢unique ⊢lit ⊢lit = refl
⊢unique (⊢var x∈Γ) (⊢var x∈Γ₁) = {!!}
⊢unique (⊢ann t1) (⊢ann t2) = refl
⊢unique (⊢app t1) (⊢app t2) with ⊢unique t1 t2
... | refl = refl
⊢unique (⊢lam₁ t1) (⊢lam₁ t2) rewrite ⊢unique t1 t2 = refl
⊢unique (⊢lam₂ t1 up-c t3) (⊢lam₂ t2 up-c₁ t4) = {!!}
⊢unique (⊢sub t1 ne gc s) (⊢sub t2 ne₁ gc₁ s₁) = {!!}
⊢unique (⊢tabs t1) (⊢tabs t2) = cong `∀_ (⊢unique t1 t2)
