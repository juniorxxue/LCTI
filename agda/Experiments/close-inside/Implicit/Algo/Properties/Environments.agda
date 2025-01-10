module Implicit.Algo.Properties.Environments where

open import Implicit.Language
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Extension
open import Implicit.Algo.Properties.OpenClose
open import Implicit.Algo.Properties.Polarity


t-⊆-prv : Γ ⊢ Σ ⇒ e ⇒ A
        → Γ ⊆ Δ
        → Closed Δ
        → Δ ⊢ Σ ⇒ e ⇒ A

-- we split Γ to be Γ₁ ++ Γ₂, in the k-th position
-- and free variables in A must appear in Γ₂

infix 3 _∤_⊢oˣ_
data _∤_⊢oˣ_ : Env n m → Fin m → Fin m → Set where

  opnx= : Γ ∋= X
        → Γ ∤ k ⊢oˣ X

  opnx∙ : Γ ∋∙ X
        → Γ ∤ k ⊢oˣ X

  opnx^ : Γ ∋^ X
        → X #< k
        → Γ ∤ k ⊢oˣ X

infix 3 _∤_⊢o_
data _∤_⊢o_ : Env n m → Fin m → Type m → Set where

  opn-int : Γ ∤ k ⊢o Int

  opn-var : Γ ∤ k ⊢oˣ X
          → Γ ∤ k ⊢o ‶ X

  opn-arr : Γ ∤ k ⊢o A
          → Γ ∤ k ⊢o B
          → Γ ∤ k ⊢o A `→ B

  opn-∀ : Γ ,∙ ∤ #S k ⊢o A
        → Γ ∤ k ⊢o `∀ A

infix 3 _⊆_∣_⊆_by_
data _⊆_∣_⊆_by_ : Env n m → Env n m → Env n m → Env n m → Fin m → Set where

  ⊆⊆-Z : (ext : Γ ⊆ Δ)
       → Γ ⊆ Δ ∣ Γ ⊆ Δ by #0
  ⊆⊆-S, : Γ₁ ⊆ Δ₁ ∣ Γ₂ ⊆ Δ₂ by k
        → Γ₁ , A ⊆ Δ₁ , A ∣ Γ₂ , A ⊆ Δ₂ , A by k
  ⊆-S^^  : Γ₁ ⊆ Δ₁ ∣ Γ₂ ⊆ Δ₂ by k
        → Γ₁ ,^ ⊆ Δ₁ ,^ ∣ Γ₂ ,^ ⊆ Δ₂ ,^ by #S k
  ⊆-S∙∙  : Γ₁ ⊆ Δ₁ ∣ Γ₂ ⊆ Δ₂ by k
        → Γ₁ ,∙ ⊆ Δ₁ ,∙ ∣ Γ₂ ,∙ ⊆ Δ₂ ,∙ by #S k
  ⊆-S==  : Γ₁ ⊆ Δ₁ ∣ Γ₂ ⊆ Δ₂ by k
         → Γ₁ ,= A ⊆ Δ₁ ,= A ∣ Γ₂ ,= A ⊆ Δ₂ ,= A by #S k
  ⊆-S^=  : Γ₁ ⊆ Δ₁ ∣ Γ₂ ⊆ Δ₂ by k
         → Γ₁ ,^ ⊆ Δ₁ ,^ ∣ Γ₂ ,= A ⊆ Δ₂ ,= A by #S k


⊆⊆-one-input : Γ₁ ⊆ Δ₁ ∣ Γ₁ ⊆ Δ₂ by k
             → Δ₁ ≡ Δ₂
⊆⊆-one-input (⊆⊆-Z ext) = refl
⊆⊆-one-input (⊆⊆-S, exts) rewrite ⊆⊆-one-input exts = refl
⊆⊆-one-input (⊆-S^^ exts) rewrite ⊆⊆-one-input exts = refl
⊆⊆-one-input (⊆-S∙∙ exts) rewrite ⊆⊆-one-input exts = refl
⊆⊆-one-input (⊆-S== exts) rewrite ⊆⊆-one-input exts = refl


postulate
  s-⊆-prv : Γ ⊢ A ⌞ ≤ ⌝ Σ ⊣ Γ ↪ B
          → Γ ⊆ Δ
          → Δ ⊢ A ⌞ ≤ ⌝ Σ ⊣ Δ ↪ B

{-
T ++ T2 |- A <: S -| T ++ T3 ~~> B ->
fv(A) in T2   <-- unsolved variables in A must be in T2
------------------------------------
D ++ T2 |- A <: S -| D ++ T3 ~~> B
-}

{-

s-⊆-prv-gen+ : Γ₁ ⊢ A ⌞ ≤⁺ ⌝ Σ ⊣ Γ₂ ↪ B
             → Γ₁ ∤ k ⊢o A
             → Γ₁ ⊆ Δ₁ ∣ Γ₂ ⊆ Δ₂ by k -- consistently replace the inner envs, keep the outer envs, distinguished by k-th position
             → Δ₁ ⊢ A ⌞ ≤⁺ ⌝ Σ ⊣ Δ₂ ↪ B

s-⊆-prv-gen- : Γ₁ ⊢ A ⌞ ≤⁻ ⌝ τ C ⊣ Γ₂ ↪ B
             → Γ₁ ∤ k ⊢o C
             → Γ₁ ⊆ Δ₁ ∣ Γ₂ ⊆ Δ₂ by k
             → Δ₁ ⊢ A ⌞ ≤⁻ ⌝ Σ ⊣ Δ₂ ↪ B

s-⊆-prv-gen+ s-int opn-int ext rewrite ⊆⊆-one-input ext = s-int
s-⊆-prv-gen+ (s-empty clo) opn ext with ⊆⊆-one-input ext
... | refl = s-empty {!!}
s-⊆-prv-gen+ s-var opn ext with ⊆⊆-one-input ext
... | refl = s-var
s-⊆-prv-gen+ (s-ex-l^ x-in inst) (opn-var x) ext = s-ex-l^ {!!} {!!}
s-⊆-prv-gen+ (s-ex-l= x-in s) opn ext = {!!}
s-⊆-prv-gen+ (s-ex-r= x-in s) opn ext = {!!}
s-⊆-prv-gen+ (s-arr s s₁) (opn-arr opn opn₁) ext = {!!}
s-⊆-prv-gen+ (s-term-c ⊢e s) opn ext = {!!}
s-⊆-prv-gen+ (s-term-o opnA ⊢e s s₁) (opn-arr opn opn₁) ext =
  s-term-o {!!} {!!} (s-⊆-prv-gen- s opn {!!}) (s-⊆-prv-gen+ s₁ {!!} {!!})
s-⊆-prv-gen+ (s-∀ s) (opn-∀ opn) ext = s-∀ (s-⊆-prv-gen+ s opn (⊆-S∙∙ ext))
s-⊆-prv-gen+ (s-∀l s upᶜ upᵉ st₁ st₂) (opn-∀ opn) ext = s-∀l (s-⊆-prv-gen+ s {!!} (⊆-S^= ext)) upᶜ upᵉ st₁ st₂

s-⊆-prv-gen- s-int opn ext = {!!}
s-⊆-prv-gen- s-var opn ext = {!!}
s-⊆-prv-gen- (s-ex-l= x-in s) opn ext = {!!}
s-⊆-prv-gen- (s-ex-r^ x-in inst) opn ext = {!!}
s-⊆-prv-gen- (s-ex-r= x-in s) opn ext = {!!}
s-⊆-prv-gen- (s-arr s s₁) opn ext = {!!}
s-⊆-prv-gen- (s-∀ s) opn ext = {!!}
-}

t-⊆-prv (⊢lit cloΓ) ext cloΔ = ⊢lit cloΔ
t-⊆-prv (⊢var cloΓ x∈Γ) ext cloΔ = ⊢var cloΔ (⊆-in⦂ x∈Γ ext)
t-⊆-prv (⊢ann ⊢e) ext cloΔ = ⊢ann (t-⊆-prv ⊢e ext cloΔ)
t-⊆-prv (⊢app ⊢e) ext cloΔ = ⊢app (t-⊆-prv ⊢e ext cloΔ)
t-⊆-prv ⊢e'@(⊢lam₁ ⊢e) ext cloΔ with ⊢close-τ ⊢e'
... | (⊢c-arr cloA cloB) with t-⊆-prv ⊢e (var ext) (clo-S, cloΔ (⊆-closed cloA ext))
... | ind = ⊢lam₁ ind
t-⊆-prv (⊢lam₂ ⊢e up-c ⊢e₁) ext cloΔ =
  ⊢lam₂ (t-⊆-prv ⊢e ext cloΔ) up-c (t-⊆-prv ⊢e₁ (var ext) (clo-S, cloΔ (⊢closeA (t-⊆-prv ⊢e ext cloΔ))))
t-⊆-prv (⊢sub ⊢e ne gc cloΣ s) ext cloΔ =
  ⊢sub (t-⊆-prv ⊢e ext cloΔ) ne gc (⊆-closedᶜ cloΣ ext) (s-⊆-prv s ext)
t-⊆-prv (⊢tabs ⊢e) ext cloΔ = ⊢tabs (t-⊆-prv ⊢e (uvar ext) (clo-S∙ cloΔ))
