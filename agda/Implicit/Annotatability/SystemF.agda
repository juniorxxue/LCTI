module Implicit.Annotatability.SystemF where

open import Implicit.Language.All
open import Implicit.Decl.Typing

infix 3 _𝕄_
data _𝕄_ : Type m → Type m → Set where

  𝕄-arr : A `→ B 𝕄 A `→ B
  M-∀ : ⟦ T ⟧ A ⇘ A*
       → A* 𝕄 B `→ C
       → `∀ A 𝕄 B `→ C

infix 3 _⊢_needFunT_
data _⊢_needFunT_ : Env n m → Type m → Counter m → Set where
  ndft-var1 : Γ ∋= X
            → Γ ⊢ ‶ X needFunT Z
  ndft-var2 : Γ ∋^ X
            → Γ ⊢ ‶ X needFunT ∞
  ndft-arr1 : Γ ⊢c A
            → Γ ⊢ B needFunT j
            → Γ ⊢ A `→ B needFunT 𝕔 j
  ndft-arr2 : Γ ⊢o A
            → Γ ⊆ Δ w/t A
            → Δ ⊢ B needFunT j
            → Γ ⊢ A `→ B needFunT 𝕚 j
  ndft-∀ : Γ ,^ ⊢ A needFunT j'
         → ↑tyʲ0 j ⇘ j'
         → Γ ⊢ `∀ A needFunT j

infix 3 _⊢_needFun_
data _⊢_needFun_ : Env n m → Term n m → Counter m → Set where
  ndf-var : Γ ∋ x ⦂ A
          → Γ ⋈ ⊢ A needFunT j
          → Γ ⊢ ` x needFun j
  ndf-lam : Γ , A ⊢ e needFun j
          → Γ ⊢ ƛ e needFun 𝕚 j
  ndf-app1 : Γ ⊢ e₁ needFun 𝕚 j
           → Γ ⊢ e₁ · e₂ needFun j
  ndf-app2 : Γ ⊢ e₁ needFun 𝕔 j
           → Γ ⊢ e₁ · e₂ needFun j

infix 3 _⊢_need_
data _⊢_need_ : Env n m → Term n m → Counter m → Set where
  nd-lit : Γ ⊢ lit n need Z
  nd-var : Γ ⊢ ` x need Z
  nd-lam : Γ , A ⊢ e need j
         → Γ ⊢ ƛ e need 𝕚 j
  nd-app1 : Γ ⊢ e₁ needFun 𝕚 j
          → Γ ⊢ e₁ · e₂ need j
  nd-app2 : Γ ⊢ e₁ needFun 𝕔 j
          → Γ ⊢ e₁ · e₂ need j

infix 3 _⊢_⦂_⟶_
data _⊢_⦂_⟶_ : Env n m → Term n m → Type m → Term n m → Set where

  ela-lit : Γ ⊢ (lit n) ⦂ Int ⟶ (lit n)
  ela-var : Γ ∋ x ⦂ A
          → Γ ⊢ ` x ⦂ A ⟶ ` x
  ela-lam : Γ , A ⊢ e ⦂ B ⟶ e'
          → Γ ⊢ ƛ e ⦂ A `→ B ⟶ ƛ e'
  ela-app1 : (ndf : Γ ⊢ e₁ needFun 𝕔 j)
           → Γ ⊢ e₁ ⦂ A ⟶ e₁'
           → A 𝕄 B `→ C
           → Γ ⊢ e₂ ⦂ B ⟶ e₂'
           → Γ ⊢ e₁ · e₂ ⦂ C ⟶ e₁' · e₂'
  ela-app2 : (nd : Γ ⊢ e₂ need Z)
           → Γ ⊢ e₁ ⦂ A ⟶ e₁'
           → A 𝕄 B `→ C
           → Γ ⊢ e₂ ⦂ B ⟶ e₂'
           → Γ ⊢ e₁ · e₂ ⦂ C ⟶ e₁' · e₂'
  ela-app3 : (ndf : Γ ⊢ e₁ needFun 𝕚 j)
           → (nd : Γ ⊢ e₂ need 𝕚 j')
           → Γ ⊢ e₁ ⦂ A ⟶ e₁'
           → A 𝕄 B `→ C
           → Γ ⊢ e₂ ⦂ B ⟶ e₂'
           → Γ ⊢ e₁ · e₂ ⦂ C ⟶ e₁' · (e₂' ⦂ A)


_ : ∅ , `∀ (‶ #0 `→ ‶ #0) ⊢ (` #0) · (lit 1) ⦂ Int ⟶ (` #0) · (lit 1)
_ = ela-app2 nd-lit (ela-var Z)
     (M-∀ (st-arr (st-var stx-eq) (st-var stx-eq)) 𝕄-arr) ela-lit

_ : ∅ , `∀ (‶ #0 `→ ‶ #0) ⊢ (` #0) · (ƛ ` #0) ⦂ Int `→ Int ⟶ (` #0) · ((ƛ ` #0) ⦂ Int `→ Int)
_ = {!!}

postulate
  needFun-unique : Γ ⊢ e needFun j₁
                 → Γ ⊢ e needFun j₂
                 → j₁ ≡ j₂


𝕄-finite : A 𝕄 B
         → B 𝕄 C
         → B ≡ C
𝕄-finite 𝕄-arr 𝕄-arr = refl
𝕄-finite (M-∀ x m1) 𝕄-arr = refl

𝕄-finite' : A 𝕄 B `→ C
          → C 𝕄 D
          → C ≡ D
𝕄-finite' 𝕄-arr m2 = {!!}
𝕄-finite' (M-∀ x m1) m2 = 𝕄-finite' m1 m2


annotatability : Γ ⊢ e ⦂ A ⟶ e'
               → Γ ⊢ e need j
               → Γ ⊢ j # e' ⦂ A

annotatability-fun : Γ ⊢ e ⦂ A ⟶ e'
                   → Γ ⊢ e needFun j
                   → A 𝕄 B
                   → Γ ⊢ j # e' ⦂ B

annotatability ela-lit nd-lit = ⊢lit {!!}
annotatability (ela-var x) nd-var = ⊢var {!!} x
annotatability (ela-lam ⊢e) (nd-lam nd) = ⊢lam₂ (annotatability ⊢e {!!})
annotatability (ela-app1 ndf ⊢e x ⊢e₁) (nd-app1 x₁) = ⊥-elim {!!}
annotatability (ela-app1 ndf ⊢e x ⊢e₁) (nd-app2 x₁)
  with refl ← needFun-unique x₁ ndf = ⊢app₁ (annotatability-fun ⊢e x₁ x) {!!}
annotatability (ela-app2 nd₁ ⊢e x ⊢e₁) nd = {!!}
annotatability (ela-app3 ndf nd₁ ⊢e x ⊢e₁) nd = {!!}

annotatability-fun (ela-var x) (ndf-var x₁ x₂) ma = {!!}
annotatability-fun (ela-lam ⊢e) nd ma = {!!}
annotatability-fun (ela-app1 ndf ⊢e x ⊢e₁) (ndf-app1 nd) ma = ⊥-elim {!!}
annotatability-fun (ela-app1 ndf ⊢e x ⊢e₁) (ndf-app2 nd) ma
  with refl ← needFun-unique nd ndf = ⊢app₁ {!annotatability-fun ⊢e ? x!} {!!}
annotatability-fun (ela-app2 nd₁ ⊢e x ⊢e₁) (ndf-app1 nd) ma =
  ⊢app₂ {!annotatability-fun ⊢e nd x!} (annotatability ⊢e₁ nd₁)
annotatability-fun (ela-app2 nd₁ ⊢e x ⊢e₁) (ndf-app2 nd) ma =
  ⊢app₂ {!annotatability-fun ⊢e nd x!} (annotatability ⊢e₁ nd₁)
annotatability-fun (ela-app3 ndf nd₁ ⊢e x ⊢e₁) nd ma =
  ⊢app₂ {!!} {!!}
