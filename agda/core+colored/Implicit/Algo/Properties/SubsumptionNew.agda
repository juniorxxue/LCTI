{-# OPTIONS --allow-unsolved-metas #-}
module Implicit.Algo.Properties.SubsumptionNew where

open import Implicit.Language.All
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.PShift
open import Implicit.Algo.Properties.Id
open import Implicit.Algo.Properties.Reflexivity
open import Implicit.Algo.Properties.Extension
open import Implicit.Algo.Properties.PRegularity
open import Implicit.Algo.Properties.Polarity
open import Implicit.Algo.Properties.PStrengthenTVar
open import Implicit.Algo.Properties.PStrengthenSVar
open import Implicit.Algo.Properties.Weaken
open import Implicit.Algo.Properties.Irrelevance

infix 3 _≊P_by_
data _≊P_by_ : ParType m → ParType m → Type m → Set where
  ≊P-Z : AMatch1 A P
       → □ ≊P P by A
  ≊P-S : P₁ ≊P P₂ by B
       → A ◐↝ P₁ ≊P A ◐↝ P₂ by A `→ B

infix 3 _≊E_by_
data _≊E_by_ : EContext m → EContext m → Type m → Set where
  p2τ : p P ≊E τ A by A
  p2p : P₁ ≊P P₂ by A
      → p P₁ ≊E p P₂ by A

infix 3 _≊_by_
data _≊_by_ : Context n m → Context n m → Type m → Set where
  ≋E : δ₁ ≊E δ₂ by A
     → (Context n m ∋⦂ 𝔼 δ₁) ≊ 𝔼 δ₂ by A
  ≊S : Σ ≊ Σ' by B
     → [ e ]↝ Σ ≊ [ e ]↝ Σ' by A `→ B
  ≊⓪ : Σ ≊ Σ' by B*
     → ⟦ A ⟧ B ⇘ B*
     → A ⓪↝ Σ ≊ A ⓪↝ Σ' by `∀ B


amatch-s : AMatch1 B P
         → SRegular Γ
         → Γ ≫ A ⇘ B
         → Γ ⊢c A
         → Γ ⊢ A ≤⁺ 𝔼 (p P) ⊣ Γ ↪ B
amatch-s amt1-z regΓ grd cloA = s-empty regΓ cloA grd
amatch-s (amt1-s am) regΓ (grd-var= x) cloA = s-svar-par x (s-term-p {!!} (amatch-s am regΓ {!!} {!!}))
amatch-s (amt1-s am) regΓ (grd-arr grd grd₁) (⊢c-arr cloA cloA₁) = s-term-p {!!} (amatch-s am regΓ grd₁ cloA₁)

-- ok
s-p-output-eq : Γ ⊢ A ≤⁺ `p P ⊣ Γ ↪ B
              → Γ ⊢r A
              → A ≡ B
s-p-output-eq (s-empty regΓ cloA grd) regA = {!!}
s-p-output-eq (s-term-p ss s) regA = {!!}
s-p-output-eq (s-svar-par x s) (⊢r-var-∙ inΓ) = ⊥-elim {!!}


subsumption : Γ ⊢ Σ ⇒ e ⇒ A
             → Σ ≊ Σ' by A
             → Γ ⊢ Σ' ⇒ e ⇒ A

subsumption0 : Γ ⊢ `p P ⇒ e ⇒ A
              → Γ ⊢ `τ A ⇒ e ⇒ A
subsumption0 ⊢e = subsumption ⊢e (≋E p2τ)

subsumption1 : Γ ⊢ `p P₁ ⇒ e ⇒ A
             → P₁ ≊P P₂ by A
             → Γ ⊢ `p P₂ ⇒ e ⇒ A
subsumption1 ⊢e newP = subsumption ⊢e (≋E (p2p newP))

-- ok
s-sub : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
      → Σ ≊ Σ' by B
      → Γ ⊢ A ≤⁺ Σ' ⊣ Δ ↪ B
s-sub (s-empty regΓ cloA grd) (≋E p2τ) = s-type {!!}
s-sub (s-empty regΓ cloA grd) (≋E (p2p (≊P-Z x))) = amatch-s x regΓ grd cloA
s-sub (s-type ss) (≋E ())
s-sub (s-term-c cloA ap ⊢e s) (≊S new) = s-term-c cloA ap ⊢e (s-sub s new)
s-sub (s-term-o opnA conv ⊢e ss s) (≊S new) = s-term-o opnA conv ⊢e ss (s-sub s new)
s-sub (s-term-p ss s) (≋E p2τ) with s-sub s (≋E p2τ)
... | s-type ss₁ = s-type (s-arr ss ss₁)
s-sub (s-term-p ss s) (≋E (p2p (≊P-S x))) = s-term-p ss (s-sub s (≋E (p2p x)))
s-sub (s-∀l s upᶜ upᵉ upC upD) (≊S new) = s-∀l (s-sub s {!!}) {!!} upᵉ upC upD
s-sub (s-tapp s upᶜ) (≊⓪ new x) = s-tapp (s-sub s {!!}) {!!}
s-sub (s-svar-par x s) (≋E p2τ)
  with refl ← s-p-output-eq s (∋:=-⊢r (s-env-in s) x) = s-type (s-ex-l= (s-env-in s) x)
s-sub (s-svar-par x s) (≋E (p2p (≊P-S x₁))) = s-svar-par x (s-sub s (≋E (p2p (≊P-S x₁))))
s-sub (s-svar-term x s) (≊S new) = s-svar-term x (s-sub s (≊S new))
s-sub (s-svar-tapp x s) (≊⓪ new x₁) = s-svar-tapp x (s-sub s (≊⓪ new x₁))

subsumption (⊢lit regΓ) (≋E p2τ) = {!!}
subsumption (⊢lit regΓ) (≋E (p2p (≊P-Z amt1-z))) = ⊢lit regΓ
subsumption (⊢var regΓ x∈Γ) new = {!!}
subsumption (⊢ann ⊢e) new = {!!}
subsumption (⊢app ⊢e) new = ⊢app (subsumption ⊢e (≊S new))
subsumption (⊢lam₁ ⊢e) new = {!!}
subsumption (⊢lam₂ ⊢e up-c ⊢e₁) (≊S new) = ⊢lam₂ ⊢e {!!} (subsumption ⊢e₁ {!!})
subsumption (⊢lam₃ ⊢e) new = {!!}
subsumption (⊢sub ⊢e ne gc s) new = ⊢sub ⊢e {!!} gc {!s-sub!}
subsumption (⊢tabs ⊢e) (≋E p2τ) = ⊢sub (⊢tabs ⊢e) ne-τ gc-tlam (s-type {!!})
subsumption (⊢tabs ⊢e) (≋E (p2p (≊P-Z amt1-z))) = ⊢tabs ⊢e
subsumption (⊢tapp ⊢e st) new = ⊢tapp (subsumption ⊢e (≊⓪ new st)) st
