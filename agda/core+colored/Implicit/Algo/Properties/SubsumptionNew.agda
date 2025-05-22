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
         → Γ ≫ A ⇘ B
         → Γ ⊢c A
         → Γ ⊢ A ≤⁺ 𝔼 (p P) ⊣ Γ ↪ B
amatch-s amt1-z grd cloA = s-empty {!!} cloA grd
amatch-s (amt1-s mt) (grd-var= x) cloA = {!!}
amatch-s (amt1-s mt) (grd-arr grd grd₁) cloA = {!!}


subsumption : Γ ⊢ Σ ⇒ e ⇒ A
             → Σ ≊ Σ' by A
             → Γ ⊢ Σ' ⇒ e ⇒ A



s-sub : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
      → Σ ≊ Σ' by B
      → Γ ⊢ A ≤⁺ Σ' ⊣ Δ ↪ B
s-sub (s-empty regΓ cloA grd) (≋E p2τ) = s-type {!!}
s-sub (s-empty regΓ cloA grd) (≋E (p2p (≊P-Z amt1-z))) = {!!}
s-sub (s-empty regΓ cloA (grd-var= x₁)) (≋E (p2p (≊P-Z (amt1-s x)))) = {!!}
s-sub (s-empty regΓ cloA (grd-arr grd grd₁)) (≋E (p2p (≊P-Z (amt1-s x)))) = {!!}
s-sub (s-type ss) new = {!!}
s-sub (s-term-c cloA ap ⊢e s) new = {!!}
s-sub (s-term-o opnA conv ⊢e ss s) new = {!!}
s-sub (s-term-p ss s) new = {!!}
s-sub (s-∀l s upᶜ upᵉ upC upD) new = {!!}
s-sub (s-tapp s upᶜ) new = {!!}

subsumption (⊢lit regΓ) (≋E p2τ) = {!⊢sub!}
subsumption (⊢lit regΓ) (≋E (p2p (≊P-Z amt1-z))) = ⊢lit regΓ
subsumption (⊢var regΓ x∈Γ) new = {!!}
subsumption (⊢ann ⊢e) new = {!!}
subsumption (⊢app ⊢e) new = ⊢app (subsumption ⊢e (≊S new))
subsumption (⊢lam₁ ⊢e) new = {!!}
subsumption (⊢lam₂ ⊢e up-c ⊢e₁) (≊S new) = ⊢lam₂ ⊢e {!!} (subsumption ⊢e₁ {!!})
subsumption (⊢lam₃ ⊢e) new = {!!}
subsumption (⊢sub ⊢e ne gc s) new = ⊢sub ⊢e {!!} gc {!!}
subsumption (⊢tabs ⊢e) (≋E p2τ) = {!!}
subsumption (⊢tabs ⊢e) (≋E (p2p (≊P-Z x))) = {!!}
subsumption (⊢tapp ⊢e st) new = ⊢tapp (subsumption ⊢e (≊⓪ new st)) st
