module Implicit.Algo2Interm.Corollaries where

open import Implicit.Language.All
open import Implicit.Interm.All
open import Implicit.Algo.All

open import Implicit.Algo2Interm.Context2Counter
open import Implicit.Algo2Interm.AlgoCounter.All
open import Implicit.Algo2Interm.Main

-- corollaries are bridged via completeness of AlgoCounter

data JustType (Γ : Env n m) (Σ : Context n m) (e : Term n m) (A : Type m) : Set where
  typs : ∀ {j}
    → (j~Σ : Γ ⊢ ⟨ j , A ⟩ ~t Σ)
    → (⊢e : Γ ⊢ Σ ⇒ e ⇒ A ↡ j)
    → JustType Γ Σ e A

data JustSub (Γ : Env n m) (A : Type m) (Σ : Context n m) (Δ : Env n m) (B : Type m) : Set where
  subs : ∀ {j}
    → (j~Σ : Δ ⊢ ⟨ j , B ⟩ ~s Σ)
    → (s : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B ↡ j)
    → JustSub Γ A Σ Δ B

data JustInfs (Γ : Env n m) (Σ : Context n m) (A : Type m) : Set where
  infss : ∀ {j}
    → (j~Σ : Γ ⊢ ⟨ j , A ⟩ ~inf Σ)
    → (infs : Γ ⊨ Σ ⟹ A ↡ j)
    → JustInfs Γ Σ A

tc-complete : Γ ⊢ Σ ⇒ e ⇒ A
            → JustType Γ Σ e A

sc-complete : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
            → JustSub Γ A Σ Δ B

infs-complete : Γ ⊨ Σ ⟹ A
            → JustInfs Γ Σ A

tc-complete (⊢lit regΓ) = typs ~tZ (⊢lit regΓ)
tc-complete (⊢var regΓ x∈Γ) = typs ~tZ (⊢var regΓ x∈Γ)
tc-complete (⊢ann ⊢e) with tc-complete ⊢e
... | typs ~t∞ ⊢e₁ = typs ~tZ (⊢ann ⊢e₁)
tc-complete (⊢app ⊢e) with tc-complete ⊢e
... | typs (~tI ⊢e₂ j~Σ) ⊢e₁ = typs j~Σ (⊢app ⊢e₁)
... | typs (~tC ⊢e₂ j~Σ) ⊢e₁ = typs j~Σ (⊢app ⊢e₁)
tc-complete (⊢lam₁ ⊢e) with tc-complete ⊢e
... | typs ~t∞ ⊢e₁ = typs ~t∞ (⊢lam₁ ⊢e₁)
tc-complete (⊢lam₂ ⊢e up-c ⊢e₁) with tc-complete ⊢e | tc-complete ⊢e₁
... | typs ~tZ ⊢e₂ | typs j~Σ₁ ⊢e₃ = typs (~tI (sound ⊢e₂) (~t-strengthen,0 j~Σ₁ up-c)) (⊢lam₂ ⊢e₂ up-c ⊢e₃)
tc-complete (⊢sub ⊢e ne gc s) with sc-complete s | tc-complete ⊢e
... | subs j~Σ s₁ | typs ~tZ ⊢e' = typs (~s-~t j~Σ) (⊢sub ⊢e' ne gc s₁)
tc-complete (⊢tabs ⊢e) with tc-complete ⊢e
... | typs ~tZ ⊢e₁ = typs ~tZ (⊢tabs ⊢e₁)
tc-complete (⊢tabs-τ ⊢e) with tc-complete ⊢e
... | typs ~t∞ ⊢e₁ = typs ~t∞ (⊢tabs-τ ⊢e₁)
tc-complete (⊢tapp ⊢e st regA s) with sc-complete s | tc-complete ⊢e
... | subs j~Σ s₁ | typs ~tZ ⊢e₁ = typs (~s-~t j~Σ) (⊢tapp ⊢e₁ st regA s₁)

sc-complete (s-empty regΓ cloA x) = subs ~sZ (s-empty regΓ cloA x)
sc-complete (s-type ss) = subs ~s∞ (s-type ss)
sc-complete (s-term-c cloA ap ⊢e s) with sc-complete s | tc-complete ⊢e
... | subs j~Σ s₁ | typs ~t∞ ⊢e₁ = subs (~sC (t-⊆-prv (sound ⊢e₁) (sc-⊆ s₁)) j~Σ)
                                        (s-term-c cloA ap ⊢e₁ s₁)
sc-complete s'@(s-term-o opnA ⊢e ss s) with sc-complete s | tc-complete ⊢e
... | subs j~Σ s₁ | typs ~tZ ⊢e₁ = subs (~sI (t-⊆-prv (sound ⊢e₁) (s-⊆ s')) j~Σ)
                                        (s-term-o opnA ⊢e₁ ss s₁)
sc-complete (s-∀l s upᶜ upᵉ upC upD) with sc-complete s
... | subs {j = i · j} j~Σ s₁
  = subs (~s-strengthen=0 j~Σ (↑ty-arr upC upD) (↑tyᶜ-e upᵉ upᶜ)) (s-∀l s₁ upᶜ upᵉ upC upD)
sc-complete (s-svar-term inΓ s) with sc-complete s
... | subs j~Σ s₁ = subs j~Σ (s-svar-term inΓ s₁)
sc-complete (s-∀l-no s upᶜ upᵉ upC upD) with sc-complete s
... | subs {j = i · j} j~Σ s₁
  = subs (~s-strengthen^0 j~Σ (↑ty-arr upC upD) (↑tyᶜ-e upᵉ upᶜ)) (s-∀l-no s₁ upᶜ upᵉ upC upD)
sc-complete (s-evar-infers infs inst) with infs-complete infs
... | infss ~j'@(~iI ⊢e j~Σ) infs₁ = subs (~s-irrev-⊆ (~t-~s (~infs-~t ~j')) (inst-⊆ inst)) (s-evar-infers infs₁ inst)

infs-complete (infs-z regΓ regA) = infss ~i∞ (infs-z regΓ regA)
infs-complete (infs-s ⊢e infs)
  with typs ~tZ ⊢e₁ ← tc-complete ⊢e
  with infss ~j infs' ← infs-complete infs = infss (~iI (sound ⊢e₁) ~j) (infs-s ⊢e₁ infs')

----------------------------------------------------------------------
--+                          corollaries                           +--
----------------------------------------------------------------------

sound0 : Γ ⊢ □ ⇒ e ⇒ A
       → Γ ⊢ `■ # e ⦂ A
sound0 ⊢e with tc-complete ⊢e
... | typs ~tZ ⊢e₁ = sound ⊢e₁

sound∞ : Γ ⊢ τ B ⇒ e ⇒ A
       → Γ ⊢ `□ # e ⦂ B
sound∞ ⊢e with tc-complete ⊢e
... | typs ~t∞ ⊢e₁ = sound ⊢e₁
