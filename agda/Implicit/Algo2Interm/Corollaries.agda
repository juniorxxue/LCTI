module Implicit.Algo2Interm.Corollaries where

open import Implicit.Language.All
open import Implicit.Interm.All
open import Implicit.Algo.All

open import Implicit.Algo2Interm.Context2Counter
open import Implicit.Algo2Interm.AlgoCounter.All
open import Implicit.Algo2Interm.Main

↑tyʲ0-exist : Γ ⊢ ⟨ j' , A ⟩ ~s Σ'
            → ↑tyᶜ0 Σ ⇘ Σ'
            → ∃[ j ](↑tyʲ0 j ⇘ j')
↑tyʲ0-exist ~sZ ↑tyᶜ-□ = ⟨ Z , ↑tyʲ-Z ⟩
↑tyʲ0-exist ~s∞ (↑tyᶜ-τ up-t) = ⟨ ∞ , ↑tyʲ-∞ ⟩
↑tyʲ0-exist (~sI ⊢e ~s) (↑tyᶜ-e up-e upΣ) = ⟨ 𝕚 (↑tyʲ0-exist ~s upΣ .proj₁) ,
                                             ↑tyʲ-𝕚 (↑tyʲ0-exist ~s upΣ .proj₂) ⟩
↑tyʲ0-exist (~sC ⊢e ~s) (↑tyᶜ-e up-e upΣ) = ⟨ 𝕔 (↑tyʲ0-exist ~s upΣ .proj₁) ,
                                             ↑tyʲ-𝕔 (↑tyʲ0-exist ~s upΣ .proj₂) ⟩
↑tyʲ0-exist (~sT ~s st) (↑tyᶜ-⓪ {A = A} x upΣ) = ⟨ 𝕥₍ A ₎ ↑tyʲ0-exist ~s upΣ .proj₁ ,
                                          ↑tyʲ-𝕥 (↑tyʲ0-exist ~s upΣ .proj₂) x ⟩

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

tc-complete : Γ ⊢ Σ ⇒ e ⇒ A
            → JustType Γ Σ e A

sc-complete : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
            → JustSub Γ A Σ Δ B

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
tc-complete (⊢tapp ⊢e st) with tc-complete ⊢e
... | typs (~tT j~Σ st₁) ⊢e₁
  with refl ← st-unique st st₁ = typs j~Σ (⊢tapp ⊢e₁ st)

sc-complete (s-empty regΓ cloA x) = subs ~sZ (s-empty regΓ cloA x)
sc-complete (s-type ss) = subs ~s∞ (s-type ss)
sc-complete (s-term-c nd s cloA ap ⊢e) with sc-complete s | tc-complete ⊢e
... | subs j~Σ s₁ | typs ~t∞ ⊢e₁ = subs (~sC (sound ⊢e₁) j~Σ) (s-term-c nd s₁ cloA ap ⊢e₁)
sc-complete s'@(s-term-o opnA ⊢e ss s) with sc-complete s | tc-complete ⊢e
... | subs j~Σ s₁ | typs ~tZ ⊢e₁ = subs (~sI (t-⊆-prv (sound ⊢e₁) (s-⊆ s')) j~Σ)
                                        (s-term-o opnA ⊢e₁ ss s₁)
sc-complete (s-∀l s upᶜ upᵉ upC upD) with sc-complete s
sc-complete (s-∀l s upᶜ upᵉ upC upD) | subs {𝕚 j} j~Σ s₁
  with ⟨ j' , ↑tyʲ-𝕚 upj' ⟩ ← ↑tyʲ0-exist j~Σ (↑tyᶜ-e upᵉ upᶜ)
  = subs (~s-strengthen=0 j~Σ (↑ty-arr upC upD) (↑tyᶜ-e upᵉ upᶜ) (↑tyʲ-𝕚 upj'))
                          (s-∀l-𝕚 s₁ upᶜ upj' upᵉ upC upD)
sc-complete (s-∀l s upᶜ upᵉ upC upD) | subs {𝕔 j} j~Σ s₁
  with ⟨ j' , ↑tyʲ-𝕔 upj' ⟩ ← ↑tyʲ0-exist j~Σ (↑tyᶜ-e upᵉ upᶜ)
  = subs (~s-strengthen=0 j~Σ (↑ty-arr upC upD) (↑tyᶜ-e upᵉ upᶜ) (↑tyʲ-𝕔 upj'))
                    (s-∀l-𝕔 s₁ upᶜ upj' upᵉ upC upD)
sc-complete (s-tapp {B = B} {C = C} s upᶜ) with sc-complete s
... | subs j~Σ s₁
  with ⟨ B* , stB ⟩ ← st0-total B C
  with ⟨ j' , upj' ⟩ ← ↑tyʲ0-exist j~Σ upᶜ
  = subs (~sT (~s-strengthen=0 j~Σ (st-↑ty (⊢r-¬ε (s-⊢r s) Z) stB) upᶜ upj') stB) (s-tapp s₁ upᶜ upj')

----------------------------------------------------------------------
--+                          corollaries                           +--
----------------------------------------------------------------------

sound0 : Γ ⊢ □ ⇒ e ⇒ A
       → Γ ⊢ Z # e ⦂ A
sound0 ⊢e with tc-complete ⊢e
... | typs ~tZ ⊢e₁ = sound ⊢e₁

sound∞ : Γ ⊢ τ B ⇒ e ⇒ A
       → Γ ⊢ ∞ # e ⦂ B
sound∞ ⊢e with tc-complete ⊢e
... | typs ~t∞ ⊢e₁ = sound ⊢e₁
