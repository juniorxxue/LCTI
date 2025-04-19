module Implicit.Interm2Algo.PExtIrrev where

open import Implicit.Language.All

open import Implicit.AuxLemmas

infix 3 _⊆_w/t_w/c_

data _⊆_w/t_w/c_ : Env n m → Env n m → Type m → Counter m → Set where
  ⊆Z : (regΓ : SRegular Γ)
     → Γ ⊆ Γ w/t A w/c Z
  ⊆∞ : (ext : Γ ⊆ Δ w/t A)
     → Γ ⊆ Δ w/t A w/c ∞
  ⊆I : (ext : Γ ⊆ Ω w/t A)
     → Ω ⊆ Δ w/t B w/c j
     → Γ ⊆ Δ w/t (A `→ B) w/c (𝕚 j)
  ⊆C : (cloA : Δ ⊢c A)
     → Γ ⊆ Δ w/t B w/c j
     → Γ ⊆ Δ w/t (A `→ B) w/c (𝕔 j)
  ⊆∀-I : Γ ,^ ⊆ Δ ,= B w/t A w/c (𝕚 j')
       → (upj : ↑tyʲ0 j ⇘ j')
       → Γ ⊆ Δ w/t `∀ A w/c (𝕚 j)
  ⊆∀-C : Γ ,^ ⊆ Δ ,= B w/t A w/c (𝕔 j')
       → (upj : ↑tyʲ0 j ⇘ j')
       → Γ ⊆ Δ w/t `∀ A w/c (𝕔 j)
  ⊆∀-T : Γ ,= B ⊆ Δ ,= B w/t A w/c j'
       → (upj : ↑tyʲ0 j ⇘ j')
       → Γ ⊆ Δ w/t `∀ A w/c 𝕥₍ B ₎ j


postulate
  ⊆/c-⊆ : Γ ⊆ Δ w/t A w/c j
        → Γ ⊆ Δ

postulate
  ⊆/x-^in-=out-inst : Γ ∋^ X
                  → Δ ∋ X := A
                          → Γ ⊆ Δ w/v X
                          → [ A / X ] Γ ⟹ Δ

postulate
  =⟹-unique : [ B / k ] Γ =⟹ Γ'
            → [ B / k ] Γ =⟹ Δ'
            → Γ' ≡ Δ'

postulate
  =⟹-∋∙ : Γ ∋∙ X
        → [ A / k ] Γ =⟹ Γ'
        → Γ' ∋∙ X

postulate
  =⟹-∋=-prv : Γ ∋= X
            → [ A / k ] Γ =⟹ Γ'
            → Γ' ∋= X

postulate
  =⟹-⊢r :  Γ ⊢r B
        → [ A / k ] Γ =⟹ Γ'
        → Γ' ⊢r B

postulate
  =⟹-⊢c : Γ ⊢c B
        → [ A / k ] Γ =⟹ Γ'
        → Γ' ⊢c B

postulate
  =⟹-sregular : [ B / k ] Γ =⟹ Γ'
              → SRegular Γ'

postulate
  ⊆/x-irrev-== : Γ ⊆ Δ w/v X
               → [ B / k ] Γ =⟹ Γ'
               → [ B / k ] Δ =⟹ Δ'
               → Γ' ⊆ Δ' w/v X

postulate
  ⊆/-irrev-== : Γ ⊆ Δ w/t A
              → [ B / k ] Γ =⟹ Γ'
              → [ B / k ] Δ =⟹ Δ'
              → Γ' ⊆ Δ' w/t A

postulate
  ⊆/c-irrev-== : Γ ⊆ Δ w/t A w/c j
               → [ B / k ] Γ =⟹ Γ'
               → [ B / k ] Δ =⟹ Δ'
               → Γ' ⊆ Δ' w/t A w/c j

postulate
  ⊆/v-irrev-^= : Γ ⊆ Δ w/v k
               → Γ ∋^ k
               → [ B / k ] Δ =⟹ Δ'
               → Γ ⊆ Δ' w/v k

postulate
  ⊆/-irrev-^= : Γ ⊆ Δ w/t A
              → Γ ∋^ k
              → [ B / k ] Δ =⟹ Δ'
              → k ε A
              → Γ ⊆ Δ' w/t A

postulate
  ⊆/c-irrev-^= : Γ ⊆ Δ w/t A w/c j
               → Γ ∋^ k
               → [ B / k ] Δ =⟹ Δ'
               → find A k j
               → Γ ⊆ Δ' w/t A w/c j

postulate
  ⊆/c-irrev-^=0 : Γ ,^ ⊆ Δ ,= B₁ w/t A w/c j
                → find A #0 j
                → Δ ⊢r B₂
                → Γ ,^ ⊆ Δ ,= B₂ w/t A w/c j

postulate
  ◎-∋∙ : Γ ∋∙ X
       → Γ ◎ k ⇘ Γ'
       → Γ' ∋∙ X

postulate
  ◎-∋=-≢ : Γ ∋= X
         → Γ ◎ k ⇘ Γ'
         → X ≢ k
         → Γ' ∋= X

postulate
  ◎-⊢c : Γ ⊢c A
       → Γ ◎ k ⇘ Γ'
       → k ¬ε A
       → Γ' ⊢c A

postulate
  ◎-total : Ω ∋= k
          → ∃[ Ω' ](Ω ◎ k ⇘ Ω')

postulate
  ◎-∋= : Γ ◎ k ⇘ Γ'
       → Γ ∋= k

postulate
  ◎-⊢r : Γ ⊢r A
       → Γ ◎ k ⇘ Γ'
       → Γ' ⊢r A

postulate
  ◎-sregular : SRegular Γ
             → Γ ◎ k ⇘ Γ'
             → SRegular Γ'

postulate
  ◎-unique : Γ ◎ k ⇘ Γ'
           → Γ ◎ k ⇘ Δ'
           → Γ' ≡ Δ'

postulate
  ⊆/v-irrev-^^ : Γ ⊆ Δ w/v X
               → Γ ◎ k ⇘ Γ'
               → Δ ◎ k ⇘ Δ'
               → X ≢ k
               → Γ' ⊆ Δ' w/v X

postulate
  ⊆/-irrev-^^ : Γ ⊆ Δ w/t A
              → k ¬ε A
              → Γ ◎ k ⇘ Γ'
              → Δ ◎ k ⇘ Δ'
              → Γ' ⊆ Δ' w/t A

postulate
  ⊆/v-irrev-^ : Γ ⊆ Δ w/v k
              → Γ ◎ k ⇘ Γ'
              → Γ' ⊆ Δ w/v k

postulate
  ⊆/-irrev-^ : Γ ⊆ Δ w/t A
             → k ε A
             → Γ ◎ k ⇘ Γ'
             → Γ' ⊆ Δ w/t A

postulate
  ⊆/c-irrev-^ : Γ ⊆ Δ w/t A w/c j
              → find A k j
              → Γ ◎ k ⇘ Γ'
              → Γ' ⊆ Δ w/t A w/c j

postulate
  ⊆/c-irrev-^0 : Γ ,= B ⊆ Δ ,= B w/t A w/c j
               → find A #0 j
               → Γ ,^ ⊆ Δ ,= B w/t A w/c j

