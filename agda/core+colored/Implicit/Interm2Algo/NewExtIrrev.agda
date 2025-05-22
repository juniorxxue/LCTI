module Implicit.Interm2Algo.NewExtIrrev where

open import Implicit.Language.All

open import Implicit.AuxLemmas

infix 3 _⊆_w/t_w/n_
data _⊆_w/t_w/n_ : Env n m → Env n m → Type m → ℕ → Set where

  ⊆/n-Z : (regΓ : SRegular Γ)
        → Γ ⊆ Γ w/t A w/n 0

  ⊆/n-S : (ext : Γ ⊆ Ω w/t A)
        → Ω ⊆ Δ w/t B w/n i
        → Γ ⊆ Δ w/t A `→ B w/n (suc i)


infix 3 _⊆_w/t_w/e_
data _⊆_w/t_w/e_ : Env n m → Env n m → Type m → ENat → Set where

  ⊆/e-∞ : (ext : Γ ⊆ Δ w/t A)
        → Γ ⊆ Δ w/t A w/e ∞

  ⊆/e-𝕟 : (ext-n : Γ ⊆ Δ w/t A w/n i)
        → Γ ⊆ Δ w/t A w/e (𝕟 i)


infix 3 _⊆_w/t_w/n!_
data _⊆_w/t_w/n!_ : Env n m → Env n m → Type m → ℕ → Set where

  ⊆/n-Z : (regΓ : SRegular Γ)
        → Γ ⊆ Δ w/t A
        → Γ ⊆ Δ w/t A w/n! 0

  ⊆/n-S : Γ ⊆ Δ w/t B w/n! i
        → Γ ⊆ Δ w/t A `→ B w/n! (suc i)

infix 3 _⊆_w/t_w/e!_
data _⊆_w/t_w/e!_ : Env n m → Env n m → Type m → ENat → Set where

  ⊆/e!-∞ : (cloA : Γ ⊢c A)
         → Γ ⊆ Γ w/t A w/e! ∞
  ⊆/e!-𝕟 : (ext-n : Γ ⊆ Δ w/t A w/n! i)
         → Γ ⊆ Δ w/t A w/e! (𝕟 i)


infix 3 _⊆_w/t_w/c_
data _⊆_w/t_w/c_ : Env n m → Env n m → Type m → Counter m → Set where

  ⊆/c-𝔼 : (ext-e : Γ ⊆ Δ w/t A w/e 𝕖)
        → Γ ⊆ Δ w/t A w/c (𝔼 𝕖)

  ⊆/c-𝕊 : (ext-e : Γ ⊆ Ω w/t A w/e! 𝕖)
        → Ω ⊆ Δ w/t B w/c j
        → Γ ⊆ Δ w/t A `→ B w/c (𝕊₍ 𝕖 ₎ j)

  ⊆/c-𝕊-∀ : Γ ,^ ⊆ Δ ,= B w/t A w/c (𝕊₍ 𝕖 ₎ j')
          → (upj : ↑tyʲ0 j ⇘ j')
          → Γ ⊆ Δ w/t `∀ A w/c (𝕊₍ 𝕖 ₎ j)

  ⊆/c-𝕋 : Γ ,= B ⊆ Δ ,= B w/t A w/c j'
        → (upj : ↑tyʲ0 j ⇘ j')
        → Γ ⊆ Δ w/t `∀ A w/c 𝕋₍ B ₎ j

postulate
  ⊆/c-⊆ : Γ ⊆ Δ w/t A w/c j
      → Γ ⊆ Δ

  ⊆/n-⊆ : Γ ⊆ Δ w/t A w/n i
      → Γ ⊆ Δ

  ⊆/e!-openclose : Γ ⊆ Δ w/t A w/e! 𝕖
              → Γ ⊢o A ⊎ Γ ⊢c A


_ : (∅ ⋈ ,^) ⊆ ∅ ⋈ ,= Int w/t (Int `→ ‶ #0) `→ ‶ #0 w/c (𝕊₍ (𝕟 1) ₎ `𝕫)
_ = ⊆/c-𝕊 (⊆/e!-𝕟 (⊆/n-S (⊆/n-Z (reg-S^ (reg-Z reg-Z))
                           (ext-var (ext-Z^ (reg-Z reg-Z) ⊢r-int))))) (⊆/c-𝔼 (⊆/e-𝕟 (⊆/n-Z (reg-S= (reg-Z reg-Z) ⊢r-int))))
