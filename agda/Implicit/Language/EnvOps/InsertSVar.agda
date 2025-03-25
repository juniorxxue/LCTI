module Implicit.Language.EnvOps.InsertSVar where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Lookup.All
open import Implicit.Language.Regular.Base
open import Implicit.Language.OpenClose.Base
open import Implicit.Language.Ground.Base
open import Implicit.Language.EnvOps.Base

infix 3 _▶_,=_⇘_
data _▶_,=_⇘_ : Env n m → Fin (1 + m) → Type m → Env n (1 + m) → Set where
  ▶Z  : (regA : Γ ⊢r A)
      → Γ ▶ #0 ,= A ⇘ Γ ,= A
  ▶S, : Γ ▶ k ,= A ⇘ Γ'
      → (up : B ↑ty k ⇘ B')
      → Γ , B ▶ k ,= A ⇘ Γ' , B'
  ▶S^ : Γ ▶ k ,= A ⇘ Γ'
      → ↑ty0 A ⇘ A'
      → Γ ,^ ▶ #S k ,= A' ⇘ Γ' ,^
  ▶S∙ : Γ ▶ k ,= A ⇘ Γ'
      → ↑ty0 A ⇘ A'
      → Γ ,∙ ▶ #S k ,= A' ⇘ Γ' ,∙
  ▶S= : Γ ▶ k ,= A ⇘ Γ'
      → ↑ty0 A ⇘ A'
      → B ↑ty k ⇘ B'
      → Γ ,= B ▶ #S k ,= A' ⇘ Γ' ,= B'
  ▶S⋈ : Γ ▶ k ,= A ⇘ Γ'
      → Γ ⋈ ▶ k ,= A ⇘ Γ' ⋈
