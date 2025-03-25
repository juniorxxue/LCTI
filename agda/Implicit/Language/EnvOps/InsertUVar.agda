module Implicit.Language.EnvOps.InsertUVar where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Lookup.All
open import Implicit.Language.Regular.Base
open import Implicit.Language.OpenClose.Base
open import Implicit.Language.Ground.Base
open import Implicit.Language.EnvOps.Base


infix 3 _▶_,∙⇘_
data _▶_,∙⇘_ : Env n m → Fin (1 + m) → Env n (1 + m) → Set where
  ▶Z : Γ ▶ #0 ,∙⇘ Γ ,∙
  ▶S, : Γ ▶ k ,∙⇘ Γ'
      → A ↑ty k ⇘ A'
      → Γ , A ▶ k ,∙⇘ Γ' , A'
  ▶S^ : Γ ▶ k ,∙⇘ Γ'
      → Γ ,^ ▶ #S k ,∙⇘ Γ' ,^
  ▶S∙ : Γ ▶ k ,∙⇘ Γ'
      → Γ ,∙ ▶ #S k ,∙⇘ Γ' ,∙
  ▶S= : Γ ▶ k ,∙⇘ Γ'
      → B ↑ty k ⇘ B'
      → Γ ,= B ▶ #S k ,∙⇘ Γ' ,= B'
  ▶S⋈ : Γ ▶ k ,∙⇘ Γ'
      → Γ ⋈ ▶ k ,∙⇘ Γ' ⋈
