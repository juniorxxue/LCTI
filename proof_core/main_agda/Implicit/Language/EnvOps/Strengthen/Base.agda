module Implicit.Language.EnvOps.Strengthen.Base where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All

-- remove solution entry, without doing subst
infix 3 _◀_⇘_
data _◀_⇘_ : Env n (1 + m) → Fin (1 + m) → Env n m → Set where
  ◀Z^  : Γ ,^ ◀ #0 ⇘ Γ
  ◀Z=  : Γ ,= T ◀ #0 ⇘ Γ
  ◀Z∙  : Γ ,∙ ◀ #0 ⇘ Γ
  ◀S, : Γ ◀ k ⇘ Γ'
      → (up : B ↑ty k ⇘ B')
      → Γ , B' ◀ k ⇘ Γ' , B
  ◀S^ : Γ ◀ k ⇘ Γ'
      → Γ ,^ ◀ #S k ⇘ Γ' ,^
  ◀S∙ : Γ ◀ k ⇘ Γ'
      → Γ ,∙ ◀ #S k ⇘ Γ' ,∙
  ◀S= : Γ ◀ k ⇘ Γ'
      → A ↑ty k ⇘ A'
      → Γ ,= A' ◀ #S k ⇘ Γ' ,= A
  ◀S⋈ : Γ ◀ k ⇘ Γ'
        → Γ ⋈ ◀ k ⇘ Γ' ⋈


infix 3 _⨟_◀_⇘_⨟_
data _⨟_◀_⇘_⨟_ : Env n (1 + m) → Env n (1 + m) → Fin (1 + m) → Env n m → Env n m → Set where
  ◀Z^  : Γ ,^ ⨟ Δ ,^ ◀ #0 ⇘ Γ ⨟ Δ
  ◀Z=  : Γ ,= T ⨟ Δ ,= T ◀ #0 ⇘ Γ ⨟ Δ
  ◀Z∙  : Γ ,∙ ⨟ Δ ,∙ ◀ #0 ⇘ Γ ⨟ Δ
  ◀S, : Γ ⨟ Δ ◀ k ⇘ Γ' ⨟ Δ'
      → (up : B ↑ty k ⇘ B')
      → Γ , B' ⨟ Δ , B' ◀ k ⇘ Γ' , B ⨟ Δ' , B
  ◀S^ : Γ ⨟ Δ ◀ k ⇘ Γ' ⨟ Δ'
      → Γ ,^ ⨟ Δ ,^ ◀ #S k ⇘ Γ' ,^ ⨟ Δ' ,^
  ◀S∙ : Γ ⨟ Δ ◀ k ⇘ Γ' ⨟ Δ'
      → Γ ,∙ ⨟ Δ ,∙ ◀ #S k ⇘ Γ' ,∙ ⨟ Δ' ,∙
  ◀S= : Γ ⨟ Δ ◀ k ⇘ Γ' ⨟ Δ'
      → A ↑ty k ⇘ A'
      → Γ ,= A' ⨟ Δ ,= A' ◀ #S k ⇘ Γ' ,= A ⨟ Δ' ,= A
  ◀S⋈ : Γ ⨟ Δ ◀ k ⇘ Γ' ⨟ Δ'
      → Γ ⋈ ⨟ Δ ⋈ ◀ k ⇘ Γ' ⋈ ⨟ Δ' ⋈
