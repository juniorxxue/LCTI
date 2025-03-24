module Implicit.Language.EnvOps.InsertTVar where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Lookup.All
open import Implicit.Language.Regular.Base
open import Implicit.Language.OpenClose.Base
open import Implicit.Language.Ground.Base
open import Implicit.Language.EnvOps.Base

infix 3 _▶_,_⇘_
data _▶_,_⇘_ : Env n m → Fin (1 + n) → Type m → Env (1 + n) m → Set where
  ▶Z  : (regA : Γ ⊢r A)
      → Γ ▶ #0 , A ⇘ Γ , A
  ▶S, : Γ ▶ k , A ⇘ Γ'
      → (Γ , B) ▶ #S k , A ⇘ Γ' , B
  ▶S^ : Γ ▶ k , A ⇘ Γ'
      → ↑ty0 A ⇘ A'
      → (Γ ,^) ▶ k , A' ⇘ Γ' ,^
  ▶S∙ : Γ ▶ k , A ⇘ Γ'
      → ↑ty0 A ⇘ A'
      → (Γ ,∙) ▶ k , A' ⇘ Γ' ,∙
  ▶S= : Γ ▶ k , A  ⇘ Γ'
      → ↑ty0 A ⇘ A'
      → (Γ ,= B) ▶ k , A' ⇘ Γ' ,= B
  ▶S⋈ : Γ ▶ k , A  ⇘ Γ'
      → Γ ⋈ ▶ k , A ⇘ Γ' ⋈

infix 3 _⨟_▶_,_⇘_⨟_
data _⨟_▶_,_⇘_⨟_ : Env n m → Env n m → Fin (1 + n) → Type m → Env (1 + n) m → Env (1 + n) m → Set where
  ▶Z  : (regA : Γ ⊢r T)
      → Γ ⨟ Δ ▶ #0 , T ⇘ Γ , T ⨟ Δ , T
  ▶S, : Γ ⨟ Δ ▶ k , T ⇘ Γ' ⨟ Δ'
      → Γ , A ⨟ Δ , A ▶ #S k , T ⇘ Γ' , A ⨟ Δ' , A
  ▶S^ : Γ ⨟ Δ ▶ k , T ⇘ Γ' ⨟ Δ'
      → ↑ty0 T ⇘ T'
      → Γ ,^ ⨟ Δ ,^ ▶ k , T' ⇘ Γ' ,^ ⨟ Δ' ,^
  ▶S∙ : Γ ⨟ Δ ▶ k , T ⇘ Γ' ⨟ Δ'
      → ↑ty0 T ⇘ T'
      → Γ ,∙ ⨟ Δ ,∙ ▶ k , T' ⇘ Γ' ,∙ ⨟ Δ' ,∙
  ▶S= : Γ ⨟ Δ ▶ k , T  ⇘ Γ' ⨟ Δ'
      → ↑ty0 T ⇘ T'
      → Γ ,= A ⨟ Δ ,= A ▶ k , T' ⇘ Γ' ,= A ⨟ Δ' ,= A
  ▶S^= : Γ ⨟ Δ ▶ k , T  ⇘ Γ' ⨟ Δ'
      → ↑ty0 T ⇘ T'
      → Γ ,^ ⨟ Δ ,= A ▶ k , T' ⇘ Γ' ,^ ⨟ Δ' ,= A
  ▶S⋈ : Γ ⨟ Δ ▶ k , T  ⇘ Γ' ⨟ Δ'
      → Γ ⋈ ⨟ Δ ⋈ ▶ k , T  ⇘ Γ' ⋈ ⨟ Δ' ⋈
