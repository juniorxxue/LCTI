module Implicit.Language.EnvOps.RemoveTVar where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Lookup.All
open import Implicit.Language.Regular.Base
open import Implicit.Language.OpenClose.Base
open import Implicit.Language.Ground.Base

-- remove (x : A) from k-th position
infix 3 _◀_,⇘_
data _◀_,⇘_ : Env (1 + n) m → Fin (1 + n) → Env n m → Set where
  ◀Z : Γ , A ◀ #0 ,⇘ Γ
  ◀S, : Γ ◀ k ,⇘ Γ'
      → Γ , B ◀ #S k ,⇘ Γ' , B
  ◀S^ : Γ ◀ k ,⇘ Γ'
      → (Γ ,^) ◀ k ,⇘ Γ' ,^
  ◀S∙ : Γ ◀ k ,⇘ Γ'
      → (Γ ,∙) ◀ k ,⇘ Γ' ,∙
  ◀S= : Γ ◀ k ,⇘ Γ'
      → (Γ ,= A) ◀ k ,⇘ Γ' ,= A
  ◀S⋈ : Γ ◀ k ,⇘ Γ'
      → Γ ⋈ ◀ k ,⇘ Γ' ⋈

∋⦂-strengthen, : Γ ∋ punchIn k x ⦂ A
      → Γ ◀ k ,⇘ Γ'
      → Γ' ∋ x ⦂ A
∋⦂-strengthen, {k = #0} {#0} (S, inΓ) ◀Z = inΓ
∋⦂-strengthen, {k = #0} {#0} (S∙ inΓ up) (◀S∙ newΓ) = S∙ (∋⦂-strengthen, inΓ newΓ) up
∋⦂-strengthen, {k = #0} {#0} (S^ inΓ up) (◀S^ newΓ) = S^ (∋⦂-strengthen, inΓ newΓ) up
∋⦂-strengthen, {k = #0} {#0} (S= inΓ up) (◀S= newΓ) = S= (∋⦂-strengthen, inΓ newΓ) up
∋⦂-strengthen, {k = #0} {#S x} (S, inΓ) ◀Z = inΓ
∋⦂-strengthen, {k = #0} {#S x} (S^ inΓ up) (◀S^ newΓ) = S^ (∋⦂-strengthen, inΓ newΓ) up
∋⦂-strengthen, {k = #0} {#S x} (S∙ inΓ up) (◀S∙ newΓ) = S∙ (∋⦂-strengthen, inΓ newΓ) up
∋⦂-strengthen, {k = #0} {#S x} (S= inΓ up) (◀S= newΓ) = S= (∋⦂-strengthen, inΓ newΓ) up
∋⦂-strengthen, {k = #S k} {#0} Z (◀S, newΓ) = Z
∋⦂-strengthen, {k = #S k} {#0} (S∙ inΓ up) (◀S∙ newΓ) = S∙ (∋⦂-strengthen, inΓ newΓ) up
∋⦂-strengthen, {k = #S k} {#0} (S^ inΓ up) (◀S^ newΓ) = S^ (∋⦂-strengthen, inΓ newΓ) up
∋⦂-strengthen, {k = #S k} {#0} (S= inΓ up) (◀S= newΓ) = S= (∋⦂-strengthen, inΓ newΓ) up
∋⦂-strengthen, {k = #S k} {#S x} (S, inΓ) (◀S, newΓ) = S, (∋⦂-strengthen, inΓ newΓ)
∋⦂-strengthen, {k = #S k} {#S x} (S∙ inΓ up) (◀S∙ newΓ) = S∙ (∋⦂-strengthen, inΓ newΓ) up
∋⦂-strengthen, {k = #S k} {#S x} (S^ inΓ up) (◀S^ newΓ) = S^ (∋⦂-strengthen, inΓ newΓ) up
∋⦂-strengthen, {k = #S k} {#S x} (S= inΓ up) (◀S= newΓ) = S= (∋⦂-strengthen, inΓ newΓ) up

∋:=-strengthen, : Γ ∋ X := A
       → Γ ◀ k ,⇘ Γ'
       → Γ' ∋ X := A
∋:=-strengthen, (Z up) (◀S= newΓ) = Z up
∋:=-strengthen, (S∙ inΓ up) (◀S∙ newΓ) = S∙ (∋:=-strengthen, inΓ newΓ) up
∋:=-strengthen, (S^ inΓ up) (◀S^ newΓ) = S^ (∋:=-strengthen, inΓ newΓ) up
∋:=-strengthen, (S= inΓ up) (◀S= newΓ) = S= (∋:=-strengthen, inΓ newΓ) up

∋∙-strengthen, : Γ ∋∙ X
      → Γ ◀ k ,⇘ Γ'
      → Γ' ∋∙ X
∋∙-strengthen, Z (◀S∙ newΓ') = Z
∋∙-strengthen, (S, inΓ) ◀Z = inΓ
∋∙-strengthen, (S, inΓ) (◀S, newΓ') = S, (∋∙-strengthen, inΓ newΓ')
∋∙-strengthen, (S∙ inΓ) (◀S∙ newΓ') = S∙ (∋∙-strengthen, inΓ newΓ')
∋∙-strengthen, (S= inΓ) (◀S= newΓ') = S= (∋∙-strengthen, inΓ newΓ')
∋∙-strengthen, (S^ inΓ) (◀S^ newΓ') = S^ (∋∙-strengthen, inΓ newΓ')
∋∙-strengthen, (S⋈ inΓ) (◀S⋈ newΓ') = S⋈ (∋∙-strengthen, inΓ newΓ')

∋=-strengthen, : Γ ∋= X
       → Γ ◀ k ,⇘ Γ'
       → Γ' ∋= X
∋=-strengthen, Z (◀S= newΓ') = Z
∋=-strengthen, (S∙ inΓ) (◀S∙ newΓ') = S∙ (∋=-strengthen, inΓ newΓ')
∋=-strengthen, (S^ inΓ) (◀S^ newΓ') = S^ (∋=-strengthen, inΓ newΓ')
∋=-strengthen, (S= inΓ) (◀S= newΓ') = S= (∋=-strengthen, inΓ newΓ')

postulate


  tregular-strengthen, : TRegular Γ
                     → Γ ◀ k ,⇘ Γ'
                     → TRegular Γ'

  sregular-strengthen, : SRegular Γ
                     → Γ ◀ k ,⇘ Γ'
                     → SRegular Γ'

  ⊢c-strengthen, : Γ ⊢c A
               → Γ ◀ k ,⇘ Γ'
               → Γ' ⊢c A

  ≫-strengthen, : Γ ≫ A ⇘ B
              → Γ ◀ k ,⇘ Γ'
              → Γ' ≫ A ⇘ B
