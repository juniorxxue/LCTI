module Implicit.Language.EnvOps.Base where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Subst.All
open import Implicit.Language.OpenClose.Base
open import Implicit.Language.Regular.Base
open import Implicit.Language.Lookup.Base

----------------------------------------------------------------------
--+                         Entry Removal                          +--
----------------------------------------------------------------------




-- remove an entry a=A, we should be careful about this
-- removing an entry a=A requires us to do substittuiion on the remaining env

-- in algo, we need to first lookup the type A
-- then use type A to manipuate remaining envs to produce a new env
-- in this relation, we could assume we know A
infix 3 _◀_:=_⇘_
data _◀_:=_⇘_ : Env n (1 + m) → Fin (1 + m) → Type m → Env n m → Set where
  ◀Z : Γ ,= A ◀ #0 := A ⇘ Γ
  ◀S, : Γ ◀ k := A ⇘ Γ'
      → ⟦ k / A ⟧ B ⇘ B*
      → Γ , B ◀ k := A ⇘ Γ' , B*
  ◀S^ : Γ ◀ k := A ⇘ Γ'
      → (up : ↑ty0 A ⇘ A')
      → Γ ,^ ◀ #S k := A' ⇘ Γ' ,^
  ◀S∙ : Γ ◀ k := A ⇘ Γ'
      → (up : ↑ty0 A ⇘ A')
      → Γ ,∙ ◀ #S k := A' ⇘ Γ' ,∙
  ◀S= : Γ ◀ k := A ⇘ Γ'
      → (up : ↑ty0 A ⇘ A')
      → ⟦ k / A ⟧ B ⇘ B*
      → Γ ,= B ◀ #S k := A' ⇘ Γ' ,= B*

----------------------------------------------------------------------
--+                       Entry Replacement                        +--
----------------------------------------------------------------------

-- could be a combination of weaken and strengthen




-- replace entry a=A with a solution a=B in an environment
infix 3 [_/_]_=⟹_
data [_/_]_=⟹_ : Type m → Fin m → Env n m → Env n m → Set where
  =⟹=0 : (up : ↑ty0 A ⇘ A')
         → (regA : Γ ⊢r A)
         → (env : SRegular Γ)
        → [ A' / #0 ] (Γ ,= B) =⟹ (Γ ,= A)

  =⟹^S : [ A / k ] Γ =⟹ Γ'
        → (up1 : ↑ty0 A ⇘ A')
        → [ A' / #S k ] (Γ ,^) =⟹ Γ' ,^

  =⟹∙S : [ A / k ] Γ =⟹ Γ'
        → (up1 : ↑ty0 A ⇘ A')
        → [ A' / #S k ] (Γ ,∙) =⟹ (Γ' ,∙)

  =⟹=S : [ A / k ] Γ =⟹ Γ'
        → (up1 : ↑ty0 A ⇘ A')
        → (regB : Γ ⊢r B)
        → [ A' / #S k ] (Γ ,= B) =⟹ (Γ' ,= B)

=⟹-∋= : [ A / k ] Γ =⟹ Γ'
      → Γ ∋= k
=⟹-∋= (=⟹=0 up regA regΓ) = Z
=⟹-∋= (=⟹^S inst up1) = S^ (=⟹-∋= inst)
=⟹-∋= (=⟹∙S inst up1) = S∙ (=⟹-∋= inst)
=⟹-∋= (=⟹=S inst up1 regB) = S= (=⟹-∋= inst)



----------------------------------------------------------------------
--+                          replacement                           +--
----------------------------------------------------------------------


-- in k position, we replace a ,= B with ,^
infix 3 _◎_⇘_
data _◎_⇘_ : Env n m → Fin m → Env n m → Set where
  ◎Z : Γ ,= A ◎ #0 ⇘ Γ ,^
  ◎S∙ : Γ ◎ k ⇘ Γ'
      → Γ ,∙ ◎ #S k ⇘ Γ' ,∙
  ◎S= : Γ ◎ k ⇘ Γ'
      → Γ ,= A ◎ #S k ⇘ Γ' ,= A
  ◎S^ : Γ ◎ k ⇘ Γ'
      → Γ ,^ ◎ #S k ⇘ Γ' ,^
  ◎S, : Γ ◎ k ⇘ Γ'
      → Γ , A ◎ k ⇘ Γ' , A

-- in k position, we replace a ,^ with ,∙
infix 3 _◇_⇘_
data _◇_⇘_ : Env n m → Fin m → Env n m → Set where
  ◇Z  : Γ ,^ ◇ #0 ⇘ Γ ,∙
  ◇S, : Γ ◇ k ⇘ Γ'
      → Γ , A ◇ k ⇘ Γ' , A
  ◇S∙ : Γ ◇ k ⇘ Γ'
      → Γ ,∙ ◇ #S k ⇘ Γ' ,∙
  ◇S= : Γ ◇ k ⇘ Γ'
      → Γ ,= A ◇ #S k ⇘ Γ' ,= A
  ◇S^ : Γ ◇ k ⇘ Γ'
      → Γ ,^ ◇ #S k ⇘ Γ' ,^

-- in k position, we replace a ,∙ with ,^
infix 3 _◈_⇘_
data _◈_⇘_ : Env n m → Fin m → Env n m → Set where
  ◈Z  : Γ ,∙ ◈ #0 ⇘ Γ ,^
  ◈S, : Γ ◈ k ⇘ Γ'
      → Γ , A ◈ k ⇘ Γ' , A
  ◈S∙ : Γ ◈ k ⇘ Γ'
      → Γ ,∙ ◈ #S k ⇘ Γ' ,∙
  ◈S= : Γ ◈ k ⇘ Γ'
      → Γ ,= A ◈ #S k ⇘ Γ' ,= A
  ◈S^ : Γ ◈ k ⇘ Γ'
      → Γ ,^ ◈ #S k ⇘ Γ' ,^
