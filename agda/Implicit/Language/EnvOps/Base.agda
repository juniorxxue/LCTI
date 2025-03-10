module Implicit.Language.EnvOps.Base where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Subst.All
open import Implicit.Language.OpenClose.Base
open import Implicit.Language.Regular.All
open import Implicit.Language.Lookup.Base

----------------------------------------------------------------------
--+                         Entry Removal                          +--
----------------------------------------------------------------------

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

-- remove exsitential variable â from k-th posititon
infix 3 _◀_^⇘_
data _◀_^⇘_ : Env n (1 + m) → Fin (1 + m) → Env n m → Set where
  ◀Z  : Γ ,^ ◀ #0 ^⇘ Γ
  ◀S, : Γ ◀ k ^⇘ Γ'
      → B ↑ty k ⇘ B'
      → Γ , B' ◀ k ^⇘ Γ' , B
  ◀S^ : Γ ◀ k ^⇘ Γ'
      → Γ ,^ ◀ #S k ^⇘ Γ' ,^
  ◀S∙ : Γ ◀ k ^⇘ Γ'
      → Γ ,∙ ◀ #S k ^⇘ Γ' ,∙
  ◀S= : Γ ◀ k ^⇘ Γ'
      → A ↑ty k ⇘ A'
      → Γ ,= A' ◀ #S k ^⇘ Γ' ,= A

-- remove type variable a from k-th posititon
infix 3 _◀_∙⇘_
data _◀_∙⇘_ : Env n (1 + m) → Fin (1 + m) → Env n m → Set where
  ◀Z  : Γ ,∙ ◀ #0 ∙⇘ Γ
  ◀S, : Γ ◀ k ∙⇘ Γ'
      → A ↑ty k ⇘ A'
      → Γ , A' ◀ k ∙⇘ Γ' , A
  ◀S^ : Γ ◀ k ∙⇘ Γ'
      → Γ ,^ ◀ #S k ∙⇘ Γ' ,^
  ◀S∙ : Γ ◀ k ∙⇘ Γ'
      → Γ ,∙ ◀ #S k ∙⇘ Γ' ,∙
  ◀S= : Γ ◀ k ∙⇘ Γ'
      → A ↑ty k ⇘ A'
      → Γ ,= A' ◀ #S k ∙⇘ Γ' ,= A

-- remove solution entry, without doing subst
infix 3 _◀_=⇘_
data _◀_=⇘_ : Env n (1 + m) → Fin (1 + m) → Env n m → Set where
  ◀Z  : Γ ,= T ◀ #0 =⇘ Γ
  ◀S, : Γ ◀ k =⇘ Γ'
      → B ↑ty k ⇘ B'
      → Γ , B' ◀ k =⇘ Γ' , B
  ◀S^ : Γ ◀ k =⇘ Γ'
      → Γ ,^ ◀ #S k =⇘ Γ' ,^
  ◀S∙ : Γ ◀ k =⇘ Γ'
      → Γ ,∙ ◀ #S k =⇘ Γ' ,∙
  ◀S= : Γ ◀ k =⇘ Γ'
      → A ↑ty k ⇘ A'
      → Γ ,= A' ◀ #S k =⇘ Γ' ,= A


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
--+                         Entry Insertion                        +--
----------------------------------------------------------------------

infix 3 _▶_,_⇘_
data _▶_,_⇘_ : Env n m → Fin (1 + n) → Type m → Env (1 + n) m → Set where
  ▶Z  : (cloA : Γ ⊢r A)
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
      → Γ ⋈ ▶ k , A' ⇘ Γ' ⋈


infix 3 _⨟_▶_,_⇘_⨟_
data _⨟_▶_,_⇘_⨟_ : Env n m → Env n m → Fin (1 + n) → Type m → Env (1 + n) m → Env (1 + n) m → Set where
  ▶Z  : (cloA : Γ ⊢r A)
      → (cloA' : Δ ⊢r A)
      → Γ ⨟ Δ ▶ #0 , A ⇘ Γ , A ⨟ Δ , A
  ▶S, : Γ ⨟ Δ ▶ k , A ⇘ Γ' ⨟ Δ'
      → Γ , B ⨟ Δ , B ▶ #S k , A ⇘ Γ' , B ⨟ Δ' , B
  ▶S^ : Γ ⨟ Δ ▶ k , A ⇘ Γ' ⨟ Δ'
      → ↑ty0 A ⇘ A'
      → Γ ,^ ⨟ Δ ,^ ▶ k , A' ⇘ Γ' ,^ ⨟ Δ' ,^
  ▶S∙ : Γ ⨟ Δ ▶ k , A ⇘ Γ' ⨟ Δ'
      → ↑ty0 A ⇘ A'
      → Γ ,∙ ⨟ Δ ,∙ ▶ k , A' ⇘ Γ' ,∙ ⨟ Δ' ,∙
  ▶S= : Γ ⨟ Δ ▶ k , A  ⇘ Γ' ⨟ Δ'
      → ↑ty0 A ⇘ A'
      → Γ ,= B ⨟ Δ ,= B ▶ k , A' ⇘ Γ' ,= B ⨟ Δ' ,= B
  ▶S^= : Γ ⨟ Δ ▶ k , A  ⇘ Γ' ⨟ Δ'
      → ↑ty0 A ⇘ A'
      → Γ ,^ ⨟ Δ ,= B ▶ k , A' ⇘ Γ' ,^ ⨟ Δ' ,= B



infix 3 _▶_,^⇘_
data _▶_,^⇘_ : Env n m → Fin (1 + m) → Env n (1 + m) → Set where
  ▶Z : Γ ▶ #0 ,^⇘ Γ ,^
  ▶S, : Γ ▶ k ,^⇘ Γ'
      → (upA : A ↑ty k ⇘ A')
      → Γ , A ▶ k ,^⇘ Γ' , A'
  ▶S^ : Γ ▶ k ,^⇘ Γ'
      → Γ ,^ ▶ #S k ,^⇘ Γ' ,^
  ▶S∙ : Γ ▶ k ,^⇘ Γ'
      → Γ ,∙ ▶ #S k ,^⇘ Γ' ,∙
  ▶S= : Γ ▶ k ,^⇘ Γ'
      → (upB : B ↑ty k ⇘ B')
      → Γ ,= B ▶ #S k ,^⇘ Γ' ,= B'
  ▶S⋈ : Γ ▶ k ,^⇘ Γ'
      → Γ ⋈ ▶ k ,^⇘ Γ' ⋈

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

infix 3 _▶_,=_⇘_
data _▶_,=_⇘_ : Env n m → Fin (1 + m) → Type m → Env n (1 + m) → Set where
  ▶Z  : (cloA : Γ ⊢r A)
      → Γ ▶ #0 ,= A ⇘ Γ ,= A
  ▶S, : Γ ▶ k ,= A ⇘ Γ'
      → (up : B ↑ty k ⇘ B')
      → Γ , B ▶ k ,= A ⇘ Γ' , B'
  ▶S^ : Γ ▶ k ,= A ⇘ Γ'
      → ↑ty0 A ⇘ A' -- an alternative is defining an unshift
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

----------------------------------------------------------------------
--+                       Entry Replacement                        +--
----------------------------------------------------------------------

-- could be a combination of weaken and strengthen

-- replace entry ^a with a solution ^a=A in an environment
infix 3 [_/_]_⟹_
data [_/_]_⟹_ : Type m → Fin m → Env n m → Env n m → Set where
  ⟹^0 : (up : ↑ty0 A ⇘ A')
        → (regA : Γ ⊢r A)
        → (env : SRegular Γ)
        → [ A' / #0 ] (Γ ,^) ⟹ (Γ ,= A)

  ⟹^S : [ A / k ] Γ ⟹ Γ'
        → (up1 : ↑ty0 A ⇘ A')
        → [ A' / #S k ] (Γ ,^) ⟹ Γ' ,^

  ⟹∙S : [ A / k ] Γ ⟹ Γ'
        → (up1 : ↑ty0 A ⇘ A')
        → [ A' / #S k ] (Γ ,∙) ⟹ (Γ' ,∙)

  ⟹=S : [ A / k ] Γ ⟹ Γ'
        → (up1 : ↑ty0 A ⇘ A')
        → (regB : Γ ⊢r B)
        → [ A' / #S k ] (Γ ,= B) ⟹ (Γ' ,= B)

inst-⊢r : [ A / k ] Γ ⟹ Δ
        → Γ ⊢r A
inst-⊢r (⟹^0 up regA env) = ⊢r-weaken^0 regA up
inst-⊢r (⟹^S inst up1) = ⊢r-weaken^0 (inst-⊢r inst) up1
inst-⊢r (⟹∙S inst up1) = ⊢r-weaken∙0 (inst-⊢r inst) up1
inst-⊢r (⟹=S inst up1 regB) = ⊢r-weaken=0 (inst-⊢r inst) up1 regB

inst-∋^ : [ A / k ] Γ ⟹ Δ
        → Γ ∋^ k
inst-∋^ (⟹^0 up regA env) = Z
inst-∋^ (⟹^S inst up1) = S^ (inst-∋^ inst)
inst-∋^ (⟹∙S inst up1) = S∙ (inst-∋^ inst)
inst-∋^ (⟹=S inst up1 regB) = S= (inst-∋^ inst)

-- replace entry a with a solution ^a=A in an environment
infix 3 [_/_]_∙⟹_
data [_/_]_∙⟹_ : Type m → Fin m → Env n m → Env n m → Set where
  ∙⟹^0 : (up : ↑ty0 A ⇘ A')
        → [ A' / #0 ] (Γ ,∙) ∙⟹ (Γ ,= A)

  ∙⟹^S : [ A / k ] Γ ∙⟹ Γ'
        → (up1 : ↑ty0 A ⇘ A')
        → [ A' / #S k ] (Γ ,^) ∙⟹ Γ' ,^

  ∙⟹∙S : [ A / k ] Γ ∙⟹ Γ'
        → (up1 : ↑ty0 A ⇘ A')
        → [ A' / #S k ] (Γ ,∙) ∙⟹ (Γ' ,∙)

{-
  ∙⟹,S : [ A / k ] Γ ∙⟹ Γ'
       → [ A / k ] (Γ , B) ∙⟹ (Γ' , B)
-}

  ∙⟹=S : [ A / k ] Γ ∙⟹ Γ'
        → (up1 : ↑ty0 A ⇘ A')
        → [ A' / #S k ] (Γ ,= B) ∙⟹ (Γ' ,= B)

-- replace entry a with a solution ^a=A in an environment
infix 3 [_/_]_=⟹_
data [_/_]_=⟹_ : Type m → Fin m → Env n m → Env n m → Set where
  =⟹=0 : (up : ↑ty0 A ⇘ A')
        → [ A' / #0 ] (Γ ,= B) =⟹ (Γ ,= A)

  =⟹^S : [ A / k ] Γ =⟹ Γ'
        → (up1 : ↑ty0 A ⇘ A')
        → [ A' / #S k ] (Γ ,^) =⟹ Γ' ,^

  =⟹∙S : [ A / k ] Γ =⟹ Γ'
        → (up1 : ↑ty0 A ⇘ A')
        → [ A' / #S k ] (Γ ,∙) =⟹ (Γ' ,∙)
{-
  =⟹,S : [ A / k ] Γ =⟹ Γ'
       → [ A / k ] (Γ , B) =⟹ (Γ' , B)
-}

  =⟹=S : [ A / k ] Γ =⟹ Γ'
        → (up1 : ↑ty0 A ⇘ A')
        → [ A' / #S k ] (Γ ,= B) =⟹ (Γ' ,= B)

=⟹-∋= : [ A / k ] Γ =⟹ Γ'
      → Γ ∋= k
=⟹-∋= (=⟹=0 up) = Z
=⟹-∋= (=⟹^S inst up1) = S^ (=⟹-∋= inst)
=⟹-∋= (=⟹∙S inst up1) = S∙ (=⟹-∋= inst)
=⟹-∋= (=⟹=S inst up1) = S= (=⟹-∋= inst)

{-
=⟹-total : Γ ∋= k
          → k ¬ε⋆ A
          → ∃[ Γ' ]([ A / k ] Γ =⟹ Γ')
=⟹-total {Γ = Γ ,= _} Z ninA with ↑ty-surjective⋆ ninA z≤n
... | ⟨ A' , upA ⟩ = ⟨ Γ ,= A' , =⟹^0 upA ⟩
=⟹-total {Γ = Γ ,∙} (S∙ inΓ) ninA
  with ⟨ A' , upA ⟩ ← ↑ty-surjective⋆ ninA z≤n
  with ⟨ Γ' , newΓ ⟩ ← =⟹-total inΓ (¬ε⋆-↑ty'0 ninA upA) = ⟨ Γ' ,∙ , =⟹∙S newΓ upA ⟩
=⟹-total {Γ = Γ} (S^ inΓ) ninA with ⟨ A' , upA ⟩ ← ↑ty-surjective⋆ ninA z≤n
  with ⟨ Γ' , newΓ ⟩ ← =⟹-total infΓ (¬ε⋆-↑ty'0 ninA upA) = ⟨ Γ' ,^ , =⟹^S newΓ upA ⟩
=⟹-total {Γ = Γ ,= B} (S= inΓ) ninA with ⟨ A' , upA ⟩ ← ↑ty-surjective⋆ ninA z≤n
  with ⟨ Γ' , newΓ ⟩ ← =⟹-total inΓ (¬ε⋆-↑ty'0 ninA upA) = ⟨ Γ' ,= B , =⟹=S newΓ upA ⟩



↑ty-¬ε⋆ : ↑ty0 A ⇘ A'
        → #0 ¬ε⋆ A' by #0
↑ty-¬ε⋆ ↑ty-int = ¬ε⋆-int
↑ty-¬ε⋆ ↑ty-var = ¬ε⋆-var-f (s≤s z≤n)
↑ty-¬ε⋆ (↑ty-arr upA upA₁) = ¬ε⋆-arr (↑ty-¬ε⋆ upA) (↑ty-¬ε⋆ upA₁)
↑ty-¬ε⋆ (↑ty-∀ upA) = ¬ε⋆-∀ {!!}

=⟹-¬ε⋆ : [ A / k ] Γ =⟹ Γ'
       → k ¬ε⋆ A
=⟹-¬ε⋆ (=⟹^0 up) = {!!}
=⟹-¬ε⋆ (=⟹^S inst up1) = ¬ε⋆-↑ty (=⟹-¬ε⋆ inst) up1 z≤n
=⟹-¬ε⋆ (=⟹∙S inst up1) = ¬ε⋆-↑ty (=⟹-¬ε⋆ inst) up1 z≤n
=⟹-¬ε⋆ (=⟹=S inst up1) = ¬ε⋆-↑ty (=⟹-¬ε⋆ inst) up1 z≤n
-}


----------------------------------------------------------------------
--+                          replacement                           +--
----------------------------------------------------------------------

-- in k position, we replace a ,= B with ,∙
infix 3 _◆_⇘_
data _◆_⇘_ : Env n m → Fin m → Env n m → Set where
  ◆Z : Γ ,= A ◆ #0 ⇘ Γ ,∙
  ◆S, : Γ ◆ k ⇘ Γ'
      → Γ , A ◆ k ⇘ Γ' , A
  ◆S∙ : Γ ◆ k ⇘ Γ'
      → Γ ,∙ ◆ #S k ⇘ Γ' ,∙
  ◆S= : Γ ◆ k ⇘ Γ'
      → Γ ,= A ◆ #S k ⇘ Γ' ,= A
  ◆S^ : Γ ◆ k ⇘ Γ'
      → Γ ,^ ◆ #S k ⇘ Γ' ,^

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
