module Implicit.Algo where

open import Implicit.Common
open import Implicit.Properties

-- Env for algorithmic subtyping
data SEnv : ℕ → ℕ → Set where
  ∅     : SEnv 0 0
  _,_   : SEnv n m → (A : Type m) → SEnv (1 + n) m
  _,∙   : SEnv n m → SEnv n (1 + m) -- universal variable
  _,^   : SEnv n m → SEnv n (1 + m) -- existential variable
  _,=_  : SEnv n m → (A : Type m) → SEnv n (1 + m) -- solved equation

----------------------------------------------------------------------
--+                             Typing                             +--
----------------------------------------------------------------------

infixr 7 [_]↝_

data Context : ℕ → ℕ → Set where
  □     : Context n m
  τ_    : (A : Type m) → Context n m
  [_]↝_ : (e : Term n m) → Context n m → Context n m

data NonEmpty : Context n m → Set where
  ne-τ    : ∀ {A : Type m} → NonEmpty (Context n m ∋⦂ τ A)
  ne-app  : ∀ {e} {Σ : Context n m} → NonEmpty ([ e ]↝ Σ)
  

↑Σ : Fin (1 + n) → Context n m → Context (1 + n) m
↑Σ k □ = □
↑Σ k (τ A) = τ A
↑Σ k ([ e ]↝ Σ) = [ ↑tm k e ]↝ (↑Σ k Σ)

↑Σ0 : Context n m → Context (1 + n) m
↑Σ0 = ↑Σ #0

↑tyΣ : Fin (1 + m) → Context n m → Context n (1 + m)
↑tyΣ k □ = □
↑tyΣ k (τ A) = τ (↑ty k A)
↑tyΣ k ([ e ]↝ Σ) = [ ↑ty-in-tm k e ]↝ (↑tyΣ k Σ)

↑tyΣ0 : Context n m → Context n (1 + m)
↑tyΣ0 = ↑tyΣ #0

infix 3 [_/_]ᶜ_⇨_
data [_/_]ᶜ_⇨_ : Fin (1 + m) → Type m → Context n (1 + m) → Context n m → Set where
  empty : ∀ {k A}
    → [ k / A ]ᶜ □ ⇨ (Context n m ∋⦂ □)
  fulltype : ∀ {k A B B'}
    → [ k / A ]ˢ B ⇨ B'
    → [ k / A ]ᶜ (τ B) ⇨ (Context n m ∋⦂ (τ B'))
  term : ∀ {k A e e' Σ Σ'}
    → [ k / A ]ᶜ Σ ⇨ Σ'
    → [ k / A ]ᵗ e ⇨ e'
    → [ k / A ]ᶜ ([ e ]↝ Σ) ⇨ (Context n m ∋⦂ ([ e' ]↝ Σ'))

infix 3 [_]ᶜ_⇨_
[_]ᶜ_⇨_ : Type m → Context n (1 + m) → Context n m → Set
[_]ᶜ_⇨_ = [_/_]ᶜ_⇨_ #0

infix 6 [_]ᶜ_
[_]ᶜ_ : Type m → Context n (1 + m) → Context n m
[ A ]ᶜ □ = □
[ A ]ᶜ (τ B) = τ ([ A ]ˢ B)
[ A ]ᶜ ([ e ]↝ Σ) = [ [ A ]ᵗ e ]↝ ([ A ]ᶜ Σ)

↓tyΣ0 : Context n (1 + m) → Context n m
↓tyΣ0 Σ = [ Int ]ᶜ Σ

{-
-- environment substition
[_/ᵉ_] : SEnv n m → Type m → Type m
[ Ψ /ᵉ Int ] = Int
[ Ψ /ᵉ ‶ #0 ] = {!!}
[ Ψ /ᵉ ‶ #S X ] = {!!}
[ Ψ /ᵉ A `→ B ] = ([ Ψ /ᵉ A ]) `→ ([ Ψ /ᵉ B ])
[ Ψ /ᵉ `∀ A ] = {!!}
-}

infix 3 _↪_,_
data _↪_,_ : SEnv n (1 + m) → Env n m → Type m → Set where
  
private
  variable
    Γ : Env n m
    Ψ Ψ' Ψ₁ Ψ₂ Ψ₃ : SEnv n m
    Σ : Context n m

data GenericConsumer : Term n m → Set where
  gc-i : ∀ {i} → GenericConsumer (Term n m ∋⦂ lit i)
  gc-var : ∀ {x} → GenericConsumer (Term n m ∋⦂ ` x)
  gc-ann : ∀ {e : Term n m} {A} → GenericConsumer (e ⦂ A)
  gc-tlam : ∀ {e : Term n (1 + m)} → GenericConsumer (Λ e)

infix 3 _⊢c_
infix 3 _⊢o_

-- closed: no free existential variables
data _⊢c_ : SEnv n m → Type m → Set where
  ⊢c-int : Ψ ⊢c Int
  ⊢c-var∙0 : Ψ ,∙ ⊢c ‶ #0
  ⊢c-var=0 : ∀ {A} → Ψ ,= A ⊢c ‶ #0
  ⊢c-var,S : ∀ {X A}
    → Ψ ⊢c ‶ X
    → Ψ , A ⊢c ‶ X
  ⊢c-var∙S : ∀ {X}
    → Ψ ⊢c ‶ X
    → Ψ ,∙ ⊢c ‶ #S X
  ⊢c-var^S : ∀ {X}
    → Ψ ⊢c ‶ X
    → Ψ ,^ ⊢c ‶ #S X
  ⊢c-var=S : ∀ {A X}
    → Ψ ⊢c ‶ X
    → Ψ ,= A ⊢c ‶ #S X
  ⊢c-arr : ∀ {A B}
    → Ψ ⊢c A
    → Ψ ⊢c B
    → Ψ ⊢c (A `→ B)
  ⊢c-∀ : ∀ {A}
    → Ψ ,∙ ⊢c A
    → Ψ ⊢c `∀ A

-- open: have free existential variables
data _⊢o_ : SEnv n m → Type m → Set where
  ⊢o-var^0 : Ψ ,^ ⊢o ‶ #0
  ⊢o-var∙S : ∀ {X}
    → Ψ ⊢o ‶ X
    → Ψ ,∙ ⊢o ‶ #S X
  ⊢o-var,S : ∀ {X : Fin (1 + m)} {A}
    → Ψ ⊢o ‶ X
    → Ψ , A ⊢o ‶ X
  ⊢o-var^S : ∀ {X}
    → Ψ ⊢o ‶ X
    → Ψ ,^ ⊢o ‶ #S X
  ⊢o-var=S : ∀ {A X}
    → Ψ ⊢o ‶ X
    → Ψ ,= A ⊢o ‶ #S X
  ⊢o-arr-l : ∀ {A B}
    → Ψ ⊢o A
    → Ψ ⊢o (A `→ B)
  ⊢o-arr-r : ∀ {A B}
    → Ψ ⊢o B
    → Ψ ⊢o (A `→ B)    
  ⊢o-∀ : ∀ {A}
    → Ψ ,∙ ⊢o A
    → Ψ ⊢o `∀ A

infix 3 _:=_∈_
data _:=_∈_ : Fin m → Type m → SEnv n m → Set where

  Z : ∀ {A : Type m} {A'}
    → ↑ty0 A ⇨ A'
    → #0 := A' ∈ Ψ ,= A
  S, : ∀ {k} {A B}
    → k := A ∈ Ψ
    → k := A ∈ Ψ , B
  S^ : ∀ {k} {A : Type m} {A'}
    → k := A ∈ Ψ
    → ↑ty0 A ⇨ A'
    → #S k := A' ∈ Ψ ,^
  S∙ : ∀ {k} {A : Type m} {A'}
    → k := A ∈ Ψ
    → ↑ty0 A ⇨ A'
    → #S k := A' ∈ Ψ ,∙
  S= : ∀ {k B} {A : Type (1 + m)}
    → k := [ B ]ˢ A ∈ Ψ
    → #S k := A ∈ Ψ ,= B

-- the above is an version that extract the type out of the context
-- try to define a version with the exact type

{-
infix 3 _:=_∈/_
data _:=_∈/_ :  Fin m' → Type m' → SEnv n m → Set where
  Z : ∀ {A}
    → #0 := A ∈/ Ψ ,= A
  S, : ∀ {k : Fin m'} {A B}
    → k := A ∈/ Ψ
    → k := A ∈/ Ψ , B
  S^ : ∀ {k : Fin m'} {A}
    → k := A ∈/ Ψ
    → #S k := A ∈/ Ψ ,^ -- not okay here
-}    

infix 5 inst_[_]⟹_
data inst_[_]⟹_ : SEnv n m → Type m → Type m → Set where
  inst-int : inst Ψ [ Int ]⟹ Int
  inst-var : ∀ {X A A'}
    → X := A ∈ Ψ
    → inst Ψ [ A ]⟹ A'
    → inst Ψ [ ‶ X ]⟹ A'
  inst-arr : ∀ {A B A' B'}
    → inst Ψ [ A ]⟹ A'
    → inst Ψ [ B ]⟹ B'
    → inst Ψ [ A `→ B ]⟹ A' `→ B'
  inst-∀ : ∀ {A A'}
    → inst (Ψ ,∙) [ A ]⟹ A'
    → inst Ψ [ `∀ A ]⟹ `∀ A'

infix 4 [_/_]_⟹_
data [_/_]_⟹_ : Type m → Fin m → SEnv n m → SEnv n m → Set where

{-
  ⟹, : ∀ {Ψ Ψ' : Env n m} {k A B}
    → [ A / k ] Ψ ⟹ Ψ'
    → [ A / k ] (Ψ , B) ⟹ Ψ' , B
-}
    
  ⟹^0 : ∀ {Ψ : SEnv n m} {A A'}
    → ↑ty0 A ⇨ A'
    → [ A' / #0 ] (Ψ ,^) ⟹ (Ψ ,= A)

  ⟹^S : ∀ {Ψ Ψ' : SEnv n m} {A k A'}
    → [ A / k ] Ψ ⟹ Ψ'
    → ↑ty0 A ⇨ A'
    → [ A' / #S k ] (Ψ ,^) ⟹ Ψ' ,^

{-
  ⟹=0 : ∀ {Ψ : SEnv n m} {A B}
    → [ A / #0 ] (Ψ ,= B) ⟹ Ψ ,= B -- this is wrong, should be some equivlent reasoning
-}

  ⟹∙S : ∀ {Ψ Ψ' : SEnv n m} {A k A'}
    → [ A / k ] Ψ ⟹ Ψ'
    → ↑ty0 A ⇨ A'
    → [ A' / #S k ] (Ψ ,∙) ⟹ (Ψ' ,∙)

  ⟹,S : ∀ {Ψ Ψ' : SEnv n m} {A k B}
    → [ A / k ] Ψ ⟹ Ψ'
    → [ A / k ] (Ψ , B) ⟹ (Ψ' , B)

  ⟹=S : ∀ {Ψ Ψ' : SEnv n m} {A B k}
    → [ [ B ]ˢ A / k ] Ψ ⟹ Ψ'
    → [ A / #S k ] (Ψ ,= B) ⟹ (Ψ' ,= B)

infix 3 _^∈_
data _^∈_ : Fin m → SEnv n m → Set where

  Z : #0 ^∈ Ψ ,^
  S^ : ∀ {k}
    → k ^∈ Ψ
    → #S k ^∈ Ψ ,^
  S∙ : ∀ {k}
    → k ^∈ Ψ
    → #S k ^∈ Ψ ,∙
  S, : ∀ {k A}
    → k ^∈ Ψ
    → k ^∈ Ψ , A
  S= : ∀ {k A}
    → k ^∈ Ψ
    → #S k ^∈ Ψ ,= A

infix 3 _∙∈_
data _∙∈_ : Fin m → SEnv n m → Set where
  
  Z : #0 ∙∈ Ψ ,∙
  S^ : ∀ {k}
    → k ∙∈ Ψ
    → #S k ∙∈ Ψ ,^
  S∙ : ∀ {k}
    → k ∙∈ Ψ
    → #S k ∙∈ Ψ ,∙
  S, : ∀ {k A}
    → k ∙∈ Ψ
    → k ∙∈ Ψ , A
  S= : ∀ {k A}
    → k ∙∈ Ψ
    → #S k ∙∈ Ψ ,= A
 

infix 8 𝕎 𝕄

𝕎 : Env n m → SEnv n m
𝕎 ∅ = ∅
𝕎 (Γ , A) = 𝕎 Γ , A
𝕎 (Γ ,∙) = 𝕎 Γ ,∙
𝕎 (Γ ,= A) = 𝕎 Γ ,= A

𝕄 : SEnv n m → Env n m
𝕄 ∅ = ∅
𝕄 (Ψ , A) = 𝕄 Ψ , A
𝕄 (Ψ ,∙) = 𝕄 Ψ ,∙
𝕄 (Ψ ,^) = 𝕄 Ψ ,= Int
𝕄 (Ψ ,= A) = 𝕄 Ψ ,= A


infix 3 _⊢_⇒_⇒_
infix 3 _⊢_≤_⊣_↪_

data _⊢_⇒_⇒_ : Env n m → Context n m → Term n m → Type m → Set
-- we cannot syntactically distinguish the result type here, which should contain unsolved variables
data _⊢_≤_⊣_↪_ : SEnv n m → Type m → Context n m → SEnv n m → Type m → Set

data _⊢_⇒_⇒_ where

  ⊢lit : ∀ {i}
    → Γ ⊢ □ ⇒ lit i ⇒ Int

  ⊢var : ∀ {x A}
    → (x∈Γ : lookup Γ x ≡ A)
    → Γ ⊢ □ ⇒ ` x ⇒ A

  ⊢ann : ∀ {e A B}
    → Γ ⊢ τ A ⇒ e ⇒ B
    → Γ ⊢ □ ⇒ e ⦂ A ⇒ A

  ⊢app : ∀ {e₁ e₂ A B}
    → Γ ⊢ [ e₂ ]↝ Σ ⇒ e₁ ⇒ A `→ B
    → Γ ⊢ Σ ⇒ e₁ · e₂ ⇒ B

  ⊢lam₁ : ∀ {A B C e}
    → Γ , A ⊢ τ B ⇒ e ⇒ C
    → Γ ⊢ τ (A `→ B) ⇒ ƛ e ⇒ A `→ C

  ⊢lam₂ : ∀ {A B e e₂}
    → Γ ⊢ □ ⇒ e₂ ⇒ A
    → Γ , A ⊢ ↑Σ0 Σ ⇒ e ⇒ B
    → Γ ⊢ [ e₂ ]↝ Σ ⇒ ƛ e ⇒ A `→ B

  ⊢sub : ∀ {g A B}
    → Γ ⊢ □ ⇒ g ⇒ A          --- Γ ⊢ Z # e : A
    → (ne : NonEmpty Σ)
    → (gc : GenericConsumer g)
    → (s : 𝕎 Γ ⊢ A ≤ Σ ⊣ 𝕎 Γ ↪ B)    --- Γ ⊢ j # A ≤ B
    → Γ ⊢ Σ ⇒ g ⇒ B          --- Γ ⊢ j # e ∶ B

  -- design choices here,
  -- (1) we maybe need a checking for tabs
  -- (2) we need a context (must have, if we intend to be consistent)
  ⊢tabs : ∀ {e A}
    → Γ ,∙ ⊢ □ ⇒ e ⇒ A
    → Γ ⊢ □ ⇒ Λ e ⇒ `∀ A
  
data _⊢_≤_⊣_↪_ where
  s-int :
      Ψ ⊢ Int ≤ τ Int ⊣ Ψ ↪ Int

  s-empty : ∀ {A}
    → (p : Ψ ⊢c A)
--    → inst Ψ [ A ]⟹ A'
    → Ψ ⊢ A ≤ □ ⊣ Ψ ↪ A

  s-var : ∀ {X}
    → (is-∙ : X ∙∈ Ψ)
    → Ψ ⊢ ‶ X ≤ τ (‶ X) ⊣ Ψ ↪ ‶ X -- reconsider this rule, should it be restricted to noly univseral variable?

  s-ex-l^ : ∀ {A X}
    → (clo : Ψ ⊢c A)
    → (x-in : X ^∈ Ψ)
    → (inst : [ A / X ] Ψ ⟹ Ψ')
    → Ψ ⊢ ‶ X ≤ τ A ⊣ Ψ' ↪ A
 
  s-ex-l= : ∀ {A B X A'}
    → (clo : Ψ ⊢c A)
    → (x-in : X := B ∈ Ψ)
    → Ψ ⊢ B ≤ τ A ⊣ Ψ' ↪ A'
    → Ψ ⊢ ‶ X ≤ τ A ⊣ Ψ' ↪ A

  s-ex-r^ : ∀ {A X}
    → (clo : Ψ ⊢c A)
    → (x-in : X ^∈ Ψ)
    → (inst : [ A / X ] Ψ ⟹ Ψ')
    → Ψ ⊢ A ≤ τ (‶ X) ⊣ Ψ' ↪ ‶ X

  -- this rule attempts to break the property "if context is a full type, the result should be same"
  -- but the definition of full type is whether contain a solved existetial variable

  s-ex-r= : ∀ {A A₂ B X}
    → (clo : Ψ ⊢c A)
    → (x-in : X := B ∈ Ψ)
    → Ψ ⊢ A ≤ τ B ⊣ Ψ' ↪ A₂
    → Ψ ⊢ A ≤ τ (‶ X) ⊣ Ψ' ↪ (‶ X)

  s-arr : ∀ {A B C D A' D'}
    → Ψ₁ ⊢ C ≤ τ A ⊣ Ψ₂ ↪ A'
    → Ψ₂ ⊢ B ≤ τ D ⊣ Ψ₃ ↪ D'
    → Ψ₁ ⊢ A `→ B ≤ τ (C `→ D) ⊣ Ψ₃ ↪ (C `→ D)

  s-term-c : ∀ {A B A' D e}
    → (cloA : Ψ ⊢c A)
    → (⊢e : (𝕄 Ψ) ⊢ τ A ⇒ e ⇒ A')
    → Ψ ⊢ B ≤ Σ ⊣ Ψ' ↪ D
    → Ψ ⊢ (A `→ B) ≤ ([ e ]↝ Σ) ⊣ Ψ' ↪ A' `→ D

  s-term-o : ∀ {A A' B C D e}
    → (opnA : Ψ ⊢o A)
    → (⊢e : (𝕄 Ψ) ⊢ □ ⇒ e ⇒ C)
    → Ψ ⊢ C ≤ τ A ⊣ Ψ₁ ↪ A'
    → Ψ₁ ⊢ B ≤ Σ ⊣ Ψ₂ ↪ D
    → Ψ ⊢ A `→ B ≤ ([ e ]↝ Σ) ⊣ Ψ₂ ↪ C `→ D

  s-∀ : ∀ {A B C}
    → Ψ ,∙ ⊢ A ≤ τ B ⊣ Ψ' ,∙ ↪ C
    → Ψ ⊢ `∀ A ≤ τ (`∀ B) ⊣ Ψ' ↪ `∀ C

  s-∀l : ∀ {A B C C' D D' e}
    → Ψ ,^ ⊢ A ≤ ↑tyΣ0 ([ e ]↝ Σ) ⊣ Ψ' ,= B ↪ (C `→ D)
    → (st₁ : [ B ]ˢ C ⇨ C')
    → (st₂ : [ B ]ˢ D ⇨ D')
    → Ψ ⊢ `∀ A ≤ ([ e ]↝ Σ) ⊣ Ψ' ↪ C' `→ D'


infix 4 ⟦_,_⟧→⟦_,_,_,_⟧

data ⟦_,_⟧→⟦_,_,_,_⟧ : Context n m → Type m → Apps n m → Context n m → AppsType m → Type m → Set where

  none-□ : ∀ {A}
    → ⟦ (Context n m ∋⦂ □) , A ⟧→⟦ nil , □ , nil , A ⟧

  none-τ : ∀ {A B}
    → ⟦ (Context n m ∋⦂ τ A) , B ⟧→⟦ nil , τ A , nil , B ⟧

  have-e : ∀ {Σ : Context n m} {e A B e̅ A' B' B̅}
    → ⟦ Σ , B ⟧→⟦ e̅ , A' , B̅ , B' ⟧
    → ⟦ ([ e ]↝ Σ) , A `→ B ⟧→⟦ e ∷a e̅ , A' , A ∷a B̅ , B' ⟧

infix 4 ⟦_,_⟧→s⟦_,_⟧
data ⟦_,_⟧→s⟦_,_⟧ : Context n m → Type m → Context n m → Type m → Set where

  none-□ : ∀ {A}
    → ⟦ (Context n m ∋⦂ □) , A ⟧→s⟦ □ , A ⟧

  none-τ : ∀ {A B}
    → ⟦ (Context n m ∋⦂ τ A) , B ⟧→s⟦ τ A , B ⟧

  have-e : ∀ {Σ : Context n m} {e A B Σ' B'}
    → ⟦ Σ , B ⟧→s⟦ Σ' , B' ⟧
    → ⟦ ([ e ]↝ Σ) , A `→ B ⟧→s⟦ Σ' , B' ⟧


infix 3 _⊆_
data _⊆_ : SEnv n m → SEnv n m → Set where
  base : ∅ ⊆ ∅
  uvar : ∀ {Ψ Ψ' : SEnv n m}
    → Ψ ⊆ Ψ'
    → Ψ ,∙ ⊆ Ψ' ,∙
  var : ∀ {Ψ Ψ' : SEnv n m} {A}
    → Ψ ⊆ Ψ'
    → Ψ , A ⊆ Ψ' , A
  evar : ∀ {Ψ Ψ' : SEnv n m}
    → Ψ ⊆ Ψ'
    → Ψ ,^ ⊆ Ψ' ,^
  evar-sol : ∀ {Ψ Ψ' : SEnv n m} {A}
    → Ψ ⊆ Ψ'
    → Ψ ,^ ⊆ Ψ' ,= A    
  svar : ∀ {Ψ Ψ' : SEnv n m} {A}
    → Ψ ⊆ Ψ'
    → Ψ ,= A ⊆ Ψ' ,= A
