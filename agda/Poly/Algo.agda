module Poly.Algo where

open import Poly.Common

-- Env for algorithmic subtyping
data SEnv : ℕ → ℕ → Set where
  𝕓     : (Γ : Env n m) → SEnv n m
  _,∙   : SEnv n m → SEnv n (1 + m) -- universal variable
  _,^   : SEnv n m → SEnv n (1 + m) -- existential variable
  _,=_  : SEnv n m → (A : Type m) → SEnv n (1 + m) -- solved equation

----------------------------------------------------------------------
--+                             Typing                             +--
----------------------------------------------------------------------

infixr 7 [_]↝_
infixr 7 ⟦_⟧↝_

data Context : ℕ → ℕ → Set where
  □     : Context n m
  τ_    : (A : Type m) → Context n m
  [_]↝_ : (e : Term n m) → Context n m → Context n m
  ⟦_⟧↝_ : (A : Type m) → Context n m → Context n m

data NonEmpty : Context n m → Set where
  ne-τ    : ∀ {A : Type m} → NonEmpty (Context n m ∋⦂ τ A)
  ne-app  : ∀ {e} {Σ : Context n m} → NonEmpty ([ e ]↝ Σ)
  ne-tapp : ∀ {A} {Σ : Context n m} → NonEmpty (⟦ A ⟧↝ Σ)
  

↑Σ : Fin (1 + n) → Context n m → Context (1 + n) m
↑Σ k □ = □
↑Σ k (τ A) = τ A
↑Σ k ([ e ]↝ Σ) = [ ↑tm k e ]↝ (↑Σ k Σ)
↑Σ k (⟦ A ⟧↝ Σ) = ⟦ A ⟧↝ (↑Σ k Σ)

↑Σ0 : Context n m → Context (1 + n) m
↑Σ0 = ↑Σ #0

↑tyΣ : Fin (1 + m) → Context n m → Context n (1 + m)
↑tyΣ k □ = □
↑tyΣ k (τ A) = τ (↑ty k A)
↑tyΣ k ([ e ]↝ Σ) = [ ↑ty-in-tm k e ]↝ (↑tyΣ k Σ)
↑tyΣ k (⟦ A ⟧↝ Σ) = ⟦ ↑ty k A ⟧↝ (↑tyΣ k Σ)

↑tyΣ0 : Context n m → Context n (1 + m)
↑tyΣ0 = ↑tyΣ #0

{-
-- environment substition
[_/ᵉ_] : SEnv n m → Type m → Type m
[ Ψ /ᵉ Int ] = Int
[ Ψ /ᵉ ‶ #0 ] = {!!}
[ Ψ /ᵉ ‶ #S X ] = {!!}
[ Ψ /ᵉ A `→ B ] = ([ Ψ /ᵉ A ]) `→ ([ Ψ /ᵉ B ])
[ Ψ /ᵉ `∀ A ] = {!!}
-}

Ψ→Γ : SEnv n m → Env n m
Ψ→Γ (𝕓 Γ)    = Γ
Ψ→Γ (Ψ ,∙)   = (Ψ→Γ Ψ) ,∙
-- this seems to be dangerous, I give a solution which could never reach (`e` is shifted)
-- so that I no need to touch the indices in expression `e`
Ψ→Γ (Ψ ,^)   = (Ψ→Γ Ψ) ,= Int
Ψ→Γ (Ψ ,= A) = (Ψ→Γ Ψ) ,= A

infix 3 _↪_,_
data _↪_,_ : SEnv n (1 + m) → Env n m → Type m → Set where
  
private
  variable
    Γ : Env n m
    Ψ Ψ' Ψ₁ Ψ₂ Ψ₃ : SEnv n m
    Σ : Context n m

infix 3 _⊢c_
infix 3 _⊢o_

-- closed: no free existential variables
data _⊢c_ : SEnv n m → Type m → Set where
  ⊢c-int : Ψ ⊢c Int
  ⊢c-base : ∀ {X}
    → 𝕓 Γ ⊢c ‶ X
  ⊢c-var∙0 : Ψ ,∙ ⊢c ‶ #0
  ⊢c-var∙S : ∀ {X}
    → Ψ ⊢c ‶ X
    → Ψ ,∙ ⊢c ‶ #S X
  ⊢c-var^S : ∀ {X}
    → Ψ ⊢c ‶ X
    → Ψ ,^ ⊢c ‶ #S X
  ⊢c-var=0 : ∀ {A} → Ψ ,= A ⊢c ‶ #0
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
  ⊢o-var∙S : ∀ {X}
    → Ψ ⊢o ‶ X
    → Ψ ,∙ ⊢o ‶ #S X
  ⊢o-var^0 : Ψ ,^ ⊢o ‶ #0
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

  kΓ : ∀ {k} {A}
    → k := A ∈' Γ
    → k := A ∈ (𝕓 Γ)
  Z : ∀ {A} → #0 := A ∈ Ψ ,= ↓ty0 A
  S^ : ∀ {k} {A : Type (1 + m)}
    → k := ↓ty0 A ∈ Ψ
    → #S k := A ∈ Ψ ,^
  S∙ : ∀ {k} {A : Type (1 + m)}
    → k := ↓ty0 A ∈ Ψ
    → #S k := A ∈ Ψ ,∙
  S= : ∀ {k B} {A : Type (1 + m)}
    → k := ↓ty0 A ∈ Ψ
    → #S k := A ∈ Ψ ,= B

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
    
  ⟹^0 : ∀ {Ψ : SEnv n m} {A}
    → [ A / #0 ] (Ψ ,^) ⟹ (Ψ ,= (↓ty0 A))

  ⟹^S : ∀ {Ψ Ψ' : SEnv n m} {A k}
    → [ ↓ty0 A / k ] Ψ ⟹ Ψ'
    → [ A / #S k ] (Ψ ,^) ⟹ Ψ' ,^

{-
  ⟹=0 : ∀ {Ψ : SEnv n m} {A B}
    → [ A / #0 ] (Ψ ,= B) ⟹ Ψ ,= B -- this is wrong, should be some equivlent reasoning
-}

  ⟹∙S : ∀ {Ψ Ψ' : SEnv n m} {A k}
    → [ ↓ty0 A / k ] Ψ ⟹ Ψ'
    → [ A / #S k ] (Ψ ,∙) ⟹ (Ψ' ,∙)

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
  S= : ∀ {k A}
    → k ^∈ Ψ
    → #S k ^∈ Ψ ,= A    



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
    → NonEmpty Σ
    → 𝕓 Γ ⊢ A ≤ Σ ⊣ Ψ ↪ B    --- Γ ⊢ j # A ≤ B
    → Γ ⊢ Σ ⇒ g ⇒ B          --- Γ ⊢ j # e ∶ B

  -- design choices here,
  -- (1) we maybe need a checking for tabs
  -- (2) we need a context (must have, if we intend to be consistent)
  ⊢tabs₁ : ∀ {e A}
    → Γ ,∙ ⊢ □ ⇒ e ⇒ A
    → Γ ⊢ □ ⇒ Λ e ⇒ `∀ A

  ⊢tapp : ∀ {e A B B'}
    → Γ ⊢ ⟦ A ⟧↝ Σ ⇒ e ⇒ `∀ B
    → (st : [ A ]ˢ B ⇨ B')
    → Γ ⊢ Σ ⇒ e [ A ] ⇒ B'    
  
data _⊢_≤_⊣_↪_ where
  s-int :
      Ψ ⊢ Int ≤ τ Int ⊣ Ψ ↪ Int

  s-empty : ∀ {A A'}
    → (p : Ψ ⊢c A)
    → inst Ψ [ A ]⟹ A'
    → Ψ ⊢ A ≤ □ ⊣ Ψ ↪ A'

  s-var : ∀ {X}
    → Ψ ⊢ ‶ X ≤ τ (‶ X) ⊣ Ψ ↪ ‶ X

  s-ex-l^ : ∀ {A X}
    → Ψ ⊢c A
    → X ^∈ Ψ
    → [ A / X ] Ψ ⟹ Ψ'
    → Ψ ⊢ ‶ X ≤ τ A ⊣ Ψ' ↪ A

  s-ex-l= : ∀ {A A₁ A₂ B X}
    → Ψ ⊢c A
    → X := B ∈ Ψ
    → Ψ ⊢ B ≤ τ A ⊣ Ψ' ↪ A₁
    → Ψ ⊢ ‶ X ≤ τ A ⊣ Ψ' ↪ A₂

  s-ex-r^ : ∀ {A X}
    → Ψ ⊢c A
    → X ^∈ Ψ
    → [ A / X ] Ψ ⟹ Ψ'
    → Ψ ⊢ A ≤ τ (‶ X) ⊣ Ψ' ↪ A

  -- this rule attempts to break the property "if context is a full type, the result should be same"
  -- but the definition of full type is whether contain a solved existetial variable
  s-ex-r= : ∀ {A A₂ B X}
    → Ψ ⊢c A
    → X := B ∈ Ψ
    → Ψ ⊢ A ≤ τ B ⊣ Ψ' ↪ A₂
    → Ψ ⊢ A ≤ τ (‶ X) ⊣ Ψ' ↪ (‶ X)

  s-arr : ∀ {A B C D A' D'}
    → Ψ₁ ⊢ C ≤ τ A ⊣ Ψ₂ ↪ A'
    → Ψ₂ ⊢ B ≤ τ D ⊣ Ψ₃ ↪ D'
    → Ψ₁ ⊢ A `→ B ≤ τ (C `→ D) ⊣ Ψ₃ ↪ (C `→ D)

  s-term-c : ∀ {A B A' D e}
    → Ψ ⊢c A
    → Ψ ⊢c B
    → (Ψ→Γ Ψ) ⊢ τ A ⇒ e ⇒ A'
    → Ψ ⊢ B ≤ Σ ⊣ Ψ' ↪ D
    → Ψ ⊢ (A `→ B) ≤ ([ e ]↝ Σ) ⊣ Ψ' ↪ A `→ D

  s-term-o : ∀ {A A' B C D e}
    → Ψ ⊢o A
    → (Ψ→Γ Ψ) ⊢ □ ⇒ e ⇒ C
    → Ψ ⊢ C ≤ τ A ⊣ Ψ₁ ↪ A'
    → Ψ₁ ⊢ B ≤ Σ ⊣ Ψ₂ ↪ D
    → Ψ ⊢ A `→ B ≤ ([ e ]↝ Σ) ⊣ Ψ₂ ↪ A' `→ D

  s-∀ : ∀ {A B C}
    → Ψ ,∙ ⊢ A ≤ τ B ⊣ Ψ' ,∙ ↪ C
    → Ψ ⊢ `∀ A ≤ τ (`∀ B) ⊣ Ψ' ↪ `∀ C

  s-∀l-^ : ∀ {A B e}
    → Ψ ,^ ⊢ A ≤ ↑tyΣ0 ([ e ]↝ Σ) ⊣ Ψ' ,^ ↪ ↑ty0 B
    → Ψ ⊢ `∀ A ≤ ([ e ]↝ Σ) ⊣ Ψ' ↪ B

  s-∀l-eq : ∀ {A B C e}
    → Ψ ,^ ⊢ A ≤ ↑tyΣ0 ([ e ]↝ Σ) ⊣ Ψ' ,= C ↪ B
    → Ψ ⊢ `∀ A ≤ ([ e ]↝ Σ) ⊣ Ψ' ↪ [ C ]ˢ B

  -- explicit type applicatoin
{-
  s-∀-t : ∀ {A B C}
    → Ψ ⊢ [ B ]ˢ A ≤ Σ ⊣ Ψ' ↪ C
    → Ψ ⊢ `∀ A ≤ (⟦ B ⟧↝ Σ) ⊣ Ψ' ↪ C
-}
  s-∀-t : ∀ {A B C}
    → Ψ ,= B ⊢ A ≤ ↑tyΣ0 Σ ⊣ Ψ' ,= B ↪ C
    → Ψ ⊢ `∀ A ≤ (⟦ B ⟧↝ Σ) ⊣ Ψ' ↪ [ B ]ˢ C

----------------------------------------------------------------------
--+                            Examples                            +--
----------------------------------------------------------------------
{-
idEnv : Env 1 0
idEnv = ∅ , `∀ (‶ #0 `→ ‶ #0)

sub-id[Int]1 : ∀ {Γ : Env n m} → 𝕓 Γ ⊢ `∀ ‶ #0 `→ ‶ #0 ≤ ⟦ Int ⟧↝ [ lit 1 ]↝ □ ⊣ 𝕓 Γ ↪ Int `→ Int
sub-id[Int]1 {Γ = Γ} = s-∀-t (s-term-c ⊢c-var=0 ⊢c-var=0
                             (⊢sub {Ψ = 𝕓 (Γ ,= Int)} ⊢lit ne-τ (s-ex-r= ⊢c-int (kΓ Z) s-int))
                             (s-empty ⊢c-var=0 (inst-var Z inst-int)))


sub-id[Int] : ∀ {Γ : Env n m} → 𝕓 Γ ⊢ `∀ ‶ #0 `→ ‶ #0 ≤ ⟦ Int ⟧↝ □ ⊣ 𝕓 Γ ↪ Int `→ Int
sub-id[Int] = s-∀-t (s-empty (⊢c-arr ⊢c-var=0 ⊢c-var=0) (inst-arr (inst-var Z inst-int) (inst-var Z inst-int)))

sub-id1 : ∀ {Γ : Env n m} → 𝕓 Γ ⊢ `∀ ‶ #0 `→ ‶ #0 ≤ [ lit 1 ]↝ □ ⊣ 𝕓 Γ ↪ Int `→ Int
sub-id1 = s-∀l-eq (s-term-o ⊢o-var^0
                           ⊢lit
                           (s-ex-r^ ⊢c-int Z ⟹^0)
                           (s-empty ⊢c-var=0 (inst-var Z inst-int)))

id[Int]1 : idEnv ⊢ □ ⇒ ((` #0) [ Int ]) · (lit 1) ⇒ Int
id[Int]1 = ⊢app (⊢tapp (⊢sub (⊢var refl)
                             ne-tapp
                             sub-id[Int]1))
idExp : Term 0 0
idExp = Λ (((ƛ ` #0) ⦂ ‶ #0 `→ ‶ #0))

idExp[Int]1 : ∅ ⊢ □ ⇒ (idExp [ Int ]) · (lit 1) ⇒ Int
idExp[Int]1 = ⊢app (⊢tapp (⊢sub
                            (⊢tabs₁ (⊢ann (⊢lam₁ (⊢sub (⊢var refl) ne-τ s-var)))) ne-tapp (sub-id[Int]1 {Γ = ∅})))

idExp[Int] : ∅ ⊢ □ ⇒ idExp [ Int ] ⇒ Int `→ Int
idExp[Int] = ⊢tapp (⊢sub (⊢tabs₁ (⊢ann (⊢lam₁ (⊢sub (⊢var refl) ne-τ s-var)))) ne-tapp sub-id[Int])

-- implicit inst
id1 : idEnv ⊢ □ ⇒ (` #0) · (lit 1) ⇒ Int
id1 = ⊢app (⊢sub (⊢var refl) ne-app sub-id1)


-- [e1] -> [e2] -> [e3] -> []
-- ------- Inf----- Chk -------

-- [1] -> [2] -> [] -- can we ensure the order of inference of 1 / 2
-}
