module Implicit.Algo.Environments where

open import Implicit.Common
open import Implicit.Properties
open import Implicit.Algo
open import Implicit.Algo.Extension

private variable
  Ψ Ψ' : SEnv n m
  A B C : Type m
  k : Fin m
  Σ : Context n m
  e : Term n m

inst-in : ∀ {X}
  → [ A / X ] Ψ ⟹ Ψ'
  → X := A ∈ Ψ'
inst-in (⟹^0 x) = Z x
inst-in (⟹^S st x) = S^ (inst-in st) x
inst-in (⟹∙S st x) = S∙ (inst-in st) x
inst-in (⟹,S st) = S, (inst-in st)
inst-in (⟹=S st) = S= (inst-in st)

-- Ψ ⊢ k ^∈ A
-- A contains type variable k, which is unsolved ex-var in Ψ
infix 3 _⊢_^∈_
data _⊢_^∈_ : SEnv n m → Fin m → Type m → Set where
  ^in-var :
      (is-^ : k ^∈ Ψ)
    → Ψ ⊢ k ^∈ (‶ k)
  ^in-arr-l :
      Ψ ⊢ k ^∈ A
    → Ψ ⊢ k ^∈ A `→ B
  ^in-arr-r :
      Ψ ⊢ k ^∈ B
    → Ψ ⊢ k ^∈ A `→ B
  ^in-∀ :
      Ψ ,∙ ⊢ #S k ^∈ A
    → Ψ ⊢ k ^∈ `∀ A
{-    
  ^in-∀^ :
      Ψ ,^ ⊢ #S k ^∈ A
    → Ψ ⊢ k ^∈ `∀ A
-}    

to^∈Ψ : Ψ ⊢ k ^∈ A
      → k ^∈ Ψ
to^∈Ψ (^in-var is-^) = is-^
to^∈Ψ (^in-arr-l inA) = to^∈Ψ inA
to^∈Ψ (^in-arr-r inA) = to^∈Ψ inA
to^∈Ψ (^in-∀ inA) with to^∈Ψ inA
... | S∙ ind = ind

⊢c-^∈-false' :
  k ^∈ Ψ → Ψ ⊢c ‶ k → ⊥
⊢c-^∈-false' (S^ ^in) (⊢c-var^S clo) = ⊢c-^∈-false' ^in clo
⊢c-^∈-false' (S∙ ^in) (⊢c-var∙S clo) = ⊢c-^∈-false' ^in clo
⊢c-^∈-false' (S, ^in) (⊢c-var,S clo) = ⊢c-^∈-false' ^in clo
⊢c-^∈-false' (S= ^in) (⊢c-var=S clo) = ⊢c-^∈-false' ^in clo

⊢c-^∈-false :
    Ψ ⊢c A
  → Ψ ⊢ k ^∈ A
  → ⊥
⊢c-^∈-false clo (^in-var x) = ⊢c-^∈-false' x clo
⊢c-^∈-false (⊢c-arr clo clo₁) (^in-arr-l ^in) = ⊢c-^∈-false clo ^in
⊢c-^∈-false (⊢c-arr clo clo₁) (^in-arr-r ^in) = ⊢c-^∈-false clo₁ ^in
⊢c-^∈-false (⊢c-∀ clo) (^in-∀ ^in) = ⊢c-^∈-false clo ^in

^∈-∙∈-false :
    k ^∈ Ψ
  → k ∙∈ Ψ
  → ⊥
^∈-∙∈-false (S^ ^in) (S^ ∙in) = ^∈-∙∈-false ^in ∙in
^∈-∙∈-false (S∙ ^in) (S∙ ∙in) = ^∈-∙∈-false ^in ∙in
^∈-∙∈-false (S, ^in) (S, ∙in) = ^∈-∙∈-false ^in ∙in
^∈-∙∈-false (S= ^in) (S= ∙in) = ^∈-∙∈-false ^in ∙in

^∈-=∈-false :
    k ^∈ Ψ
  → k := A ∈ Ψ
  → ⊥
^∈-=∈-false (S^ in1) (S^ in2 up₁) = ^∈-=∈-false in1 in2
^∈-=∈-false (S∙ in1) (S∙ in2 up₁) = ^∈-=∈-false in1 in2
^∈-=∈-false (S, in1) (S, in2) = ^∈-=∈-false in1 in2
^∈-=∈-false (S= in1) (S= in2) = ^∈-=∈-false in1 in2

infix 3 _⊢_:=_∈_
data _⊢_:=_∈_ : SEnv n m → Fin m → Type m → Type m → Set where
  ^:=-var :
      k := C ∈ Ψ
    → Ψ ⊢ k := C ∈ (‶ k)
  ^:=-arr-l :
      Ψ ⊢ k := C ∈ A
    → Ψ ⊢ k := C ∈ A `→ B
  ^:=-arr-r :
      Ψ ⊢ k := C ∈ B
    → Ψ ⊢ k := C ∈ A `→ B
  ^:=-∀ : ∀ {C'}
    → Ψ ,∙ ⊢ #S k := C' ∈ A
    → (up : ↑ty0 C ⇘ C')
    → Ψ ⊢ k := C ∈ `∀ A

postulate
  ↑ty0-pred : ∀ {A₁ : Type m} {A₂ A'} → ↑ty0 A₁ ⇘ A' → ↑ty0 A₂ ⇘ A' → A₁ ≡ A₂

to=∈Ψ : Ψ ⊢ k := A ∈ B
      → k := A ∈ Ψ
to=∈Ψ (^:=-var x) = x
to=∈Ψ (^:=-arr-l inΨ) = to=∈Ψ inΨ
to=∈Ψ (^:=-arr-r inΨ) = to=∈Ψ inΨ
to=∈Ψ (^:=-∀ inΨ up) with to=∈Ψ inΨ
... | S∙ ind up₁ rewrite ↑ty0-pred up up₁ = ind
  

infix 3 _⊢_^∈ᶜ_
data _⊢_^∈ᶜ_ : SEnv n m → Fin m → Context n m → Set where
  ^∈-type  : Ψ ⊢ k ^∈ A
           → Ψ ⊢ k ^∈ᶜ (τ A)
           
  ^∈-term  : Ψ ⊢ k  ^∈ᶜ Σ
           → Ψ ⊢ k ^∈ᶜ ([ e ]↝ Σ)

⊆-in= : k := C ∈ Ψ
      → Ψ ⊆ Ψ'
      → k := C ∈ Ψ'
⊆-in= (Z x) (svar ss) = Z x
⊆-in= (S, inΨ) (var ss) = S, (⊆-in= inΨ ss)
⊆-in= (S^ inΨ x) (evar ss) = S^ (⊆-in= inΨ ss) x
⊆-in= (S^ inΨ x) (evar-sol {A = A} ss) rewrite sym (↑ty⇘-st {C = A} x) = S= (⊆-in= inΨ ss)
⊆-in= (S∙ inΨ x) (uvar ss) = S∙ (⊆-in= inΨ ss) x
⊆-in= (S= inΨ) (svar ss) = S= (⊆-in= inΨ ss)

data ExSol (Ψ : SEnv n m) (k : Fin m) : Set where
  case-ex : (inΨ : k ^∈ Ψ) → ExSol Ψ k
  case-sol : ∀ {A} → (inΨ : k := A ∈ Ψ) → ExSol Ψ k

data ExSolType (Ψ : SEnv n m) (k : Fin m) (A : Type m) : Set where

  case-ex : (inΨ : Ψ ⊢ k ^∈ A) → ExSolType Ψ k A
  case-sol : ∀ {B} → (inΨ : Ψ ⊢ k := B ∈ A) → ExSolType Ψ k A

⊆-in^' : k ^∈ Ψ
       → Ψ ⊆ Ψ'
       → ExSol Ψ' k
⊆-in^' Z (evar ss) = case-ex Z
⊆-in^' Z (evar-sol ss) = case-sol (Z {!!})
⊆-in^' (S^ inΨ) (evar ss) with ⊆-in^' inΨ ss
... | case-ex inΨ₁ = case-ex (S^ inΨ₁)
... | case-sol inΨ₁ = case-sol (S^ inΨ₁ {!!})
⊆-in^' (S^ inΨ) (evar-sol ss) with ⊆-in^' inΨ ss
... | case-ex inΨ₁ = case-ex (S= inΨ₁)
... | case-sol inΨ₁ = case-sol (S= {!!})
⊆-in^' (S∙ inΨ) (uvar ss) with ⊆-in^' inΨ ss
... | case-ex inΨ₁ = case-ex (S∙ inΨ₁)
... | case-sol inΨ₁ = case-sol (S∙ inΨ₁ {!!})
⊆-in^' (S, inΨ) (var ss) with ⊆-in^' inΨ ss
... | case-ex inΨ₁ = case-ex (S, inΨ₁)
... | case-sol inΨ₁ = case-sol (S, inΨ₁)
⊆-in^' (S= inΨ) ss = {!!}

⊆-in^ : Ψ ⊢ k ^∈ A
      → Ψ ⊆ Ψ'
      → ExSolType Ψ' k A
⊆-in^ (^in-var is-^) ss = {!!}
⊆-in^ (^in-arr-l inΨ) ss with ⊆-in^ inΨ ss
... | case-ex x = case-ex (^in-arr-l x)
... | case-sol x = case-sol (^:=-arr-l x)
⊆-in^ (^in-arr-r inΨ) ss with ⊆-in^ inΨ ss
... | case-ex x = case-ex (^in-arr-r x)
... | case-sol x = case-sol (^:=-arr-r x)
⊆-in^ (^in-∀ inΨ) ss with ⊆-in^ inΨ (uvar ss)
... | case-ex inΨ₁ = case-ex (^in-∀ inΨ₁)
... | case-sol inΨ₁ = case-sol (^:=-∀ inΨ₁ {!⊆-in^!})

data SolEnv (k : Fin m) (Ψ : SEnv n m) : Set where
  sols : ∀ {C}
    → (inΨ : k := C ∈ Ψ)
    → SolEnv k Ψ

^∈-∀-ext : Ψ ⊢ k ^∈ `∀ A
         → (Ψ ,^) ⊢ #S k ^∈ A

----------------------------------------------------------------------
--+ Invariant: appearing existentials must be solved in output env +--
----------------------------------------------------------------------

^in^=out-l : ∀ {Ψ : SEnv n (1 + m)}
  → Ψ ⊢ A ≤ Σ ⊣ Ψ' ↪ B
  → Ψ ⊢ k ^∈ A
  → SolEnv k Ψ'

^in^=out-r : ∀ {Ψ : SEnv n (1 + m)}
  → Ψ ⊢ A ≤ Σ ⊣ Ψ' ↪ B
  → Ψ ⊢ k ^∈ᶜ Σ
  → SolEnv k Ψ'

^in^=out-l (s-empty p) ^inA = ⊥-elim (⊢c-^∈-false p ^inA)
^in^=out-l (s-var is-∙) (^in-var is-^) = ⊥-elim (^∈-∙∈-false is-^ is-∙)
^in^=out-l (s-ex-l^ clo x-in inst) (^in-var is-^) = sols (inst-in inst)
^in^=out-l (s-ex-l= clo x-in s) (^in-var is-^) = sols (⊆-in= x-in (s-⊆ s))
^in^=out-l (s-ex-r^ clo x-in inst) ^inA = ⊥-elim (⊢c-^∈-false clo ^inA)
^in^=out-l (s-ex-r= clo x-in s) ^inA = ^in^=out-l s ^inA
^in^=out-l (s-arr s s₁) (^in-arr-l ^inA) with ^in^=out-r s (^∈-type ^inA)
... | sols inΨ = sols (⊆-in= inΨ (s-⊆ s₁))
^in^=out-l (s-arr s s₁) (^in-arr-r ^inA) with ⊆-in^ ^inA (s-⊆ s)
... | case-ex inΨ = ^in^=out-l s₁ inΨ
... | case-sol inΨ = sols (⊆-in= (to=∈Ψ inΨ) (s-⊆ s₁))
^in^=out-l (s-term-c cloA ⊢e s) (^in-arr-l ^inA) = ⊥-elim (⊢c-^∈-false cloA ^inA)
^in^=out-l (s-term-c cloA ⊢e s) (^in-arr-r ^inA) = ^in^=out-l s ^inA
^in^=out-l (s-term-o opnA ⊢e s s₁) (^in-arr-l ^inA) with ^in^=out-r s (^∈-type ^inA)
... | sols inΨ = sols (⊆-in= inΨ (s-⊆ s₁))
^in^=out-l (s-term-o opnA ⊢e s s₁) (^in-arr-r ^inA) with ⊆-in^ ^inA (s-⊆ s)
... | case-ex inΨ = ^in^=out-l s₁ inΨ
... | case-sol inΨ = sols (⊆-in= (to=∈Ψ inΨ) (s-⊆ s₁))
^in^=out-l (s-∀ s) (^in-∀ ^inA) with ^in^=out-l s ^inA
... | sols (S∙ inΨ up₁) = sols inΨ
^in^=out-l (s-∀l s st₁ st₂) ^inA'@(^in-∀ ^inA) = {!^in^=out-l s !}

^in^=out-r s-int (^∈-type ())
^in^=out-r (s-empty p) ()
^in^=out-r (s-var is-∙) (^∈-type (^in-var is-^)) = ⊥-elim (^∈-∙∈-false is-^ is-∙)
^in^=out-r (s-ex-l^ clo x-in inst) (^∈-type x) = ⊥-elim (⊢c-^∈-false clo x)
^in^=out-r (s-ex-l= clo x-in s) ^inΣ = ^in^=out-r s ^inΣ
^in^=out-r (s-ex-r^ clo x-in inst) (^∈-type (^in-var is-^)) = sols (inst-in inst)
^in^=out-r (s-ex-r= clo x-in s) (^∈-type (^in-var is-^)) = ⊥-elim (^∈-=∈-false is-^ x-in)
^in^=out-r (s-arr s s₁) ^inΣ = {!!}
^in^=out-r (s-term-c cloA ⊢e s) (^∈-term ^inΣ) = ^in^=out-r s ^inΣ
^in^=out-r (s-term-o opnA ⊢e s s₁) (^∈-term ^inΣ) = {!!}
^in^=out-r (s-∀ s) ^inΣ = {!!}
^in^=out-r (s-∀l s st₁ st₂) ^inΣ = {!!}



