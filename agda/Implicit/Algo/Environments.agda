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

----------------------------------------------------------------------
--+                          Definitions                           +--
----------------------------------------------------------------------


infix 3 _ε_
data _ε_ : Fin m → Type m → Set where
  ^in-var :
      k ε (‶ k)
  ^in-arr-l :
      k ε A
    → k ε A `→ B
  ^in-arr-r :
      k ε B
    → k ε A `→ B
  ^in-∀ :
      #S k ε A
    → k ε `∀ A


infix 3 _εᶜ_
data _εᶜ_ : Fin m → Context n m → Set where
  ^∈-type  : (inA : k ε A)
           → k εᶜ (Context n m ∋⦂ (τ A))
           
  ^∈-term  : k εᶜ Σ
           → k εᶜ ([ e ]↝ Σ)


----------------------------------------------------------------------
--+                          Small Lemmas                          +--
----------------------------------------------------------------------


inst-in : ∀ {X}
  → [ A / X ] Ψ ⟹ Ψ'
  → X := A ∈ Ψ'
inst-in (⟹^0 x) = Z x
inst-in (⟹^S st x) = S^ (inst-in st) x
inst-in (⟹∙S st x) = S∙ (inst-in st) x
inst-in (⟹,S st) = S, (inst-in st)
inst-in (⟹=S st) = S= (inst-in st)

⊢c-^∈-false' :
  k ^∈ Ψ → Ψ ⊢c ‶ k → ⊥
⊢c-^∈-false' (S^ ^in) (⊢c-var^S clo) = ⊢c-^∈-false' ^in clo
⊢c-^∈-false' (S∙ ^in) (⊢c-var∙S clo) = ⊢c-^∈-false' ^in clo
⊢c-^∈-false' (S, ^in) (⊢c-var,S clo) = ⊢c-^∈-false' ^in clo
⊢c-^∈-false' (S= ^in) (⊢c-var=S clo) = ⊢c-^∈-false' ^in clo
    
⊢c-^∈-false : k ε A
            → k ^∈ Ψ
            → Ψ ⊢c A
            → ⊥
⊢c-^∈-false ^in-var inΨ cloA = ⊢c-^∈-false' inΨ cloA
⊢c-^∈-false (^in-arr-l inA) inΨ (⊢c-arr cloA cloA₁) = ⊢c-^∈-false inA inΨ cloA
⊢c-^∈-false (^in-arr-r inA) inΨ (⊢c-arr cloA cloA₁) = ⊢c-^∈-false inA inΨ cloA₁
⊢c-^∈-false (^in-∀ inA) inΨ (⊢c-∀ cloA) = ⊢c-^∈-false inA (S∙ inΨ) cloA

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

postulate
  ↑ty0-pred : ∀ {A₁ : Type m} {A₂ A'} → ↑ty0 A₁ ⇘ A' → ↑ty0 A₂ ⇘ A' → A₁ ≡ A₂

ε-up : ∀ {A' k₁ k₂}
     → k₁ ε A
     → ty A ↑ k₂ ⇘ A'
     → k₂ #≤ k₁
     → #S k₁ ε A'
ε-up ^in-var ↑var sm rewrite punchIn-≤ sm = ^in-var
ε-up (^in-arr-l inA) (↑arr up₁ up₂) sm = ^in-arr-l (ε-up inA up₁ sm)
ε-up (^in-arr-r inA) (↑arr up₁ up₂) sm = ^in-arr-r (ε-up inA up₂ sm)
ε-up (^in-∀ inA) (↑∀ up₁) sm = ^in-∀ (ε-up inA up₁ (s≤s sm))

ε-up0 : ∀ {A'}
  → k ε A
  → ↑ty0 A ⇘ A'
  → #S k ε A'
ε-up0 inA up = ε-up inA up z≤n


----------------------------------------------------------------------
--+                   Lemmas around env extension                  +--
----------------------------------------------------------------------

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

⊆-in^ : k ^∈ Ψ
       → Ψ ⊆ Ψ'
       → ExSol Ψ' k
⊆-in^ Z (evar ss) = case-ex Z
⊆-in^ Z (evar-sol ss) = case-sol (Z {!!})
⊆-in^ (S^ inΨ) (evar ss) with ⊆-in^ inΨ ss
... | case-ex inΨ₁ = case-ex (S^ inΨ₁)
... | case-sol inΨ₁ = case-sol (S^ inΨ₁ {!!})
⊆-in^ (S^ inΨ) (evar-sol ss) with ⊆-in^ inΨ ss
... | case-ex inΨ₁ = case-ex (S= inΨ₁)
... | case-sol inΨ₁ = case-sol (S= {!!})
⊆-in^ (S∙ inΨ) (uvar ss) with ⊆-in^ inΨ ss
... | case-ex inΨ₁ = case-ex (S∙ inΨ₁)
... | case-sol inΨ₁ = case-sol (S∙ inΨ₁ {!!})
⊆-in^ (S, inΨ) (var ss) with ⊆-in^ inΨ ss
... | case-ex inΨ₁ = case-ex (S, inΨ₁)
... | case-sol inΨ₁ = case-sol (S, inΨ₁)
⊆-in^ (S= inΨ) (svar ss) with ⊆-in^ inΨ ss
... | case-ex inΨ₁ = case-ex (S= inΨ₁)
... | case-sol inΨ₁ = case-sol (S= {!!})

data SolEnv (k : Fin m) (Ψ : SEnv n m) : Set where
  sols : ∀ {C}
    → (inΨ : k := C ∈ Ψ)
    → SolEnv k Ψ

----------------------------------------------------------------------
--+ Invariant: appearing existentials must be solved in output env +--
----------------------------------------------------------------------

^in^=out-l : ∀ {Ψ : SEnv n (1 + m)}
  → Ψ ⊢ A ≤ Σ ⊣ Ψ' ↪ B
  → k ε A
  → k ^∈ Ψ
  → SolEnv k Ψ'

^in^=out-r : ∀ {Ψ : SEnv n (1 + m)}
  → Ψ ⊢ A ≤ Σ ⊣ Ψ' ↪ B
  → k εᶜ Σ
  → k ^∈ Ψ
  → SolEnv k Ψ'

^in^=out-l (s-empty p) inA inΨ = ⊥-elim (⊢c-^∈-false inA inΨ p)
^in^=out-l (s-var is-∙) ^in-var inΨ = ⊥-elim (^∈-∙∈-false inΨ is-∙)
^in^=out-l (s-ex-l^ clo x-in inst) ^in-var inΨ = sols (inst-in inst)
^in^=out-l (s-ex-l= clo x-in s) ^in-var inΨ = sols (⊆-in= x-in (s-⊆ s))
^in^=out-l (s-ex-r^ clo x-in inst) inA inΨ = ⊥-elim (⊢c-^∈-false inA inΨ clo)
^in^=out-l (s-ex-r= clo x-in s) inA inΨ = ⊥-elim (⊢c-^∈-false inA inΨ clo)
^in^=out-l (s-arr s s₁) (^in-arr-l inA) inΨ with ^in^=out-r s (^∈-type inA) inΨ
... | sols inΨ₁ = sols (⊆-in= inΨ₁ (s-⊆ s₁))
^in^=out-l (s-arr s s₁) (^in-arr-r inA) inΨ with ⊆-in^ inΨ (s-⊆ s)
... | case-ex inΨ₁ = ^in^=out-l s₁ inA inΨ₁
... | case-sol inΨ₁ = sols (⊆-in= inΨ₁ (s-⊆ s₁))
^in^=out-l (s-term-c cloA ⊢e s) (^in-arr-l inA) inΨ = ⊥-elim (⊢c-^∈-false inA inΨ cloA)
^in^=out-l (s-term-c cloA ⊢e s) (^in-arr-r inA) inΨ = ^in^=out-l s inA inΨ
^in^=out-l (s-term-o opnA ⊢e s s₁) (^in-arr-l inA) inΨ with ^in^=out-r s (^∈-type inA) inΨ
... | sols inΨ₁ = sols (⊆-in= inΨ₁ (s-⊆ s₁))
^in^=out-l (s-term-o opnA ⊢e s s₁) (^in-arr-r inA) inΨ with ⊆-in^ inΨ (s-⊆ s)
... | case-ex inΨ₁ = ^in^=out-l s₁ inA inΨ₁
... | case-sol inΨ₁ = sols (⊆-in= inΨ₁ (s-⊆ s₁))
^in^=out-l (s-∀ s) (^in-∀ inA) inΨ with ^in^=out-l s inA (S∙ inΨ)
... | sols (S∙ inΨ₁ up₁) = sols inΨ₁
^in^=out-l (s-∀l s st₁ st₂) (^in-∀ inA) inΨ with ^in^=out-l s inA (S^ inΨ)
... | sols (S= inΨ₁) = sols inΨ₁

^in^=out-r s-int (^∈-type ()) inΨ
^in^=out-r (s-var is-∙) (^∈-type ^in-var) inΨ = ⊥-elim (^∈-∙∈-false inΨ is-∙)
^in^=out-r (s-ex-l^ clo x-in inst) (^∈-type x) inΨ = ⊥-elim (⊢c-^∈-false x inΨ clo)
^in^=out-r (s-ex-l= clo x-in s) (^∈-type inA) inΨ = ⊥-elim (⊢c-^∈-false inA inΨ clo)
^in^=out-r (s-ex-r^ clo x-in inst) (^∈-type ^in-var) inΨ = sols (inst-in inst)
^in^=out-r (s-ex-r= clo x-in s) (^∈-type ^in-var) inΨ = ⊥-elim (^∈-=∈-false inΨ x-in)
^in^=out-r (s-arr s s₁) (^∈-type (^in-arr-l inA)) inΨ with ^in^=out-l s inA inΨ
... | sols inΨ' = sols (⊆-in= inΨ' (s-⊆ s₁))
^in^=out-r (s-arr s s₁) (^∈-type (^in-arr-r inA)) inΨ with ⊆-in^ inΨ (s-⊆ s)
... | case-ex inΨ₁ = ^in^=out-r s₁ (^∈-type inA) inΨ₁
... | case-sol inΨ₁ = sols (⊆-in= inΨ₁ (s-⊆ s₁))
^in^=out-r (s-term-c cloA ⊢e s) (^∈-term inΣ) inΨ = ^in^=out-r s inΣ inΨ
^in^=out-r (s-term-o opnA ⊢e s s₁) (^∈-term inΣ) inΨ with ⊆-in^ inΨ (s-⊆ s)
... | case-ex inΨ₁ = ^in^=out-r s₁ inΣ inΨ₁
... | case-sol inΨ₁ = sols (⊆-in= inΨ₁ (s-⊆ s₁))
^in^=out-r (s-∀ s) (^∈-type (^in-∀ inA)) inΨ with ^in^=out-r s (^∈-type inA) (S∙ inΨ)
... | sols (S∙ inΨ₁ up₁) = sols inΨ₁
^in^=out-r {k = k} (s-∀l s st₁ st₂) (^∈-term inΣ) inΨ with ^in^=out-r {k = #S k} s {!!} (S^ inΨ)
... | sols (S= inΨ₁) = sols inΨ₁


