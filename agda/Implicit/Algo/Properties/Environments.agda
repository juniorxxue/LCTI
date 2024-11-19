module Implicit.Algo.Properties.Environments where

open import Implicit.Language
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Extension
open import Implicit.Algo.Properties.OpenClose
open import Implicit.Algo.Properties.Lookup

private variable
  Ψ Ψ' : SEnv n m
  A B C : Type m
  k : Fin m
  Σ : Context n m
  e : Term n m

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
inst-in (⟹=S up st) = S= (inst-in st) up

----------------------------------------------------------------------
--+                   Lemmas around env extension                  +--
----------------------------------------------------------------------

⊆-in= : k := C ∈ Ψ
      → Ψ ⊆ Ψ'
      → k := C ∈ Ψ'
⊆-in= (Z x) (svar ss) = Z x
⊆-in= (S, inΨ) (var ss) = S, (⊆-in= inΨ ss)
⊆-in= (S^ inΨ x) (evar ss) = S^ (⊆-in= inΨ ss) x
⊆-in= (S^ inΨ x) (evar-sol {A = A} ss) = S= (⊆-in= inΨ ss) (↑ty-st x)
⊆-in= (S∙ inΨ x) (uvar ss) = S∙ (⊆-in= inΨ ss) x
⊆-in= (S= inΨ st) (svar ss) = S= (⊆-in= inΨ ss) st

data ExSol (Ψ : SEnv n m) (k : Fin m) : Set where
  case-ex : (inΨ : k ^∈ Ψ) → ExSol Ψ k
  case-sol : ∀ {A} → (inΨ : k := A ∈ Ψ) → ExSol Ψ k

⊆-in^ : k ^∈ Ψ
       → Ψ ⊆ Ψ'
       → ExSol Ψ' k
⊆-in^ Z (evar ss) = case-ex Z
⊆-in^ Z (evar-sol {A = A} ss) = case-sol (Z (proj₂ (↑ty0-total A)))
⊆-in^ (S^ inΨ) (evar ss) with ⊆-in^ inΨ ss
... | case-ex inΨ₁ = case-ex (S^ inΨ₁)
... | case-sol {A = A} inΨ₁ = case-sol (S^ inΨ₁ (proj₂ (↑ty0-total A)))
⊆-in^ (S^ inΨ) (evar-sol ss) with ⊆-in^ inΨ ss
... | case-ex inΨ₁ = case-ex (S= inΨ₁)
... | case-sol {A = A'} inΨ₁ = let ⟨ _ , st ⟩ = st0-total-rev A'
                               in case-sol (S= inΨ₁ st)
⊆-in^ (S∙ inΨ) (uvar ss) with ⊆-in^ inΨ ss
... | case-ex inΨ₁ = case-ex (S∙ inΨ₁)
... | case-sol {A = A} inΨ₁ = case-sol (S∙ inΨ₁ (proj₂ (↑ty0-total A)))
⊆-in^ (S, inΨ) (var ss) with ⊆-in^ inΨ ss
... | case-ex inΨ₁ = case-ex (S, inΨ₁)
... | case-sol inΨ₁ = case-sol (S, inΨ₁)
⊆-in^ (S= inΨ) (svar ss) with ⊆-in^ inΨ ss
... | case-ex inΨ₁ = case-ex (S= inΨ₁)
... | case-sol {A = A'} inΨ₁ = let ⟨ _ , st ⟩ = st0-total-rev A'
                               in case-sol (S= inΨ₁ st)

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
^in^=out-l (s-var clo) ε-var inΨ = ⊥-elim (⊢c-^∈-false ε-var inΨ clo)
^in^=out-l (s-ex-l^ clo x-in inst) ε-var inΨ = sols (inst-in inst)
^in^=out-l (s-ex-l= clo x-in s) ε-var inΨ = sols (⊆-in= x-in (s-⊆ s))
^in^=out-l (s-ex-r^ clo x-in inst) inA inΨ = ⊥-elim (⊢c-^∈-false inA inΨ clo)
^in^=out-l (s-ex-r= clo x-in s) inA inΨ = ⊥-elim (⊢c-^∈-false inA inΨ clo)
^in^=out-l (s-arr s s₁) (ε-arr-l inA) inΨ with ^in^=out-r s (^∈-type inA) inΨ
... | sols inΨ₁ = sols (⊆-in= inΨ₁ (s-⊆ s₁))
^in^=out-l (s-arr s s₁) (ε-arr-r inA) inΨ with ⊆-in^ inΨ (s-⊆ s)
... | case-ex inΨ₁ = ^in^=out-l s₁ inA inΨ₁
... | case-sol inΨ₁ = sols (⊆-in= inΨ₁ (s-⊆ s₁))
^in^=out-l (s-term-c cloA ⊢e s) (ε-arr-l inA) inΨ = ⊥-elim (⊢c-^∈-false inA inΨ cloA)
^in^=out-l (s-term-c cloA ⊢e s) (ε-arr-r inA) inΨ = ^in^=out-l s inA inΨ
^in^=out-l (s-term-o opnA ⊢e s s₁) (ε-arr-l inA) inΨ with ^in^=out-r s (^∈-type inA) inΨ
... | sols inΨ₁ = sols (⊆-in= inΨ₁ (s-⊆ s₁))
^in^=out-l (s-term-o opnA ⊢e s s₁) (ε-arr-r inA) inΨ with ⊆-in^ inΨ (s-⊆ s)
... | case-ex inΨ₁ = ^in^=out-l s₁ inA inΨ₁
... | case-sol inΨ₁ = sols (⊆-in= inΨ₁ (s-⊆ s₁))
^in^=out-l (s-∀ s) (ε-∀ inA) inΨ with ^in^=out-l s inA (S∙ inΨ)
... | sols (S∙ inΨ₁ up₁) = sols inΨ₁
^in^=out-l (s-∀l s upc upe st₁ st₂) (ε-∀ inA) inΨ with ^in^=out-l s inA (S^ inΨ)
... | sols (S= inΨ₁ st) = sols inΨ₁

^in^=out-r s-int (^∈-type ()) inΨ
^in^=out-r (s-var clo) (^∈-type ε-var) inΨ = ⊥-elim (⊢c-^∈-false ε-var inΨ clo)
^in^=out-r (s-ex-l^ clo x-in inst) (^∈-type x) inΨ = ⊥-elim (⊢c-^∈-false x inΨ clo)
^in^=out-r (s-ex-l= clo x-in s) (^∈-type inA) inΨ = ⊥-elim (⊢c-^∈-false inA inΨ clo)
^in^=out-r (s-ex-r^ clo x-in inst) (^∈-type ε-var) inΨ = sols (inst-in inst)
^in^=out-r (s-ex-r= clo x-in s) (^∈-type ε-var) inΨ = ⊥-elim (^∈-=∈-false inΨ x-in)
^in^=out-r (s-arr s s₁) (^∈-type (ε-arr-l inA)) inΨ with ^in^=out-l s inA inΨ
... | sols inΨ' = sols (⊆-in= inΨ' (s-⊆ s₁))
^in^=out-r (s-arr s s₁) (^∈-type (ε-arr-r inA)) inΨ with ⊆-in^ inΨ (s-⊆ s)
... | case-ex inΨ₁ = ^in^=out-r s₁ (^∈-type inA) inΨ₁
... | case-sol inΨ₁ = sols (⊆-in= inΨ₁ (s-⊆ s₁))
^in^=out-r (s-term-c cloA ⊢e s) (^∈-term inΣ) inΨ = ^in^=out-r s inΣ inΨ
^in^=out-r (s-term-o opnA ⊢e s s₁) (^∈-term inΣ) inΨ with ⊆-in^ inΨ (s-⊆ s)
... | case-ex inΨ₁ = ^in^=out-r s₁ inΣ inΨ₁
... | case-sol inΨ₁ = sols (⊆-in= inΨ₁ (s-⊆ s₁))
^in^=out-r (s-∀ s) (^∈-type (ε-∀ inA)) inΨ with ^in^=out-r s (^∈-type inA) (S∙ inΨ)
... | sols (S∙ inΨ₁ up₁) = sols inΨ₁
^in^=out-r {k = k} (s-∀l s upc upe st₁ st₂) inΣ inΨ with ^in^=out-r s (εᶜ-↑tyᶜ0 inΣ (↑tyᶜ-e upe upc)) (S^ inΨ)
... | sols (S= inΨ₁ st) = sols inΨ₁


