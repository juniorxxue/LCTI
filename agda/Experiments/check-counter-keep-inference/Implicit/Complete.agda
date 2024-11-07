module Implicit.Complete where

open import Implicit.Common
open import Implicit.Decl renaming (_:=_∈_ to _:=_∈d_)
open import Implicit.Algo renaming (_:=_∈_ to _:=_∈a_)
open import Implicit.Algo.Subsumption
open import Implicit.Algo.Postulates

infix 3 _⊢_~_

data _⊢_~_ : Env n m → Counter × Type m → Context n m → Set

data _⊢_~_ where

  ~Z : ∀ {Γ : Env n m} {A}
    → Γ ⊢ ⟨ Z , A ⟩ ~ □

  ~∞ : ∀ {Γ : Env n m} {A }
    → Γ ⊢ ⟨ ∞ , A ⟩ ~ τ A

  ~I : ∀ {Γ : Env n m} {j A B Σ e}
    → (⊢e : Γ ⊢ □ ⇒ e ⇒ A)
    → Γ ⊢ ⟨ j , B ⟩ ~ Σ
    → Γ ⊢ ⟨ I j , A `→ B ⟩ ~ ([ e ]↝ Σ)

  ~C : ∀ {Γ : Env n m} {j A B Σ e}
    → (⊢e : Γ ⊢ τ A ⇒ e ⇒ A)
    → Γ ⊢ ⟨ j , B ⟩ ~ Σ
    → Γ ⊢ ⟨ C j , A `→ B ⟩ ~ ([ e ]↝ Σ)

postulate
  ~weaken0 : ∀ {Γ : Env n m} {Σ A B j}
    → Γ ⊢ ⟨ j , B ⟩ ~ Σ
    → Γ , A ⊢ ⟨ j , B ⟩ ~ ↑Σ0 Σ
    
  ⊢d→⊢c : ∀ {Γ : Env n m} {e A j}
    → Γ ⊢ j # e ⦂ A
    → 𝕎 Γ ⊢c A

  ⊢m-w : ∀ {Γ : Env n m} {A e j}
    → Γ ⊢ j # e ⦂ A
    → 𝕄 (𝕎 Γ) ⊢ j # e ⦂ A

complete : ∀ {Γ : Env n m} {Σ j e A}
  → Γ ⊢ j # e ⦂ A
  → Γ ⊢ ⟨ j , A ⟩ ~ Σ
  → Γ ⊢ Σ ⇒ e ⇒ A

complete-≤ : ∀ {Γ : Env n m} {Σ j A B}
  → Γ ⊢ j # B ≤ A
  → Γ ⊢ ⟨ j , A ⟩ ~ Σ -- should be gen to consider existential vars
  → 𝕎 Γ ⊢ B ≤ Σ ⊣ 𝕎 Γ ↪ A -- too strict

complete-≤' : ∀ {Γ : Env n m} {Ψ Σ j A B}
  → Γ ⊢ j # B ≤ A
  → Γ ⊢ ⟨ j , A ⟩ ~ Σ
  → Ψ ⊢ B ≤ Σ ⊣ 𝕎 Γ ↪ A -- this is too loose, abtrary Ψ cannot prove simple cases
  
complete-inf : ∀ {Γ : Env n m} {e A}
  → Γ ⊢ Z # e ⦂ A
  → Γ ⊢ □ ⇒ e ⇒ A
complete-inf ⊢e = complete ⊢e ~Z  

complete-chk : ∀ {Γ : Env n m} {e A}
  → Γ ⊢ ∞ # e ⦂ A
  → Γ ⊢ τ A ⇒ e ⇒ A
complete-chk ⊢e = complete ⊢e ~∞

complete-≤-chk : ∀ {Γ : Env n m} {A B}
  → Γ ⊢ ∞ # B ≤ A
  → 𝕎 Γ ⊢ B ≤ τ A ⊣ 𝕎 Γ ↪ A
complete-≤-chk B≤A = complete-≤ B≤A ~∞  

complete ⊢lit ~Z = ⊢lit
complete (⊢var x) ~Z = ⊢var x
complete (⊢ann ⊢e) ~Z = ⊢ann (complete-chk ⊢e)
complete (⊢lam₁ ⊢e) ~∞ = ⊢lam₁ (complete-chk ⊢e)
complete (⊢lam₂ ⊢e) (~I ⊢e' j~Σ) = ⊢lam₂ ⊢e' (complete ⊢e (~weaken0 j~Σ))
complete {Γ = Γ} (⊢app₁ ⊢e ⊢e₁) j~Σ = ⊢app (complete ⊢e (~C (complete-chk ⊢e₁) j~Σ))
complete (⊢app₂ ⊢e ⊢e₁) j~Σ = ⊢app (complete ⊢e (~I (complete-inf ⊢e₁) j~Σ))
complete (⊢sub ⊢e B≤A j≢Z) j~Σ = subsumption0 (complete-inf ⊢e) (complete-≤ B≤A j~Σ)
complete (⊢tabs ⊢e) ~Z = ⊢tabs (complete-inf ⊢e)

complete-≤ (s-refl) ~Z = s-empty {!!} -- ok
complete-≤ s-int ~∞ = s-int
complete-≤ s-var ~∞ = s-var
complete-≤ (s-arr₁ s s₁) ~∞ = s-arr (complete-≤-chk s) (complete-≤-chk s₁)
complete-≤ (s-arr₂ s s₁) (~I ⊢e j~Σ) = s-term-o (⊢a-m-w ⊢e) (complete-≤ s ~∞) (complete-≤ s₁ j~Σ)
complete-≤ (s-arr₃ s) (~C ⊢e ~j) = s-term-c {!!} (⊢a-m-w ⊢e) (complete-≤ s ~j)
complete-≤ (s-∀ s) ~∞ = s-∀ (complete-≤-chk s)
complete-≤ (s-∀l s have-i fd st₁ st₂) (~I ⊢e ~j) = s-∀l {!complete-≤ s ?!} st₁ st₂
complete-≤ (s-∀l s have-i fd st₁ st₂) (~C ⊢e ~j) = s-∀l {!!} st₁ st₂
complete-≤ (s-var-l x s) ~∞ = s-ex-l= {!!} {!!} (complete-≤-chk s) -- ok
complete-≤ (s-var-r x s) ~∞ = s-ex-r= {!!} {!!} (complete-≤-chk s) -- ok
