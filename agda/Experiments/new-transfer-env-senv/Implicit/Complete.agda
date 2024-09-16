module Implicit.Complete where

open import Implicit.Common
open import Implicit.Decl
open import Implicit.Algo
open import Implicit.Algo.Subsumption

infix 3 _⊢_~_

data _⊢_~_ : Env n m → Counter × Type m → Context n m → Set

data _⊢_~_ where

  ~Z : ∀ {Γ : Env n m} {A}
    → Γ ⊢ ⟨ Z , A ⟩ ~ □

  ~∞ : ∀ {Γ : Env n m} {A }
    → Γ ⊢ ⟨ ∞ , A ⟩ ~ τ A

  ~S : ∀ {Γ : Env n m} {j A B Σ e}
    → (⊢e : Γ ⊢ □ ⇒ e ⇒ A)
    → Γ ⊢ ⟨ j , B ⟩ ~ Σ
    → Γ ⊢ ⟨ S j , A `→ B ⟩ ~ ([ e ]↝ Σ)

{-
  ~∀ : ∀ {Γ : Env n m} {j A B Σ}
    → Γ ,= A ⊢ ⟨ j , B ⟩ ~ ↑tyΣ0 Σ
    → Γ ⊢ ⟨ j , `∀ B ⟩ ~ (⟦ A ⟧↝ Σ)
-}    


postulate
  ~weaken0 : ∀ {Γ : Env n m} {Σ A B j}
    → Γ ⊢ ⟨ j , B ⟩ ~ Σ
    → Γ , A ⊢ ⟨ j , B ⟩ ~ ↑Σ0 Σ

  ⊢a→⊢c : ∀ {Γ : Env n m} {Σ e A}
    → Γ ⊢ Σ ⇒ e ⇒ A
    → 𝕎 Γ ⊢c A
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
complete (⊢lam₂ ⊢e) (~S ⊢e' j~Σ) = ⊢lam₂ ⊢e' (complete ⊢e (~weaken0 j~Σ))
complete {Γ = Γ} (⊢app₁ ⊢e ⊢e₁) ~Z = ⊢app (subsumption0 (complete-inf ⊢e)
                                    (s-term-c (⊢d→⊢c ⊢e₁) (⊢c-arr-inv-r (⊢d→⊢c ⊢e)) (complete-chk (⊢m-w ⊢e₁)) (s-empty (⊢c-arr-inv-r (⊢d→⊢c ⊢e)))))
-- maybe some property like checking rule in previous system could be generlised
complete (⊢app₂ ⊢e ⊢e₁) j~Σ = ⊢app (complete ⊢e (~S (complete-inf ⊢e₁) j~Σ))
complete (⊢sub ⊢e B≤A j≢Z) j~Σ = subsumption0 (complete-inf ⊢e) (complete-≤ B≤A j~Σ)
complete (⊢tabs₁ ⊢e) ~Z = ⊢tabs₁ (complete-inf ⊢e)
complete (⊢tapp ⊢e st) ~Z = ⊢tapp (subsumption0 (complete-inf ⊢e) (s-∀-t (s-empty (⊢c-∀-= (⊢d→⊢c ⊢e))) st))

complete-≤ (s-refl) ~Z = s-empty {!!} -- ok
complete-≤ s-int ~∞ = s-int
complete-≤ s-var ~∞ = s-var
complete-≤ (s-arr₁ s s₁) ~∞ = s-arr (complete-≤-chk s) (complete-≤-chk s₁)
complete-≤ (s-arr₂ s s₁) (~S ⊢e j~Σ) = s-term-c {!!} {!!} {!!} (complete-≤ s₁ j~Σ) -- ok
complete-≤ (s-∀ s) ~∞ = s-∀ (complete-≤-chk s)
complete-≤ (s-∀l s fd st₁ st₂) (~S ⊢e j~Σ) = s-∀l-eq {!!} (st-arr st₁ st₂)
complete-≤ (s-var-l x s) ~∞ = s-ex-l= {!!} {!!} (complete-≤-chk s) -- ok
complete-≤ (s-var-r x s) ~∞ = s-ex-r= {!!} {!!} (complete-≤-chk s) -- ok
