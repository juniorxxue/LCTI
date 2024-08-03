module Poly.Complete where

open import Poly.Common
open import Poly.Decl
open import Poly.Algo
open import Poly.Basic
open import Poly.Algo.Subsumption

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
    → Γ ⊢ ⟨ S j , A `→ B ⟩ ~ ([ e ]↝ Σ) -- got a deeper undersantding of it, how the S will be eliminated, at least in two places in STLC

↑tmGenCon : ∀ {e : Term n m} {k }
  → GenericConsumer e 
  → GenericConsumer (↑tm k e)
↑tmGenCon {e = .(Term _ _ ∋⦂ lit _)} gc-i = gc-i
↑tmGenCon {e = .(Term _ _ ∋⦂ ` _)} gc-var = gc-var
↑tmGenCon {e = .(_ ⦂ _)} gc-ann = gc-ann
↑tmGenCon {e = .(Λ _)} gc-tlam = gc-tlam 

↑ΣnonEmpty : ∀ {Σ : Context n m} {k}
  → NonEmpty Σ
  → NonEmpty (↑Σ k Σ)
↑ΣnonEmpty ne-τ = ne-τ
↑ΣnonEmpty ne-app = ne-app
↑ΣnonEmpty ne-tapp = ne-tapp

↑Σsymm : ∀ {Σ : Context n m} {k}
  → ↑Σ0 (↑Σ k Σ) ≡ ↑Σ (#S k) (↑Σ0 Σ)
↑Σsymm = {!   !}

∈-weaken : ∀ {Γ : Env (1 + n) m} {k x A}
  → (Γ /ˣ k) ∋ x ⦂ A
  → Γ ∋ (punchIn k x) ⦂ A
∈-weaken ∈Γ = {!   !} 

weaken_cons_eq : ∀ {Γ : Env (1 + n) m} {A k} → 
  ((Γ /ˣ k) , A) ≡ ((Γ , A) /ˣ ( #S k ))
weaken_cons_eq = refl

mutual
  ≤weaken : ∀ {Γ : Env (1 + n) m} {Σ k A}
    → (Γ /ˣ k) ⊢ A ≤ Σ
    → Γ ⊢ A ≤ ↑Σ k Σ
  ≤weaken s-empty = s-empty
  ≤weaken s-refl = s-refl
  ≤weaken (s-arr ≤A ⊢e) = s-arr (≤weaken ≤A) (⊢weaken ⊢e)
  ≤weaken (s-∀-t st ≤A) = s-∀-t st (≤weaken ≤A)

  ⊢weaken : ∀ {Γ : Env (1 + n) m} { Σ k e A }
    → (Γ /ˣ k) ⊢ Σ ⇒ e ⇒ A
    → Γ ⊢ ↑Σ k Σ ⇒ ↑tm k e ⇒ A
  ⊢weaken ⊢lit = ⊢lit
  ⊢weaken (⊢var x∈Γ) = ⊢var (∈-weaken x∈Γ)
  ⊢weaken (⊢ann ⊢e) = ⊢ann (⊢weaken ⊢e)
  ⊢weaken (⊢app ⊢e) = ⊢app (⊢weaken ⊢e)
  ⊢weaken (⊢lam₁ ⊢e) = ⊢lam₁ (⊢weaken ⊢e)
  ⊢weaken {Γ = Γ} {k = k} (⊢lam₂ {Σ = Σ} {A} ⊢e ⊢e₁) rewrite (weaken_cons_eq { Γ = Γ } { A = A } { k =  k } ) with ⊢weaken {Γ = Γ , A} { k = #S k} ⊢e₁ 
  ... | p rewrite (sym (↑Σsymm {Σ = Σ} {k = k})) = ⊢lam₂ (⊢weaken ⊢e) p
  ⊢weaken (⊢sub ⊢e ¬□ gc s) = ⊢sub (⊢weaken ⊢e) (↑ΣnonEmpty ¬□) (↑tmGenCon gc) (≤weaken s)
  ⊢weaken (⊢tabs₁ ⊢e) = ⊢tabs₁ (⊢weaken ⊢e)
  ⊢weaken (⊢tapp ⊢e st) = ⊢tapp (⊢weaken ⊢e) st  

-- postulate
~weaken : ∀ {Γ : Env (1 + n) m} {Σ B j k}
  → Γ /ˣ k ⊢ ⟨ j , B ⟩ ~ Σ
  → Γ ⊢ ⟨ j , B ⟩ ~ ↑Σ k Σ 
~weaken ~Z = ~Z 
~weaken ~∞ = ~∞
~weaken (~S ⊢e ~) = ~S (⊢weaken ⊢e) (~weaken ~)

~weaken0 : ∀ {Γ : Env n m} {Σ A B j}
  → Γ ⊢ ⟨ j , B ⟩ ~ Σ
  → Γ , A ⊢ ⟨ j , B ⟩ ~ ↑Σ0 Σ
~weaken0 {Γ = Γ} {A = A} ~ = ~weaken {Γ = Γ , A} { k = #0 } ~

complete : ∀ {Γ : Env n m} {Σ j e A}
  → Γ ⊢ j # e ⦂ A
  → Γ ⊢ ⟨ j , A ⟩ ~ Σ
  → Γ ⊢ Σ ⇒ e ⇒ A

complete-≤ : ∀ {Γ : Env n m} {Σ j A}
--  → Γ ⊢m j # A
  → Γ ⊢ ⟨ j , A ⟩ ~ Σ
  → Γ ⊢ A ≤ Σ
  
complete-inf : ∀ {Γ : Env n m} {e A}
  → Γ ⊢ Z # e ⦂ A
  → Γ ⊢ □ ⇒ e ⇒ A
complete-inf ⊢e = complete ⊢e ~Z  

complete-chk : ∀ {Γ : Env n m} {e A}
  → Γ ⊢ ∞ # e ⦂ A
  → Γ ⊢ τ A ⇒ e ⇒ A
complete-chk ⊢e = complete ⊢e ~∞

complete ⊢lit ~Z = ⊢lit
complete (⊢var x) ~Z = ⊢var x
complete (⊢ann ⊢e) ~Z = ⊢ann (complete-chk ⊢e)
complete (⊢lam₁ ⊢e) ~∞ = ⊢lam₁ (complete-chk ⊢e)
complete (⊢lam₂ ⊢e) (~S ⊢e₁ j~Σ) = ⊢lam₂ ⊢e₁ (complete ⊢e (~weaken0 j~Σ))
complete (⊢app₁ ⊢e ⊢e₁) ~Z = ⊢app (subsumption0 (complete-inf ⊢e) (s-arr s-empty (complete-chk ⊢e₁)))
complete (⊢app₂ ⊢e ⊢e₁) j~Σ = ⊢app (complete ⊢e (~S (complete-inf ⊢e₁) j~Σ))
complete (⊢sub ⊢e j≢Z) j~Σ = subsumption0 (complete-inf ⊢e) (complete-≤ j~Σ)
complete (⊢tabs₁ ⊢e) ~Z = ⊢tabs₁ (complete-inf ⊢e)
complete (⊢tapp ⊢e st) j~Σ = ⊢tapp (subsumption0 (complete-inf ⊢e) (s-∀-t st (complete-≤ j~Σ))) st

complete-≤ ~Z = s-empty
complete-≤ ~∞ = s-refl
complete-≤ (~S ⊢e j~Σ) = s-arr (complete-≤ j~Σ) (subsumption0 ⊢e s-refl)
