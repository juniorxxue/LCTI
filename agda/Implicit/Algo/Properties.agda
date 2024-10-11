module Implicit.Algo.Properties where

open import Implicit.Common
open import Implicit.Properties
open import Implicit.Algo

⊢c-arr-inv-l : ∀ {Ψ : SEnv n m} {A B}
  → Ψ ⊢c (A `→ B)
  → Ψ ⊢c A
⊢c-arr-inv-l (⊢c-arr s s₁) = s

⊢c-arr-inv-r : ∀ {Ψ : SEnv n m} {A B}
  → Ψ ⊢c (A `→ B)
  → Ψ ⊢c B
⊢c-arr-inv-r (⊢c-arr s s₁) = s₁

postulate
  ⊢c-∀-= : ∀ {Ψ : SEnv n m} {A B}
    → Ψ ⊢c `∀ B
    → Ψ ,= A ⊢c B -- requires a lemma: if a universal varialbe in a context, you can replace it with a solution without affecting it's closedness


↑tyΣ-st : ∀ (Σ : Context n m) {A}
  → [ A ]ᶜ (↑tyΣ0 Σ) ≡ Σ
↑tyΣ-st □ = refl
↑tyΣ-st (τ B) {A = A} rewrite ↑ty-st' B {C = A} = refl
↑tyΣ-st ([ e ]↝ Σ) {A = A} rewrite ↑ty-tm-st' e {C = A} | ↑tyΣ-st Σ {A = A} = refl


-- open import Relation.Binary.PropositionalEquality.≡-Reasoning
-- why does it not work?

data Γ-like : SEnv n m → Set where
  Z : Γ-like ∅
  S, : ∀ {Ψ : SEnv n m} {A}
    → Γ-like Ψ
    → Γ-like (Ψ , A)
  S∙ : ∀ {Ψ : SEnv n m}
    → Γ-like Ψ
    → Γ-like (Ψ ,∙)
  S= : ∀ {Ψ : SEnv n m} {A}
    → Γ-like Ψ
    → Γ-like (Ψ ,= A)


infix 3 _~~_
data _~~_ : SEnv n m → SEnv n m → Set where
  base : ∅ ~~ ∅
  uvar : ∀ {Ψ Ψ' : SEnv n m}
    → Ψ ~~ Ψ'
    → Ψ ,∙ ~~ Ψ' ,∙
  var : ∀ {Ψ Ψ' : SEnv n m} {A}
    → Ψ ~~ Ψ'
    → Ψ , A ~~ Ψ' , A
  evar : ∀ {Ψ Ψ' : SEnv n m}
    → Ψ ~~ Ψ'
    → Ψ ,^ ~~ Ψ' ,^
  evar-sol : ∀ {Ψ Ψ' : SEnv n m} {A}
    → Ψ ~~ Ψ'
    → Ψ ,^ ~~ Ψ' ,= A    
  svar : ∀ {Ψ Ψ' : SEnv n m} {A}
    → Ψ ~~ Ψ'
    → Ψ ,= A ~~ Ψ' ,= A


~~Γ-like : ∀ {Ψ Ψ' : SEnv n m}
  → Γ-like Ψ
  → Ψ ~~ Ψ'
  → Ψ ≡ Ψ'
~~Γ-like gl base = refl
~~Γ-like (S∙ gl) (uvar ~~Ψ) rewrite ~~Γ-like gl ~~Ψ = refl
~~Γ-like (S, gl) (var ~~Ψ) rewrite ~~Γ-like gl ~~Ψ = refl
~~Γ-like (S= gl) (svar ~~Ψ) rewrite ~~Γ-like gl ~~Ψ = refl

~~refl : ∀ {n m} {Ψ : SEnv n m}
  → Ψ ~~ Ψ
~~refl {Ψ = ∅} = base
~~refl {Ψ = Ψ , A} = var ~~refl
~~refl {Ψ = Ψ ,∙} = uvar ~~refl
~~refl {Ψ = Ψ ,^} = evar ~~refl
~~refl {Ψ = Ψ ,= A} = svar ~~refl

~~trans : ∀ {n m} {Ψ Ψ' Ψ'' : SEnv n m}
  → Ψ ~~ Ψ'
  → Ψ' ~~ Ψ''
  → Ψ ~~ Ψ''
~~trans base base = base
~~trans (uvar ~~1) (uvar ~~2) = uvar (~~trans ~~1 ~~2)
~~trans (var ~~1) (var ~~2) = var (~~trans ~~1 ~~2)
~~trans (evar ~~1) (evar ~~2) = evar (~~trans ~~1 ~~2)
~~trans (evar ~~1) (evar-sol ~~2) = evar-sol (~~trans ~~1 ~~2)
~~trans (evar-sol ~~1) (svar ~~2) = evar-sol (~~trans ~~1 ~~2)
~~trans (svar ~~1) (svar ~~2) = svar (~~trans ~~1 ~~2)

⟹closed : ∀ {Ψ Ψ' : SEnv n m} {A X} 
  → [ A / X ] Ψ ⟹ Ψ'
  → Ψ ~~ Ψ'
⟹closed ⟹^0 = evar-sol ~~refl
⟹closed (⟹,S s) = var (⟹closed s)
⟹closed (⟹^S s) = evar (⟹closed s)
⟹closed (⟹∙S s) = uvar (⟹closed s)
⟹closed (⟹=S s) = svar (⟹closed s)  

s-closed-gen : ∀ {Ψ Ψ' : SEnv n m} {A B Σ}
  → Ψ ⊢ A ≤ Σ ⊣ Ψ' ↪ B
  → Ψ ~~ Ψ'
s-closed-gen s-int = ~~refl
s-closed-gen (s-empty p) = ~~refl
s-closed-gen s-var = ~~refl
s-closed-gen (s-ex-l^ x x₁ x₂) = ⟹closed x₂
s-closed-gen (s-ex-l= x x₁ s) = s-closed-gen s
s-closed-gen (s-ex-r^ x x₁ x₂) = ⟹closed x₂
s-closed-gen (s-ex-r= x x₁ s) = s-closed-gen s
s-closed-gen (s-arr s s₁) = ~~trans (s-closed-gen s) (s-closed-gen s₁)
s-closed-gen (s-term-c x x₁ x₂ s) = s-closed-gen s
s-closed-gen (s-term-o x x₁ s s₁) = ~~trans (s-closed-gen s) (s-closed-gen s₁)
s-closed-gen (s-∀ s) with s-closed-gen s
... | uvar r = r
s-closed-gen (s-∀l-^ s) with s-closed-gen s
... | evar r = r
s-closed-gen (s-∀l-eq s st st') with s-closed-gen s
... | evar-sol r = r

𝕎-Γ-like : ∀ (Γ : Env n m)
  → Γ-like (𝕎 Γ)
𝕎-Γ-like ∅ = Z
𝕎-Γ-like (Γ , A) = S, (𝕎-Γ-like Γ)
𝕎-Γ-like (Γ ,∙) = S∙ (𝕎-Γ-like Γ)
𝕎-Γ-like (Γ ,= A) = S= (𝕎-Γ-like Γ)
  
s-closed : ∀ {Ψ : SEnv n m} {Γ A B Σ}
  → 𝕎 Γ ⊢ A ≤ Σ ⊣ Ψ ↪ B
  → Ψ ≡ 𝕎 Γ
s-closed {Γ = Γ} s with s-closed-gen s
... | r = sym (~~Γ-like (𝕎-Γ-like Γ) r)

----------------------------------------------------------------------
--+                   when context is full type                    +--
----------------------------------------------------------------------

postulate
  spl-weaken-ty : ∀ {Σ : Context n m} {B Bs A' es T}
    → ⟦ Σ , B ⟧→⟦ es , τ T , Bs , A' ⟧
    → ⟦ ↑tyΣ0 Σ , ↑ty0 B ⟧→⟦ upty0 es , τ ↑ty0 T , uptyT0 Bs , ↑ty0 A' ⟧

#S-pred : ∀ {x y : Fin m}
  → #S x ≡ #S y
  → x ≡ y
#S-pred refl = refl

tvar-pred : ∀ {x y : Fin m}
  → ‶ x ≡ ‶ y
  → x ≡ y
tvar-pred refl = refl

punchIn-pred : ∀ {k : Fin (1 + m)} {x y}
  → punchIn k x ≡ punchIn k y
  → x ≡ y
punchIn-pred {k = #0} {x = x} {.x} refl = refl
punchIn-pred {k = #S k} {x = #0} {#0} eq = refl
punchIn-pred {k = #S k} {x = #S x} {#S y} eq = cong #S (punchIn-pred (#S-pred eq))

arr-pred : ∀ {A B C D : Type m}
  → A `→ B ≡ C `→ D
  → A ≡ C × B ≡ D
arr-pred refl = ⟨ refl , refl ⟩

∀-pred : ∀ {A B : Type (1 + m)}
  → `∀ A ≡ `∀ B
  → A ≡ B
∀-pred refl = refl  
    
↑ty-pred : ∀ {k : Fin (1 + m)} {A B}
  → ↑ty k A ≡ ↑ty k B
  → A ≡ B
↑ty-pred {A = Int} {Int} eq = refl
↑ty-pred {A = ‶ X} {‶ Y} eq = cong ‶_ (punchIn-pred (tvar-pred eq))
↑ty-pred {A = A `→ A₁} {B `→ B₁} eq with arr-pred eq
... | ⟨ eq1 , eq2 ⟩ rewrite ↑ty-pred {A = A} {B} eq1 | ↑ty-pred {A = A₁} {B₁} eq2 = refl
↑ty-pred {A = `∀ A} {`∀ B} eq = cong `∀_ (↑ty-pred (∀-pred eq))

data Split : (Σ : Context n m) → (B : Type m) → Set where
  case-τ : ∀ {Σ : Context n m} {B T B'}
    → (spl : ⟦ Σ , B ⟧→s⟦ τ T , B' ⟧)
    → (eq : T ≡ B')
    → Split Σ B
    
  case-□ : ∀ {Σ : Context n m} {B B'}
    → (spl : ⟦ Σ , B ⟧→s⟦ □ , B' ⟧)
    → Split Σ B

spl-deterministic : ∀ {Σ : Context n m} {A A₁ A₂ Σ₁ Σ₂}
  → ⟦ Σ , A ⟧→s⟦ Σ₁ ,  A₁ ⟧
  → ⟦ Σ , A ⟧→s⟦ Σ₂ ,  A₂ ⟧
  → Σ₁ ≡ Σ₂ × A₁ ≡ A₂
spl-deterministic none-□ none-□ = ⟨ refl , refl ⟩  
spl-deterministic none-τ none-τ = ⟨ refl , refl ⟩
spl-deterministic (have-e spl1) (have-e spl2) = spl-deterministic spl1 spl2

spl-↑ty : ∀ {Σ : Context n (1 + m)} {B Σ' A C}
  → ⟦ Σ , B ⟧→s⟦ Σ' , A ⟧
  → ⟦ [ C ]ᶜ Σ , [ C ]ˢ B ⟧→s⟦ [ C ]ᶜ Σ' , [ C ]ˢ A ⟧
spl-↑ty none-□ = none-□  
spl-↑ty none-τ = none-τ
spl-↑ty (have-e spl) = have-e (spl-↑ty spl)

spl-↑ty-case : ∀ {Σ : Context n m} {Σ' e B T C}
  → ⟦ ↑tyΣ0 ([ e ]↝ Σ) , ↑ty #0 B ⟧→s⟦ Σ' , T ⟧
  → ⟦ [ e ]↝ Σ , B ⟧→s⟦ [ C ]ᶜ Σ' , [ C ]ˢ T ⟧
spl-↑ty-case {Σ = Σ} {e = e} {B = B} {C = C} spl with spl-↑ty {C = C} spl
... | spl' rewrite ↑ty-st' B {C = C} | ↑tyΣ-st ([ e ]↝ Σ) {A = C} = spl'

spl-↑ty-case' : ∀ {Σ : Context n m} {Σ' e B T C}
  → ⟦ ↑tyΣ0 ([ e ]↝ Σ) , B ⟧→s⟦ Σ' , T ⟧
  → ⟦ [ e ]↝ Σ , [ C ]ˢ B ⟧→s⟦ [ C ]ᶜ Σ' , [ C ]ˢ T ⟧
spl-↑ty-case' {Σ = Σ} {e = e} {B = B} {C = C} spl with spl-↑ty {C = C} spl
... | spl' rewrite ↑tyΣ-st ([ e ]↝ Σ) {A = C} = spl'

spl-implies-simple : ∀ {Σ Σ' : Context n m} {es A As A'}
  → ⟦ Σ , A ⟧→⟦ es , Σ' , As , A' ⟧
  → ⟦ Σ , A ⟧→s⟦ Σ' , A' ⟧
spl-implies-simple none-□ = none-□
spl-implies-simple none-τ = none-τ
spl-implies-simple (have-e spl) = have-e (spl-implies-simple spl)

spl-weaken : ∀ {Σ Σ' : Context n m} {A es As A' k}
  → ⟦ Σ , A ⟧→⟦ es , Σ' , As , A' ⟧
  → ⟦ ↑Σ k Σ , A ⟧→⟦ up k es , ↑Σ k Σ' , As , A' ⟧
spl-weaken none-□ = none-□
spl-weaken none-τ = none-τ
spl-weaken (have-e spl) = have-e (spl-weaken spl)
  
⊢id : ∀ {Γ : Env n m } {Σ e A A' T es As}
  → Γ ⊢ Σ ⇒ e ⇒ A
  → ⟦ Σ , A ⟧→⟦ es , τ T , As , A' ⟧
  → T ≡ A'

≤id : ∀ {Ψ Ψ' : SEnv n m} {Σ A B}
  → Ψ ⊢ A ≤ Σ ⊣ Ψ' ↪ B
  → Split Σ B

≤id' : ∀ {Ψ Ψ' : SEnv n m} {Σ A B T B'}
  → Ψ ⊢ A ≤ Σ ⊣ Ψ' ↪ B
  → ⟦ Σ , B ⟧→s⟦ τ T , B' ⟧
  → T ≡ B'
≤id' s spl with ≤id s
... | case-τ spl' refl with spl-deterministic spl spl'
... | ⟨ refl , refl ⟩ = refl
≤id' s spl | case-□ spl' with spl-deterministic spl spl'
... | ()

⊢id (⊢app ⊢e) spl = ⊢id ⊢e (have-e spl)
⊢id (⊢lam₁ ⊢e) none-τ rewrite ⊢id ⊢e none-τ = refl
⊢id (⊢lam₂ ⊢e ⊢e₁) (have-e spl) = ⊢id ⊢e₁ (spl-weaken spl)
⊢id (⊢sub ⊢e ne gc s) spl = ≤id' s (spl-implies-simple spl)

≤id s-int = case-τ none-τ refl
≤id (s-empty p) = case-□ none-□
≤id s-var = case-τ none-τ refl
≤id (s-ex-l^ clo x-in inst) = case-τ none-τ refl
≤id (s-ex-l= clo x-in s) = case-τ none-τ refl
≤id (s-ex-r^ clo x-in inst) = case-τ none-τ refl
≤id (s-ex-r= clo x-in s) = case-τ none-τ refl
≤id (s-arr s s₁) = case-τ none-τ refl
≤id (s-term-c cloA cloB ⊢e s) with ≤id s
... | case-τ spl eq = case-τ (have-e spl) eq
... | case-□ spl = case-□ (have-e spl)
≤id (s-term-o op ⊢e s s₁) with ≤id s₁
... | case-τ spl eq = case-τ (have-e spl) eq
... | case-□ spl = case-□ (have-e spl)
≤id (s-∀ s) with ≤id s
... | case-τ none-τ refl = case-τ none-τ refl
≤id (s-∀l-^ s) with ≤id s
... | case-τ spl refl = case-τ (spl-↑ty-case {C = Int} spl) refl
... | case-□ spl = case-□ (spl-↑ty-case {C = Int} spl)
≤id (s-∀l-eq {B = B} s st₁ st₂) with ≤id s
... | case-τ spl refl rewrite sym (st-st st₁) | sym (st-st st₂) = case-τ (spl-↑ty-case' {C = B} spl) refl
... | case-□ spl rewrite sym (st-st st₁) | sym (st-st st₂) = case-□ (spl-↑ty-case' {C = B} spl)


-- corollaries
⊢id0 : ∀ {Γ : Env n m} {e A B}
  → Γ ⊢ τ B ⇒ e ⇒ A
  → B ≡ A
⊢id0 ⊢e = ⊢id ⊢e none-τ

≤id0 : ∀ {Ψ Ψ' : SEnv n m} {A B C}
  → Ψ ⊢ A ≤ τ B ⊣ Ψ' ↪ C
  → B ≡ C
≤id0 s = ≤id' s none-τ  

-- aux lemmas

⊢id0-h : ∀ {Γ : Env n m} {e A B}
  → Γ ⊢ τ B ⇒ e ⇒ A
  → Γ ⊢ τ A ⇒ e ⇒ A
⊢id0-h ⊢e with ⊢id0 ⊢e
... | refl = ⊢e
