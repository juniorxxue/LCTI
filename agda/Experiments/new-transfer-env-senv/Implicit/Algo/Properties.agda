module Implicit.Algo.Properties where

open import Implicit.Common
open import Implicit.Properties
open import Implicit.Algo

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
s-closed-gen (s-∀l-eq s st st1) with s-closed-gen s
... | evar-sol r = r
s-closed-gen (s-∀-t st s) = s-closed-gen s

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
  spl-weaken : ∀ {Σ : Context n m} {B Bs A' es T}
    → ⟦ Σ , B ⟧→⟦ es , τ T , Bs , A' ⟧
    → ⟦ ↑Σ0 Σ , B ⟧→⟦ up0 es , τ T , Bs , A' ⟧
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

-- structurally similar
infix 4 _≋_
data _≋_ : Type m → Type m' → Set where
  int : (Type m ∋⦂ Int) ≋ (Type m' ∋⦂ Int)
  var-l : ∀ {x : Fin m} {A : Type m'}
    → ‶ x ≋ A
  var-r : ∀ {A : Type m} {x : Fin m'}
    → A ≋ ‶ x
  arr : ∀ {A B : Type m} {C D : Type m'}
--    → A ≋ C
    → B ≋ D
    → A `→ B ≋ C `→ D
  `∀ : ∀ {A B : Type (1 + m)}
    → A ≋ B
    → `∀ A ≋ `∀ B

spl-≋ : ∀ {Σ : Context n m} {T As A' es B A}
  → ⟦ Σ , A ⟧→⟦ es , τ T , As , A' ⟧
  → A ≋ B
  → ∃[ Bs ] ∃[ B' ](⟦ ↑tyΣ0 Σ , B ⟧→⟦ upty0 es , τ ↑ty0 T , Bs , B' ⟧)
spl-≋ {B = B} none-τ A≋B = ⟨ nil , ⟨ B , none-τ ⟩ ⟩
spl-≋ (have-e spl) var-r = {!!}
spl-≋ (have-e spl) (arr A≋B) = {!!}
spl-≋ (have-t spl) A≋B = {!!}

-- issue: splitting doesn't preserve before subst

spl-pre-st : ∀ {Σ : Context n m} {T As A' es C B A}
  → ⟦ Σ , A ⟧→⟦ es , τ T , As , A' ⟧
  → [ C ]ˢ B ⇨ A
  → ∃[ Bs ] ∃[ B' ](⟦ ↑tyΣ0 Σ , B ⟧→⟦ upty0 es , τ ↑ty0 T , Bs , B' ⟧)
spl-pre-st {B = B} none-τ st = ⟨ nil , ⟨ B , none-τ ⟩ ⟩
spl-pre-st (have-e spl) st-var-eq with spl-pre-st spl st-var-eq
... | ⟨ Bs , ⟨ B' , pre-spl ⟩ ⟩ = {!!}
spl-pre-st {B = A `→ C} (have-e spl) (st-arr st st₁) = ⟨ A ∷a spl-pre-st spl st₁ .proj₁ ,
                                                        ⟨ spl-pre-st spl st₁ .proj₂ .proj₁ ,
                                                        have-e (spl-pre-st spl st₁ .proj₂ .proj₂) ⟩
                                                        ⟩
spl-pre-st (have-t spl) st = ⟨ spl-pre-st spl st .proj₁ ,
                              ⟨ spl-pre-st spl st .proj₂ .proj₁ ,
                              have-t (spl-pre-st spl st .proj₂ .proj₂) ⟩
                              ⟩

spl-st : ∀ {Σ : Context n m} {T As A' es C B A Bs B'}
  → ⟦ Σ , A ⟧→⟦ es , τ T , As , A' ⟧
  → [ C ]ˢ B ⇨ A
  → ⟦ ↑tyΣ0 Σ , B ⟧→⟦ upty0 es , τ ↑ty0 T , Bs , B' ⟧
  → [ C ]ˢ B' ⇨ A'
spl-st none-τ st none-τ = st
spl-st (have-e spl) (st-arr st st₁) (have-e pre-spl) = spl-st spl st₁ pre-spl
spl-st (have-t spl) st (have-t pre-spl) = spl-st spl st pre-spl
  

⊢id : ∀ {Γ : Env n m } {Σ e A A' T es As}
  → Γ ⊢ Σ ⇒ e ⇒ A
  → ⟦ Σ , A ⟧→⟦ es , τ T , As , A' ⟧
  → T ≡ A'

≤id : ∀ {Ψ Ψ' : SEnv n m} {Σ A B Bs B' es T}
  → Ψ ⊢ A ≤ Σ ⊣ Ψ' ↪ B
  → ⟦ Σ , B ⟧→⟦ es , τ T , Bs , B' ⟧
  → T ≡ B'
  
⊢id (⊢app ⊢e) spl = ⊢id ⊢e (have-e spl)
⊢id (⊢lam₁ ⊢e) none-τ rewrite ⊢id ⊢e none-τ = refl
⊢id (⊢lam₂ ⊢e ⊢e₁) (have-e spl) = ⊢id ⊢e₁ (spl-weaken spl)
⊢id (⊢sub ⊢e ne gc s) spl = ≤id s spl
⊢id (⊢tapp ⊢e) spl = ⊢id ⊢e (have-t spl)

≤id s-int none-τ = refl
≤id s-var none-τ = refl
≤id (s-ex-l^ clo x-in inst) none-τ = refl
≤id (s-ex-l= clo x-in s) none-τ = refl
≤id (s-ex-r^ clo x-in inst) none-τ = refl
≤id (s-ex-r= clo x-in s) none-τ = refl
≤id (s-arr s s₁) none-τ = refl
≤id (s-term-c cloA cloB ⊢e s) (have-e spl) = ≤id s spl
≤id (s-term-o op ⊢e s s₁) (have-e spl) = ≤id s₁ spl
≤id (s-∀ s) none-τ = cong `∀_ (≤id s none-τ)
≤id (s-∀l-^ s) (have-e spl) with ≤id s (have-e (spl-weaken-ty spl))
... | r = ↑ty-pred r
≤id (s-∀l-eq s st1 st2) spl'@(have-e spl) with spl-pre-st spl' (st-arr st1 st2)
... | ⟨ Bs' , ⟨ B' , pre-spl ⟩ ⟩ = helper (≤id s pre-spl) (spl-st (have-e spl) (st-arr st1 st2) pre-spl)
  where helper : ∀ {A : Type m}{B B' C}
               → ↑ty0 A ≡ B
               → [ C ]ˢ B ⇨ B'
               → A ≡ B'
        helper refl st = ↑ty-st st
≤id (s-∀-t st s) (have-t spl) = ≤id s spl -- solved by a workaround
