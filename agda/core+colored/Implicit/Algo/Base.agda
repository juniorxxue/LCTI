module Implicit.Algo.Base where

open import Implicit.Language.All

open import Implicit.Algo.Constructs.Syntax public
open import Implicit.Algo.Constructs.Shift public
open import Implicit.Algo.Constructs.Subst public
open import Implicit.Algo.Constructs.Lookup public

infix 3 _⊢_⌞_⌝_⊣_
data _⊢_⌞_⌝_⊣_ : Env n m → Type m → Polar → Type m → Env n m → Set where
  s-int :
      (regΓ : SRegular Δ)
    → Δ ⊢ Int ⌞ ≤ ⌝ Int ⊣ Δ

  s-var-∙ :
      (regΓ : SRegular Δ)
    → Δ ∋∙ X
    → Δ ⊢ (‶ X) ⌞ ≤ ⌝ (‶ X) ⊣ Δ

  s-ex-l^ :
--      (x-in : Δ ∋^ X)
--    → (regA : Δ ⊢r A)
      (inst : [ A / X ] Δ ⟹ Ψ)
    → Δ ⊢ ‶ X ⌞ ≤⁺ ⌝ A ⊣ Ψ

  s-ex-r^ :
--      (x-in : Δ ∋^ X) -- implied by inst
--    → (regA : Γ ⊢r A) -- implied by the inst
      (inst : [ A / X ] Δ ⟹ Ψ)
    → Δ ⊢ A ⌞ ≤⁻ ⌝ (‶ X) ⊣ Ψ

  s-ex-l= :
      (regΓ : SRegular Δ)
    → (x-in : Δ ∋ X := A)
    → Δ ⊢ ‶ X ⌞ ≤⁺ ⌝ A ⊣ Δ

  s-ex-r= :
      (regΓ : SRegular Δ)
    → (x-in : Δ ∋ X := A)
    → Δ ⊢ A ⌞ ≤⁻ ⌝ (‶ X) ⊣ Δ

  s-arr :
      Δ ⊢ C ⌞ ⋆ ≤ ⌝ A ⊣ Ω
    → Ω ⊢ B ⌞ ≤ ⌝ D ⊣ Ψ
    → Δ ⊢ A `→ B ⌞ ≤ ⌝ (C `→ D) ⊣ Ψ

  s-∀ :
      Δ ,∙ ⊢ A ⌞ ≤ ⌝ B ⊣ Ψ ,∙
    → Δ ⊢ `∀ A ⌞ ≤ ⌝ (`∀ B) ⊣ Ψ

infix 3 _⊢_⇒_⇒_
infix 3 _⊢_≤⁺_⊣_↪_

data _⊢_⇒_⇒_ : Env n m → Context n m → Term n m → Type m → Set
data _⊢_≤⁺_⊣_↪_ : Env n m → Type m → Context n m → Env n m → Type m → Set

data _⊢_⇒_⇒_ where

  ⊢lit : ∀ {num : ℕ}
    → (regΓ : TRegular Γ)
    → Γ ⊢ `□ ⇒ lit num ⇒ Int

  ⊢var :
      (regΓ : TRegular Γ)
    → (x∈Γ : Γ ∋ x ⦂ A)
    → Γ ⊢ `□ ⇒ ` x ⇒ A

  ⊢ann :
      Γ ⊢ `τ A ⇒ e ⇒ B
    → Γ ⊢ `□ ⇒ e ⦂ A ⇒ A

  ⊢app :
      Γ ⊢ [ e₂ ]↝ Σ ⇒ e₁ ⇒ A `→ B
    → Γ ⊢ Σ ⇒ e₁ · e₂ ⇒ B

  ⊢lam₁ :
      Γ , A ⊢ `τ B ⇒ e ⇒ C
    → Γ ⊢ `τ (A `→ B) ⇒ ƛ e ⇒ A `→ C

  ⊢lam₂ :
      Γ ⊢ `□ ⇒ e₂ ⇒ A
    → (up-c : ↑tmᶜ0 Σ ⇘ Σ')
    → Γ , A ⊢ Σ' ⇒ e ⇒ B
    → Γ ⊢ [ e₂ ]↝ Σ ⇒ ƛ e ⇒ A `→ B

  ⊢lam₃ :
      Γ , A ⊢ `p P ⇒ e ⇒ B
    → Γ ⊢ A `◐↝ P ⇒ ƛ e ⇒ A `→ B

  ⊢sub :
      Γ ⊢ `□ ⇒ g ⇒ A
    → (ne : NonEmpty Σ)
    → (gc : GenericConsumer g)
    → (s : Γ ⋈ ⊢ A ≤⁺ Σ ⊣ Γ ⋈ ↪ B)
    → Γ ⊢ Σ ⇒ g ⇒ B

  ⊢tabs :
      Γ ,∙ ⊢ `□ ⇒ e ⇒ A
    → Γ ⊢ `□ ⇒ Λ e ⇒ `∀ A

  ⊢tapp :
      Γ ⊢ A ⓪↝ Σ ⇒ e ⇒ `∀ B
    → (st : ⟦ A ⟧ B ⇘ B*)
    → Γ ⊢ Σ ⇒ e ⓪ A ⇒ B*

data _⊢_≤⁺_⊣_↪_ where

  s-empty :
      (regΓ : SRegular Δ)
    → (cloA : Δ ⊢c A)
    → (grd : Δ ≫ A ⇘ A%)
    → Δ ⊢ A ≤⁺ `□ ⊣ Δ ↪ A%

  s-type :
      (ss : Δ ⊢ A ⌞ ≤⁺ ⌝ B ⊣ Ψ)
    → Δ ⊢ A ≤⁺ (`τ B) ⊣ Ψ ↪ B

  s-term-c :
      (cloA : Δ ⊢c A)
    → (ap : Δ ≫ A ⇘ A%)
    → (⊢e : 𝕣 Δ ⊢ `τ A% ⇒ e ⇒ A')
    → Δ ⊢ B ≤⁺ Σ ⊣ Ψ ↪ D
    → Δ ⊢ (A `→ B) ≤⁺ ([ e ]↝ Σ) ⊣ Ψ ↪ A% `→ D

  s-term-o :
      (opnA : Δ ⊢o A)
    → (conv : Δ ⊢ A ↦₁ P)
    → (⊢e : 𝕣 Δ ⊢ `p P ⇒ e ⇒ C)
    → (ss : Δ ⊢ C ⌞ ≤⁻ ⌝ A ⊣ Ω)
    → Ω ⊢ B ≤⁺ Σ ⊣ Ψ ↪ D
    → Δ ⊢ A `→ B ≤⁺ ([ e ]↝ Σ) ⊣ Ψ ↪ C `→ D

  s-term-p :
     (ss : Δ ⊢ C ⌞ ≤⁻ ⌝ A ⊣ Ω)
    → Ω ⊢ B ≤⁺ `p P ⊣ Ψ ↪ D
    → Δ ⊢ A `→ B ≤⁺ (C `◐↝ P) ⊣ Ψ ↪ C `→ D

  s-∀l :
      Δ ,^ ⊢ A ≤⁺ ([ e' ]↝ Σ') ⊣ Ψ ,= B ↪ (C' `→ D')
    → (upᶜ : ↑tyᶜ0 Σ ⇘ Σ')
    → (upᵉ : ↑tyᵉ0 e ⇘ e')
    → (upC : ↑ty0 C ⇘ C')
    → (upD : ↑ty0 D ⇘ D')
    → Δ ⊢ `∀ A ≤⁺ ([ e ]↝ Σ) ⊣ Ψ ↪ C `→ D

  s-tapp :
      Δ ,= B ⊢ A ≤⁺ Σ' ⊣ Ψ ,= B ↪ C
    → (upᶜ : ↑tyᶜ0 Σ ⇘ Σ')
    → Δ ⊢ `∀ A ≤⁺ (B ⓪↝ Σ) ⊣ Ψ ↪ `∀ C


data AMatch1 : Type m → ParType m → Set where
  amt1-z : AMatch1 A □
  amt1-s : AMatch1 B P
        → AMatch1 (A `→ B) (A ◐↝ P)

data AMatch2 : Type m → EContext m → Set where
  amt2-p : AMatch1 A P
         → AMatch2 A (p P)
  amt2-τ : AMatch2 A (τ A)

data AMatch : Type m → Context n m → Set where
  amt-𝔼 : AMatch2 A δ
        → AMatch A (Context n m ∋⦂ (𝔼 δ))
  amt-term : AMatch B Σ
           → AMatch (A `→ B) ([ e ]↝ Σ)
  amt-tapp : AMatch A* Σ
           → (st : ⟦ B ⟧ A ⇘ A*)
           → AMatch (`∀ A) (B ⓪↝ Σ)

postulate
  t-amatch : Γ ⊢ Σ ⇒ e ⇒ A
         → AMatch A Σ

  s-amatch : Γ ⊢ A ≤⁺ Σ ⊣ Ψ ↪ B
         → AMatch B Σ

{-
s-amatch (s-empty regΓ cloA grd) = amt-𝔼 (amt2-p amt1-z)
s-amatch (s-type ss) = amt-𝔼 amt2-τ
s-amatch (s-term-c cloA ap ⊢e s) = amt-term (s-amatch s)
s-amatch (s-term-o opnA conv ⊢e ss s) = amt-term (s-amatch s)
s-amatch (s-term-p ss s) with s-amatch s
... | amt-𝔼 (amt2-p x) = amt-𝔼 (amt2-p (amt1-s x))
s-amatch (s-∀l s upᶜ upᵉ upC upD) with s-amatch s
... | amt-term r = amt-term {!!}
s-amatch (s-tapp s upᶜ) with s-amatch s
... | r = amt-tapp {!!} {!!}

t-amatch (⊢lit regΓ) = amt-𝔼 (amt2-p amt1-z)
t-amatch (⊢var regΓ x∈Γ) = amt-𝔼 (amt2-p amt1-z)
t-amatch (⊢ann ⊢e) = amt-𝔼 (amt2-p amt1-z)
t-amatch (⊢app ⊢e) with t-amatch ⊢e
... | amt-term r = r
t-amatch (⊢lam₁ ⊢e) with t-amatch ⊢e
... | amt-𝔼 amt2-τ = amt-𝔼 amt2-τ
t-amatch (⊢lam₂ ⊢e up-c ⊢e₁) with t-amatch ⊢e
... | amt-𝔼 (amt2-p amt1-z) = amt-term {!!}
t-amatch (⊢lam₃ ⊢e) with t-amatch ⊢e
... | amt-𝔼 (amt2-p mt) = amt-𝔼 (amt2-p (amt1-s mt))
t-amatch (⊢sub ⊢e ne gc s) = s-amatch s
t-amatch (⊢tabs ⊢e) = amt-𝔼 (amt2-p amt1-z)
t-amatch (⊢tapp ⊢e st) with t-amatch ⊢e
... | amt-tapp r st₁ = {!!}
-}


_ : ∅ , `∀ ((Int `→ ‶ #0) `→ ‶ #0) ⊢ `□ ⇒ (` #0 · (ƛ ` #0)) ⇒ Int
_ = ⊢app (⊢sub (⊢var
                 (reg-S, reg-Z
                  (⊢r-∀ (⊢r-arr (⊢r-arr ⊢r-int (⊢r-var-∙ Z)) (⊢r-var-∙ Z))))
                 Z) ne-app gc-var
                 (s-∀l {B = Int} {C = Int `→ Int} {D = Int}
                 (s-term-o (⊢o-arr-r (⊢o-var-^ Z))
                 (tf-arr ⊢c-int grd-int tf-tvar)
                 (⊢lam₃
                   (⊢var
                    (reg-S,
                     (reg-S^
                      (reg-S, reg-Z
                       (⊢r-∀ (⊢r-arr (⊢r-arr ⊢r-int (⊢r-var-∙ Z)) (⊢r-var-∙ Z)))))
                     ⊢r-int)
                    Z))
                 (s-arr (s-int
                          (reg-S^
                           (reg-Z
                            (reg-S, reg-Z
                             (⊢r-∀ (⊢r-arr (⊢r-arr ⊢r-int (⊢r-var-∙ Z)) (⊢r-var-∙ Z))))))) (s-ex-r^
                                                                                             (⟹^0 ↑ty-int ⊢r-int
                                                                                              (reg-Z
                                                                                               (reg-S, reg-Z
                                                                                                (⊢r-∀ (⊢r-arr (⊢r-arr ⊢r-int (⊢r-var-∙ Z)) (⊢r-var-∙ Z))))))))
                 (s-empty
                   (reg-S=
                    (reg-Z
                     (reg-S, reg-Z
                      (⊢r-∀ (⊢r-arr (⊢r-arr ⊢r-int (⊢r-var-∙ Z)) (⊢r-var-∙ Z)))))
                    ⊢r-int)
                   (⊢c-var-= Z) (grd-var= (Z ↑ty-int))))
                 (↑tyᶜ-𝔼 (↑tyᴱ-p ↑tyᵖ-nil)) (↑tyᵉ-ƛ ↑tyᵉ-var) (↑ty-arr ↑ty-int ↑ty-int) ↑ty-int))
