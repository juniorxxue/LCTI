module Implicit.CompleteIntermAlgo where

open import Implicit.Language.All
open import Implicit.Algo.All
open import Implicit.Temp.Interm

{- Proof

Case arrow :

Δ ⊢∞ C ≤ A        Δ ⊢∞ B ≤ D
---------------------------------------- S-Arr
Δ ⊢∞ A → B ≤ C → D

and we have

Γ ⊆ Ω w/t A
Ω ⊆ Δ w/t B  -- note that this Ω is picked by the destruction

our goal is (let's ignore the inference type for now)

Γ ⊢ A → B ≤ C → D ⊣ Δ

which has two subgoals

(1) Γ  ⊢ C ≤ A ⊣ ?Ω
(2) ?Ω ⊢ B ≤ D ⊣ Δ


by the i.h.

(1) Ω ⊢ B ≤ D ⊣ Δ
(2) ?       becasue from Δ ⊢∞ C ≤ A, we need a relation to determine input environment ?Γ
            the cause of this is also because in interm. systems, C ≤ A can see all the solution Δ (things solved in B ≤ D), we need to deal with this gap


if we use the i.h. (1), we determine the ?Ω by Ω picked by the system, we then need to prove that
the subgoal (1), Γ ⊢ C ≤ A ⊣ Ω, seems unideal to have

in other words, the destruction of Γ ⊆ Δ by A → B is not useful, we need to construct the middle env Ω we want,
say we have a function f,
  which first diffs the Γ and Δ (Δ has more solutiosn than Γ, those solutions appear in A and B)
  then diff the freevars in A and B, to find freevars only appear in B, then remove those freevars from the Δ, and get Ω⋆

we need to prove that
(1) Γ  ⊆ Ω⋆ w/t A
(2) Ω⋆ ⊆ Δ  w/t B

then let's use the i.h. again

(1) Ω⋆ ⊢ B ≤ D ⊣ Δ
(2) ?1 ⊢ C ≤ A ⊣ Δ if we have Δ ⊆ ?1 w/t A

the only subgoal left is Γ ⊢ C ≤ A ⊣ Ω⋆

compare two

we have: ?1 ⊢ C ≤ A ⊣ Δ     -- (s1)
goal is: Γ  ⊢ C ≤ A ⊣ Ω⋆    -- (s2)

we need a rebase property: moving from s1 to s2, by removing (transform solved into unsolved) unrelated entries

we want to have Ω⋆ ⊆ Δ w/t B, we need ?1 to satify the property diff(?1, Γ) ≡ diff(Δ, Ω⋆), in this way we can prove the subgoal.


Γ ⊢ A ≤ B ⊣ Δ
diff(Γ*, Γ) not in A & B
diff(Δ*, Δ) not in A & B
----------------------
Γ* ⊢ A ≤ B ⊣ Δ

-}

{- Case arrow 2

Δ ⊢∞ C ≤ A        Δ ⊢n B ≤ D
---------------------------------------- S-Arr2
Δ ⊢(I n) A → B ≤ C → D

we have

(1) Δ ⊢(I n) A → B ≤⁺ C → D
  (1.1) Δ ⊢∞ C ≤ A
  (1.2) Δ ⊢n B ≤ D

(2) Γ ⊆ Δ w/t A → B(n)
  (2.1) Γ ⊆ Ω w/t A
  (2.2) Ω ⊆ Δ w/t B(n)

(3) <(I n) , C ‵→ D> ~~ [e] → Σ
  (3.1) Γ ⊢ [] ⇒ e ⇒ C
  (3.2) <n, D> ~~ Σ

we need to prove

Γ ⊢ A → B ≤ [e] → Σ ⊣ Δ ↝ (C → D)'

⚠️ we need to have a case analysis

1️⃣ A is open under Γ

the subgoals are

(1) Γ ⊢ [] ⇒ e ⇒ C
(2) Γ ⊢ C ≤ A ⊣ ?1 ↝ _
(3) ?1 ⊢ B ≤ Σ ⊣ Δ ↝ D'

let's try the same step with algo

first we diff Δ and Γ, and diff A and B(n), we pick freevars only in B(n), and remove that from Δ
then we could have Ω⋆

👉 we shall prove that Ω⋆ ⊆ Δ w/t B(n) and Γ ⊆ Ω⋆ w/t A

👉 then by i.h. (Δ ⊢n B ≤ D, Ω⋆ ⊆ Δ w/t B(n), Ω⋆ ⊢ (n, D) ~~ Σ), we have Ω⋆ ⊢ B ≤ Σ ⊣ Δ ↝ D'

subgoal (2) can be proved by first construct ?1, and i.h. then proved by rebase properties by removing something not in A

2️⃣ A is closed under Γ

the the subgoals are

(1) Γ ⊢ A ⇒ e ⇒ ?
  (2) Γ ⊢ C ≤ A ⊣ Γ
(2) Γ ⊢ B ≤ Σ ⊣ Δ ↝ D'

-}

{- Case Arr3

Δ ⊢∞ A ≤ A        Δ ⊢n B ≤ D
---------------------------------------- S-Arr2
Δ ⊢(C n) A → B ≤ A → D

what we have

(1) Δ ⊢(C n) A → B ≤ A → D
  (1.1) Δ ⊢∞ A ≤ A
  (1.2) Δ ⊢n B ≤ D

(2) Γ ⊆ Δ w/t (A `→ B)(C n)
  (2.1) Γ ⊆ Δ w/t B(n)

(3) Γ ⊢ (A → B, C n) ~ [e] → Σ
  (3.1) Γ ⊢ A ⇒ e ⇒ A
  (3.2) Γ ⊢ (B, n) ~ Σ

our goal is to prove

Γ ⊢ A → B ≤ [e] → Σ ⊣ Δ ↝ (A → D)'

-}

infix 3 _⊢_≊_
data _⊢_≊_ : Env n m → Type m → Type m → Set where

  ≊-int : Γ ⊢ Int ≊ Int

  ≊-var∙ : Γ ∋∙ X
        → Γ ⊢ ‶ X ≊ ‶ X

  ≊-var= : Γ ∋= X
        → Γ ⊢ ‶ X ≊ ‶ X

  ≊-left : Γ ∋ X := A
         → Γ ⊢ ‶ X ≊ A

  ≊-right : Γ ∋ X := A
          → Γ ⊢ A ≊ ‶ X

  ≊-arr : Γ ⊢ A' ≊ A
        → Γ ⊢ B ≊ B'
        → Γ ⊢ A `→ B ≊ A' `→ B'

  ≊-∀ : Γ ,∙ ⊢ A ≊ B
      → Γ ⊢ `∀ A ≊ `∀ B

≊-refl : Γ ⊢c A
       → Γ ⊢ A ≊ A
≊-refl ⊢c-int = ≊-int
≊-refl (⊢c-var-∙ inΓ) = ≊-var∙ inΓ
≊-refl (⊢c-var-= inΓ) = ≊-var= inΓ
≊-refl (⊢c-arr cloA cloA₁) = ≊-arr (≊-refl cloA) (≊-refl cloA₁)
≊-refl (⊢c-∀ cloA) = ≊-∀ (≊-refl cloA)


infix 3 _⊢_~_
data _⊢_~_ : Env n m → Counter × Type m → Context n m → Set where

  ~Z : ∀ {Γ : Env n m} {A}
    → Γ ⊢ ⟨ Z , A ⟩ ~ □

  ~∞ : ∀ {Γ : Env n m} {A }
    → Γ ⊢ ⟨ ∞ , A ⟩ ~ τ A

  ~I : ∀ {Γ : Env n m} {j A B Σ e}
    → (⊢e : Γ ⊢ □ ⇒ e ⇒ A)
    → Γ ⊆ Ω w/t A
    → Ω ⊢ ⟨ j , B ⟩ ~ Σ
    → Γ ⊢ ⟨ 𝕚 j , A `→ B ⟩ ~ ([ e ]↝ Σ)

  ~C : ∀ {Γ : Env n m} {j A B Σ e}
    → (⊢e : Γ ⊢ τ A ⇒ e ⇒ A)
    → Γ ⊢ ⟨ j , B ⟩ ~ Σ
    → Γ ⊢ ⟨ 𝕔 j , A `→ B ⟩ ~ ([ e ]↝ Σ)

infix 3 _⊆_w/t_w/c_
data _⊆_w/t_w/c_ : Env n m → Env n m → Type m → Counter → Set where
  ⊆Z : Γ ⊆ Γ w/t A w/c Z
  ⊆∞ : Γ ⊆ Δ w/t A
     → Γ ⊆ Δ w/t A w/c ∞
  ⊆I : (ext : Γ ⊆ Ω w/t A)
     → Ω ⊆ Δ w/t B w/c j
     → Γ ⊆ Δ w/t (A `→ B) w/c (𝕚 j)
  ⊆C : Γ ⊆ Δ w/t B w/c j
     → Γ ⊆ Δ w/t (A `→ B) w/c (𝕔 j)
  ⊆∀-I : Γ ,∙ ⊆ Δ ,∙ w/t A w/c (𝕚 j)
     → Γ ⊆ Δ w/t `∀ A w/c (𝕚 j)
  ⊆∀-C : Γ ,∙ ⊆ Δ ,∙ w/t A w/c (𝕔 j)
     → Γ ⊆ Δ w/t `∀ A w/c (𝕔 j)


postulate
  open-close : ∀ (Γ : Env n m) A → Γ ⊢c A ⊎ Γ ⊢o A
  subsumption0 : Γ ⊢ □ ⇒ e ⇒ A
               → Γ ⊢ A ⌞ ≤⁻ ⌝ τ B ⊣ Γ ↪ B'
               → Γ ⊢c B
               → Γ ⊢ τ B ⇒ e ⇒ B'

{-

data SimSub (Γ : Env n m) (A : Type m) (Δ : Env n m) (B : Type m) (j : Counter) : Set where
  justss : ∀ {B' Σ}
    → Γ ⊢ ⟨ j , B ⟩ ~ Σ
    → (s : Γ ⊢ A ⌞ ≤⁺ ⌝ Σ ⊣ Δ ↪ B')
    → (sim : Γ ⊢ B' ≊ B)
    → SimSub Γ A Δ B j


complete-≤⁺ : Δ ⊢ j # A ⌞ ≤⁺ ⌝ B
            → Γ ⊆ Δ w/t A w/c j
            → SimSub Γ A Δ B j

complete-≤⁻ : Δ ⊢ ∞ # A ⌞ ≤⁻ ⌝ B
            → Γ ⊆ Δ w/t B
            → Γ ⊢ A ⌞ ≤⁻ ⌝ τ B ⊣ Δ ↪ B

complete-≤⁺ (s-refl cloΓ cloA) ext = {!!}
complete-≤⁺ (s-int cloΓ) ext = {!!}
complete-≤⁺ (s-var-∙ cloΓ inΓ) ext = {!!}
complete-≤⁺ (s-var-= cloΓ inΓ) ext = {!!}
complete-≤⁺ (s-arr₁ s s₁) ext = {!!}
complete-≤⁺ (s-arr₂ s s₁) ext = {!!}
complete-≤⁺ (s-arr₃ cloA s) ext = {!!}
complete-≤⁺ (s-∀ s) (⊆∞ (ext-∀ x)) with complete-≤⁺ s (⊆∞ x)
... | justss x₁ s₁ sim = justss ~∞ {!s-∀!} (≊-∀ sim)
complete-≤⁺ {Γ = Γ} (s-∀l s ic fd stC stD) ext with complete-≤⁺ {Γ = Γ ,^} s {!!}
... | justss (~I ⊢e x x₁) s₁ (≊-arr sim sim₁) = justss (~I {!!} {!!} {!!}) (s-∀l s₁ {!!} {!!} {!!} {!!}) {!!}
... | justss (~C ⊢e x) s₁ sim = justss {!!} (s-∀l {!!} {!!} {!!} {!!} {!!}) {!!}
complete-≤⁺ (s-var-l inΓ s) ext = {!!}
complete-≤⁺ (s-var-r inΓ s) ext = {!!}
-}

data SimSub (Γ : Env n m) (A : Type m) (Σ : Context n m) (Δ : Env n m) (B : Type m) : Set where
  justss : ∀ {B'}
    → (s : Γ ⊢ A ⌞ ≤⁺ ⌝ Σ ⊣ Δ ↪ B')
    → (sim : Γ ⊢ B' ≊ B)
    → SimSub Γ A Σ Δ B

complete-≤⁺ : Δ ⊢ j # A ⌞ ≤⁺ ⌝ B
            → Γ ⊆ Δ w/t A w/c j
            → Γ ⊢ ⟨ j , B ⟩ ~ Σ -- Σ is not uniquely determined by others
            → SimSub Γ A Σ Δ B

complete-≤⁻ : Δ ⊢ ∞ # A ⌞ ≤⁻ ⌝ B
            → Γ ⊆ Δ w/t B
            → Γ ⊢ A ⌞ ≤⁻ ⌝ τ B ⊣ Δ ↪ B

complete-≤⁺ (s-refl cloΓ cloA) ⊆Z ~Z = justss (s-empty cloA) (≊-refl cloA)
complete-≤⁺ (s-int cloΓ) (⊆∞ x) ~∞ with ⊆/-close-eq ⊢c-int x
... | refl = justss s-int ≊-int
complete-≤⁺ (s-var-∙ cloΓ inΓ) (⊆∞ x) ~∞ with ⊆/-close-eq (⊢c-var-∙ {!!}) x
... | r = {!!}
complete-≤⁺ (s-var-= cloΓ inΓ) (⊆∞ x) ~∞ = justss {!!} {!!}
complete-≤⁺ (s-arr₁ s s₁) ext j~Σ = {!!}
complete-≤⁺ {Γ = Γ} (s-arr₂ {A = A} s s₁) (⊆I x₁ ext) (~I ⊢e x j~Σ) with open-close Γ A
... | inj₁ cloA = justss (s-term-c (subsumption0 ⊢e (complete-≤⁻ {!!} {!!}) cloA) {!!}) {!!}
... | inj₂ opnA = {!!}
complete-≤⁺ (s-arr₃ cloA s) (⊆C ext) (~C ⊢e j~Σ) with complete-≤⁺ s ext j~Σ
... | justss s₁ sim = justss (s-term-c ⊢e s₁) (≊-arr (≊-refl (⊢closeA ⊢e)) sim)
complete-≤⁺ (s-∀ s) (⊆∞ (ext-∀ x)) ~∞ with complete-≤⁺ s (⊆∞ x) ~∞
... | justss s₁ sim = justss (s-∀ s₁) (≊-∀ sim)
complete-≤⁺ {Γ = Γ} (s-∀l s ic fd stC stD) ext j~Σ with complete-≤⁺ {Γ = Γ ,^} s {!!} {!!}
... | r = justss {!!} {!!}
complete-≤⁺ (s-var-l inΓ s) (⊆∞ (ext-var x)) ~∞ with complete-≤⁺ s {!!} ~∞
... | justss s₁ sim = justss (s-ex-l= {!!} s₁) {!!} -- requires extra thoughts
complete-≤⁺ (s-var-r inΓ s) ext j~Σ = {!!}

complete-≤⁻ s ext = {!!}


test : Γ ⊢ ⟨ j , C* `→ D* ⟩ ~ Σ
     → ↑tyᶜ0 Σ ⇘ Σ'
     → ⟦ B ⟧ C ⇘ C*
     → ⟦ B ⟧ D ⇘ D*
     → Γ ,^ ⊢ ⟨ j , C `→ D ⟩ ~ Σ'
test ~Z ↑tyᶜ-□ st1 st = ~Z
test ~∞ (↑tyᶜ-τ (↑ty-arr up-t up-t₁)) st1 st = {!!}
test (~I ⊢e x s) up st1 st = {!!}
test (~C ⊢e s) up st1 st = {!!}
