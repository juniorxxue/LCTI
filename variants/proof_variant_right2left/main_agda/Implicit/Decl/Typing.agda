module Implicit.Decl.Typing where

open import Implicit.Language.All
open import Implicit.Decl.Subtyping

----------------------------------------------------------------------
--+                             Typing                             +--
----------------------------------------------------------------------

infix 3 _⊢_#_⦂_
data _⊢_#_⦂_ : Env n m → Counter m → Term n m → Type m → Set where
  ⊢lit : ∀ {num : ℕ}
    → (regΓ : TRegular Γ)
    → Γ ⊢ Z # (lit num) ⦂ Int
  ⊢var :
      (regΓ : TRegular Γ)
    → (x∈Γ : Γ ∋ x ⦂ A)
    → Γ ⊢ Z # ` x ⦂ A
  ⊢ann :
      Γ ⊢ ∞ # e ⦂ A
    → Γ ⊢ Z # (e ⦂ A) ⦂ A
  ⊢lam₁ :
      Γ , A ⊢ ∞ # e ⦂ B
    → Γ ⊢ ∞ # ƛ e ⦂ A `→ B
  ⊢lam₂ :
      Γ , A ⊢ j # e ⦂ B
    → Γ ⊢ 𝕚 j # ƛ e ⦂ A `→ B
  ⊢app₁ :
      Γ ⊢ 𝕔 j # e₁ ⦂ A `→ B
    → Γ ⊢ ∞ # e₂ ⦂ A
    → Γ ⊢ j # e₁ · e₂ ⦂ B
  ⊢app₂ :
      Γ ⊢ 𝕚 j # e₁ ⦂ A `→ B
    → Γ ⊢ Z # e₂ ⦂ A
    → Γ ⊢ j # e₁ · e₂ ⦂ B
  ⊢sub :
      Γ ⊢ Z # g ⦂ A
    → (B≤A : Γ ⋈ ⊢ j # A ≤ B)
    → (gc : GenericConsumer g)
    → (j≢Z : NonZ j)
    → Γ ⊢ j # g ⦂ B
  ⊢tabs :
      Γ ,∙ ⊢ Z # e ⦂ A
    → Γ ⊢ Z # Λ e ⦂ `∀ A
  ⊢tapp :
      Γ ⊢ 𝕥₍ A ₎ j # e ⦂ `∀ B
    → (st : ⟦ A ⟧ B ⇘ B*)
    → Γ ⊢ j # e ⓪ A ⦂ B*



s-sregular : Γ ⊢ j # A ≤ B
           → SRegular Γ
s-sregular (s-refl regΔ cloA) = regΔ
s-sregular (s-int regΔ) = regΔ
s-sregular (s-var-∙ regΔ inΔ) = regΔ
s-sregular (s-arr₁ s s₁) = s-sregular s
s-sregular (s-arr₂ s s₁) = s-sregular s
s-sregular (s-arr₃ regA s) = s-sregular s
s-sregular (s-∀ s) with s-sregular s
... | reg-S∙ r = r
s-sregular (s-∀l regB st s ic fd upj) = s-sregular s
s-sregular (s-tapp regB st s upC) = s-sregular s
s-sregular (s-∀l-no-appear regB st x ic fd) = s-sregular x

t-tregular : Γ ⊢ j # e ⦂ A
           → TRegular Γ
t-tregular (⊢lit regΓ) = regΓ
t-tregular (⊢var regΓ x∈Γ) = regΓ
t-tregular (⊢ann ⊢e) = t-tregular ⊢e
t-tregular (⊢lam₁ ⊢e) with t-tregular ⊢e
... | reg-S, r regA = r
t-tregular (⊢lam₂ ⊢e) with t-tregular ⊢e
... | reg-S, r regA = r
t-tregular (⊢app₁ ⊢e ⊢e₁) = t-tregular ⊢e
t-tregular (⊢app₂ ⊢e ⊢e₁) = t-tregular ⊢e
t-tregular (⊢sub ⊢e B≤A gc j≢Z) = t-tregular ⊢e
t-tregular (⊢tabs ⊢e) with t-tregular ⊢e
... | reg-S∙ r = r
t-tregular (⊢tapp ⊢e st) = t-tregular ⊢e


⊢rʲ-⋈' : Γ ⋈ ⊢rʲ j
       → Γ ⊢rʲ j
⊢rʲ-⋈' rj-Z = rj-Z
⊢rʲ-⋈' rj-∞ = rj-∞
⊢rʲ-⋈' (rj-𝕚 regj) = rj-𝕚 (⊢rʲ-⋈' regj)
⊢rʲ-⋈' (rj-𝕔 regj) = rj-𝕔 (⊢rʲ-⋈' regj)
⊢rʲ-⋈' (rj-𝕥 regj regA) = rj-𝕥 (⊢rʲ-⋈' regj) (⊢r-𝕣' regA)

⊢rʲ-strengthen,0 : Γ , A ⊢rʲ j
                 → Γ ⊢rʲ j
⊢rʲ-strengthen,0 rj-Z = rj-Z
⊢rʲ-strengthen,0 rj-∞ = rj-∞
⊢rʲ-strengthen,0 (rj-𝕚 regj) = rj-𝕚 (⊢rʲ-strengthen,0 regj)
⊢rʲ-strengthen,0 (rj-𝕔 regj) = rj-𝕔 (⊢rʲ-strengthen,0 regj)
⊢rʲ-strengthen,0 (rj-𝕥 regj regA) = rj-𝕥 (⊢rʲ-strengthen,0 regj) (⊢r-strengthen,0 regA)


s-⊢rʲ : Γ ⊢ j # A ≤ B
      → Γ ⊢rʲ j
s-⊢rʲ (s-refl regΔ cloA) = rj-Z
s-⊢rʲ (s-int regΔ) = rj-∞
s-⊢rʲ (s-var-∙ regΔ inΔ) = rj-∞
s-⊢rʲ (s-arr₁ s s₁) = s-⊢rʲ s
s-⊢rʲ (s-arr₂ s s₁) = rj-𝕚 (s-⊢rʲ s₁)
s-⊢rʲ (s-arr₃ regA s) = rj-𝕔 (s-⊢rʲ s)
s-⊢rʲ (s-∀ s) = rj-∞
s-⊢rʲ (s-∀l regB st s ic fd upj) = s-⊢rʲ s
s-⊢rʲ (s-tapp regB st s upC) = rj-𝕥 (s-⊢rʲ s) regB
s-⊢rʲ (s-∀l-no-appear regB st x ic fd) = s-⊢rʲ x

t-⊢rʲ : Γ ⊢ j # e ⦂ A
      → Γ ⊢rʲ j
t-⊢rʲ (⊢lit regΓ) = rj-Z
t-⊢rʲ (⊢var regΓ x∈Γ) = rj-Z
t-⊢rʲ (⊢ann ⊢e) = rj-Z
t-⊢rʲ (⊢lam₁ ⊢e) = rj-∞
t-⊢rʲ (⊢lam₂ ⊢e) = rj-𝕚 (⊢rʲ-strengthen,0 (t-⊢rʲ ⊢e))
t-⊢rʲ (⊢app₁ ⊢e ⊢e₁) with t-⊢rʲ ⊢e
... | rj-𝕔 r = r
t-⊢rʲ (⊢app₂ ⊢e ⊢e₁) with t-⊢rʲ ⊢e
... | rj-𝕚 r = r
t-⊢rʲ (⊢sub ⊢e B≤A gc j≢Z) = ⊢rʲ-⋈' (s-⊢rʲ B≤A)
t-⊢rʲ (⊢tabs ⊢e) = rj-Z
t-⊢rʲ (⊢tapp ⊢e st) with t-⊢rʲ ⊢e
... | rj-𝕥 r regA = r

t-⊢r : Γ ⊢ j # e ⦂ A
     → Γ ⊢r A
t-⊢r (⊢lit regΓ) = ⊢r-int
t-⊢r (⊢var regΓ x∈Γ) = ∋⦂-⊢r regΓ x∈Γ
t-⊢r (⊢ann ⊢e) = t-⊢r ⊢e
t-⊢r (⊢lam₁ ⊢e) with t-tregular ⊢e
... | reg-S, r regA = ⊢r-arr regA (⊢r-strengthen,0 (t-⊢r ⊢e))
t-⊢r (⊢lam₂ ⊢e) with t-tregular ⊢e
... | reg-S, r regA = ⊢r-arr regA (⊢r-strengthen,0 (t-⊢r ⊢e))
t-⊢r (⊢app₁ ⊢e ⊢e₁) with t-⊢r ⊢e
... | ⊢r-arr r r₁ = r₁
t-⊢r (⊢app₂ ⊢e ⊢e₁) with t-⊢r ⊢e
... | ⊢r-arr r r₁ = r₁
t-⊢r (⊢sub ⊢e B≤A gc j≢Z) = ⊢r-𝕣' (s1-⊢r-r B≤A)
t-⊢r (⊢tabs ⊢e) = ⊢r-∀ (t-⊢r ⊢e)
t-⊢r (⊢tapp ⊢e st) with t-⊢rʲ ⊢e
... | rj-𝕥 r regA = st0-⊢r (t-⊢r ⊢e) regA st


infix 3 _≋_
data _≋_ : Counter m → Counter m → Set where
  Z≋ : ∀ {nj : Counter m}
       → Z ≋ nj
  𝕚≋ : ∀ {nj}
       → j ≋ nj
     → 𝕚 j ≋ 𝕚 nj
  𝕔≋ : ∀ {nj}
     → j ≋ nj
     → 𝕔 j ≋ 𝕔 nj
  𝕥≋ : ∀ {nj}
     → j ≋ nj
     → 𝕥₍ A ₎ j ≋ 𝕥₍ A ₎ nj

↑ty-≋ : ∀ {nj nj'}
      → j ≋ nj
      → j ↑tyʲ k ⇘ j'
      → nj ↑tyʲ k ⇘ nj'
      → j' ≋ nj'
↑ty-≋ Z≋ ↑tyʲ-Z up2 = Z≋
↑ty-≋ (𝕚≋ new) (↑tyʲ-𝕚 up1) (↑tyʲ-𝕚 up2) = 𝕚≋ (↑ty-≋ new up1 up2)
↑ty-≋ (𝕔≋ new) (↑tyʲ-𝕔 up1) (↑tyʲ-𝕔 up2) = 𝕔≋ (↑ty-≋ new up1 up2)
↑ty-≋ (𝕥≋ new) (↑tyʲ-𝕥 up1 upA) (↑tyʲ-𝕥 up2 upA₁)
  with refl ← ↑ty-unique upA upA₁
  = 𝕥≋ (↑ty-≋ new up1 up2)


find-≋ : ∀ {nj}
       → find A k j
       → j ≋ nj
       → find A k nj
find-≋ (f-arr-𝕚-l ¬inA x) (𝕚≋ ~j) = f-arr-𝕚-l ¬inA x
find-≋ (f-arr-𝕚-r fd) (𝕚≋ ~j) = f-arr-𝕚-r (find-≋ fd ~j)
find-≋ (f-arr-𝕔 fd) (𝕔≋ ~j) = f-arr-𝕔 (find-≋ fd ~j)
find-≋ (f-∀-𝕚 fd upj) (𝕚≋ {nj = nj} ~j)
  with ⟨ nj' , upnj ⟩ ← ↑tyʲ0-total nj
  = f-∀-𝕚 (find-≋ fd (𝕚≋ (↑ty-≋ ~j upj upnj))) upnj
find-≋ (f-∀-𝕔 fd upj) (𝕔≋ {nj = nj} ~j)
  with ⟨ nj' , upnj ⟩ ← ↑tyʲ0-total nj
  = f-∀-𝕔 (find-≋ fd (𝕔≋ (↑ty-≋ ~j upj upnj))) upnj
find-≋ (f-𝕥 fd upj) (𝕥≋ {nj = nj} ~j)
  with ⟨ nj' , upnj ⟩ ← ↑tyʲ0-total nj
  = f-𝕥 (find-≋ fd (↑ty-≋ ~j upj upnj)) upnj


s-trans-∞ : Γ ⊢ ∞ # A ≤ B
          → Γ ⊢ ∞ # B ≤ C
          → Γ ⊢ ∞ # A ≤ C
s-trans-∞ (s-int regΔ) (s-int regΔ₁) = s-int regΔ
s-trans-∞ (s-var-∙ regΔ inΔ) s2 = s2
s-trans-∞ (s-arr₁ s1 s3) (s-arr₁ s2 s4) = s-arr₁ (s-trans-∞ s2 s1) (s-trans-∞ s3 s4)
s-trans-∞ (s-∀ s1) (s-∀ s2) = s-∀ (s-trans-∞ s1 s2)

s-trans-∞-eq : Γ ⊢ ∞ # A ≤ B
             → A ≡ B
s-trans-∞-eq (s-int regΔ) = refl
s-trans-∞-eq (s-var-∙ regΔ inΔ) = refl
s-trans-∞-eq (s-arr₁ s s₁) = cong₂ _`→_ (sym (s-trans-∞-eq s)) (s-trans-∞-eq s₁)
s-trans-∞-eq (s-∀ s) = cong `∀_ (s-trans-∞-eq s)


s-refl-∞ : SRegular Γ
         → Γ ⊢r A
         → Γ ⊢ ∞ # A ≤ A
s-refl-∞ regΓ ⊢r-int = s-int regΓ
s-refl-∞ regΓ (⊢r-var-∙ inΓ) = s-var-∙ regΓ inΓ
s-refl-∞ regΓ (⊢r-arr regA regA₁) = s-arr₁ (s-refl-∞ regΓ regA) (s-refl-∞ regΓ regA₁)
s-refl-∞ regΓ (⊢r-∀ regA) = s-∀ (s-refl-∞ (reg-S∙ regΓ) regA)

s-trans : Γ ⊢ j # A ≤ B
        → j ≋ j'
        → Γ ⊢ j' # B ≤ C
        → Γ ⊢ j' # A ≤ C
s-trans (s-refl regΔ cloA) ~j s2 = s2
s-trans (s-arr₂ s1 s3) (𝕚≋ ~j) (s-arr₂ s2 s4) = s-arr₂ (s-trans-∞ s2 s1) (s-trans s3 ~j s4)
s-trans (s-arr₃ regA s1) (𝕔≋ ~j) (s-arr₃ regA₁ s2) = s-arr₃ regA (s-trans s1 ~j s2)
s-trans (s-∀l regB st s1 () fd upj) Z≋ (s-refl regΔ cloA)
s-trans (s-∀l regB st s1 () fd upj) Z≋ (s-arr₁ s2 s3)
s-trans (s-∀l regB st s1 ic fd (↑tyʲ-𝕚 upj)) (𝕚≋ {nj = nj} ~j) (s-arr₂ s2 s3)
  with ⟨ nj' , upnj ⟩ ← ↑tyʲ0-total nj
  = s-∀l regB st (s-trans s1 (𝕚≋ ~j) (s-arr₂ s2 s3)) case-𝕚 (find-≋ fd (𝕚≋ (↑ty-≋ ~j upj upnj))) (↑tyʲ-𝕚 upnj)
s-trans (s-∀l regB st s1 ic fd (↑tyʲ-𝕔 upj)) (𝕔≋ {nj = nj} ~j) (s-arr₃ regA s2)
  with ⟨ nj' , upnj ⟩ ← ↑tyʲ0-total nj
  = s-∀l regB st (s-trans s1 (𝕔≋ ~j) (s-arr₃ regA s2)) case-𝕔 (find-≋ fd (𝕔≋ (↑ty-≋ ~j upj upnj))) (↑tyʲ-𝕔 upnj)
s-trans (s-∀l-no-appear regB st s1 ic fd) (𝕚≋ ~j) (s-arr₂ s2 s3)
  = s-∀l-no-appear regB st (s-trans s1 (𝕚≋ ~j) (s-arr₂ s2 s3)) case-𝕚 fd
s-trans (s-∀l-no-appear regB st s1 ic fd) (𝕔≋ ~j) (s-arr₃ regA s3)
  = s-∀l-no-appear regB st (s-trans s1 (𝕔≋ ~j) (s-arr₃ regA s3)) case-𝕔 fd
s-trans (s-tapp regB st s1 upC) (𝕥≋ ~j) (s-tapp regB₁ st₁ s2 upC₁)
  with refl ← ↑ty-st-eq upC st₁ = s-tapp regB st (s-trans s1 ~j s2) upC₁

gen-sub : Γ ⊢ j # e ⦂ A
        → j ≋ j'
        → Γ ⋈ ⊢ j' # A ≤ B
        → Γ ⊢ j' # e ⦂ B
gen-sub {j' = Z} ⊢e Z≋ (s-refl regΔ cloA) = ⊢e

gen-sub {j' = ∞} (⊢lit regΓ) Z≋ s = ⊢sub (⊢lit regΓ) s gc-i nz-∞
gen-sub {j' = ∞} (⊢var regΓ x∈Γ) Z≋ s = ⊢sub (⊢var regΓ x∈Γ) s gc-var nz-∞
gen-sub {j' = ∞} (⊢ann ⊢e) Z≋ s = ⊢sub (⊢ann ⊢e) s gc-ann nz-∞
gen-sub {j' = ∞} (⊢app₁ ⊢e ⊢e₁) Z≋ s = ⊢app₁ (gen-sub ⊢e (𝕔≋ Z≋) (s-arr₃ (⊢r-𝕣 (t-⊢r ⊢e₁)) s)) ⊢e₁
gen-sub {j' = ∞} (⊢app₂ ⊢e ⊢e₁) Z≋ s = ⊢app₂ (gen-sub ⊢e (𝕚≋ Z≋) (s-arr₂ (s-refl-∞ (s-sregular s) (⊢r-𝕣 (t-⊢r ⊢e₁))) s)) ⊢e₁
gen-sub {j' = ∞} (⊢tabs ⊢e) Z≋ s = ⊢sub (⊢tabs ⊢e) s gc-tlam nz-∞
gen-sub {j' = ∞} {B = B} (⊢tapp ⊢e st) Z≋ s
  with ⟨ B' , upB ⟩ ← ↑ty0-total B
  with rj-𝕥 regj regA ← t-⊢rʲ ⊢e
  = ⊢tapp (gen-sub ⊢e (𝕥≋ Z≋) (s-tapp (⊢r-𝕣 regA) st s upB)) (↑ty-st upB)

gen-sub {j' = 𝕚 j'} (⊢var regΓ x∈Γ) ~j s = ⊢sub (⊢var regΓ x∈Γ) s gc-var nz-I
gen-sub {j' = 𝕚 j'} (⊢ann ⊢e) ~j s = ⊢sub (⊢ann ⊢e) s gc-ann nz-I
gen-sub {j' = 𝕚 j'} (⊢lam₂ ⊢e) (𝕚≋ ~j) (s-arr₂ s s₁)
  with reg-S, regΓ regA ← t-tregular ⊢e
  with refl ← s-trans-∞-eq s = ⊢lam₂ (gen-sub ⊢e ~j (s1-weaken,0 s₁ regA))
gen-sub {j' = 𝕚 j'} (⊢app₁ ⊢e ⊢e₁) ~j s = ⊢app₁ (gen-sub ⊢e (𝕔≋ ~j) (s-arr₃ (⊢r-𝕣 (t-⊢r ⊢e₁)) s)) ⊢e₁
gen-sub {j' = 𝕚 j'} (⊢app₂ ⊢e ⊢e₁) ~j s = ⊢app₂ (gen-sub ⊢e (𝕚≋ ~j) (s-arr₂ (s-refl-∞ (s-sregular s) (⊢r-𝕣 (t-⊢r ⊢e₁))) s)) ⊢e₁
gen-sub {j' = 𝕚 j'} (⊢sub ⊢e B≤A gc j≢Z) (𝕚≋ ~j) s = ⊢sub ⊢e (s-trans B≤A (𝕚≋ ~j) s) gc nz-I
gen-sub {j' = 𝕚 j'} (⊢tabs ⊢e) ~j s = ⊢sub (⊢tabs ⊢e) s gc-tlam nz-I
gen-sub {j' = 𝕚 j'} {B = B} (⊢tapp ⊢e st) ~j s
  with ⟨ B' , upB ⟩ ← ↑ty0-total B
  with rj-𝕥 regj regA ← t-⊢rʲ ⊢e
  = ⊢tapp (gen-sub ⊢e (𝕥≋ ~j) (s-tapp (⊢r-𝕣 regA) st s upB)) (↑ty-st upB)

gen-sub {j' = 𝕔 j'} (⊢var regΓ x∈Γ) ~j s = ⊢sub (⊢var regΓ x∈Γ) s gc-var nz-C
gen-sub {j' = 𝕔 j'} (⊢ann ⊢e) ~j s = ⊢sub (⊢ann ⊢e) s gc-ann nz-C
gen-sub {j' = 𝕔 j'} (⊢app₁ ⊢e ⊢e₁) ~j s = ⊢app₁ (gen-sub ⊢e (𝕔≋ ~j) (s-arr₃ (⊢r-𝕣 (t-⊢r ⊢e₁)) s)) ⊢e₁
gen-sub {j' = 𝕔 j'} (⊢app₂ ⊢e ⊢e₁) ~j s = ⊢app₂ (gen-sub ⊢e (𝕚≋ ~j) (s-arr₂ (s-refl-∞ (s-sregular s) (⊢r-𝕣 (t-⊢r ⊢e₁))) s)) ⊢e₁
gen-sub {j' = 𝕔 j'} (⊢sub ⊢e B≤A gc j≢Z) ~j s = ⊢sub ⊢e (s-trans B≤A ~j s) gc nz-C
gen-sub {j' = 𝕔 j'} (⊢tabs ⊢e) ~j s = ⊢sub (⊢tabs ⊢e) s gc-tlam nz-C
gen-sub {j' = 𝕔 j'} {B = B} (⊢tapp ⊢e st) ~j s
  with ⟨ B' , upB ⟩ ← ↑ty0-total B
  with rj-𝕥 regj regA ← t-⊢rʲ ⊢e
  = ⊢tapp (gen-sub ⊢e (𝕥≋ ~j) (s-tapp (⊢r-𝕣 regA) st s upB)) (↑ty-st upB)

gen-sub {j' = 𝕥₍ A ₎ j'} (⊢var regΓ x∈Γ) ~j s = ⊢sub (⊢var regΓ x∈Γ) s gc-var nz-T
gen-sub {j' = 𝕥₍ A ₎ j'} (⊢ann ⊢e) ~j s = ⊢sub (⊢ann ⊢e) s gc-ann nz-T
gen-sub {j' = 𝕥₍ A ₎ j'} (⊢app₁ ⊢e ⊢e₁) ~j s = ⊢app₁ (gen-sub ⊢e (𝕔≋ ~j) (s-arr₃ (⊢r-𝕣 (t-⊢r ⊢e₁)) s)) ⊢e₁
gen-sub {j' = 𝕥₍ A ₎ j'} (⊢app₂ ⊢e ⊢e₁) ~j s = ⊢app₂ (gen-sub ⊢e (𝕚≋ ~j) (s-arr₂ (s-refl-∞ (s-sregular s) (⊢r-𝕣 (t-⊢r ⊢e₁))) s)) ⊢e₁
gen-sub {j' = 𝕥₍ A ₎ j'} (⊢sub ⊢e B≤A gc j≢Z) ~j s = ⊢sub ⊢e (s-trans B≤A ~j s) gc nz-T
gen-sub {j' = 𝕥₍ A ₎ j'} (⊢tabs ⊢e) ~j s = ⊢sub (⊢tabs ⊢e) s gc-tlam nz-T
gen-sub {j' = 𝕥₍ A ₎ j'} {B = B} (⊢tapp ⊢e st) ~j s
  with ⟨ B' , upB ⟩ ← ↑ty0-total B
  with rj-𝕥 regj regA ← t-⊢rʲ ⊢e
  = ⊢tapp (gen-sub ⊢e (𝕥≋ ~j) (s-tapp (⊢r-𝕣 regA) st s upB)) (↑ty-st upB)

gen-sub0 : Γ ⊢ Z # g ⦂ A
         → Γ ⋈ ⊢ j # A ≤ B
         → Γ ⊢ j # g ⦂ B
gen-sub0 ⊢e s = gen-sub ⊢e Z≋ s
