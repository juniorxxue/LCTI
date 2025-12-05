module Implicit.Decl.Trans where

open import Implicit.Language.All
open import Implicit.Decl.Subtyping


s-trans' : Γ ⊢d j # A ≤ B
        → Γ ⊢d j # B ≤ C
        → Γ ⊢d j # A ≤ C
s-trans' (s-refl regΔ cloA) (s-refl regΔ₁ cloA₁) = s-refl regΔ cloA₁
s-trans' (s-int regΔ) (s-int regΔ₁) = s-int regΔ
s-trans' (s-var-∙ regΔ inΔ) (s-var-∙ regΔ₁ inΔ₁) = s-var-∙ regΔ inΔ₁
s-trans' (s-arr₁ s1 s3) (s-arr₁ s2 s4) = s-arr₁ (s-trans' s2 s1) (s-trans' s3 s4)
s-trans' (s-arr₂ s1 s3) (s-arr₂ s2 s4) = s-arr₂ (s-trans' s2 s1) (s-trans' s3 s4)
s-trans' (s-arr₃ regA s1) (s-arr₃ regA₁ s2) = s-arr₃ regA (s-trans' s1 s2)
s-trans' (s-∀ s1) (s-∀ s2) = s-∀ (s-trans' s1 s2)
s-trans' (s-∀l regB st s1 ic fd upj) (s-arr₂ s2 s3) = s-∀l regB st (s-trans' s1 (s-arr₂ s2 s3)) ic fd upj
s-trans' (s-∀l regB st s1 ic fd upj) (s-arr₃ regA s2) = s-∀l regB st (s-trans' s1 (s-arr₃ regA s2)) ic fd upj
s-trans' (s-∀l-peek regB st s1 ic fd upj) (s-arr₂ s2 s3) = s-∀l-peek regB st (s-trans' s1 (s-arr₂ s2 s3)) ic fd upj
s-trans' (s-∀l-peek regB st s1 ic fd upj) (s-arr₃ regA s2) = s-∀l-peek regB st (s-trans' s1 (s-arr₃ regA s2)) ic fd upj
s-trans' (s-∀l-no-appear regB st s1 ic fd) (s-arr₂ s2 s3) = s-∀l-no-appear regB st (s-trans' s1 (s-arr₂ s2 s3)) ic fd
s-trans' (s-∀l-no-appear regB st s1 ic fd) (s-arr₃ regA s2) = s-∀l-no-appear regB st (s-trans' s1 (s-arr₃ regA s2)) ic fd
s-trans' (s-tapp regB st s1 upC) (s-tapp regB₁ st₁ s2 upC₁)
  with refl ← ↑ty-st-eq upC st₁ = s-tapp regB st (s-trans' s1 s2) upC₁


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
  refl≋ : j ≋ j


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
↑ty-≋ refl≋ upj upnj
  with refl ← ↑tyʲ-unique upj upnj = refl≋

≋-isoinf : ∀ {nj}
         → j ≋ nj
         → IsoInf j
         → IsoInf nj
≋-isoinf (𝕚≋ refl≋) i∞-z = i∞-z
≋-isoinf (𝕚≋ newj) (i∞-i iso) = i∞-i (≋-isoinf newj iso)
≋-isoinf refl≋ iso = iso

find-≋ : ∀ {nj}
       → find A k j
       → j ≋ nj
       → find A k nj
find-≋ (f-arr-𝕚-l x) (𝕚≋ ~j) = f-arr-𝕚-l x
find-≋ (f-arr-𝕚-r ¬inA fd) (𝕚≋ ~j) = f-arr-𝕚-r ¬inA (find-≋ fd ~j)
find-≋ (f-arr-𝕔 ¬inA fd) (𝕔≋ ~j) = f-arr-𝕔 ¬inA (find-≋ fd ~j)
find-≋ (f-∀-𝕚 fd upj) (𝕚≋ {nj = nj} ~j)
  with ⟨ nj' , upnj ⟩ ← ↑tyʲ0-total nj
  = f-∀-𝕚 (find-≋ fd (𝕚≋ (↑ty-≋ ~j upj upnj))) upnj
find-≋ (f-∀-𝕔 fd upj) (𝕔≋ {nj = nj} ~j)
  with ⟨ nj' , upnj ⟩ ← ↑tyʲ0-total nj
  = f-∀-𝕔 (find-≋ fd (𝕔≋ (↑ty-≋ ~j upj upnj))) upnj
find-≋ (f-𝕥 fd upj) (𝕥≋ {nj = nj} ~j)
  with ⟨ nj' , upnj ⟩ ← ↑tyʲ0-total nj
  = f-𝕥 (find-≋ fd (↑ty-≋ ~j upj upnj)) upnj
find-≋ (f-iso iso) (𝕚≋ ~j) = f-iso (≋-isoinf (𝕚≋ ~j) iso)
find-≋ (f-iso iso) refl≋ = f-iso iso
find-≋ fd refl≋ = fd

peek-≋ : ∀ {nj}
       → peek A k j
       → j ≋ nj
       → peek A k nj
peek-≋ pk refl≋ = pk
peek-≋ (peek-arr-i pk) (𝕚≋ ~j) = peek-arr-i (peek-≋ pk ~j)
peek-≋ (peek-arr-c pk) (𝕔≋ ~j) = peek-arr-c (peek-≋ pk ~j)
peek-≋ (peek-∀-i pk upj) (𝕚≋ {nj = nj} ~j)
  with ⟨ nj' , upnj ⟩ ← ↑tyʲ0-total nj
  = peek-∀-i (peek-≋ pk (𝕚≋ (↑ty-≋ ~j upj upnj))) upnj
peek-≋ (peek-∀-c pk upj) (𝕔≋ {nj = nj} ~j)
  with ⟨ nj' , upnj ⟩ ← ↑tyʲ0-total nj
  = peek-∀-c (peek-≋ pk (𝕔≋ (↑ty-≋ ~j upj upnj))) upnj
peek-≋ (peek-∀-t pk upj) (𝕥≋ {nj = nj} ~j)
  with ⟨ nj' , upnj ⟩ ← ↑tyʲ0-total nj
  = peek-∀-t (peek-≋ pk (↑ty-≋ ~j upj upnj)) upnj

s-trans-∞ : Γ ⊢d ∞ # A ≤ B
          → Γ ⊢d ∞ # B ≤ C
          → Γ ⊢d ∞ # A ≤ C
s-trans-∞ (s-int regΔ) (s-int regΔ₁) = s-int regΔ
s-trans-∞ (s-var-∙ regΔ inΔ) s2 = s2
s-trans-∞ (s-arr₁ s1 s3) (s-arr₁ s2 s4) = s-arr₁ (s-trans-∞ s2 s1) (s-trans-∞ s3 s4)
s-trans-∞ (s-∀ s1) (s-∀ s2) = s-∀ (s-trans-∞ s1 s2)

s-trans-∞-eq : Γ ⊢d ∞ # A ≤ B
             → A ≡ B
s-trans-∞-eq (s-int regΔ) = refl
s-trans-∞-eq (s-var-∙ regΔ inΔ) = refl
s-trans-∞-eq (s-arr₁ s s₁) = cong₂ _`→_ (sym (s-trans-∞-eq s)) (s-trans-∞-eq s₁)
s-trans-∞-eq (s-∀ s) = cong `∀_ (s-trans-∞-eq s)


s-refl-∞ : SRegular Γ
         → Γ ⊢r A
         → Γ ⊢d ∞ # A ≤ A
s-refl-∞ regΓ ⊢r-int = s-int regΓ
s-refl-∞ regΓ (⊢r-var-∙ inΓ) = s-var-∙ regΓ inΓ
s-refl-∞ regΓ (⊢r-arr regA regA₁) = s-arr₁ (s-refl-∞ regΓ regA) (s-refl-∞ regΓ regA₁)
s-refl-∞ regΓ (⊢r-∀ regA) = s-∀ (s-refl-∞ (reg-S∙ regΓ) regA)

s-trans : Γ ⊢d j # A ≤ B
        → j ≋ j'
        → Γ ⊢d j' # B ≤ C
        → Γ ⊢d j' # A ≤ C
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
s-trans (s-∀l-peek regB st s1 () fd upj) Z≋ (s-arr₁ s2 s3)
s-trans (s-∀l-peek regB st s1 ic fd (↑tyʲ-𝕚 upj)) (𝕚≋ {nj = nj} ~j) (s-arr₂ s2 s3)
  with ⟨ nj' , upnj ⟩ ← ↑tyʲ0-total nj
  = s-∀l-peek regB st (s-trans s1 (𝕚≋ ~j) (s-arr₂ s2 s3)) case-𝕚 (peek-≋ fd (𝕚≋ (↑ty-≋ ~j upj upnj))) (↑tyʲ-𝕚 upnj)
s-trans (s-∀l-peek regB st s1 ic fd (↑tyʲ-𝕔 upj)) (𝕔≋ {nj = nj} ~j) (s-arr₃ regA s2)
  with ⟨ nj' , upnj ⟩ ← ↑tyʲ0-total nj
  = s-∀l-peek regB st (s-trans s1 (𝕔≋ ~j) (s-arr₃ regA s2)) case-𝕔 (peek-≋ fd (𝕔≋ (↑ty-≋ ~j upj upnj))) (↑tyʲ-𝕔 upnj)
s-trans (s-∀l-no-appear regB st s1 ic fd) (𝕚≋ ~j) (s-arr₂ s2 s3)
  = s-∀l-no-appear regB st (s-trans s1 (𝕚≋ ~j) (s-arr₂ s2 s3)) case-𝕚 fd
s-trans (s-∀l-no-appear regB st s1 ic fd) (𝕔≋ ~j) (s-arr₃ regA s3)
  = s-∀l-no-appear regB st (s-trans s1 (𝕔≋ ~j) (s-arr₃ regA s3)) case-𝕔 fd
s-trans (s-tapp regB st s1 upC) (𝕥≋ ~j) (s-tapp regB₁ st₁ s2 upC₁)
  with refl ← ↑ty-st-eq upC st₁ = s-tapp regB st (s-trans s1 ~j s2) upC₁
s-trans s1 refl≋ s2 = s-trans' s1 s2
