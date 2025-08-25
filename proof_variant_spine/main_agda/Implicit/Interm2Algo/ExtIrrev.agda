module Implicit.Interm2Algo.ExtIrrev where

open import Implicit.Language.All

open import Implicit.Interm2Algo.ReExtension

{-
infix 3 _⊆_w/t_w/p_
data _⊆_w/t_w/p_ : Env n m → Env n m → Type m → Counter m → Set where
  ⊆p-∞ : (ext : Γ ⊆ Δ w/t A)
       → Γ ⊆ Δ w/t A w/p ∞
  ⊆p-I : Γ ⊆ Δ w/t B w/p j
       → Γ ⊆ Δ w/t A `→ B w/p 𝕚 j
  ⊆p-C : Γ ⊆ Δ w/t B w/p j
       → Γ ⊆ Δ w/t A `→ B w/p 𝕔 j
  ⊆∀p-I : Γ ,^ ⊆ Δ ,= B w/t A w/p (𝕚 j')
       → (upj : ↑tyʲ0 j ⇘ j')
       → Γ ⊆ Δ w/t `∀ A w/p (𝕚 j)
  ⊆∀p-I-no : Γ ,^ ⊆ Δ ,^ w/t A w/p (𝕚 j')
       → (upj : ↑tyʲ0 j ⇘ j')
       → Γ ⊆ Δ w/t `∀ A w/p (𝕚 j)
  ⊆∀p-C : Γ ,^ ⊆ Δ ,= B w/t A w/p (𝕔 j')
       → (upj : ↑tyʲ0 j ⇘ j')
       → Γ ⊆ Δ w/t `∀ A w/p (𝕔 j)
  ⊆∀p-C-no : Γ ,^ ⊆ Δ ,^ w/t A w/p (𝕔 j')
       → (upj : ↑tyʲ0 j ⇘ j')
       → Γ ⊆ Δ w/t `∀ A w/p (𝕔 j)
  ⊆∀p-T : Γ ,= B ⊆ Δ ,= B w/t A w/p j'
       → (upj : ↑tyʲ0 j ⇘ j')
       → Γ ⊆ Δ w/t `∀ A w/p 𝕥₍ B ₎ j
-}


----------------------------------------------------------------------
--+          extension is irrelevant to solution                   +--
----------------------------------------------------------------------


⊆/x-irrev-== : Γ ⊆ Δ w/v X
             → [ B / k ] Γ =⟹ Γ'
             → [ B / k ] Δ =⟹ Δ'
             → Γ' ⊆ Δ' w/v X
⊆/x-irrev-== (ext-Z^ regΓ regA) (=⟹^S new1 up1) (=⟹=S new2 up2 regB)
  with refl ← ↑ty-unique-inver up1 up2
  with refl ← =⟹-unique new1 new2 = ext-Z^ (=⟹-sregular new1) (=⟹-⊢r regA new1)
⊆/x-irrev-== (ext-Z∙ regΓ) (=⟹∙S new1 up1) (=⟹∙S new2 up2)
  with refl ← ↑ty-unique-inver up1 up2
  with refl ← =⟹-unique new1 new2 = ext-Z∙ (=⟹-sregular new1)
⊆/x-irrev-== (ext-Z= regΓ regA) (=⟹=0 up regA₁ env) (=⟹=0 up₁ regA₂ env₁)
  with refl ← ↑ty-unique-inver up up₁ = ext-Z= regΓ regA₁
⊆/x-irrev-== (ext-Z= regΓ regA) (=⟹=S new1 up1 regB) (=⟹=S new2 up2 regB₁)
  with refl ← ↑ty-unique-inver up1 up2
  with refl ← =⟹-unique new1 new2 = ext-Z= (=⟹-sregular new1) (=⟹-⊢r regA new1)
⊆/x-irrev-== (ext-S^ ext) (=⟹^S new1 up1) (=⟹^S new2 up2)
  with refl ← ↑ty-unique-inver up1 up2 = ext-S^ (⊆/x-irrev-== ext new1 new2)
⊆/x-irrev-== (ext-S∙ ext) (=⟹∙S new1 up1) (=⟹∙S new2 up2)
 with refl ← ↑ty-unique-inver up1 up2 = ext-S∙ (⊆/x-irrev-== ext new1 new2)
⊆/x-irrev-== (ext-S= ext regA) (=⟹=0 up regA₁ env) (=⟹=0 up₁ regA₂ env₁)
 with refl ← ↑ty-unique-inver up up₁ = ext-S= ext regA₁
⊆/x-irrev-== (ext-S= ext regA) (=⟹=S new1 up1 regB) (=⟹=S new2 up2 regB₁)
  with refl ← ↑ty-unique-inver up1 up2 = ext-S= (⊆/x-irrev-== ext new1 new2) (=⟹-⊢r regA new1)

⊆/-irrev-== : Γ ⊆ Δ w/t A
            → [ B / k ] Γ =⟹ Γ'
            → [ B / k ] Δ =⟹ Δ'
            → Γ' ⊆ Δ' w/t A
⊆/-irrev-== (ext-int x) newΓ newΔ with refl ← =⟹-unique newΓ newΔ = ⊆/-refl (=⟹-sregular newΓ) ⊢c-int
⊆/-irrev-== (ext-var x) newΓ newΔ = ext-var (⊆/x-irrev-== x newΓ newΔ)
⊆/-irrev-== (ext-arr ext ext₁) newΓ newΔ = let ⟨ Ω' , inst ⟩ = inst-exist' newΓ (⊆/-⊆ ext)
                     in ext-arr (⊆/-irrev-== ext newΓ inst) (⊆/-irrev-== ext₁ inst newΔ)
⊆/-irrev-== {B = B} (ext-∀ ext) newΓ newΔ = let ⟨ B' , upB ⟩ = ↑ty0-total B
                                                     in ext-∀ (⊆/-irrev-== ext (=⟹∙S newΓ upB) (=⟹∙S newΔ upB))

⊆/c-irrev-== : Γ ⊆ Δ w/t A w/c j
             → [ B / k ] Γ =⟹ Γ'
             → [ B / k ] Δ =⟹ Δ'
             → Γ' ⊆ Δ' w/t A w/c j
⊆/c-irrev-== (⊆Z regΓ cloA) new1 new2 with refl ← =⟹-unique new1 new2 = ⊆Z (=⟹-sregular new1) (=⟹-⊢c cloA new1)
⊆/c-irrev-== (⊆I ext ext₁) new1 new2
  with ⟨ Ω , inst ⟩ ← inst-exist' new1 (⊆/-⊆ ext) = ⊆I (⊆/-irrev-== ext new1 inst) (⊆/c-irrev-== ext₁ inst new2)
⊆/c-irrev-== (⊆C x ext) new1 new2 = ⊆C (=⟹-⊢c x new1) (⊆/c-irrev-== ext new1 new2)
⊆/c-irrev-== {B = B} (⊆∀-I ext upj) new1 new2
  with evar-sol r regA ← ⊆/c-⊆ ext
  with ⟨ B' , upB ⟩ ← ↑ty0-total B = ⊆∀-I (⊆/c-irrev-== ext (=⟹^S new1 upB) (=⟹=S new2 upB regA)) upj
⊆/c-irrev-== {B = B} (⊆∀-C ext upj) new1 new2
  with evar-sol r regA ← ⊆/c-⊆ ext
  with ⟨ B' , upB ⟩ ← ↑ty0-total B = ⊆∀-C (⊆/c-irrev-== ext (=⟹^S new1 upB) (=⟹=S new2 upB regA)) upj
⊆/c-irrev-== {B = B} (⊆∀-T ext upj) new1 new2
  with svar r regA ← ⊆/c-⊆ ext
  with ⟨ B' , upB ⟩ ← ↑ty0-total B = ⊆∀-T (⊆/c-irrev-== ext (=⟹=S new1 upB regA) (=⟹=S new2 upB (⊆-⊢r regA r))) upj
⊆/c-irrev-== (⊆I-X regΓ cloA) new1 new2 with refl ← =⟹-unique new1 new2 = ⊆I-X (=⟹-sregular new1) (=⟹-⊢c cloA new1)
⊆/c-irrev-== (⊆C-X regΓ cloA) new1 new2 with refl ← =⟹-unique new1 new2 = ⊆C-X (=⟹-sregular new1) (=⟹-⊢c cloA new1)
⊆/c-irrev-== (⊆T-X regΓ cloA) new1 new2 with refl ← =⟹-unique new1 new2 = ⊆T-X (=⟹-sregular new1) (=⟹-⊢c cloA new1)
⊆/c-irrev-== {B = B} (⊆∀-I-no ext upj) new1 new2
  with ⟨ B' , upB ⟩ ← ↑ty0-total B  = ⊆∀-I-no (⊆/c-irrev-== ext (=⟹^S new1 upB) (=⟹^S new2 upB)) upj
⊆/c-irrev-== {B = B} (⊆∀-C-no ext upj) new1 new2
  with ⟨ B' , upB ⟩ ← ↑ty0-total B  = ⊆∀-C-no (⊆/c-irrev-== ext (=⟹^S new1 upB) (=⟹^S new2 upB)) upj
⊆/c-irrev-== (⊆Inf-X extx iso) new1 new2 = ⊆Inf-X (⊆/x-irrev-== extx new1 new2) iso
⊆/c-irrev-== (⊆∞ ext) new1 new2 = ⊆∞ (⊆/-irrev-== ext new1 new2)
⊆/c-irrev-== {B = B} (⊆∀-I-new ext upj) new1 new2
  with svar r regA ← ⊆/c-⊆ ext
  with ⟨ B' , upB ⟩ ← ↑ty0-total B
  = ⊆∀-I-new (⊆/c-irrev-== ext (=⟹=S new1 upB regA) (=⟹=S new2 upB (⊆-⊢r regA r))) upj
⊆/c-irrev-== {B = B} (⊆∀-C-new ext upj) new1 new2
  with svar r regA ← ⊆/c-⊆ ext
  with ⟨ B' , upB ⟩ ← ↑ty0-total B
  = ⊆∀-C-new (⊆/c-irrev-== ext (=⟹=S new1 upB regA) (=⟹=S new2 upB (⊆-⊢r regA r))) upj

⊆/v-irrev-^= : Γ ⊆ Δ w/v k
             → Γ ∋^ k
             → [ B / k ] Δ =⟹ Δ'
             → Γ ⊆ Δ' w/v k

⊆/v-irrev-^= (ext-Z^ regΓ regA) Z (=⟹=0 up regA₁ env) = ext-Z^ regΓ regA₁
⊆/v-irrev-^= (ext-S^ ext) (S^ inΓ) (=⟹^S newΔ up1) = ext-S^ (⊆/v-irrev-^= ext inΓ newΔ)
⊆/v-irrev-^= (ext-S∙ ext) (S∙ inΓ) (=⟹∙S newΔ up1) = ext-S∙ (⊆/v-irrev-^= ext inΓ newΔ)
⊆/v-irrev-^= (ext-S= ext regA) (S= inΓ) (=⟹=S newΔ up1 regB) = ext-S= (⊆/v-irrev-^= ext inΓ newΔ) regA

⊆/-irrev-^= : Γ ⊆ Δ w/t A
            → Γ ∋^ k
            → [ B / k ] Δ =⟹ Δ'
            → k ε A
            → Γ ⊆ Δ' w/t A
⊆/-irrev-^= (ext-var x) inΓ newΔ ε-var = ext-var (⊆/v-irrev-^= x inΓ newΔ)
⊆/-irrev-^= (ext-arr ext ext₁) inΓ newΔ (ε-arr-l inA) with inst-exist newΔ (⊆/-⊆ ext₁) (⊆/-^in-=out ext inA inΓ)
... | ⟨ Ω' , newΩ ⟩ = ext-arr (⊆/-irrev-^= ext inΓ newΩ inA) (⊆/-irrev-== ext₁ newΩ newΔ)
⊆/-irrev-^= (ext-arr ext ext₁) inΓ newΔ (ε-arr-r ¬inA inB) = ext-arr ext (⊆/-irrev-^= ext₁ (⊆/-^in-^out ext ¬inA inΓ) newΔ inB)
⊆/-irrev-^= {B = B} (ext-∀ ext) inΓ newΔ (ε-∀ inA) = ext-∀ (⊆/-irrev-^= ext (S∙ inΓ) (=⟹∙S newΔ (proj₂ (↑ty0-total B))) inA)

⊆/c-irrev-^= : Γ ⊆ Δ w/t A w/c j
             → Γ ∋^ k
             → [ B / k ] Δ =⟹ Δ'
             → find A k j
             → Γ ⊆ Δ' w/t A w/c j
⊆/c-irrev-^= (⊆∞ ext) x x₁ (f-∞ inA) = ⊆∞ (⊆/-irrev-^= ext x x₁ inA)
⊆/c-irrev-^= (⊆Z regΓ cloA) inΓ newΔ fd = ⊥-elim (∋^-∋=-false inΓ (=⟹-∋= newΔ))
⊆/c-irrev-^= (⊆I ext ext₁) inΓ newΔ (f-arr-𝕚-l x) with inst-exist newΔ (⊆/c-⊆ ext₁) (⊆/-^in-=out ext x inΓ)
... | ⟨ Ω' , inst-Ω ⟩ = ⊆I (⊆/-irrev-^= ext inΓ inst-Ω x) (⊆/c-irrev-== ext₁ inst-Ω newΔ)
⊆/c-irrev-^= (⊆I ext ext₁) inΓ newΔ (f-arr-𝕚-r ¬inA fd) =
  ⊆I ext (⊆/c-irrev-^= ext₁ (⊆/-^in-^out ext ¬inA inΓ) newΔ fd)
⊆/c-irrev-^= (⊆C x ext) inΓ newΔ (f-arr-𝕔 ¬inA fd) = ⊆C x (⊆/c-irrev-^= ext inΓ newΔ fd)
⊆/c-irrev-^= {B = B} (⊆∀-I ext upj') inΓ newΔ (f-∀-𝕚 fd upj) with ⊆/c-⊆ ext
... | evar-sol r regA
   with refl ← ↑tyʲ-unique upj upj' = ⊆∀-I (⊆/c-irrev-^= ext (S^ inΓ) (=⟹=S newΔ (proj₂ (↑ty0-total B)) regA) fd) upj'
⊆/c-irrev-^= {B = B} (⊆∀-C ext upj') inΓ newΔ (f-∀-𝕔 fd upj) with ⊆/c-⊆ ext
... | evar-sol r regA
  with refl ← ↑tyʲ-unique upj upj' = ⊆∀-C (⊆/c-irrev-^= ext (S^ inΓ) (=⟹=S newΔ (proj₂ (↑ty0-total B)) regA) fd) upj'
⊆/c-irrev-^= {B = B} (⊆∀-T ext upj) inΓ newΔ (f-𝕥 fd upj₁) with ⊆/c-⊆ ext
... | svar r regA
  with refl ← ↑tyʲ-unique upj upj₁ = ⊆∀-T (⊆/c-irrev-^= ext (S= inΓ) (=⟹=S newΔ (proj₂ (↑ty0-total B)) (⊆-⊢r regA r)) fd) upj
⊆/c-irrev-^= {B = B} (⊆∀-I-no ext upj) inΓ newΔ (f-∀-𝕚 fd upj₁)
  with refl ← ↑tyʲ-unique upj upj₁ = ⊆∀-I-no (⊆/c-irrev-^= ext (S^ inΓ) (=⟹^S newΔ (proj₂ (↑ty0-total B))) fd) upj
⊆/c-irrev-^= {B = B} (⊆∀-C-no ext upj) inΓ newΔ (f-∀-𝕔 fd upj₁)
  with refl ← ↑tyʲ-unique upj upj₁ = ⊆∀-C-no (⊆/c-irrev-^= ext (S^ inΓ) (=⟹^S newΔ (proj₂ (↑ty0-total B))) fd) upj
⊆/c-irrev-^= (⊆I-X regΓ cloA) inΓ newΔ (f-iso iso) = ⊥-elim (⊢c-^∈-false ε-var inΓ cloA)
⊆/c-irrev-^= (⊆C-X regΓ cloA) inΓ newΔ (f-iso iso) = ⊥-elim (⊢c-^∈-false ε-var inΓ cloA)
⊆/c-irrev-^= (⊆T-X regΓ cloA) inΓ newΔ (f-iso iso) = ⊥-elim (⊢c-^∈-false ε-var inΓ cloA)
⊆/c-irrev-^= (⊆Inf-X extx iso) inΓ newΔ (f-iso iso₁) = ⊆Inf-X (⊆/v-irrev-^= extx inΓ newΔ) iso
⊆/c-irrev-^= (⊆∞ regΓ) inΓ newΔ (f-iso ())
⊆/c-irrev-^= {B = B} (⊆∀-I-new ext upj) inΓ newΔ (f-∀-𝕚 fd upj₁)
  with svar r regA ← ⊆/c-⊆ ext
  with ⟨ B' , upB ⟩ ←  ↑ty0-total B
  with refl ← ↑tyʲ-unique upj upj₁ = ⊆∀-I-new (⊆/c-irrev-^= ext (S= inΓ) (=⟹=S newΔ upB (⊆-⊢r regA r)) fd) upj
⊆/c-irrev-^= {B = B} (⊆∀-C-new ext upj) inΓ newΔ (f-∀-𝕔 fd upj₁)
  with refl ← ↑tyʲ-unique upj upj₁
  with svar r regA ← ⊆/c-⊆ ext
  with ⟨ B' , upB ⟩ ←  ↑ty0-total B = ⊆∀-C-new (⊆/c-irrev-^= ext (S= inΓ) (=⟹=S newΔ upB (⊆-⊢r regA r)) fd) upj

⊆/c-irrev-^=0 : Γ ,^ ⊆ Δ ,= B₁ w/t A w/c j
              → find A #0 j
              → Δ ⊢r B₂
              → Γ ,^ ⊆ Δ ,= B₂ w/t A w/c j
⊆/c-irrev-^=0 {B₂ = B₂} ext fd regB with ⊆/c-⊆ ext
... | evar-sol r regA = ⊆/c-irrev-^= ext Z (=⟹=0 (proj₂ (↑ty0-total B₂)) regB (⊆-sregular' r)) fd


⊆/c-irrev-^=0' : Γ ,^ ⊆ Δ ,= B₁ w/t A w/c j
              → Δ ⊢r B₂
              → Γ ,^ ⊆ Δ ,= B₂ w/t A w/c j
⊆/c-irrev-^=0' ext regB = ⊆/c-irrev-^=0 ext (⊆/c-find0 ext) regB

----------------------------------------------------------------------
--+                       another transform                        +--
----------------------------------------------------------------------


◎-∋∙ : Γ ∋∙ X
     → Γ ◎ k ⇘ Γ'
     → Γ' ∋∙ X
◎-∋∙ Z (◎S∙ newΓ) = Z
◎-∋∙ (S∙ inΓ) (◎S∙ newΓ) = S∙ (◎-∋∙ inΓ newΓ)
◎-∋∙ (S= inΓ) ◎Z = S^ inΓ
◎-∋∙ (S= inΓ) (◎S= newΓ) = S= (◎-∋∙ inΓ newΓ)
◎-∋∙ (S^ inΓ) (◎S^ newΓ) = S^ (◎-∋∙ inΓ newΓ)
◎-∋∙ (S, inΓ) (◎S, newΓ) = S, (◎-∋∙ inΓ newΓ)



◎-∋=-≢ : Γ ∋= X
       → Γ ◎ k ⇘ Γ'
       → X ≢ k
       → Γ' ∋= X
◎-∋=-≢ Z ◎Z neq = ⊥-elim (neq refl)
◎-∋=-≢ Z (◎S= newΓ) neq = Z
◎-∋=-≢ (S∙ inΓ) (◎S∙ newΓ) neq = S∙ (◎-∋=-≢ inΓ newΓ (≢-pred neq))
◎-∋=-≢ (S^ inΓ) (◎S^ newΓ) neq = S^ (◎-∋=-≢ inΓ newΓ (≢-pred neq))
◎-∋=-≢ (S= inΓ) ◎Z neq = S^ inΓ
◎-∋=-≢ (S= inΓ) (◎S= newΓ) neq = S= (◎-∋=-≢ inΓ newΓ (≢-pred neq))
◎-∋=-≢ (S, inΓ) (◎S, newΓ) neq = S, (◎-∋=-≢ inΓ newΓ neq)

◎-⊢c : Γ ⊢c A
     → Γ ◎ k ⇘ Γ'
     → k ¬ε A
     → Γ' ⊢c A
◎-⊢c ⊢c-int newΓ ninA = ⊢c-int
◎-⊢c (⊢c-var-∙ inΔ) newΓ (¬ε-var x) = ⊢c-var-∙ (◎-∋∙ inΔ newΓ)
◎-⊢c (⊢c-var-= inΔ) newΓ (¬ε-var x) = ⊢c-var-= (◎-∋=-≢ inΔ newΓ x)
◎-⊢c (⊢c-arr cloA cloA₁) newΓ (¬ε-arr ninA ninA₁) = ⊢c-arr (◎-⊢c cloA newΓ ninA) (◎-⊢c cloA₁ newΓ ninA₁)
◎-⊢c (⊢c-∀ cloA) newΓ (¬ε-∀ ninA) = ⊢c-∀ (◎-⊢c cloA (◎S∙ newΓ) ninA)


◎-total : Ω ∋= k
        → ∃[ Ω' ](Ω ◎ k ⇘ Ω')
◎-total (Z {Δ = Δ}) = ⟨ Δ ,^ , ◎Z ⟩
◎-total (S∙ inΩ) = ⟨ ◎-total inΩ .proj₁ ,∙ , ◎S∙ (◎-total inΩ .proj₂) ⟩
◎-total (S^ inΩ) = ⟨ ◎-total inΩ .proj₁ ,^ , ◎S^ (◎-total inΩ .proj₂) ⟩
◎-total (S= {B = B} inΩ) = ⟨ ◎-total inΩ .proj₁ ,= B , ◎S= (◎-total inΩ .proj₂) ⟩
◎-total (S, {A = A} inΩ) = ⟨ (◎-total inΩ .proj₁ , A) , ◎S, (◎-total inΩ .proj₂) ⟩

◎-∋= : Γ ◎ k ⇘ Γ'
     → Γ ∋= k
◎-∋= ◎Z = Z
◎-∋= (◎S∙ newΓ) = S∙ (◎-∋= newΓ)
◎-∋= (◎S= newΓ) = S= (◎-∋= newΓ)
◎-∋= (◎S^ newΓ) = S^ (◎-∋= newΓ)
◎-∋= (◎S, newΓ) = S, (◎-∋= newΓ)

◎-⊢r : Γ ⊢r A
     → Γ ◎ k ⇘ Γ'
     → Γ' ⊢r A
◎-⊢r ⊢r-int newΓ = ⊢r-int
◎-⊢r (⊢r-var-∙ inΓ) newΓ = ⊢r-var-∙ (◎-∋∙ inΓ newΓ)
◎-⊢r (⊢r-arr regA regA₁) newΓ = ⊢r-arr (◎-⊢r regA newΓ) (◎-⊢r regA₁ newΓ)
◎-⊢r (⊢r-∀ regA) newΓ = ⊢r-∀ (◎-⊢r regA (◎S∙ newΓ))

◎-sregular : SRegular Γ
           → Γ ◎ k ⇘ Γ'
           → SRegular Γ'
◎-sregular (reg-S∙ regΓ) (◎S∙ newΓ) = reg-S∙ (◎-sregular regΓ newΓ)
◎-sregular (reg-S^ regΓ) (◎S^ newΓ) = reg-S^ (◎-sregular regΓ newΓ)
◎-sregular (reg-S= regΓ regA) ◎Z = reg-S^ regΓ
◎-sregular (reg-S= regΓ regA) (◎S= newΓ) = reg-S= (◎-sregular regΓ newΓ) (◎-⊢r regA newΓ)

◎-unique : Γ ◎ k ⇘ Γ'
         → Γ ◎ k ⇘ Δ'
         → Γ' ≡ Δ'
◎-unique ◎Z ◎Z = refl
◎-unique (◎S∙ new1) (◎S∙ new2) = cong _,∙ (◎-unique new1 new2)
◎-unique (◎S= new1) (◎S= new2) = cong₂ _,=_ (◎-unique new1 new2) refl
◎-unique (◎S^ new1) (◎S^ new2) = cong _,^ (◎-unique new1 new2)
◎-unique (◎S, new1) (◎S, new2) = cong₂ _,_ (◎-unique new1 new2) refl

⊆/v-irrev-^^ : Γ ⊆ Δ w/v X
             → Γ ◎ k ⇘ Γ'
             → Δ ◎ k ⇘ Δ'
             → X ≢ k
             → Γ' ⊆ Δ' w/v X
⊆/v-irrev-^^ (ext-Z^ regΓ regA) (◎S^ newΓ) (◎S= newΔ) neq
  with refl ← ◎-unique newΓ newΔ = ext-Z^ (◎-sregular regΓ newΓ) (◎-⊢r regA newΓ)
⊆/v-irrev-^^ (ext-Z∙ regΓ) (◎S∙ newΓ) (◎S∙ newΔ) neq
  with refl ← ◎-unique newΓ newΔ = ext-Z∙ (◎-sregular regΓ newΓ)
⊆/v-irrev-^^ (ext-Z= regΓ regA) ◎Z newΔ neq = ⊥-elim (neq refl)
⊆/v-irrev-^^ (ext-Z= regΓ regA) (◎S= newΓ) (◎S= newΔ) neq
  with refl ← ◎-unique newΓ newΔ = ext-Z= (◎-sregular regΓ newΓ) (◎-⊢r regA newΓ)
⊆/v-irrev-^^ (ext-S^ ext) (◎S^ newΓ) (◎S^ newΔ) neq = ext-S^ (⊆/v-irrev-^^ ext newΓ newΔ (≢-pred neq))
⊆/v-irrev-^^ (ext-S∙ ext) (◎S∙ newΓ) (◎S∙ newΔ) neq = ext-S∙ (⊆/v-irrev-^^ ext newΓ newΔ (≢-pred neq))
⊆/v-irrev-^^ (ext-S= ext regA) ◎Z ◎Z neq = ext-S^ ext
⊆/v-irrev-^^ (ext-S= ext regA) (◎S= newΓ) (◎S= newΔ) neq = ext-S= (⊆/v-irrev-^^ ext newΓ newΔ (≢-pred neq)) (◎-⊢r regA newΓ)

⊆/-irrev-^^ : Γ ⊆ Δ w/t A
            → k ¬ε A
            → Γ ◎ k ⇘ Γ'
            → Δ ◎ k ⇘ Δ'
            → Γ' ⊆ Δ' w/t A
⊆/-irrev-^^ (ext-int x) ninA newΓ newΔ with refl ← ◎-unique newΓ newΔ = ⊆/-refl (◎-sregular x newΓ) ⊢c-int
⊆/-irrev-^^ (ext-var x) (¬ε-var x₁) newΓ newΔ = ext-var (⊆/v-irrev-^^ x newΓ newΔ x₁)
⊆/-irrev-^^ (ext-arr ext ext₁) (¬ε-arr ninA ninA₁) newΓ newΔ
  with ⟨ Ω' , ◎Ω ⟩ ← ◎-total (⊆/-=in-=out ext (◎-∋= newΓ)) = ext-arr (⊆/-irrev-^^ ext ninA newΓ ◎Ω) (⊆/-irrev-^^ ext₁ ninA₁ ◎Ω newΔ)
⊆/-irrev-^^ (ext-∀ ext) (¬ε-∀ ninA) newΓ newΔ = ext-∀ (⊆/-irrev-^^ ext ninA (◎S∙ newΓ) (◎S∙ newΔ))

⊆/-irrev-^^0 : Γ ,= B ⊆ Δ ,= B w/t A
             → #0 ¬ε A
             → Γ ,^ ⊆ Δ ,^ w/t A
⊆/-irrev-^^0 ext nin = ⊆/-irrev-^^ ext nin ◎Z ◎Z

⊆/v-irrev-^ : Γ ⊆ Δ w/v k
            → Γ ◎ k ⇘ Γ'
            → Γ' ⊆ Δ w/v k
⊆/v-irrev-^ (ext-Z= regΓ regA) ◎Z = ext-Z^ regΓ regA
⊆/v-irrev-^ (ext-S^ ext) (◎S^ newΓ) = ext-S^ (⊆/v-irrev-^ ext newΓ)
⊆/v-irrev-^ (ext-S∙ ext) (◎S∙ newΓ) = ext-S∙ (⊆/v-irrev-^ ext newΓ)
⊆/v-irrev-^ (ext-S= ext regA) (◎S= newΓ) = ext-S= (⊆/v-irrev-^ ext newΓ) (◎-⊢r regA newΓ)

⊆/-irrev-^ : Γ ⊆ Δ w/t A
           → k ε A
           → Γ ◎ k ⇘ Γ'
           → Γ' ⊆ Δ w/t A
⊆/-irrev-^ (ext-var x) ε-var newΓ = ext-var (⊆/v-irrev-^ x newΓ)
⊆/-irrev-^ (ext-arr ext ext₁) (ε-arr-l inA) newΓ = ext-arr (⊆/-irrev-^ ext inA newΓ) ext₁
⊆/-irrev-^ (ext-arr ext ext₁) (ε-arr-r x inA) newΓ
  with ⟨ Ω' , ◎Ω ⟩ ← ◎-total (⊆/-=in-=out ext (◎-∋= newΓ)) = ext-arr (⊆/-irrev-^^ ext x newΓ ◎Ω) (⊆/-irrev-^ ext₁ inA ◎Ω)
⊆/-irrev-^ (ext-∀ ext) (ε-∀ inA) newΓ = ext-∀ (⊆/-irrev-^ ext inA (◎S∙ newΓ))

⊆/c-irrev-^ : Γ ⊆ Δ w/t A w/c j
            → find A k j
            → Γ ◎ k ⇘ Γ'
            → Γ' ⊆ Δ w/t A w/c j
⊆/c-irrev-^ (⊆∞ ext) (f-∞ inA) x = ⊆∞ (⊆/-irrev-^ ext inA x)
⊆/c-irrev-^ (⊆Z regΓ cloA) fd newΓ = ⊥-elim (find-Z-false fd)
⊆/c-irrev-^ (⊆I ext ext₁) (f-arr-𝕚-l x) newΓ = ⊆I (⊆/-irrev-^ ext x newΓ) ext₁
⊆/c-irrev-^ (⊆I ext ext₁) (f-arr-𝕚-r ¬inA fd) newΓ
  with ⟨ Ω' , ◎Ω ⟩ ← ◎-total (⊆/-=in-=out ext (◎-∋= newΓ)) = ⊆I (⊆/-irrev-^^ ext ¬inA newΓ ◎Ω) (⊆/c-irrev-^ ext₁ fd ◎Ω)
⊆/c-irrev-^ (⊆C cloA ext) (f-arr-𝕔 ¬inA fd) newΓ = ⊆C (◎-⊢c cloA newΓ ¬inA) (⊆/c-irrev-^ ext fd newΓ)
⊆/c-irrev-^ (⊆∀-I ext upj') (f-∀-𝕚 fd upj) newΓ
  with refl ← ↑tyʲ-unique upj upj' = ⊆∀-I (⊆/c-irrev-^ ext fd (◎S^ newΓ)) upj'
⊆/c-irrev-^ (⊆∀-C ext upj') (f-∀-𝕔 fd upj) newΓ
  with refl ← ↑tyʲ-unique upj upj' = ⊆∀-C (⊆/c-irrev-^ ext fd (◎S^ newΓ)) upj'
⊆/c-irrev-^ (⊆∀-T ext upj) (f-𝕥 fd upj₁) newΓ
  with refl ← ↑tyʲ-unique upj upj₁ = ⊆∀-T (⊆/c-irrev-^ ext fd (◎S= newΓ)) upj
⊆/c-irrev-^ (⊆∀-I-no ext upj) (f-∀-𝕚 fd upj₁) newΓ
  with refl ← ↑tyʲ-unique upj upj₁ = ⊆∀-I-no (⊆/c-irrev-^ ext fd (◎S^ newΓ)) upj
⊆/c-irrev-^ (⊆∀-C-no ext upj) (f-∀-𝕔 fd upj₁) newΓ
  with refl ← ↑tyʲ-unique upj upj₁ = ⊆∀-C-no (⊆/c-irrev-^ ext fd (◎S^ newΓ)) upj
⊆/c-irrev-^ (⊆I-X regΓ cloA) (f-iso iso) newΓ = ⊆Inf-X (⊆/v-irrev-^ (⊆/x-refl regΓ cloA) newΓ) iso
⊆/c-irrev-^ (⊆C-X regΓ cloA) (f-iso ()) newΓ
⊆/c-irrev-^ (⊆T-X regΓ cloA) (f-iso ()) newΓ
⊆/c-irrev-^ (⊆Inf-X extx iso) (f-iso iso₁) newΓ = ⊆Inf-X (⊆/v-irrev-^ extx newΓ) iso
⊆/c-irrev-^ (⊆∞ regΓ) (f-iso ()) new
⊆/c-irrev-^ (⊆∀-I-new ext upj) (f-∀-𝕚 fd upj₁) new
  with refl ← ↑tyʲ-unique upj upj₁ = ⊆∀-I-new (⊆/c-irrev-^ ext fd (◎S= new)) upj
⊆/c-irrev-^ (⊆∀-C-new ext upj) (f-∀-𝕔 fd upj₁) new
  with refl ← ↑tyʲ-unique upj upj₁ = ⊆∀-C-new (⊆/c-irrev-^ ext fd (◎S= new)) upj

⊆/c-irrev-^0 : Γ ,= B ⊆ Δ ,= B w/t A w/c j
             → find A #0 j
             → Γ ,^ ⊆ Δ ,= B w/t A w/c j
⊆/c-irrev-^0 ext fd = ⊆/c-irrev-^ ext fd ◎Z
