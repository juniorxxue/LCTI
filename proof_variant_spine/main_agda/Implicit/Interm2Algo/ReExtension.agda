module Implicit.Interm2Algo.ReExtension where
-- ExtIrrev is the direct follow-up module of this module

open import Implicit.Language.All

infix 3 _⊆_w/t_w/c_
data _⊆_w/t_w/c_ : Env n m → Env n m → Type m → Counter m → Set where
  ⊆Z : (regΓ : SRegular Γ)
     → Γ ⊆ Γ w/t A w/c Z
  ⊆∞ : (ext : Γ ⊆ Δ w/t A)
     → Γ ⊆ Δ w/t A w/c ∞
  ⊆I : (ext : Γ ⊆ Ω w/t A)
     → Ω ⊆ Δ w/t B w/c j
     → Γ ⊆ Δ w/t (A `→ B) w/c (𝕚 j)
  ⊆C : (cloA : Γ ⊢c A)
     → Γ ⊆ Δ w/t B w/c j
     → Γ ⊆ Δ w/t (A `→ B) w/c (𝕔 j)
  ⊆∀-I : Γ ,^ ⊆ Δ ,= B w/t A w/c (𝕚 j')
       → (upj : ↑tyʲ0 j ⇘ j')
       → Γ ⊆ Δ w/t `∀ A w/c (𝕚 j)
  ⊆∀-I-new : Γ ,= B ⊆ Δ ,= B w/t A w/c (𝕚 j')
       → (upj : ↑tyʲ0 j ⇘ j')
       → Γ ⊆ Δ w/t `∀ A w/c (𝕚 j)
  ⊆∀-C-new : Γ ,= B ⊆ Δ ,= B w/t A w/c (𝕔 j')
       → (upj : ↑tyʲ0 j ⇘ j')
       → Γ ⊆ Δ w/t `∀ A w/c (𝕔 j)
  ⊆∀-I-no : Γ ,^ ⊆ Δ ,^ w/t A w/c (𝕚 j')
       → (upj : ↑tyʲ0 j ⇘ j')
       → Γ ⊆ Δ w/t `∀ A w/c (𝕚 j)
  ⊆∀-C : Γ ,^ ⊆ Δ ,= B w/t A w/c (𝕔 j')
       → (upj : ↑tyʲ0 j ⇘ j')
       → Γ ⊆ Δ w/t `∀ A w/c (𝕔 j)
  ⊆∀-C-no : Γ ,^ ⊆ Δ ,^ w/t A w/c (𝕔 j')
       → (upj : ↑tyʲ0 j ⇘ j')
       → Γ ⊆ Δ w/t `∀ A w/c (𝕔 j)
  ⊆∀-T : Γ ,= B ⊆ Δ ,= B w/t A w/c j'
       → (upj : ↑tyʲ0 j ⇘ j')
       → Γ ⊆ Δ w/t `∀ A w/c 𝕥₍ B ₎ j
  ⊆I-X : (regΓ : SRegular Δ)
       → (cloA : Δ ⊢c (‶ X))
       → Δ ⊆ Δ w/t ‶ X w/c 𝕚 j
  ⊆C-X : (regΓ : SRegular Δ)
       → (cloA : Δ ⊢c (‶ X))
       → Δ ⊆ Δ w/t ‶ X w/c 𝕔 j
  ⊆T-X : (regΓ : SRegular Δ)
       → (cloA : Δ ⊢c (‶ X))
       → Δ ⊆ Δ w/t ‶ X w/c 𝕥₍ A ₎ j
  ⊆Inf-X : (extx : Γ ⊆ Δ w/v X)
         → (iso : IsoInf (𝕚 j))
         → Γ ⊆ Δ w/t ‶ X w/c 𝕚 j



⊆/c-⊆ : Γ ⊆ Δ w/t A w/c j
      → Γ ⊆ Δ
⊆/c-⊆ (⊆Z regΓ) = ⊆-refl regΓ
⊆/c-⊆ (⊆I ext ext₁) = ⊆-trans (⊆/-⊆ ext) (⊆/c-⊆ ext₁)
⊆/c-⊆ (⊆C x ext) = ⊆/c-⊆ ext
⊆/c-⊆ (⊆∀-I ext upj) with ⊆/c-⊆ ext
... | evar-sol r regA = r
⊆/c-⊆ (⊆∀-C ext upj) with ⊆/c-⊆ ext
... | evar-sol r regA = r
⊆/c-⊆ (⊆∀-I-no ext upj) with ⊆/c-⊆ ext
... | evar r = r
⊆/c-⊆ (⊆∀-C-no ext upj) with ⊆/c-⊆ ext
... | evar r = r
⊆/c-⊆ (⊆∀-T ext upj) with ⊆/c-⊆ ext
... | svar r regA = r
⊆/c-⊆ (⊆I-X regΓ cloA) = ⊆-refl regΓ
⊆/c-⊆ (⊆C-X regΓ cloA) = ⊆-refl regΓ
⊆/c-⊆ (⊆T-X regΓ cloA) = ⊆-refl regΓ
⊆/c-⊆ (⊆Inf-X extx iso) = ⊆/x-⊆ extx
⊆/c-⊆ (⊆∞ ext) = ⊆/-⊆ ext
⊆/c-⊆ (⊆∀-I-new ext upj) with ⊆/c-⊆ ext
... | svar r regA = r
⊆/c-⊆ (⊆∀-C-new ext upj) with ⊆/c-⊆ ext
... | svar r regA = r


⊆/c-find : Γ ⊆ Δ w/t A w/c j
         → Γ ∋^ k
         → Δ ∋= k
         → find A k j
⊆/c-find (⊆Z regΓ) in1 in2 = ⊥-elim (∋^-∋=-false in1 in2)
⊆/c-find {A = A `→ B} {k = k} (⊆I ext ext₁) in1 in2 with ε-dec {k = k} {A}
... | inj₁ p = f-arr-𝕚-l p
... | inj₂ ¬p = f-arr-𝕚-r ¬p (⊆/c-find ext₁ (⊆/-^in-^out ext ¬p in1) in2)
⊆/c-find (⊆C cloA ext) in1 in2 = f-arr-𝕔 (⊢c-^∈-¬ε cloA in1) (⊆/c-find ext in1 in2)
⊆/c-find (⊆∀-I ext upj) in1 in2 = f-∀-𝕚 (⊆/c-find ext (S^ in1) (S= in2)) upj
⊆/c-find (⊆∀-I-no ext upj) in1 in2 = f-∀-𝕚 (⊆/c-find ext (S^ in1) (S^ in2)) upj
⊆/c-find (⊆∀-C ext upj) in1 in2 = f-∀-𝕔 (⊆/c-find ext (S^ in1) (S= in2)) upj
⊆/c-find (⊆∀-C-no ext upj) in1 in2 = f-∀-𝕔 (⊆/c-find ext (S^ in1) (S^ in2)) upj
⊆/c-find (⊆∀-T ext upj) in1 in2 = f-𝕥 (⊆/c-find ext (S= in1) (S= in2)) upj
⊆/c-find (⊆I-X regΓ cloA) in1 in2 = ⊥-elim (∋^-∋=-false in1 in2)
⊆/c-find (⊆C-X regΓ cloA) in1 in2 = ⊥-elim (∋^-∋=-false in1 in2)
⊆/c-find (⊆T-X regΓ cloA) in1 in2 = ⊥-elim (∋^-∋=-false in1 in2)
⊆/c-find (⊆Inf-X extx iso) in1 in2
  with ε-var ← ^in-=out-ε (ext-var extx) in1 in2 = f-iso iso
⊆/c-find (⊆∞ ext) x x₁ = f-∞ (^in-=out-ε ext x x₁)
⊆/c-find (⊆∀-I-new x₂ upj) x x₁ = f-∀-𝕚 (⊆/c-find x₂ (S= x) (S= x₁)) upj
⊆/c-find (⊆∀-C-new x₂ upj) x x₁ = f-∀-𝕔 (⊆/c-find x₂ (S= x) (S= x₁)) upj

⊆/c-find0 : Γ ,^ ⊆ Δ ,= B w/t A w/c j
          → find A #0 j
⊆/c-find0 ext = ⊆/c-find ext Z Z


⊆/c-find-∋= : Γ ⊆ Δ w/t A w/c j
              → Γ ∋^ k
              → find A k j
              → Δ ∋= k
⊆/c-find-∋= (⊆∞ ext) inΓ (f-∞ inA) = ⊆/-^in-=out ext inA inΓ
⊆/c-find-∋= (⊆I ext ext₁) inΓ (f-arr-𝕚-l x) = ⊆-∋= (⊆/-^in-=out ext x inΓ) (⊆/c-⊆ ext₁)
⊆/c-find-∋= (⊆I ext ext₁) inΓ (f-arr-𝕚-r ¬inA fd) = ⊆/c-find-∋= ext₁ (⊆/-^in-^out ext ¬inA inΓ) fd
⊆/c-find-∋= (⊆C cloA ext) inΓ (f-arr-𝕔 ¬inA fd) = ⊆/c-find-∋= ext inΓ fd
⊆/c-find-∋= (⊆∀-I ext upj) inΓ (f-∀-𝕚 fd upj₁)
  with refl ← ↑tyʲ-unique upj upj₁
  with S= r ← ⊆/c-find-∋= ext (S^ inΓ) fd = r
⊆/c-find-∋= (⊆∀-I-no ext upj) inΓ (f-∀-𝕚 fd upj₁)
  with refl ← ↑tyʲ-unique upj upj₁
  with S^ r ← ⊆/c-find-∋= ext (S^ inΓ) fd = r
⊆/c-find-∋= (⊆∀-C ext upj) inΓ (f-∀-𝕔 fd upj₁)
  with refl ← ↑tyʲ-unique upj upj₁
  with S= r ← ⊆/c-find-∋= ext (S^ inΓ) fd = r
⊆/c-find-∋= (⊆∀-C-no ext upj) inΓ (f-∀-𝕔 fd upj₁)
  with refl ← ↑tyʲ-unique upj upj₁
  with S^ r ← ⊆/c-find-∋= ext (S^ inΓ) fd = r
⊆/c-find-∋= (⊆∀-T ext upj) inΓ (f-𝕥 fd upj₁)
  with refl ← ↑tyʲ-unique upj upj₁
  with S= r ← ⊆/c-find-∋= ext (S= inΓ) fd = r
⊆/c-find-∋= (⊆I-X regΓ cloA) inΓ (f-iso iso) = ⊥-elim (⊢c-^∈-false ε-var inΓ cloA)
⊆/c-find-∋= (⊆Inf-X extx iso₁) inΓ (f-iso iso) = ⊆/x-^in-=out extx inΓ
⊆/c-find-∋= (⊆∀-I-new ext upj) inΓ (f-∀-𝕚 fd upj₁)
  with refl ← ↑tyʲ-unique upj upj₁
  with S= r ← ⊆/c-find-∋= ext (S= inΓ) fd
  = r
⊆/c-find-∋= (⊆∀-C-new ext upj) inΓ (f-∀-𝕔 fd upj₁)
  with refl ← ↑tyʲ-unique upj upj₁
  with S= r ← ⊆/c-find-∋= ext (S= inΓ) fd
  = r
⊆/c-find-∋= (⊆Z regΓ) inΓ (f-iso ())
⊆/c-find-∋= (⊆C-X regΓ cloA) inΓ (f-iso ())
⊆/c-find-∋= (⊆T-X regΓ cloA) inΓ (f-iso ())



=⟹-unique : [ B / k ] Γ =⟹ Γ'
          → [ B / k ] Γ =⟹ Δ'
          → Γ' ≡ Δ'
=⟹-unique (=⟹=0 up regA regΓ) (=⟹=0 up₁ regA' regΓ') rewrite ↑ty-unique-inver up up₁ = refl
=⟹-unique (=⟹^S inst1 up1) (=⟹^S inst2 up2) rewrite ↑ty-unique-inver up1 up2 = cong _,^ (=⟹-unique inst1 inst2)
=⟹-unique (=⟹∙S inst1 up1) (=⟹∙S inst2 up2) rewrite ↑ty-unique-inver up1 up2 = cong _,∙ (=⟹-unique inst1 inst2)
=⟹-unique (=⟹=S inst1 up1 regB) (=⟹=S inst2 up2 regB') rewrite ↑ty-unique-inver up1 up2 = cong₂ _,=_ (=⟹-unique inst1 inst2) refl

=⟹-∋∙ : Γ ∋∙ X
      → [ A / k ] Γ =⟹ Γ'
      → Γ' ∋∙ X
=⟹-∋∙ Z (=⟹∙S inst up1) = Z
=⟹-∋∙ (S∙ inΓ) (=⟹∙S inst up1) = S∙ (=⟹-∋∙ inΓ inst)
=⟹-∋∙ (S= inΓ) (=⟹=0 up regA env) = S= inΓ
=⟹-∋∙ (S= inΓ) (=⟹=S inst up1 regB) = S= (=⟹-∋∙ inΓ inst)
=⟹-∋∙ (S^ inΓ) (=⟹^S inst up1) = S^ (=⟹-∋∙ inΓ inst)

=⟹-∋=-prv : Γ ∋= X
          → [ A / k ] Γ =⟹ Γ'
          → Γ' ∋= X
=⟹-∋=-prv Z (=⟹=0 up regA env) = Z
=⟹-∋=-prv Z (=⟹=S inst up1 regB) = Z
=⟹-∋=-prv (S∙ inΓ) (=⟹∙S inst up1) = S∙ (=⟹-∋=-prv inΓ inst)
=⟹-∋=-prv (S^ inΓ) (=⟹^S inst up1) = S^ (=⟹-∋=-prv inΓ inst)
=⟹-∋=-prv (S= inΓ) (=⟹=0 up regA env) = S= inΓ
=⟹-∋=-prv (S= inΓ) (=⟹=S inst up1 regB) = S= (=⟹-∋=-prv inΓ inst)

=⟹-⊢r :  Γ ⊢r B
      → [ A / k ] Γ =⟹ Γ'
      → Γ' ⊢r B
=⟹-⊢r ⊢r-int inst = ⊢r-int
=⟹-⊢r (⊢r-var-∙ inΓ) inst = ⊢r-var-∙ (=⟹-∋∙ inΓ inst)
=⟹-⊢r (⊢r-arr regB regB₁) inst = ⊢r-arr (=⟹-⊢r regB inst) (=⟹-⊢r regB₁ inst)
=⟹-⊢r {A = A} (⊢r-∀ regB) inst = ⊢r-∀ (=⟹-⊢r regB (=⟹∙S inst (proj₂ (↑ty0-total A))))

=⟹-⊢c : Γ ⊢c B
      → [ A / k ] Γ =⟹ Γ'
      → Γ' ⊢c B
=⟹-⊢c ⊢c-int inst = ⊢c-int
=⟹-⊢c (⊢c-var-∙ inΔ) inst = ⊢c-var-∙ (=⟹-∋∙ inΔ inst)
=⟹-⊢c (⊢c-var-= inΔ) inst = ⊢c-var-= (=⟹-∋=-prv inΔ inst)
=⟹-⊢c (⊢c-arr cloB cloB₁) inst = ⊢c-arr (=⟹-⊢c cloB inst) (=⟹-⊢c cloB₁ inst)
=⟹-⊢c {A = A} (⊢c-∀ cloB) inst = ⊢c-∀ (=⟹-⊢c cloB (=⟹∙S inst (proj₂ (↑ty0-total A))))

=⟹-sregular : [ B / k ] Γ =⟹ Γ'
            → SRegular Γ'
=⟹-sregular (=⟹=0 up regA env) = reg-S= env regA
=⟹-sregular (=⟹^S inst up1) = reg-S^ (=⟹-sregular inst)
=⟹-sregular (=⟹∙S inst up1) = reg-S∙ (=⟹-sregular inst)
=⟹-sregular (=⟹=S inst up1 regB) = reg-S= (=⟹-sregular inst) (=⟹-⊢r regB inst)


----------------------------------------------------------------------
--+                              inst                              +--
----------------------------------------------------------------------

⊆/x-^in-=out-inst : Γ ∋^ X
                → Δ ∋ X := A
                        → Γ ⊆ Δ w/v X
                        → [ A / X ] Γ ⟹ Δ
⊆/x-^in-=out-inst Z (Z up) (ext-Z^ regΓ regA) = ⟹^0 up regA regΓ
⊆/x-^in-=out-inst (S∙ inΓ) (S∙ inΔ up) (ext-S∙ ext) = ⟹∙S (⊆/x-^in-=out-inst inΓ inΔ ext) up
⊆/x-^in-=out-inst (S= inΓ) (S= inΔ up) (ext-S= ext regA) = ⟹=S (⊆/x-^in-=out-inst inΓ inΔ ext) up regA
⊆/x-^in-=out-inst (S^ inΓ) (S^ inΔ up) (ext-S^ ext) = ⟹^S (⊆/x-^in-=out-inst inΓ inΔ ext) up
