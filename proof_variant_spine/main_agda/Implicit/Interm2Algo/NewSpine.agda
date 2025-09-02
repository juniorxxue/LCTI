module Implicit.Interm2Algo.NewSpine where

open import Implicit.Language.All
open import Implicit.Algo.All
open import Implicit.Interm.All

open import Implicit.Interm2Algo.Counter2Context
open import Implicit.Interm2Algo.ReExtension
open import Implicit.Interm2Algo.ExtIrrev
open import Implicit.Interm2Algo.EnvDiff
open import Implicit.Interm2Algo.OpenClose
open import Implicit.Interm2Algo.Find
open import Implicit.Interm2Algo.AuxLemmas



⊆/c-no-appear : Γ ⊆ Δ w/t A w/c j
              → Γ ∋^ k
              → Δ ∋^ k
              → k ¬ε A
⊆/c-no-appear (⊆Z regΓ cloA) in1 in2 = ⊢c-^∈-¬ε cloA in2
⊆/c-no-appear (⊆∞ ext) in1 in2 = ^in-^out-¬ε ext in1 in2
⊆/c-no-appear (⊆I ext ext₁) in1 in2
  with inΩ ← ⊆-∋^-middle in1 in2 (⊆/-⊆ ext) (⊆/c-⊆ ext₁)
  = ¬ε-arr (^in-^out-¬ε ext in1 inΩ) (⊆/c-no-appear ext₁ inΩ in2)
⊆/c-no-appear (⊆C cloA ext) in1 in2 = ¬ε-arr (⊢c-^∈-¬ε cloA in1) (⊆/c-no-appear ext in1 in2)
⊆/c-no-appear (⊆∀-I ext upj) in1 in2 = ¬ε-∀ (⊆/c-no-appear ext (S^ in1) (S= in2))
⊆/c-no-appear (⊆∀-I-new ext upj) in1 in2 = ¬ε-∀ (⊆/c-no-appear ext (S= in1) (S= in2))
⊆/c-no-appear (⊆∀-C-new ext upj) in1 in2 = ¬ε-∀ (⊆/c-no-appear ext (S= in1) (S= in2))
⊆/c-no-appear (⊆∀-I-no ext upj) in1 in2 = ¬ε-∀ (⊆/c-no-appear ext (S^ in1) (S^ in2))
⊆/c-no-appear (⊆∀-C ext upj) in1 in2 = ¬ε-∀ (⊆/c-no-appear ext (S^ in1) (S= in2))
⊆/c-no-appear (⊆∀-C-no ext upj) in1 in2 = ¬ε-∀ (⊆/c-no-appear ext (S^ in1) (S^ in2))
⊆/c-no-appear (⊆∀-T ext upj) in1 in2 = ¬ε-∀ (⊆/c-no-appear ext (S= in1) (S= in2))
⊆/c-no-appear (⊆I-X regΓ cloA) in1 in2 = ⊢c-^∈-¬ε cloA in2
⊆/c-no-appear (⊆C-X regΓ cloA) in1 in2 = ⊢c-^∈-¬ε cloA in2
⊆/c-no-appear (⊆T-X regΓ cloA) in1 in2 = ⊢c-^∈-¬ε cloA in2
⊆/c-no-appear (⊆Inf-X extx iso) in1 in2 = ⊢c-^∈-¬ε (⊆/x-⊢c extx) in2

data peek-a : Type m → Type m → Fin m → Counter m → Type m → Set where
  pka-∞ : A ~~pk~~ B w/ k ↪ C
        → peek-a A B k ∞ C
  pka-arr-𝕚 : peek-a B D k j E
            → peek-a (A `→ B) (C `→ D) k (𝕚 j) E
  pka-arr-𝕔 : peek-a B D k j E
            → peek-a (A `→ B) (C `→ D) k (𝕔 j) E
  pka-∀-𝕚 : peek-a A (C' `→ D') (#S k) (𝕚 j') E'
          → (upC : ↑ty0 C ⇘ C')
          → (upD : ↑ty0 D ⇘ D')
          → (upE : ↑ty0 E ⇘ E')
          → (upj : ↑tyʲ0 j ⇘ j')
          → peek-a (`∀ A) (C `→ D) k (𝕚 j) E
  pka-∀-𝕔 : peek-a A (C' `→ D') (#S k) (𝕔 j') E'
          → (upC : ↑ty0 C ⇘ C')
          → (upD : ↑ty0 D ⇘ D')
          → (upE : ↑ty0 E ⇘ E')
          → (upj : ↑tyʲ0 j ⇘ j')
          → peek-a (`∀ A) (C `→ D) k (𝕔 j) E
  pka-∀-𝕥 : peek-a A B (#S k) j' E'
          → (upB : ↑ty0 E ⇘ E')
          → (upj : ↑tyʲ0 j ⇘ j')
          → peek-a (`∀ A) (`∀ B) k (𝕥₍ T ₎ j) E




peek→peek-t- : Γ ⊢ ∞ # A ⌞ ≤⁻ ⌝ B
            → Γ ∋ k := T
            → k ε B
            → B ~~pk~~ A w/ k ↪ T

peek→peek-t : Γ ⊢ ∞ # A ⌞ ≤⁺ ⌝ B
            → Γ ∋ k := T
            → k ε A
            → A ~~pk~~ B w/ k ↪ T

peek→peek-t- (s-var-∙ regΔ inΔ) inΓ ε-var = ⊥-elim (∋∙-∋:=-false inΔ inΓ)
peek→peek-t- (s-arr₁ s s₁) inΓ (ε-arr-l inB) = pk-arr-l (peek→peek-t s inΓ inB)
peek→peek-t- (s-arr₁ s s₁) inΓ (ε-arr-r ¬inA inB) = pk-arr-r (peek→peek-t- s₁ inΓ inB)
peek→peek-t- {T = T} (s-∀ s) inΓ (ε-∀ inB)
  with ⟨ T' , upT ⟩ ← ↑ty0-total T
  = pk-∀ (peek→peek-t- s (S∙ inΓ upT) inB) upT
peek→peek-t- (s-svar-r x inΔ) inΓ ε-var
  with refl ← ∋:=-unique inΓ inΔ
  = pk-var-l

peek→peek-t (s-var-∙ regΔ inΔ) inΓ ε-var = ⊥-elim (∋∙-∋:=-false inΔ inΓ)
peek→peek-t (s-arr₁ s s₁) inΓ (ε-arr-l inA) = pk-arr-l (peek→peek-t- s inΓ inA)
peek→peek-t (s-arr₁ s s₁) inΓ (ε-arr-r ¬inA inA) = pk-arr-r (peek→peek-t s₁ inΓ inA)
peek→peek-t {T = T} (s-∀ s) inΓ (ε-∀ inA)
  with ⟨ T' , upT ⟩ ← ↑ty0-total T
  = pk-∀ (peek→peek-t s (S∙ inΓ upT) inA) upT
peek→peek-t (s-svar-l x inΔ) inΓ ε-var
  with refl ← ∋:=-unique inΓ inΔ = pk-var-l

peek→peek-a : Γ ⊢ j # A ⌞ ≤⁺ ⌝ B
            → peek A k j
            → Γ ∋ k := T
            → peek-a A B k j T
peek→peek-a s (peek-base inA) inΓ = pka-∞ (peek→peek-t s inΓ inA)
peek→peek-a (s-arr₂ s s₁) (peek-arr-i pk) inΓ = pka-arr-𝕚 (peek→peek-a s₁ pk inΓ)
peek→peek-a (s-arr₃ cloA grd s) (peek-arr-c pk) inΓ = pka-arr-𝕔 (peek→peek-a s pk inΓ)
-- case peek-∀-i
peek→peek-a {T = T} (s-∀l-new s ic fd upC upD (↑tyʲ-𝕚 upj₁)) (peek-∀-i pk upj) inΓ
  with refl ← ↑tyʲ-unique upj upj₁
  with ⟨ T' , upT ⟩ ← ↑ty0-total T
  = pka-∀-𝕚 (peek→peek-a s pk (S= inΓ upT)) upC upD upT upj₁
peek→peek-a {T = T} (s-∀l-peek s ic pk₁ upC upD (↑tyʲ-𝕚 upj₁)) (peek-∀-i pk upj) inΓ
  with refl ← ↑tyʲ-unique upj upj₁
  with ⟨ T' , upT ⟩ ← ↑ty0-total T
  = pka-∀-𝕚 (peek→peek-a s pk (S= inΓ upT)) upC upD upT upj₁
peek→peek-a {T = T} (s-∀l-no-appear s ic fd upC upD (↑tyʲ-𝕚 upj₁)) (peek-∀-i pk upj) inΓ
  with refl ← ↑tyʲ-unique upj upj₁
  with ⟨ T' , upT ⟩ ← ↑ty0-total T
  = pka-∀-𝕚 (peek→peek-a s pk (S^ inΓ upT)) upC upD upT upj₁
-- case peek-∀-c
peek→peek-a {T = T} (s-∀l-new s ic fd upC upD (↑tyʲ-𝕔 upj₁)) (peek-∀-c pk upj) inΓ
  with refl ← ↑tyʲ-unique upj upj₁
  with ⟨ T' , upT ⟩ ← ↑ty0-total T
  = pka-∀-𝕔 (peek→peek-a s pk (S= inΓ upT)) upC upD upT upj₁
peek→peek-a {T = T} (s-∀l-peek s ic pk₁ upC upD (↑tyʲ-𝕔 upj₁)) (peek-∀-c pk upj) inΓ
  with refl ← ↑tyʲ-unique upj upj₁
  with ⟨ T' , upT ⟩ ← ↑ty0-total T
  = pka-∀-𝕔 (peek→peek-a s pk (S= inΓ upT)) upC upD upT upj₁
peek→peek-a {T = T} (s-∀l-no-appear s ic fd upC upD (↑tyʲ-𝕔 upj₁)) (peek-∀-c pk upj) inΓ
  with refl ← ↑tyʲ-unique upj upj₁
  with ⟨ T' , upT ⟩ ← ↑ty0-total T
  = pka-∀-𝕔 (peek→peek-a s pk (S^ inΓ upT)) upC upD upT upj₁
-- case peek-∀-t
peek→peek-a {T = T} (s-tapp s upj) (peek-∀-t pk upj₁) inΓ
  with refl ← ↑tyʲ-unique upj upj₁
  with ⟨ T' , upT ⟩ ← ↑ty0-total T
  = pka-∀-𝕥 (peek→peek-a s pk (S= inΓ upT)) upT upj

peek-a-~pk~ : peek-a A B k j C
            → Γ ⊢ ⟨ j , B ⟩ ~s Σ
            → A ~pk~ Σ w/ k ↪ C
peek-a-~pk~ (pka-∞ x) ~∞ = pk-type x
peek-a-~pk~ (pka-arr-𝕚 pka) (~I ⊢e ~j) = pk-term (peek-a-~pk~ pka ~j)
peek-a-~pk~ (pka-arr-𝕔 pka) (~C ⊢e ~j) = pk-term (peek-a-~pk~ pka ~j)
peek-a-~pk~ (pka-∀-𝕚 pka upC upD upE upj) ~j'@(~I {Σ = Σ} {e = e} ⊢e ~j)
  with ⟨ Σ' , upΣ ⟩ ← ↑tyᶜ0-total Σ
  with ⟨ e' , up-e ⟩ ← ↑tyᵉ0-total e
  = pk-∀l (peek-a-~pk~ pka (~weaken^0 ~j' (↑ty-arr upC upD) (↑tyᶜ-e up-e upΣ) (↑tyʲ-𝕚 upj))) upΣ up-e upE
peek-a-~pk~ (pka-∀-𝕔 pka upC upD upE upj) ~j'@(~C {Σ = Σ} {e = e} ⊢e ~j)
  with ⟨ Σ' , upΣ ⟩ ← ↑tyᶜ0-total Σ
  with ⟨ e' , up-e ⟩ ← ↑tyᵉ0-total e
  = pk-∀l (peek-a-~pk~ pka (~weaken^0 ~j' (↑ty-arr upC upD) (↑tyᶜ-e up-e upΣ) (↑tyʲ-𝕔 upj))) upΣ up-e upE
peek-a-~pk~ (pka-∀-𝕥 pka upB upj) (~T {Σ = Σ} ~j st)
  with ⟨ Σ' , upΣ ⟩ ← ↑tyᶜ0-total Σ
  = pk-tapp (peek-a-~pk~ pka (~weaken^0 ~j st upΣ upj)) upB upΣ


¬ε-¬pk : k ¬ε A
       → A ~pk~ Σ w/ k
       → ⊥
¬ε-¬pk ¬ε-int (pk-type ())
¬ε-¬pk (¬ε-var x) (pk-type ε-var) = x refl
¬ε-¬pk (¬ε-arr inA inA₁) (pk-type (ε-arr-l inA₂)) = ε-¬ε-false inA₂ inA
¬ε-¬pk (¬ε-arr inA inA₁) (pk-type (ε-arr-r ¬inA inA₂)) = ε-¬ε-false inA₂ inA₁
¬ε-¬pk (¬ε-arr inA inA₁) (pk-term pk) = ¬ε-¬pk inA₁ pk
¬ε-¬pk (¬ε-∀ inA) (pk-type (ε-∀ inA₁)) = ε-¬ε-false inA₁ inA
¬ε-¬pk (¬ε-∀ inA) (pk-∀l pk upΣ upe) = ¬ε-¬pk inA pk
¬ε-¬pk (¬ε-∀ inA) (pk-tapp pk upΣ) = ¬ε-¬pk inA pk


id-↑ty' : Id Σ A
       → Σ ↑tyᶜ k ⇘ Σ'
       → A ↑ty k ⇘ A'
       → Id Σ' A'
id-↑ty' id-□ ↑tyᶜ-□ upA = id-□
id-↑ty' id-τ (↑tyᶜ-τ up-t) upA
  with refl ← ↑ty-unique up-t upA = id-τ
id-↑ty' (id-e id₁) (↑tyᶜ-e up-e upΣ) (↑ty-arr upA upA₁) = id-e (id-↑ty' id₁ upΣ upA₁)
id-↑ty' {k = k} (id-⓪ {B = B} id₁ up) (↑tyᶜ-⓪ upA₁ upΣ) (↑ty-∀ upA)
  with ⟨ B' , upB ⟩ ← ↑ty-total B k
  = id-⓪ (id-↑ty' id₁ upΣ upB) (↑ty-comm0 up upA upB)


pk'~-tail-eq : A ~~pk~~ B w/ k ↪ T₁
             → A ≤ B ⟹ T₂
             → k ε' A
             → T₁ ≡ T₂
pk'~-tail-eq pk-var-l ett-var ε-var = refl
pk'~-tail-eq (pk-arr-l pk) (ett-arr tl) (ε-arr x inA) = ⊥-elim (ε-¬ε-false (pk-ε pk) x)
pk'~-tail-eq (pk-arr-r pk) (ett-arr tl) (ε-arr x inA) = pk'~-tail-eq pk tl inA
pk'~-tail-eq (pk-∀ pk upC) (ett-∀-𝕥 tl upT) (ε-∀ inA)
  with refl ← pk'~-tail-eq pk tl inA = ↑ty-unique-inver upC upT

pk-tail-eq : A ~pk~ Σ w/ k ↪ T₁
           → A ≤ B ⟹ T₂
           → k ε' A
           → Id Σ B
           → T₁ ≡ T₂
pk-tail-eq (pk-type x) tl inA id-τ = pk'~-tail-eq x tl inA
pk-tail-eq (pk-term pk) (ett-arr tl) (ε-arr x inA) (id-e id₁) = pk-tail-eq pk tl inA id₁
pk-tail-eq (pk-∀l pk upΣ upe upC) (ett-∀-𝕚 tl upB upC₁ upT) (ε-∀ inA) (id-e id₁)
  with refl ← pk-tail-eq pk tl inA (id-e (id-↑ty' id₁ upΣ upC₁)) = ↑ty-unique-inver upC upT
pk-tail-eq (pk-tapp pk upC upΣ) (ett-∀-𝕥 tl upT) (ε-∀ inA) (id-⓪ id₁ up)
  with refl ← pk-tail-eq pk tl inA (id-↑ty' id₁ upΣ up) = ↑ty-unique-inver upC upT

peek-ε-gen : peek A k j
           → k ε A
peek-ε-gen (peek-base inA) = inA
peek-ε-gen {k = k} (peek-arr-i {A = A} pk) with ε-dec {k = k} {A = A}
... | inj₁ x = ε-arr-l x
... | inj₂ y = ε-arr-r y (peek-ε-gen pk)
peek-ε-gen {k = k} (peek-arr-c {A = A} pk) with ε-dec {k = k} {A = A}
... | inj₁ x = ε-arr-l x
... | inj₂ y = ε-arr-r y (peek-ε-gen pk)
peek-ε-gen (peek-∀-i pk upj) = ε-∀ (peek-ε-gen pk)
peek-ε-gen (peek-∀-c pk upj) = ε-∀ (peek-ε-gen pk)
peek-ε-gen (peek-∀-t pk upj) = ε-∀ (peek-ε-gen pk)
