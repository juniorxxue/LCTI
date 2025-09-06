module Implicit.Interm2Algo.AuxLemmas where

open import Implicit.Language.All
open import Implicit.Algo.All
open import Implicit.Interm.All

open import Implicit.Interm2Algo.Counter2Context
open import Implicit.Interm2Algo.ReExtension
open import Implicit.Interm2Algo.ExtIrrev
open import Implicit.Interm2Algo.EnvDiff
open import Implicit.Interm2Algo.OpenClose
open import Implicit.Interm2Algo.Find


s--⊆/ : Δ ⊢ ∞ # A ⌞ ≤⁻ ⌝ B
      → Δ ⊆ Δ w/t B
s--⊆/ s = ⊆/-refl (s-sregular s) (s-⊢c-r s)

s+-⊆/ : Δ ⊢ j # A ⌞ ≤⁺ ⌝ B
      → Δ ⊆ Δ w/t A w/c j

s+-⊆/ (s-refl regΔ cloA grd) = (⊆Z regΔ cloA)
s+-⊆/ (s-int regΔ) = ⊆∞ (ext-int regΔ)
s+-⊆/ (s-var-∙ regΔ inΔ) = ⊆∞ (ext-var ((reg-⊆/x∙ regΔ inΔ)))
s+-⊆/ (s-arr₁ s s₁) with s+-⊆/ s₁
... | ⊆∞ regΓ = ⊆∞ (ext-arr (s--⊆/ s) regΓ)
s+-⊆/ (s-arr₂ s s₁) = ⊆I (s--⊆/ s) (s+-⊆/ s₁)
s+-⊆/ (s-arr₃ cloA grd s) = ⊆C cloA (s+-⊆/ s)
s+-⊆/ (s-∀ s) with s+-⊆/ s
... | ⊆∞ ext = ⊆∞ (ext-∀ ext)
s+-⊆/ (s-∀l-no-appear s ic fd upC upD upj) with s+-⊆/ s
s+-⊆/ (s-∀l-no-appear s case-𝕚 fd upC upD (↑tyʲ-𝕚 upj)) | r = ⊆∀-I-no r upj
s+-⊆/ (s-∀l-no-appear s case-𝕔 fd upC upD (↑tyʲ-𝕔 upj)) | r = ⊆∀-C-no r upj
s+-⊆/ (s-svar-l x inΔ) = ⊆∞ ((ext-var (⊆/x-refl x (⊢c-var-= (∋:=to∋= inΔ)))))
s+-⊆/ (s-tapp s upj) = ⊆∀-T (s+-⊆/ s) upj
s+-⊆/ (s-svar-𝕚 inΓ s) = ⊆I-X (s-sregular s) (⊢c-var-= (∋:=to∋= inΓ))
s+-⊆/ (s-svar-𝕔 inΓ s) = ⊆C-X (s-sregular s) (⊢c-var-= (∋:=to∋= inΓ))
s+-⊆/ (s-svar-𝕥 inΓ s) = ⊆T-X (s-sregular s) (⊢c-var-= (∋:=to∋= inΓ))
s+-⊆/ (s-∀l-peek x ic pk upC upD upj) with s+-⊆/ x
s+-⊆/ (s-∀l-peek x case-𝕚 pk upC upD (↑tyʲ-𝕚 upj)) | r = ⊆∀-I-new r upj
s+-⊆/ (s-∀l-peek x case-𝕔 pk upC upD (↑tyʲ-𝕔 upj)) | r = ⊆∀-C-new r upj
s+-⊆/ (s-∀l x case-𝕚 fd upC upD (↑tyʲ-𝕚 upj)) with s+-⊆/ x
... | r = ⊆∀-I-new r upj
s+-⊆/ (s-∀l x case-𝕔 fd upC upD (↑tyʲ-𝕔 upj)) with s+-⊆/ x
... | r = ⊆∀-C-new r upj


infix 3 _≤_⟹_
data _≤_⟹_ : Type m → Type m → Type m → Set where
  ett-var : ‶ X ≤ B ⟹ B
  ett-arr : B ≤ D ⟹ T
          → A `→ B ≤ C `→ D ⟹ T
  ett-∀-𝕚 : A ≤ B' `→ C' ⟹ T'
          → (upB : ↑ty0 B ⇘ B')
          → (upC : ↑ty0 C ⇘ C')
          → (upT : ↑ty0 T ⇘ T')
          → `∀ A ≤ B `→ C ⟹ T
  ett-∀-𝕥 : A ≤ C ⟹ T'
          → (upT : ↑ty0 T ⇘ T')
          → `∀ A ≤ `∀ C ⟹ T

infix 3 _ε'_
data _ε'_ : Fin m → Type m → Set where
  ε-var : k ε' (‶ k)
  ε-arr : k ¬ε A
        → k ε' B
        → k ε' (A `→ B)
  ε-∀ : #S k ε' A
      → k ε' (`∀ A)


ε'-ε : k ε' A
     → k ε A
ε'-ε ε-var = ε-var
ε'-ε (ε-arr x inA) = ε-arr-r x (ε'-ε inA)
ε'-ε (ε-∀ inA) = ε-∀ (ε'-ε inA)

⊆/x-exsol' : Γ ⊆ Δ
           → Δ ∋= k
           → ExSol Γ k
⊆/x-exsol' (uvar ext) (S∙ inΔ) with ⊆/x-exsol' ext inΔ
... | is-ex inΓ = is-ex (S∙ inΓ)
... | is-sol inΓ = is-sol (S∙ inΓ)
⊆/x-exsol' (evar ext) (S^ inΔ) with ⊆/x-exsol' ext inΔ
... | is-ex inΓ = is-ex (S^ inΓ)
... | is-sol inΓ = is-sol (S^ inΓ)
⊆/x-exsol' (evar-sol ext regA) Z = is-ex Z
⊆/x-exsol' (evar-sol ext regA) (S= inΔ) with ⊆/x-exsol' ext inΔ
... | is-ex inΓ = is-ex (S^ inΓ)
... | is-sol inΓ = is-sol (S^ inΓ)
⊆/x-exsol' (svar ext regA) Z = is-sol Z
⊆/x-exsol' (svar ext regA) (S= inΔ) with ⊆/x-exsol' ext inΔ
... | is-ex inΓ = is-ex (S= inΓ)
... | is-sol inΓ = is-sol (S= inΓ)

complete-ss+ : Δ ⊢ ∞ # A ⌞ ≤⁺ ⌝ B
             → Γ ⊆ Δ w/t A
             → Γ ⊢ A ⌞ ≤⁺ ⌝ B ⊣ Δ

complete-ss- : Δ ⊢ ∞ # A ⌞ ≤⁻ ⌝ B
             → Γ ⊆ Δ w/t B
             → Γ ⊢ A ⌞ ≤⁻ ⌝ B ⊣ Δ


complete-ss+ (s-int regΔ) ext with ⊆/-⊢c-eq ext ⊢c-int
... | refl = s-int regΔ
complete-ss+ (s-var-∙ regΔ inΔ) (ext-var x) with ⊆/-⊢c-eq (ext-var x) (⊢c-var-∙ (⊆/-∙out-∙in inΔ x))
... | refl = s-var-∙ regΔ inΔ
complete-ss+ (s-arr₁ s s₁) (ext-arr ext ext₁)
  with ⟨ Ψ , diff ⟩ ← ⅆ-total (⊆/-⊆ ext) (⊆/-⊆ ext₁)
  with ih ← complete-ss- {Γ = Ψ} s (ⅆ-⊆/ diff ext)
  = s-arr (s--subirrev-final ih diff (⊆/-⊢c ext)) (complete-ss+ s₁ ext₁)
complete-ss+ (s-∀ s) (ext-∀ ext) = s-∀ (complete-ss+ s ext)
complete-ss+ (s-svar-l x inΔ) ext'@(ext-var x₁) with ⊆/x-=out-in x₁ (∋:=to∋= inΔ)
... | is-ex inΓ = s-ex-l^ (⊆/x-^in-=out-inst inΓ inΔ x₁)
... | is-sol inΓ with refl ← ⊆/-⊢c-eq ext' (⊢c-var-= inΓ) = s-ex-l= x inΔ

complete-ss- (s-int regΔ) ext with ⊆/-⊢c-eq ext ⊢c-int
... | refl = s-int regΔ
complete-ss- (s-var-∙ regΔ inΔ) (ext-var x) with ⊆/-⊢c-eq (ext-var x) (⊢c-var-∙ (⊆/-∙out-∙in inΔ x))
... | refl = s-var-∙ regΔ inΔ
complete-ss- (s-arr₁ s s₁) (ext-arr ext ext₁)
  with ⟨ Ψ , diff ⟩  ← ⅆ-total (⊆/-⊆ ext) (⊆/-⊆ ext₁)
  with ih ← complete-ss+ {Γ = Ψ} s (ⅆ-⊆/ diff ext)
  = s-arr (s+-subirrev-final ih diff (⊆/-⊢c ext)) (complete-ss- s₁ ext₁)
complete-ss- (s-∀ s) (ext-∀ ext) = s-∀ (complete-ss- s ext)
complete-ss- (s-svar-r x inΔ) ext'@(ext-var x₁) with ⊆/x-=out-in x₁ (∋:=to∋= inΔ)
... | is-ex inΓ = s-ex-r^ (⊆/x-^in-=out-inst inΓ inΔ x₁)
... | is-sol inΓ with refl ← ⊆/-⊢c-eq ext' (⊢c-var-= inΓ) = s-ex-r= x inΔ

ε'-unique : k₁ ε' A
          → k₂ ε' A
          → k₁ ≡ k₂
ε'-unique ε-var ε-var = refl
ε'-unique (ε-arr x in1) (ε-arr x₁ in2) = ε'-unique in1 in2
ε'-unique (ε-∀ in1) (ε-∀ in2) with refl ← ε'-unique in1 in2 = refl


case₁ : ∃-syntax (λ k → k ε' A `→ B × Δ ∋^ k)
      → ∃-syntax (λ k → k ε' B × Δ ∋^ k)
case₁ ⟨ fst , ⟨ ε-arr x fst₁ , snd ⟩ ⟩ = ⟨ fst , ⟨ fst₁ , snd ⟩ ⟩

case₂ : ∃-syntax (λ k → k ε' `∀ A × Δ ∋^ k)
      → ∃-syntax (λ k → k ε' A × Δ ,∙ ∋^ k)
case₂ ⟨ fst , ⟨ ε-∀ fst₁ , snd ⟩ ⟩ = ⟨ #S fst , ⟨ fst₁ , S∙ snd ⟩ ⟩

case₃ : ∃-syntax (λ k → k ε' `∀ A × Γ ∋^ k)
      → ∃-syntax (λ k → k ε' A × Γ ,= T ∋^ k)
case₃ ⟨ k , ⟨ ε-∀ inA , inΓ ⟩ ⟩ = ⟨ #S k , ⟨ inA , S= inΓ ⟩ ⟩

case₄ : ∃-syntax (λ k → k ε' A × Γ ,∙ ∋^ k)
      → ∃-syntax (λ k → k ε' A × Γ ,^ ∋^ k)
case₄ ⟨ #S k , ⟨ inA , S∙ inΓ ⟩ ⟩ = ⟨ #S k , ⟨ inA , S^ inΓ ⟩ ⟩

case₅ : #0 ε' A
      → ∃-syntax (λ k → k ε' `∀ A × Γ ∋^ k)
      → ⊥
case₅ inA ⟨ k , ⟨ ε-∀ inA' , inΓ ⟩ ⟩
  with () ← ε'-unique inA inA'

⊢c-¬ε' : Δ ⊢c A
       → ∃-syntax (λ k → k ε' A × Δ ∋^ k)
       → ⊥
⊢c-¬ε' ⊢c-int = λ ()
⊢c-¬ε' (⊢c-var-∙ inΔ) ⟨ fst , ⟨ ε-var , snd ⟩ ⟩ = ⊥-elim (∋^-∋∙-false snd inΔ)
⊢c-¬ε' (⊢c-var-= inΔ) ⟨ fst , ⟨ ε-var , snd ⟩ ⟩ = ⊥-elim (∋^-∋=-false snd inΔ)
⊢c-¬ε' (⊢c-arr cloA cloA₁) p = ⊢c-¬ε' cloA₁ (case₁ p)
⊢c-¬ε' (⊢c-∀ cloA) p = ⊢c-¬ε' cloA (case₂ p)


inst-=⟹ : [ A / X ] Γ ⟹ Δ
        → [ A / X ] Δ =⟹ Δ
inst-=⟹ (⟹^0 up regA env) = =⟹=0 up regA env
inst-=⟹ (⟹^S inst up1) = =⟹^S (inst-=⟹ inst) up1
inst-=⟹ (⟹∙S inst up1) = =⟹∙S (inst-=⟹ inst) up1
inst-=⟹ (⟹=S inst up1 regB) = =⟹=S (inst-=⟹ inst) up1 (⊆-⊢r regB (inst-⊆ inst))

inst-=⟹' : [ A / X ] Γ ⟹ Δ'
           → Γ ⊆ Δ w/v X
           → [ A / X ] Δ =⟹ Δ'
inst-=⟹' (⟹^0 up regA env) (ext-Z^ regΓ regA₁) = =⟹=0 up regA regΓ
inst-=⟹' (⟹^S inst up1) (ext-S^ extx) = =⟹^S (inst-=⟹' inst extx) up1
inst-=⟹' (⟹∙S inst up1) (ext-S∙ extx) = =⟹∙S (inst-=⟹' inst extx) up1
inst-=⟹' (⟹=S inst up1 regB) (ext-S= extx regA) = =⟹=S (inst-=⟹' inst extx) up1 (⊆-⊢r regB (⊆/x-⊆ extx))

⊆-^out-^in : Δ ∋^ k
           → Γ ⊆ Δ
           → Γ ∋^ k
⊆-^out-^in Z (evar ext) = Z
⊆-^out-^in (S∙ inΔ) (uvar ext) = S∙ (⊆-^out-^in inΔ ext)
⊆-^out-^in (S= inΔ) (evar-sol ext regA) = S^ (⊆-^out-^in inΔ ext)
⊆-^out-^in (S= inΔ) (svar ext regA) = S= (⊆-^out-^in inΔ ext)
⊆-^out-^in (S^ inΔ) (evar ext) = S^ (⊆-^out-^in inΔ ext)

complete-false₁ : k ε' B
                → k₁ ε' B
                → k ¬ε A
                → k₁ ε A
                → ⊥
complete-false₁ inB1 inB2 ninA inA
  with refl ← ε'-unique inB1 inB2 = ε-¬ε-false inA ninA


complete-false₂ : Γ ⊆ Δ w/t A
                → k ε A
                → Δ ∋^ k
                → ⊥
complete-false₂ ext inA inΔ
  with inΓ ← ⊆-^out-^in inΔ (⊆/-⊆ ext) = ⊥-elim (∋^-∋=-false inΔ (⊆/-^in-=out ext inA inΓ))

complete-false₃ : Δ ⊢r A
                → k ε' A
                → Δ ∋^ k
                → ⊥
complete-false₃ regA inA inΔ = ⊢c-^∈-false (ε'-ε inA) inΔ (⊢r-⊢c regA)

complete-infs : Γ ⊢ ⟨ j , B ⟩ ~s Σ
              → Γ ⊢r B
              → IsoInf j
              → 𝕣 Γ ⊨ Σ ⟹ B
complete-infs (~I ⊢e ~∞) (⊢r-arr regB regB₁) i∞-z = infs-s ⊢e (infs-z (t-env ⊢e) (⊢r-𝕣' regB₁))
complete-infs (~I ⊢e ~j) (⊢r-arr regB regB₁) (i∞-i iso) = infs-s ⊢e (complete-infs ~j regB₁ iso)

data Complete (A : Type m) (j : Counter m) (Σ : Context n m) (Γ : Env n m) (Δ : Env n m) (B : Type m) : Set where
  normal :     (cond : ¬ (∃[ k ](k ε' A) × Γ ∋^ k))
               → (s : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B)
               → Complete A j Σ Γ Δ B

  special : ∀ {k Δ'}
               → (inA : k ε' A)
               → (inΓ^ : Γ ∋^ k)
               → (tail : A ≤ B ⟹ T)
               → (newΔ : [ T / k ] Δ =⟹ Δ')
               → (s : Γ ⊢ A ≤⁺ Σ ⊣ Δ' ↪ B)
               → Complete A j Σ Γ Δ B

ss-complete : Γ ⊢ A ⌞ ≤⁺ ⌝ B ⊣ Δ
            → Complete A ∞ (τ B) Γ Δ B
ss-complete (s-int regΓ) = normal (λ ()) (s-type (s-int regΓ))
ss-complete (s-var-∙ regΓ inΔ) = normal (⊢c-¬ε' (⊢c-var-∙ inΔ)) (s-type (s-var-∙ regΓ inΔ))
ss-complete (s-ex-l^ inst) = special ε-var (inst-∋^ inst) ett-var (inst-=⟹ inst) (s-type (s-ex-l^ inst))
ss-complete (s-ex-l= regΓ x-in) = normal (⊢c-¬ε' (⊢c-var-= (∋:=to∋= x-in))) (s-type (s-ex-l= regΓ x-in))
ss-complete (s-arr s s₁) with ss-complete s₁
ss-complete (s-arr s s₁) | normal cond s₂ = normal
  (λ where ⟨ k , ⟨ ε-arr x' inAB , inΓ ⟩ ⟩ → cond ⟨ k , ⟨ inAB , (⊆/-^in-^out (ss--⊆/ s) x' inΓ) ⟩ ⟩)
            (s-type (s-arr s s₁))
ss-complete (s-arr {A = A} s s₁) | special {k = k} inA inΓ^ tail newΔ (s-type s₂) with ε-dec {k = k} {A = A}
... | inj₁ inA' = normal (λ where ⟨ k , ⟨ ε-arr x' inB , inΓ ⟩ ⟩ → complete-false₁ inB inA x' inA')
                        (s-type (s-arr s s₁))
... | inj₂ ¬inA = special (ε-arr ¬inA inA) (⊆-^out-^in inΓ^ (ss-⊆ s)) (ett-arr tail) newΔ (s-type (s-arr s s₂))
ss-complete (s-∀ s) with ss-complete s
... | normal cond s₁ = normal (λ cond2 → cond (case₂ cond2)) (s-type (s-∀ s))
... | special inA (S∙ inΓ^) tail (=⟹∙S newΔ up1) (s-type s₁)
  = special (ε-∀ inA) inΓ^ (ett-∀-𝕥 tail up1) newΔ (s-type (s-∀ s₁))
