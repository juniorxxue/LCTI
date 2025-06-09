{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --allow-incomplete-matches #-}
module Implicit.Algo2Interm.Main where

open import Implicit.Language.All
open import Implicit.Interm.All
open import Implicit.Algo.All
open import Implicit.Algo2Interm.AlgoCounter.All
open import Implicit.Algo2Interm.Context2Counter
open import Implicit.Algo2Interm.Find
open import Implicit.Language.ExtraDefs

ε'-unique : k₁ ε' A
           → k₂ ε' A
           → k₁ ≡ k₂
ε'-unique ε-var ε-var = refl
ε'-unique (ε-arr x in1) (ε-arr x₁ in2) = ε'-unique in1 in2
ε'-unique (ε-∀ in1) (ε-∀ in2) with refl ← ε'-unique in1 in2 = refl

s-conv : Δ ⊢ j # A ⌞ ≤⁺ ⌝ B
       → k ε' A by j ↪ j'
       → Δ ∋ k := C
       → Match C B j'
       → Δ ⊢ j' # A ⌞ ≤⁺ ⌝ B
s-conv (s-refl regΔ cloA grd) (ε-var ()) inΔ mt
s-conv (s-var-∙ regΔ inΔ₁) (ε-var x) inΔ mt-∞ = ⊥-elim {!!}
s-conv (s-arr₂ s s₁) (ε-arr-𝕚 x newj) inΔ (mt-𝕚 mt) = s-arr₂ s (s-conv s₁ newj inΔ mt)
s-conv (s-arr₃ cloA grd s) (ε-arr-𝕔 x newj) inΔ (mt-𝕔 mt) = s-arr₃ cloA grd (s-conv s newj inΔ mt)
s-conv (s-∀l s ic fd upC upD (↑tyʲ-𝕚 upj)) (ε-∀-𝕚 newj upj₁ upj₂) inΔ mt
  with refl ← ↑tyʲ-unique upj upj₁ = s-∀l (s-conv s newj (S= inΔ {!!}) {!!}) {!!} {!!} upC upD upj₂
s-conv (s-∀l s ic fd upC upD upj) (ε-∀-𝕔 newj upj₁ upj₂) inΔ mt = {!!} -- same as above
s-conv (s-∀l-tail s ic tail upC upD upj) (ε-∀-𝕚 newj upj₁ upj₂) inΔ mt
   = {!!}
--  with () ← ε'-unique (ε'j→ε' newj) (ε'j→ε' tail)
s-conv (s-∀l-tail s ic tail upC upD upj) (ε-∀-𝕔 newj upj₁ upj₂) inΔ mt
  with () ← ε'-unique (ε'j→ε' newj) (ε'j→ε' tail)
s-conv (s-tapp s upj) newj inΔ mt = {!!}
s-conv (s-svar-l x inΔ₁) (ε-var x₁) inΔ mt = s-svar-l x inΔ₁
s-conv (s-svar-𝕚 x s) (ε-var isoinf) inΔ mt-∞ = s-svar-l (s-sregular s) inΔ
s-conv (s-svar-𝕔 x s) (ε-var isoinf) inΔ mt-∞ = s-svar-l (s-sregular s) inΔ
s-conv (s-svar-𝕥 x s) (ε-var ()) inΔ mt-∞


sound-ss : Γ ⊢ A ⌞ ≤ ⌝ B ⊣ Δ
         → Δ ⊢ ∞ # A ⌞ ≤ ⌝ B
sound-ss (s-int regΓ) = s-int regΓ
sound-ss (s-var-∙ regΓ x) = s-var-∙ regΓ x
sound-ss (s-ex-l^ inst) = s-svar-l (⊆-sregular' (inst-⊆ inst)) (inst-∋:= inst)
sound-ss (s-ex-r^ inst) = s-svar-r (⊆-sregular' (inst-⊆ inst)) (inst-∋:= inst)
sound-ss (s-ex-l= regΓ x-in) = s-svar-l regΓ x-in
sound-ss (s-ex-r= regΓ x-in) = s-svar-r regΓ x-in
sound-ss (s-arr s s₁) = s-arr₁ (s-⊆-prv (sound-ss s) (ss-⊆ s₁)) (sound-ss s₁)
sound-ss (s-∀ s) = s-∀ (sound-ss s)

----------------------------------------------------------------------
--+                           main logic                           +--
----------------------------------------------------------------------


tc-~ : Γ ⊢ Σ ⇒ e ⇒ A ↡ j
     → Γ ⊢ ⟨ j , A ⟩ ~t Σ

sc-~ : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B ↡ j
     → Δ ⊢ ⟨ j , B ⟩ ~s Σ

infs-~ : Γ ⊨ Σ ⟹ B ↡ j
       → Γ ⊢ ⟨ j , B ⟩ ~t Σ


sound : Γ ⊢ Σ ⇒ e ⇒ A ↡ j
      → Γ ⊢ j # e ⦂ A

sound-s : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B ↡ j
        → Δ ⊢ j # A ⌞ ≤⁺ ⌝ B

tc-~ (⊢lit regΓ) = ~tZ
tc-~ (⊢var regΓ x∈Γ) = ~tZ
tc-~ (⊢ann ⊢e) = ~tZ
tc-~ (⊢app ⊢e) with tc-~ ⊢e
... | ~tI ⊢e₁ r = r
... | ~tC ⊢e₁ r = r
tc-~ (⊢lam₁ ⊢e) with tc-id0 ⊢e
... | refl = ~t∞
tc-~ (⊢lam₂ ⊢e up-c ⊢e₁) = ~tI (sound ⊢e) (~t-strengthen,0 (tc-~ ⊢e₁) up-c)
tc-~ (⊢sub ⊢e ne gc s) = ~s-~t (sc-~ s)
tc-~ (⊢tabs ⊢e) = ~tZ
tc-~ (⊢tapp ⊢e st) with tc-~ ⊢e
... | ~tT r st₁ with refl ← st-unique st st₁ = r

sc-~ (s-empty regΓ cloA x) = ~sZ
sc-~ (s-type ss) = ~s∞
sc-~ (s-term-c cloA ap ⊢e s) with tc-id0 ⊢e
... | refl = ~sC (t-⊆-prv (sound ⊢e) (sc-⊆ s)) (sc-~ s)
sc-~ s'@(s-term-o opnA ⊢e ss s) = ~sI (t-⊆-prv (sound ⊢e) (sc-⊆ s')) (sc-~ s)
sc-~ (s-∀l-𝕚 s upᶜ upj upᵉ upC upD) = ~s-strengthen=0 (sc-~ s) (↑ty-arr upC upD) (↑tyᶜ-e upᵉ upᶜ) (↑tyʲ-𝕚 upj)
sc-~ (s-∀l-𝕔 s upᶜ upj upᵉ upC upD) = ~s-strengthen=0 (sc-~ s) (↑ty-arr upC upD) (↑tyᶜ-e upᵉ upᶜ) (↑tyʲ-𝕔 upj)
sc-~ (s-tapp {B = B} {C = C} s upᶜ upj)
  with ⟨ B* , stB ⟩ ← st0-total B C = ~sT (~s-strengthen=0 (sc-~ s) (st-↑ty (⊢r-¬ε (s-⊢r (sc-sound s)) Z) stB) upᶜ upj) stB
sc-~ (s-svar-term inΓ s) = sc-~ s
sc-~ (s-svar-tapp inΓ s) = sc-~ s
sc-~ (s-evar-infers infs inst) = {!infs-~ infs!}

infs-~ (infs-z regΓ regA) = ~t∞
infs-~ (infs-s x infs) = ~tI (sound x) (infs-~ infs)

sound (⊢lit regΓ) = ⊢lit regΓ
sound (⊢var regΓ x∈Γ) = ⊢var regΓ x∈Γ
sound (⊢ann ⊢e) with refl ← tc-id0 ⊢e = ⊢ann (sound ⊢e)
sound (⊢app ⊢e) with tc-~ ⊢e
... | ~tI ⊢e₁ r = ⊢app₂ (sound ⊢e) ⊢e₁
... | ~tC ⊢e₁ r = ⊢app₁ (sound ⊢e) ⊢e₁
sound (⊢lam₁ ⊢e) = ⊢lam₁ (sound ⊢e)
sound (⊢lam₂ ⊢e up-c ⊢e₁) = ⊢lam₂ (sound ⊢e₁)
sound (⊢sub ⊢e ne gc s) with sc-~ s
... | r = ⊢sub (sound ⊢e) (sound-s s) gc (NonEmpty-NonZ ne (~s-~t r))
sound (⊢tabs ⊢e) = ⊢tabs (sound ⊢e)
sound (⊢tapp ⊢e st) = ⊢tapp (sound ⊢e) st

sound-s (s-empty regΓ cloA x) = s-refl regΓ cloA x
sound-s (s-type ss) = sound-ss ss
sound-s (s-term-c cloA ap ⊢e s) with tc-id0 ⊢e
... | refl = s-arr₃ (⊆-⊢c cloA (sc-⊆ s)) (⊆-⊢c-≫' (sc-⊆ s) cloA ap) (sound-s s)
sound-s (s-term-o opnA ⊢e ss s) = s-arr₂ (s-⊆-prv (sound-ss ss) (sc-⊆ s)) (sound-s s)
sound-s (s-∀l-𝕚 {A = A} {B = B} s upᶜ upj upᵉ upC upD) with ε'-dec #0 A
... | inj₁ p
  with ⟨ B' , upB ⟩ ← ↑ty0-total B
  with truncated s Z (Z upB) p
... | justrun newj mt = s-∀l-tail {!sound-s s!} {!!} {!!} {!!} {!!} {!!}
-- s-∀l-tail (s-conv (sound-s s) newj (Z upB) mt) case-𝕚 newj upC upD (↑tyʲ-𝕚 upj)
... | in-type fd = s-∀l (sound-s s) case-𝕚 fd upC upD (↑tyʲ-𝕚 upj)
-- s-∀l-tail {!sound-s s!} case-𝕚 {!!} upC upD (↑tyʲ-𝕚 upj)
sound-s (s-∀l-𝕚 {A = A} s upᶜ upj upᵉ upC upD) | inj₂ ¬p = s-∀l (sound-s s) case-𝕚 (s-find'0 s upᵉ upᶜ ¬p) upC upD (↑tyʲ-𝕚 upj)
-- s-∀l (sound-s s) case-𝕚 (s-find0 s upᵉ upᶜ) upC upD (↑tyʲ-𝕚 upj)
sound-s (s-∀l-𝕔 s upᶜ upj upᵉ upC upD) = s-∀l (sound-s s) case-𝕔 (s-find0 s upᵉ upᶜ) upC upD (↑tyʲ-𝕔 upj)
sound-s (s-tapp s upᶜ upj) = s-tapp (sound-s s) upj
sound-s (s-svar-term inΓ s) with sc-~ s
... | ~sI ⊢e r = s-svar-𝕚 inΓ (sound-s s)
... | ~sC ⊢e r = s-svar-𝕔 inΓ (sound-s s)
sound-s (s-svar-tapp inΓ s) = s-svar-𝕥 inΓ (sound-s s)
sound-s (s-evar-infers (infs-s x infs) inst) = s-svar-𝕚 (inst-∋:= inst) (s-arr₂ {!!} {!!})
