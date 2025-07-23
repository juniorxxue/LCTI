module Implicit.Algo2Interm.Main where

open import Implicit.Language.All
open import Implicit.Interm.All
open import Implicit.Algo.All
open import Implicit.Algo2Interm.AlgoCounter.All
open import Implicit.Algo2Interm.Context2Counter
open import Implicit.Algo2Interm.Find


sound-ss : Γ ⊢ A ⌞ ≤ ⌝ B ⊣ Δ
         → Δ ⊢ ∞ # A ⌞ ≤ ⌝ B
sound-ss (s-int regΓ) = s-int regΓ
sound-ss (s-var-∙ regΓ x) = s-var-∙ regΓ x
sound-ss (s-ex-l^ inst) = s-svar-l (inst-∋:= inst) (s-refl-∞ {!!} {!!})
-- s-svar-l (⊆-sregular' (inst-⊆ inst)) (inst-∋:= inst)
sound-ss (s-ex-r^ inst) = s-svar-r (⊆-sregular' (inst-⊆ inst)) (inst-∋:= inst)
sound-ss (s-ex-l= regΓ x-in) = {!!}
-- s-svar-l regΓ x-in
sound-ss (s-ex-r= regΓ x-in) = s-svar-r regΓ x-in
sound-ss (s-arr s s₁) = s-arr₁ (s-⊆-prv (sound-ss s) (ss-⊆ s₁)) (sound-ss s₁)
sound-ss (s-∀ s) = s-∀ (sound-ss s)

----------------------------------------------------------------------
--+                           main logic                           +--
----------------------------------------------------------------------

s-nonempty-case1 : Γ ⋈ ⊢ A₁ ≤⁺ [ e₁ ]↝ Σ ⊣ Γ ⋈ ↪ A ↡ j
                 → NonZ j
s-nonempty-case1 (s-term-c cloA ap ⊢e s) = nz-C
s-nonempty-case1 (s-term-o opnA ⊢e ss s) = nz-I
s-nonempty-case1 (s-∀l-𝕚 s upᶜ upj upᵉ upC upD) = nz-I
s-nonempty-case1 (s-∀l-𝕔 s upᶜ upj upᵉ upC upD) = nz-C
s-nonempty-case1 (s-∀l-no-𝕚 s upᶜ upj upᵉ upC upD) = nz-I
s-nonempty-case1 (s-∀l-no-𝕔 s upᶜ upj upᵉ upC upD) = nz-C

s-nonempty-case2 : Γ ⋈ ⊢ A₁ ≤⁺ A₁ ⓪↝ Σ ⊣ Γ ⋈ ↪ A ↡ j
                 → NonZ j
s-nonempty-case2 (s-tapp s upᶜ upj) = nz-T


tc-~ : Γ ⊢ Σ ⇒ e ⇒ A ↡ j
     → Γ ⊢ ⟨ j , A ⟩ ~t Σ

sc-~ : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B ↡ j
     → Δ ⊢ ⟨ j , B ⟩ ~s Σ

infs-~ : Γ ⊨ Σ ⟹ A ↡ j
       → Γ ⊢ ⟨ j , A ⟩ ~t Σ

sound : Γ ⊢ Σ ⇒ e ⇒ A ↡ j
      → Γ ⊢ j # e ⦂ A

sound-s : Γ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B ↡ j
        → Δ ⊢ j # A ⌞ ≤⁺ ⌝ B

sound-infs : 𝕣 Γ ⊨ Σ ⟹ A ↡ j
           → Γ ⊆ Δ
           → Δ ⊢ j # A ⌞ ≤⁺ ⌝ A

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
tc-~ {e = Λ e} (⊢tabs-τ x) with tc-id0 x
... | refl = ~t∞
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
sc-~ (s-svar inΓ s) = sc-~ s
sc-~ (s-∀l-no-𝕚 s upᶜ upj upᵉ upC upD) = ~s-strengthen^0 (sc-~ s) (↑ty-arr upC upD) (↑tyᶜ-e upᵉ upᶜ) (↑tyʲ-𝕚 upj)
sc-~ (s-∀l-no-𝕔 s upᶜ upj upᵉ upC upD) = ~s-strengthen^0 (sc-~ s) (↑ty-arr upC upD) (↑tyᶜ-e upᵉ upᶜ) (↑tyʲ-𝕔 upj)
sc-~ (s-evar-infers infs inst)
  with ih ← infs-~ infs = ~s-irrev-⊆ (~t-~s ih) (inst-⊆ inst)

infs-~ (infs-z regΓ regA) = ~t∞
infs-~ (infs-s ⊢e infs) = ~tI (sound ⊢e) (infs-~ infs)

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
sound {e = Λ e} (⊢tabs-τ x) = ⊢tabs-∞ (sound x)

sound-s (s-empty regΓ cloA x) = s-refl regΓ cloA x
sound-s (s-type ss) = sound-ss ss
sound-s (s-term-c cloA ap ⊢e s) with tc-id0 ⊢e
... | refl = s-arr₃ (⊆-⊢c cloA (sc-⊆ s)) (⊆-⊢c-≫' (sc-⊆ s) cloA ap) (sound-s s)
sound-s (s-term-o opnA ⊢e ss s) = s-arr₂ (s-⊆-prv (sound-ss ss) (sc-⊆ s)) (sound-s s)
sound-s (s-∀l-𝕚 s upᶜ upj upᵉ upC upD) = s-∀l (sound-s s) case-𝕚 (s-find0 s upᵉ upᶜ) upC upD (↑tyʲ-𝕚 upj)
sound-s (s-∀l-𝕔 s upᶜ upj upᵉ upC upD) = s-∀l (sound-s s) case-𝕔 (s-find0 s upᵉ upᶜ) upC upD (↑tyʲ-𝕔 upj)
sound-s (s-tapp s upᶜ upj) = s-tapp (sound-s s) upj
sound-s (s-svar inΓ s) with sc-~ s
... | r = {!!}
sound-s (s-∀l-no-𝕚 s upᶜ upj upᵉ upC upD) = s-∀l-no-appear (sound-s s) case-𝕚 (s-¬ε (sc-sound s) Z Z) upC upD (↑tyʲ-𝕚 upj)
sound-s (s-∀l-no-𝕔 s upᶜ upj upᵉ upC upD) = s-∀l-no-appear (sound-s s) case-𝕔 (s-¬ε (sc-sound s) Z Z) upC upD (↑tyʲ-𝕔 upj)
sound-s (s-evar-infers (infs-s ⊢e infs) inst) = {!!}
-- s-svar-𝕚 (inst-∋:= inst) (sound-infs (infs-s ⊢e infs) (inst-⊆ inst))

sound-infs (infs-z regΓ regA) inst = s-refl-∞ (⊆-sregular' inst) (⊆-⊢r (⊢r-𝕣 regA) inst)
sound-infs (infs-s ⊢e infs) inst = s-arr₂ (s-refl-∞ (⊆-sregular' inst) ((⊆-⊢r (⊢r-𝕣 (tc-⊢r ⊢e)) inst))) (sound-infs infs inst)
