module Implicit.Algo2Interm.Main where

open import Implicit.Language.All
open import Implicit.Interm.All
open import Implicit.Algo.All
open import Implicit.Algo2Interm.AlgoCounter.All
open import Implicit.Algo2Interm.Context2Counter
open import Implicit.Algo2Interm.Find


sound-ss : Γ ⊢ A ⌞ ≤ ⌝ B ⊣ Δ
         → Δ ⊢ `□ # A ⌞ ≤ ⌝ B
sound-ss (s-int regΓ) = s-int regΓ
sound-ss (s-var-∙ regΓ x) = s-var-∙ regΓ x
sound-ss (s-ex-l^ inst) = s-svar-l (inst-∋:= inst) (s-refl-∞ (⊆-sregular' (inst-⊆ inst)) (⊆-⊢r (inst-⊢r inst) (inst-⊆ inst)))
sound-ss (s-ex-r^ inst) = s-svar-r (⊆-sregular' (inst-⊆ inst)) (inst-∋:= inst)
sound-ss (s-ex-l= regΓ x-in) = s-svar-l x-in (s-refl-∞ regΓ (∋:=-⊢r regΓ x-in))
sound-ss (s-ex-r= regΓ x-in) = s-svar-r regΓ x-in
sound-ss (s-arr s s₁) = s-arr₁ (s-⊆-prv (sound-ss s) (ss-⊆ s₁)) (sound-ss s₁)
sound-ss (s-∀ s) = s-∀ (sound-ss s)

----------------------------------------------------------------------
--+                           main logic                           +--
----------------------------------------------------------------------

s-nonempty-case1 : Γ ⋈ ⊢ A₁ ≤⁺ [ e₁ ]↝ Σ ⊣ Γ ⋈ ↪ A ↡ j
                 → NonZ j
s-nonempty-case1 (s-term-c cloA ap ⊢e s) = nz-app
s-nonempty-case1 (s-term-o opnA ⊢e ss s) = nz-app
s-nonempty-case1 (s-∀l s upᶜ upᵉ upC upD) = nz-app
s-nonempty-case1 (s-∀l-no s upᶜ upᵉ upC upD) = nz-app

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
tc-~ {e = e ⓪ A} (⊢tapp x st regA s) = ~s-~t (sc-~ s)

sc-~ (s-empty regΓ cloA x) = ~sZ
sc-~ (s-type ss) = ~s∞
sc-~ (s-term-c cloA ap ⊢e s) with tc-id0 ⊢e
... | refl = ~sC (t-⊆-prv (sound ⊢e) (sc-⊆ s)) (sc-~ s)
sc-~ s'@(s-term-o opnA ⊢e ss s) = ~sI (t-⊆-prv (sound ⊢e) (sc-⊆ s')) (sc-~ s)
sc-~ (s-∀l s upᶜ upᵉ upC upD) = ~s-strengthen=0 (sc-~ s) (↑ty-arr upC upD) (↑tyᶜ-e upᵉ upᶜ)
sc-~ (s-svar-term inΓ s) = sc-~ s
sc-~ (s-∀l-no s upᶜ upᵉ upC upD) = ~s-strengthen^0 (sc-~ s) (↑ty-arr upC upD) (↑tyᶜ-e upᵉ upᶜ)
sc-~ (s-evar-infers infs inst)
  with ih ← infs-~ infs = ~s-irrev-⊆ (~t-~s ih) (inst-⊆ inst)

infs-~ (infs-z regΓ regA) = ~t∞
infs-~ (infs-s ⊢e infs) = ~tI (sound ⊢e) (infs-~ infs)

sound (⊢lit regΓ) = ⊢lit regΓ
sound (⊢var regΓ x∈Γ) = ⊢var regΓ x∈Γ
sound (⊢ann ⊢e) with refl ← tc-id0 ⊢e = ⊢ann (sound ⊢e)
sound (⊢app ⊢e) with tc-~ ⊢e
... | ~tI ⊢e₁ r = ⊢app (sound ⊢e) ⊢e₁
... | ~tC ⊢e₁ r = ⊢app (sound ⊢e) ⊢e₁
sound (⊢lam₁ ⊢e) = ⊢lam₁ (sound ⊢e)
sound (⊢lam₂ ⊢e up-c ⊢e₁) = ⊢lam₂ (sound ⊢e₁)
sound (⊢sub ⊢e ne gc s) with sc-~ s
... | r = ⊢sub (sound ⊢e) (sound-s s) gc (NonEmpty-NonZ ne (~s-~t r))
sound (⊢tabs ⊢e) = ⊢tabs (sound ⊢e)
sound {e = Λ e} (⊢tabs-τ x) = ⊢tabs (sound x)
sound {e = e ⓪ A} (⊢tapp x st regA s) = ⊢tapp (sound x) regA st (sound-s s)

sound-s (s-empty regΓ cloA x) = s-refl regΓ cloA x
sound-s (s-type ss) = sound-ss ss
sound-s (s-term-c cloA ap ⊢e s) with tc-id0 ⊢e
... | refl = s-arr₃ (⊆-⊢c cloA (sc-⊆ s)) (⊆-⊢c-≫' (sc-⊆ s) cloA ap) (sound-s s)
sound-s (s-term-o opnA ⊢e ss s) = s-arr₂ (s-⊆-prv (sound-ss ss) (sc-⊆ s)) (sound-s s)
sound-s (s-∀l s upᶜ upᵉ upC upD) = s-∀l (sound-s s) (s-find0 s upᵉ upᶜ) upC upD
sound-s (s-svar-term inΓ s) = s-svar-l inΓ (sound-s s)
sound-s (s-∀l-no s upᶜ upᵉ upC upD) = s-∀l-no-appear (sound-s s) (s-¬ε (sc-sound s) Z Z) upC upD
sound-s (s-evar-infers (infs-s ⊢e infs) inst) = s-svar-l (inst-∋:= inst) (sound-infs (infs-s ⊢e infs) (inst-⊆ inst))

sound-infs (infs-z regΓ regA) inst = s-refl-∞ (⊆-sregular' inst) (⊆-⊢r (⊢r-𝕣 regA) inst)
sound-infs (infs-s ⊢e infs) inst = s-arr₂ (s-refl-∞ (⊆-sregular' inst) ((⊆-⊢r (⊢r-𝕣 (tc-⊢r ⊢e)) inst))) (sound-infs infs inst)
