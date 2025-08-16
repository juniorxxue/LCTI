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
sound-ss (s-ex-l^ inst) = s-svar-l (⊆-sregular' (inst-⊆ inst)) (inst-∋:= inst)
sound-ss (s-ex-r^ inst) = s-svar-r (⊆-sregular' (inst-⊆ inst)) (inst-∋:= inst)
sound-ss (s-ex-l= regΓ x-in) = s-svar-l regΓ x-in
sound-ss (s-ex-r= regΓ x-in) = s-svar-r regΓ x-in
sound-ss (s-arr s s₁) = s-arr₁ (s-⊆-prv (sound-ss s) (ss-⊆ s₁)) (sound-ss s₁)
sound-ss (s-∀ s) = s-∀ (sound-ss s)

peek-ε : A ~~pk~~ B w/ k ↪ C
       → k ε A
peek-ε (pk-var-l upA) = ε-var
peek-ε (pk-arr-l pk) = ε-arr-l (peek-ε pk)
peek-ε {k = k} (pk-arr-r {A = A} pk) with ε-dec {k = k} {A = A}
... | inj₁ x = ε-arr-l x
... | inj₂ y = ε-arr-r y (peek-ε pk)
peek-ε (pk-∀ pk upC) = ε-∀ (peek-ε pk)

sound-peek' : A ~pk'~ Σ w/ k ↬ B ↡ j
            → peek A k j
sound-peek' (pk-type x) = peek-base (peek-ε x)
sound-peek' (pk-term-𝕚 pk) = peek-arr-i (sound-peek' pk)
sound-peek' (pk-term-𝕔 pk) = peek-arr-c (sound-peek' pk)
sound-peek' (pk-∀l-𝕚 pk upΣ upj upe upC) = peek-∀-i (sound-peek' pk) upj
sound-peek' (pk-∀l-𝕔 pk upΣ upj upe upC) = peek-∀-c (sound-peek' pk) upj
sound-peek' (pk-tapp pk upC upΣ upj) = peek-∀-t (sound-peek' pk) upj

complete-peek : peek A k j
              → Γ ⊢ ⟨ j , B ⟩ ~s Σ
              → A ~pk~ Σ w/ k
complete-peek (peek-base inA) ~s∞ = pk-type inA
complete-peek (peek-arr-i pk) (~sI ⊢e ~j) = pk-term (complete-peek pk ~j)
complete-peek (peek-arr-c pk) (~sC ⊢e ~j) = pk-term (complete-peek pk ~j)
complete-peek (peek-∀-i pk upj) ~j'@(~sI {A = A} {B = B} {Σ = Σ} {e = e} ⊢e ~j)
  with ⟨ Σ' , upΣ ⟩ ← ↑tyᶜ0-total Σ
  with ⟨ e , up-e ⟩ ← ↑tyᵉ0-total e
  with ⟨ A' , upA ⟩ ← ↑ty0-total A
  with ⟨ B' , upB ⟩ ← ↑ty0-total B
  = pk-∀l (complete-peek pk (~s-weaken^0 ~j' (↑ty-arr upA upB) (↑tyᶜ-e up-e upΣ) (↑tyʲ-𝕚 upj))) upΣ up-e
complete-peek (peek-∀-c pk upj) ~j'@(~sC {A = A} {B = B} {Σ = Σ} {e = e} ⊢e ~j)
  with ⟨ Σ' , upΣ ⟩ ← ↑tyᶜ0-total Σ
  with ⟨ e , up-e ⟩ ← ↑tyᵉ0-total e
  with ⟨ A' , upA ⟩ ← ↑ty0-total A
  with ⟨ B' , upB ⟩ ← ↑ty0-total B
  = pk-∀l (complete-peek pk (~s-weaken^0 ~j' (↑ty-arr upA upB) (↑tyᶜ-e up-e upΣ) (↑tyʲ-𝕔 upj))) upΣ up-e
complete-peek (peek-∀-t pk upj) ~j'@(~sT {B* = B} {Σ = Σ} ~j st)
  with ⟨ Σ' , upΣ ⟩ ← ↑tyᶜ0-total Σ
  with ⟨ B' , upB ⟩ ← ↑ty0-total B
  = pk-tapp (complete-peek pk (~s-weaken^0 ~j upB upΣ upj)) upΣ

----------------------------------------------------------------------
--+                           main logic                           +--
----------------------------------------------------------------------

s-nonempty-case1 : Γ ⋈ ⊢ A₁ ≤⁺ [ e₁ ]↝ Σ ⊣ Γ ⋈ ↪ A ↡ j
                 → NonZ j
s-nonempty-case1 (s-term-c cloA ap ⊢e s) = nz-C
s-nonempty-case1 (s-term-o opnA ⊢e ss s) = nz-I
s-nonempty-case1 (s-∀l-y-𝕚 jump s upᶜ upᵉ upC upD upj) = nz-I
s-nonempty-case1 (s-∀l-y-𝕔 jump s upᶜ upᵉ upC upD upj) = nz-C
s-nonempty-case1 (s-∀l-n-y-𝕚 jump s upᶜ upᵉ upC upD upj) = nz-I
s-nonempty-case1 (s-∀l-n-y-𝕔 jump s upᶜ upᵉ upC upD upj) = nz-C
s-nonempty-case1 (s-∀l-n-n-𝕚 jump s upᶜ upᵉ upC upD upj) = nz-I
s-nonempty-case1 (s-∀l-n-n-𝕔 jump s upᶜ upᵉ upC upD upj) = nz-C

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
-- sc-~ (s-∀l-𝕚 s upᶜ upj upᵉ upC upD) = ~s-strengthen=0 (sc-~ s) (↑ty-arr upC upD) (↑tyᶜ-e upᵉ upᶜ) (↑tyʲ-𝕚 upj)
-- sc-~ (s-∀l-𝕔 s upᶜ upj upᵉ upC upD) = ~s-strengthen=0 (sc-~ s) (↑ty-arr upC upD) (↑tyᶜ-e upᵉ upᶜ) (↑tyʲ-𝕔 upj)
sc-~ (s-tapp {B = B} {C = C} s upᶜ upj)
  with ⟨ B* , stB ⟩ ← st0-total B C = ~sT (~s-strengthen=0 (sc-~ s) (st-↑ty (⊢r-¬ε (s-⊢r (sc-sound s)) Z) stB) upᶜ upj) stB
sc-~ (s-svar-term inΓ s) = sc-~ s
sc-~ (s-svar-tapp inΓ s) = sc-~ s
-- sc-~ (s-∀l-no-𝕚 s upᶜ upj upᵉ upC upD) = ~s-strengthen^0 (sc-~ s) (↑ty-arr upC upD) (↑tyᶜ-e upᵉ upᶜ) (↑tyʲ-𝕚 upj)
-- sc-~ (s-∀l-no-𝕔 s upᶜ upj upᵉ upC upD) = ~s-strengthen^0 (sc-~ s) (↑ty-arr upC upD) (↑tyᶜ-e upᵉ upᶜ) (↑tyʲ-𝕔 upj)
sc-~ (s-evar-infers infs inst)
  with ih ← infs-~ infs = ~s-irrev-⊆ (~t-~s ih) (inst-⊆ inst)
{-
sc-~ (s-∀l-y-𝕚 jump x upᶜ upᵉ upC upD upj) = ~s-strengthen=0 (sc-~ x) (↑ty-arr upC upD) (↑tyᶜ-e upᵉ upᶜ)
                                              (↑tyʲ-𝕚 upj)
sc-~ (s-∀l-y-𝕔 jump x upᶜ upᵉ upC upD upj) = ~s-strengthen=0 (sc-~ x) (↑ty-arr upC upD) (↑tyᶜ-e upᵉ upᶜ)
                                              (↑tyʲ-𝕔 upj)
sc-~ (s-∀l-n-y-𝕚 jump x upᶜ upᵉ upC upD upj) = ~s-strengthen=0 (sc-~ x) (↑ty-arr upC upD) (↑tyᶜ-e upᵉ upᶜ)
                                                (↑tyʲ-𝕚 upj)
sc-~ (s-∀l-n-y-𝕔 jump x upᶜ upᵉ upC upD upj) = ~s-strengthen=0 (sc-~ x) (↑ty-arr upC upD) (↑tyᶜ-e upᵉ upᶜ)
                                                (↑tyʲ-𝕔 upj)
sc-~ (s-∀l-n-n-𝕚 jump x upᶜ upᵉ upC upD upj) = ~s-strengthen^0 (sc-~ x) (↑ty-arr upC upD) (↑tyᶜ-e upᵉ upᶜ)
                                                (↑tyʲ-𝕚 upj)
sc-~ (s-∀l-n-n-𝕔 jump x upᶜ upᵉ upC upD upj) = ~s-strengthen^0 (sc-~ x) (↑ty-arr upC upD) (↑tyᶜ-e upᵉ upᶜ)
                                                (↑tyʲ-𝕔 upj)
-}
sc-~ (s-∀l-y-𝕚 pk x upᶜ upj upᵉ upC upD) = ~s-strengthen=0 (sc-~ x) (↑ty-arr upC upD) (↑tyᶜ-e upᵉ upᶜ)
                                            (↑tyʲ-𝕚 upj)
sc-~ (s-∀l-n-y-𝕚 ¬pk x upᶜ upj upᵉ upC upD) = ~s-strengthen=0 (sc-~ x) (↑ty-arr upC upD) (↑tyᶜ-e upᵉ upᶜ)
                                               (↑tyʲ-𝕚 upj)
sc-~ (s-∀l-n-n-𝕚 ¬pk x upᶜ upj upᵉ upC upD) = ~s-strengthen^0 (sc-~ x) (↑ty-arr upC upD) (↑tyᶜ-e upᵉ upᶜ) (↑tyʲ-𝕚 upj)
sc-~ (s-∀l-y-𝕔 pk x upᶜ upj upᵉ upC upD) = ~s-strengthen=0 (sc-~ x) (↑ty-arr upC upD) (↑tyᶜ-e upᵉ upᶜ)
                                            (↑tyʲ-𝕔 upj)
sc-~ (s-∀l-n-y-𝕔 ¬pk x upᶜ upj upᵉ upC upD) = ~s-strengthen=0 (sc-~ x) (↑ty-arr upC upD) (↑tyᶜ-e upᵉ upᶜ)
                                               (↑tyʲ-𝕔 upj)
sc-~ (s-∀l-n-n-𝕔 ¬pk x upᶜ upj upᵉ upC upD) = ~s-strengthen^0 (sc-~ x) (↑ty-arr upC upD) (↑tyᶜ-e upᵉ upᶜ)
                                               (↑tyʲ-𝕔 upj)

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
-- sound-s (s-∀l-𝕚 s upᶜ upj upᵉ upC upD) = s-∀l (sound-s s) case-𝕚 (s-find0 s upᵉ upᶜ) upC upD (↑tyʲ-𝕚 upj)
-- sound-s (s-∀l-𝕔 s upᶜ upj upᵉ upC upD) = s-∀l (sound-s s) case-𝕔 (s-find0 s upᵉ upᶜ) upC upD (↑tyʲ-𝕔 upj)
sound-s (s-tapp s upᶜ upj) = s-tapp (sound-s s) upj
sound-s (s-svar-term inΓ s) with sc-~ s
... | ~sI ⊢e r = s-svar-𝕚 inΓ (sound-s s)
... | ~sC ⊢e r = s-svar-𝕔 inΓ (sound-s s)
sound-s (s-svar-tapp inΓ s) = s-svar-𝕥 inΓ (sound-s s)
-- sound-s (s-∀l-no-𝕚 s upᶜ upj upᵉ upC upD) = s-∀l-no-appear (sound-s s) case-𝕚 (s-¬ε (sc-sound s) Z Z) upC upD (↑tyʲ-𝕚 upj)
-- sound-s (s-∀l-no-𝕔 s upᶜ upj upᵉ upC upD) = s-∀l-no-appear (sound-s s) case-𝕔 (s-¬ε (sc-sound s) Z Z) upC upD (↑tyʲ-𝕔 upj)
sound-s (s-evar-infers (infs-s ⊢e infs) inst) = s-svar-𝕚 (inst-∋:= inst) (sound-infs (infs-s ⊢e infs) (inst-⊆ inst))
sound-s (s-∀l-y-𝕚 jump x upᶜ upᵉ upC upD upj) = s-∀l-peek (sound-s x) case-𝕚 (sound-peek' jump) upD upj (↑tyʲ-𝕚 upᵉ)
sound-s (s-∀l-y-𝕔 jump x upᶜ upᵉ upC upD upj) = s-∀l-peek (sound-s x) case-𝕔 (sound-peek' jump) upD upj (↑tyʲ-𝕔 upᵉ)
sound-s (s-∀l-n-y-𝕚 ¬pk x upᶜ upj upᵉ upC upD) = s-∀l-new (sound-s x) case-𝕚 (λ x₁ → ¬pk (complete-peek x₁ (sc-~ x))) (s-find0 x) upC upD (↑tyʲ-𝕚 upj)
sound-s (s-∀l-n-n-𝕚 ¬pk x upᶜ upj upᵉ upC upD) = s-∀l-no-appear (sound-s x) case-𝕚 (s-¬ε (sc-sound x) Z Z) upC upD (↑tyʲ-𝕚 upj)
sound-s (s-∀l-n-y-𝕔 ¬pk x upᶜ upj upᵉ upC upD) = s-∀l-new (sound-s x) case-𝕔 (λ x₁ → ¬pk (complete-peek x₁ (sc-~ x))) (s-find0 x) upC upD (↑tyʲ-𝕔 upj)
sound-s (s-∀l-n-n-𝕔 ¬pk x upᶜ upj upᵉ upC upD) = s-∀l-no-appear (sound-s x) case-𝕔 (s-¬ε (sc-sound x) Z Z) upC upD (↑tyʲ-𝕔 upj)

-- sound-s (s-∀l-n-y-𝕚 jump x upᶜ upᵉ upC upD upj) = s-∀l (sound-s x) case-𝕚 (s-find0 x) upC upD (↑tyʲ-𝕚 upj)
-- sound-s (s-∀l-n-y-𝕔 jump x upᶜ upᵉ upC upD upj) = s-∀l (sound-s x) case-𝕔 (s-find0 x) upC upD (↑tyʲ-𝕔 upj)
-- sound-s (s-∀l-n-n-𝕚 jump x upᶜ upᵉ upC upD upj) = s-∀l-no-appear (sound-s x) case-𝕚 (s-¬ε (sc-sound x) Z Z) upC upD (↑tyʲ-𝕚 upj)
-- sound-s (s-∀l-n-n-𝕔 jump x upᶜ upᵉ upC upD upj) = s-∀l-no-appear (sound-s x) case-𝕔 (s-¬ε (sc-sound x) Z Z) upC upD (↑tyʲ-𝕔 upj)

sound-infs (infs-z regΓ regA) inst = s-refl-∞ (⊆-sregular' inst) (⊆-⊢r (⊢r-𝕣 regA) inst)
sound-infs (infs-s ⊢e infs) inst = s-arr₂ (s-refl-∞ (⊆-sregular' inst) ((⊆-⊢r (⊢r-𝕣 (tc-⊢r ⊢e)) inst))) (sound-infs infs inst)
