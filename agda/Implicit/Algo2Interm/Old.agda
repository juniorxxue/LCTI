module Implicit.SoundCounter where

open import Implicit.Language.All hiding (_≤_)
open import Implicit.Interm.All
open import Implicit.Algo.All
open import Implicit.AlgoCounter.All

~subst0 : (Γ ,= B) ⊢ ⟨ j , A ⟩ ~ Σ
        → ⟦ B ⟧ᶜ Σ ⇘ Σ*
        → ⟦ B ⟧ A ⇘ A*
        → Γ ⊢ ⟨ j , A* ⟩ ~ Σ*
~subst0 ~Z empty st2 = ~Z
~subst0 ~∞ (fulltype st) st2 rewrite st-unique st st2 = ~∞
~subst0 (~I ⊢e j~Σ) (term st1 ste) (st-arr st2 st3) = ~I (t-subst0 ⊢e ste st2) (~subst0 j~Σ st1 st3)
~subst0 (~C ⊢e j~Σ) (term st1 ste) (st-arr st2 st3) = ~C (t-subst0 ⊢e ste st2) (~subst0 j~Σ st1 st3)

~strengthen,0 : Γ , A ⊢ ⟨ j , B ⟩ ~ Σ'
              → ↑tmᶜ0 Σ ⇘ Σ'
              → Γ ⊢ ⟨ j , B ⟩ ~ Σ
~strengthen,0 ~Z ↑tmᶜ-□ = ~Z
~strengthen,0 ~∞ ↑tmᶜ-τ = ~∞
~strengthen,0 (~I ⊢e j~Σ) (↑tmᶜ-e up-e up) = ~I (t-strengthen,0 ⊢e up-e) (~strengthen,0 j~Σ up)
~strengthen,0 (~C ⊢e j~Σ) (↑tmᶜ-e up-e up) = ~C (t-strengthen,0 ⊢e up-e) (~strengthen,0 j~Σ up)

----------------------------------------------------------------------
--+                             Typing                             +--
----------------------------------------------------------------------

tc-~ : Γ ⊢ Σ ⇒ e ⇒ A ↡ j
     → Γ ⊢ ⟨ j , A ⟩ ~ Σ

sc-~ : Γ ⊢ A ⌞ ≤ ⌝ Σ ⊣ Δ ↪ B ↡ j
     → Polarity Γ A Σ ≤
     → Δ ⊢ ⟨ j , B ⟩ ~ Σ

sound : Γ ⊢ Σ ⇒ e ⇒ A ↡ j
      → Γ ⊢ j # e ⦂ A

sound-s : Γ ⊢ A ⌞ ≤ ⌝ Σ ⊣ Δ ↪ B ↡ j
        → Polarity Γ A Σ ≤
        → Δ ⊢ j # A ≤ B

sound-find-l : Γ ⊢ A  ⌞ ≤⁺ ⌝ Σ ⊣ Δ ↪ B ↡ j
             → Closed Γ
             → Γ ⊢cᶜ Σ
             → Γ ∋^ k
             → Δ ∋= k
             → find A k j

sound-find-r : Γ ⊢ A  ⌞ ≤⁻ ⌝ τ B ⊣ Δ ↪ C ↡ j
             → Closed Γ
             → Γ ⊢c A
             → Γ ∋^ k
             → Δ ∋= k
             → find B k j

sound-find-l0 : Γ ,^ ⊢ A ⌞ ≤⁺ ⌝ [ e' ]↝ Σ' ⊣ Δ ,= B ↪ C `→ D ↡ j
              → Closed Γ
              → Γ ⊢cᶜ [ e ]↝ Σ
              → ↑tyᵉ0 e ⇘ e'
              → ↑tyᶜ0 Σ ⇘ Σ'
              → find A #0 j
sound-find-l0 s cloΓ clo up1 up2 = sound-find-l s (clo-S^ cloΓ) (⊢cᶜ-weaken^0 clo (↑tyᶜ-e up1 up2)) Z Z

tc-~ (⊢lit cloΓ) = ~Z
tc-~ (⊢var cloΓ x∈Γ) = ~Z
tc-~ (⊢ann ⊢e) = ~Z
tc-~ (⊢app ⊢e) with tc-~ ⊢e
... | ~I ⊢e₁ r = r
... | ~C ⊢e₁ r = r
tc-~ (⊢lam₁ ⊢e) with ⊢id0 (tc-sound ⊢e)
... | refl = ~∞
tc-~ (⊢lam₂ ⊢e up-c ⊢e₁) = ~I (sound ⊢e) (~strengthen,0 (tc-~ ⊢e₁) up-c)
tc-~ (⊢sub ⊢e ne gc cloΣ s) = sc-~ s (polar-r (⊢closeΓ (tc-sound ⊢e)) cloΣ)
tc-~ (⊢tabs ⊢e) = ~Z

sc-~ s-int pr = ~∞
sc-~ (s-empty clo) pr = ~Z
sc-~ s-var pr = ~∞
sc-~ (s-ex-l^ x-in inst) pr = ~∞
sc-~ (s-ex-l= x-in s) pr = ~∞
sc-~ (s-ex-r^ x-in inst) pr = ~∞
sc-~ (s-ex-r= x-in s) pr = ~∞
sc-~ (s-arr s s₁) pr = ~∞
sc-~ (s-term-c ⊢e s) pr = ~C (t-⊆-prv (sound ⊢e) (s-⊆ (sc-sound s) (polar-tm-r pr))) (sc-~ s (polar-tm-r pr))
sc-~ s'@(s-term-o opnA ⊢e s s₁) pr =
  ~I (t-⊆-prv (sound ⊢e) (s-⊆ (sc-sound s') pr)) (sc-~ s₁ (polar-⊆ (polar-tm-r pr)
    (s-⊆ (sc-sound s) (polar-l (⊢closeΓ (tc-sound ⊢e)) (⊢closeA (tc-sound ⊢e))))))
sc-~ (s-∀ s) pr with ≤id0 (sc-sound s)
... | refl = ~∞
sc-~ (s-∀l s upᶜ upᵉ st₁ st₂) (polar-r cloΓ cloΣ) =
  ~subst0 (sc-~ s (polar-r (clo-S^ cloΓ) (⊢cᶜ-weaken^0 cloΣ (↑tyᶜ-e upᵉ upᶜ)))) (↑tyᶜ-st (↑tyᶜ-e upᵉ upᶜ)) (st-arr st₁ st₂)

sound (⊢lit cloΓ) = ⊢lit cloΓ
sound (⊢var cloΓ x∈Γ) = ⊢var cloΓ x∈Γ
sound (⊢ann ⊢e) with sound ⊢e
... | r with ⊢id0 (tc-sound ⊢e)
... | refl = ⊢ann r
sound (⊢app ⊢e) with tc-~ ⊢e
... | ~I ⊢e₁ r = ⊢app₂ (sound ⊢e) ⊢e₁
... | ~C ⊢e₁ r = ⊢app₁ (sound ⊢e) ⊢e₁
sound (⊢lam₁ ⊢e) = ⊢lam₁ (sound ⊢e)
sound (⊢lam₂ ⊢e up-c ⊢e₁) = ⊢lam₂ (sound ⊢e₁)
sound (⊢sub ⊢e ne gc cloΣ s) with sc-~ s (polar-r (⊢closeΓ (tc-sound ⊢e)) cloΣ)
... | r = ⊢sub (sound ⊢e) (sound-s s (polar-r (⊢closeΓ (tc-sound ⊢e)) cloΣ)) (NonEmpty-NonZ ne r)
sound (⊢tabs ⊢e) = ⊢tabs (sound ⊢e)

sound-s s-int pr = s-int (polar-closed pr)
sound-s (s-empty clo) pr = s-refl (polar-closed pr) clo
sound-s s-var (polar-l cloΓ (⊢c-var-∙ inΓ)) = s-var-∙ cloΓ inΓ
sound-s s-var (polar-l cloΓ (⊢c-var-= inΓ)) = s-var-= cloΓ inΓ
sound-s s-var (polar-r cloΓ (⊢c-τ (⊢c-var-∙ inΓ))) = s-var-∙ cloΓ inΓ
sound-s s-var (polar-r cloΓ (⊢c-τ (⊢c-var-= inΓ))) = s-var-= cloΓ inΓ
sound-s (s-ex-l^ x-in inst) (polar-r cloΓ (⊢c-τ cloA)) = let ext = inst-⊆ inst cloA
                      in s-var-l (inst-in inst) (s-refl-∞ (⊆-closed cloΓ ext) (⊆-cloA cloA ext))
sound-s s'@(s-ex-l= x-in s) pr with ≤id0 (sc-sound s)
... | refl = let ext = (s-⊆ (sc-sound s') pr) in s-var-l (⊆-in:= x-in ext ) (sound-s s (polar-in-l pr x-in))
sound-s s'@(s-ex-r^ x-in inst) pr@(polar-l cloΓ cloA) = let ext = s-⊆ (sc-sound s') pr
                      in s-var-r (inst-in inst) (s-refl-∞ (⊆-closed cloΓ ext) (⊆-cloA cloA ext))
sound-s s'@(s-ex-r= x-in s) pr with ≤id0 (sc-sound s)
... | refl = let ext = (s-⊆ (sc-sound s') pr) in s-var-r (⊆-in:= x-in ext ) (sound-s s (polar-in-r pr x-in))
sound-s (s-arr s s₁) pr with ≤id0 (sc-sound s) | ≤id0 (sc-sound s₁)
... | refl | refl = let pr-r = polar-arr-r (polar-⊆ pr (s-⊆ (sc-sound s) (polar-arr-l pr)))
  in s-arr₁ (s-⊆-prv (sound-s s (polar-arr-l pr)) (s-⊆ (sc-sound s₁) pr-r)) (sound-s s₁ pr-r)
sound-s s'@(s-term-c ⊢e s) pr with ⊢id0 (tc-sound ⊢e)
... | refl = let ext = s-⊆ (sc-sound s') pr in s-arr₃ (⊆-cloA (⊢closeA (tc-sound ⊢e)) ext) (sound-s s (polar-tm-r pr))
sound-s s'@(s-term-o opnA ⊢e s s₁) pr with ≤id0 (sc-sound s)
... | refl = let pr-l = polar-l (polar-closed pr) (⊢closeA (tc-sound ⊢e))
                 pr-r = polar-⊆ (polar-tm-r pr) (s-⊆ (sc-sound s) pr-l)
  in s-arr₂ (s-⊆-prv (sound-s s pr-l) (s-⊆ (sc-sound s₁) pr-r)) (sound-s s₁ pr-r)
sound-s (s-∀ s) pr = s-∀ (sound-s s (polar-∀ pr))
sound-s (s-∀l s upᶜ upᵉ st₁ st₂) (polar-r cloΓ cloΣ) = let pr' = polar-r (clo-S^ cloΓ) (⊢cᶜ-weaken^0 cloΣ (↑tyᶜ-e upᵉ upᶜ))
  in s-∀l (sound-s s pr') (ic-aux (sc-~ s pr')) (sound-find-l0 s cloΓ cloΣ upᵉ upᶜ) st₁ st₂
    where ic-aux : Δ ,= B ⊢ ⟨ j , C `→ D ⟩ ~ [ e' ]↝ Σ'
                 → 𝕚𝕔 j
          ic-aux (~I ⊢e s) = case-𝕚
          ic-aux (~C ⊢e s) = case-𝕔

sound-find-l s-int cloΓ cloA inΓ inΔ = ⊥-elim (∋^-∋=-false inΓ inΔ)
sound-find-l (s-empty clo) cloΓ cloA inΓ inΔ = ⊥-elim (∋^-∋=-false inΓ inΔ)
sound-find-l s-var cloΓ cloA inΓ inΔ = ⊥-elim (∋^-∋=-false inΓ inΔ)
sound-find-l (s-ex-l^ x-in inst) cloΓ cloA inΓ inΔ with inst-affect-one inst inΓ inΔ
... | refl = f-∞ ε-var
sound-find-l (s-ex-l= x-in s) cloΓ (⊢c-τ cloA) inΓ inΔ with s-all-closed (sc-sound s) cloΓ (∋=-closed cloΓ x-in) (⊢c-τ cloA)
... | refl = ⊥-elim (∋^-∋=-false inΓ inΔ)
sound-find-l (s-ex-r= x-in s) cloΓ cloA inΓ inΔ = sound-find-l s cloΓ (⊢c-τ (∋=-closed cloΓ x-in)) inΓ inΔ
sound-find-l (s-arr s s₁) cloΓ (⊢c-τ (⊢c-arr cloA cloA₁)) inΓ inΔ with s-⊆ (sc-sound s) (polar-l cloΓ cloA)
... | ext with s-⊆-exsol ext inΓ
... | is-ex inΓ₁ = find-arr-r (sound-find-l s₁ (⊆-closed cloΓ ext) (⊢c-τ (⊆-cloA cloA₁ ext)) inΓ₁ inΔ)
... | is-sol inΓ₁ = find-arr-l (sound-find-r s cloΓ cloA inΓ inΓ₁)
sound-find-l (s-term-c ⊢e s) cloΓ (⊢c-term cloe cloA) inΓ inΔ with ⊢id0 (tc-sound ⊢e)
... | refl = f-arr-𝕔 (⊢c-^∈-¬ε (⊢close-τ (tc-sound ⊢e)) inΓ) (sound-find-l s (⊢closeΓ (tc-sound ⊢e)) cloA inΓ inΔ)
sound-find-l (s-term-o opnA ⊢e s s₁) cloΓ (⊢c-term cloe cloA) inΓ inΔ with s-⊆ (sc-sound s) (polar-l cloΓ (⊢closeA (tc-sound ⊢e)))
... | ext with s-⊆-exsol ext inΓ
... | is-ex inΓ₁ = f-arr-𝕚-r (sound-find-l s₁ (⊆-closed cloΓ ext) (⊆-cloAᶜ cloA ext) inΓ₁ inΔ)
... | is-sol inΓ₁ = f-arr-𝕚-l (find-ε (sound-find-r s cloΓ (⊢closeA (tc-sound ⊢e)) inΓ inΓ₁))
sound-find-l (s-∀ s) cloΓ (⊢c-τ (⊢c-∀ cloA)) inΓ inΔ = f-∀ (sound-find-l s (clo-S∙ cloΓ) (⊢c-τ cloA) (S∙ inΓ) (S∙ inΔ))
sound-find-l (s-∀l s upᶜ upᵉ st₁ st₂) cloΓ cloA inΓ inΔ = f-∀ (sound-find-l s (clo-S^ cloΓ) (⊢cᶜ-weaken^0 cloA (↑tyᶜ-e upᵉ upᶜ)) (S^ inΓ) (S= inΔ))

sound-find-r s-int cloΓ cloB inΓ inΔ = ⊥-elim (∋^-∋=-false inΓ inΔ)
sound-find-r s-var cloΓ cloB inΓ inΔ = ⊥-elim (∋^-∋=-false inΓ inΔ)
sound-find-r (s-ex-l= x-in s) cloΓ cloB inΓ inΔ = sound-find-r s cloΓ (∋=-closed cloΓ x-in) inΓ inΔ
sound-find-r (s-ex-r^ x-in inst) cloΓ cloB inΓ inΔ with inst-affect-one inst inΓ inΔ
... | refl = f-∞ ε-var
sound-find-r (s-ex-r= x-in s) cloΓ cloB inΓ inΔ with s-all-closed (sc-sound s) cloΓ cloB (⊢c-τ (∋=-closed cloΓ x-in))
... | refl = ⊥-elim (∋^-∋=-false inΓ inΔ)
sound-find-r (s-arr s s₁) cloΓ (⊢c-arr cloB cloB₁) inΓ inΔ with s-⊆ (sc-sound s) (polar-r cloΓ (⊢c-τ cloB))
... | ext with s-⊆-exsol ext inΓ
... | is-ex inΓ₁ = find-arr-r (sound-find-r s₁ (⊆-closed cloΓ ext) (⊆-cloA cloB₁ ext) inΓ₁ inΔ)
... | is-sol inΓ₁ = find-arr-l (sound-find-l s cloΓ (⊢c-τ cloB) inΓ inΓ₁)
sound-find-r (s-∀ s) cloΓ (⊢c-∀ cloB) inΓ inΔ = f-∀ (sound-find-r s (clo-S∙ cloΓ) cloB (S∙ inΓ) (S∙ inΔ))

----------------------------------------------------------------------
--+                             Bridge                             +--
----------------------------------------------------------------------

data JustType (Γ : Env n m) (Σ : Context n m) (e : Term n m) (A : Type m) : Set where
  typs : ∀ {j}
    → (j~Σ : Γ ⊢ ⟨ j , A ⟩ ~ Σ)
    → (⊢e : Γ ⊢ Σ ⇒ e ⇒ A ↡ j)
    → JustType Γ Σ e A

data JustSub (Γ : Env n m) (A : Type m) (≤ : Polar) (Σ : Context n m) (Δ : Env n m) (B : Type m) : Set where
  subs : ∀ {j}
    → (j~Σ : Δ ⊢ ⟨ j , B ⟩ ~ Σ)
    → (s : Γ ⊢ A ⌞ ≤ ⌝ Σ ⊣ Δ ↪ B ↡ j)
    → JustSub Γ A ≤ Σ Δ B

t-imply : Γ ⊢ Σ ⇒ e ⇒ A
        → JustType Γ Σ e A

s-imply : Γ ⊢ A ⌞ ≤ ⌝ Σ ⊣ Δ ↪ B
        → Polarity Γ A Σ ≤
        → JustSub Γ A ≤ Σ Δ B

sound-0 : Γ ⊢ □ ⇒ e ⇒ A
        → Γ ⊢ Z # e ⦂ A
sound-0 ⊢e with t-imply ⊢e
... | typs ~Z ⊢e₁ = sound ⊢e₁

sound-∞ : Γ ⊢ τ B ⇒ e ⇒ A
        → Γ ⊢ ∞ # e ⦂ B
sound-∞ ⊢e with t-imply ⊢e
... | typs ~∞ ⊢e₁ = sound ⊢e₁

t-imply (⊢lit cloΓ) = typs ~Z (⊢lit cloΓ)
t-imply (⊢var cloΓ x∈Γ) = typs ~Z (⊢var cloΓ x∈Γ)
t-imply (⊢ann ⊢e) with t-imply ⊢e
... | typs ~∞ ⊢e₁ = typs ~Z (⊢ann ⊢e₁)
t-imply (⊢app ⊢e) with t-imply ⊢e
... | typs (~I ⊢e₂ j~Σ) ⊢e₁ = typs j~Σ (⊢app ⊢e₁)
... | typs (~C ⊢e₂ j~Σ) ⊢e₁ = typs j~Σ (⊢app ⊢e₁)
t-imply (⊢lam₁ ⊢e) with t-imply ⊢e
... | typs ~∞ ⊢e₁ = typs ~∞ (⊢lam₁ ⊢e₁)
t-imply (⊢lam₂ ⊢e up-c ⊢e₁) with t-imply ⊢e | t-imply ⊢e₁
... | typs ~Z ⊢e₂ | typs j~Σ₁ ⊢e₃ = typs (~I (sound-0 ⊢e) (~strengthen,0 j~Σ₁ up-c)) (⊢lam₂ ⊢e₂ up-c ⊢e₃)
t-imply (⊢sub ⊢e ne gc cloΣ s) with s-imply s (polar-r (⊢closeΓ ⊢e) cloΣ) | t-imply ⊢e
... | subs j~Σ s₁ | typs ~Z ⊢e₁ = typs j~Σ (⊢sub ⊢e₁ ne gc cloΣ s₁)
t-imply (⊢tabs ⊢e) with t-imply ⊢e
... | typs ~Z ⊢e₁ = typs ~Z (⊢tabs ⊢e₁)

s-imply s-int pr = subs ~∞ s-int
s-imply (s-empty clo) pr = subs ~Z (s-empty clo)
s-imply s-var pr = subs ~∞ s-var
s-imply (s-ex-l^ x-in inst) pr = subs ~∞ (s-ex-l^ x-in inst)
s-imply (s-ex-l= x-in s) pr with s-imply s (polar-in-l pr x-in)
... | subs ~∞ s₁ = subs ~∞ (s-ex-l= x-in s₁)
s-imply (s-ex-r^ x-in inst) pr = subs ~∞ (s-ex-r^ x-in inst)
s-imply (s-ex-r= x-in s) pr with s-imply s (polar-in-r pr x-in)
... | subs ~∞ s₁ = subs ~∞ (s-ex-r= x-in s₁)
s-imply (s-arr s s₁) pr with s-imply s (polar-arr-l pr) | s-imply s₁ (polar-⊆ (polar-arr-r pr) (s-⊆ s (polar-arr-l pr)))
... | subs ~∞ s₂ | subs ~∞ s₃ = subs ~∞ (s-arr s₂ s₃)
s-imply (s-term-c ⊢e s) pr with s-imply s (polar-tm-r pr) | t-imply ⊢e
... | subs j~Σ s₁ | typs ~∞ ⊢e₁ = subs (~C (t-⊆-prv (sound-∞ ⊢e) (s-⊆ s (polar-tm-r pr))) j~Σ) (s-term-c ⊢e₁ s₁)
s-imply s'@(s-term-o opnA ⊢e s s₁) pr@(polar-r cloΓ cloΣ) with s-imply s (polar-l cloΓ (⊢closeA ⊢e))
                                                          | s-imply s₁ (polar-⊆ (polar-tm-r pr) (s-⊆ s (polar-l cloΓ (⊢closeA ⊢e))))
                                                          | t-imply ⊢e
... | subs ~∞ s₂ | subs j~Σ s₃ | typs ~Z ⊢e₁ = subs (~I (t-⊆-prv (sound-0 ⊢e) (s-⊆ s' pr)) j~Σ) (s-term-o opnA ⊢e₁ s₂ s₃)
s-imply (s-∀ s) pr with s-imply s (polar-∀ pr)
... | subs ~∞ s₁ = subs ~∞ (s-∀ s₁)
s-imply (s-∀l s upᶜ upᵉ st₁ st₂) (polar-r cloΓ cloΣ) with s-imply s (polar-r (clo-S^ cloΓ) (⊢cᶜ-weaken^0 cloΣ (↑tyᶜ-e upᵉ upᶜ)))
... | subs j~Σ s₁ = subs (~subst0 j~Σ (↑tyᶜ-st (↑tyᶜ-e upᵉ upᶜ)) (st-arr st₁ st₂)) (s-∀l s₁ upᶜ upᵉ st₁ st₂)
