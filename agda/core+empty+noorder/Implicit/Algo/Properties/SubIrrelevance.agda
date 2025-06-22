{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --allow-incomplete-matches #-}
module Implicit.Algo.Properties.SubIrrelevance where

-- the irrelevance in altering (unsolving unrelated solutions in) subtyping environments

open import Implicit.Language.All
open import Implicit.Algo.Base
open import Implicit.Algo.Properties.Extension
open import Implicit.Algo.Properties.Regularity
open import Implicit.Algo.Properties.Irrelevance
open import Implicit.Algo.Properties.OpenK

-- stays the same between [0 .. k]
-- change from Γ to Δ from k + 1
infix 3 _⊆_∣_⊆_by_
data _⊆_∣_⊆_by_ : Env n m → Env n m → Env n m → Env n m → Fin (1 + m) → Set where

  ⊆⊆-Z : (ext : Γ ⊆ Δ)
       → Γ ⊆ Δ ∣ Γ ⊆ Δ by #0
--  ⊆⊆-S, : Γ₁ ⊆ Δ₁ ∣ Γ₂ ⊆ Δ₂ by k
--        → Γ₁ , A ⊆ Δ₁ , A ∣ Γ₂ , A ⊆ Δ₂ , A by k
  ⊆-S^^  : Γ₁ ⊆ Δ₁ ∣ Γ₂ ⊆ Δ₂ by k
        → Γ₁ ,^ ⊆ Δ₁ ,^ ∣ Γ₂ ,^ ⊆ Δ₂ ,^ by #S k
  ⊆-S∙∙  : Γ₁ ⊆ Δ₁ ∣ Γ₂ ⊆ Δ₂ by k
        → Γ₁ ,∙ ⊆ Δ₁ ,∙ ∣ Γ₂ ,∙ ⊆ Δ₂ ,∙ by #S k
  ⊆-S==  : Γ₁ ⊆ Δ₁ ∣ Γ₂ ⊆ Δ₂ by k
         → (regA : Γ₁ ⊢r A)
         → Γ₁ ,= A ⊆ Δ₁ ,= A ∣ Γ₂ ,= A ⊆ Δ₂ ,= A by #S k
  ⊆-S^=  : Γ₁ ⊆ Δ₁ ∣ Γ₂ ⊆ Δ₂ by k
         → (regA : Γ₁ ⊢r A)
         → Γ₁ ,^ ⊆ Δ₁ ,^ ∣ Γ₂ ,= A ⊆ Δ₂ ,= A by #S k

⊆⊆-one-input : Γ₁ ⊆ Δ₁ ∣ Γ₁ ⊆ Δ₂ by k
             → Δ₁ ≡ Δ₂
⊆⊆-one-input (⊆⊆-Z ext) = refl
⊆⊆-one-input (⊆-S^^ exts) rewrite ⊆⊆-one-input exts = refl
⊆⊆-one-input (⊆-S∙∙ exts) rewrite ⊆⊆-one-input exts = refl
⊆⊆-one-input (⊆-S== exts regA) rewrite ⊆⊆-one-input exts = refl

⊆⊆-⊆-l : Γ₁ ⊆ Δ₁ ∣ Γ₂ ⊆ Δ₂ by k
       → Γ₁ ⊆ Δ₁
⊆⊆-⊆-l (⊆⊆-Z ext) = ext
⊆⊆-⊆-l (⊆-S^^ exts) = evar (⊆⊆-⊆-l exts)
⊆⊆-⊆-l (⊆-S∙∙ exts) = uvar (⊆⊆-⊆-l exts)
⊆⊆-⊆-l (⊆-S== exts regA) = svar (⊆⊆-⊆-l exts) regA
⊆⊆-⊆-l (⊆-S^= exts regA) = evar (⊆⊆-⊆-l exts)


⊆⊆-⊆-ll : Γ₁ ⊆ Δ₁ ∣ Γ₂ ⊆ Δ₂ by k
        → Γ₁ ⊆ Γ₂
⊆⊆-⊆-ll (⊆⊆-Z ext) = ⊆-refl (⊆-sregular ext)
⊆⊆-⊆-ll (⊆-S^^ exts) = evar (⊆⊆-⊆-ll exts)
⊆⊆-⊆-ll (⊆-S∙∙ exts) = uvar (⊆⊆-⊆-ll exts)
⊆⊆-⊆-ll (⊆-S== exts regA) = svar (⊆⊆-⊆-ll exts) regA
⊆⊆-⊆-ll (⊆-S^= exts regA)
  with ih ← ⊆⊆-⊆-ll exts = evar-sol (⊆⊆-⊆-ll exts) (⊆-⊢r regA ih)

⊆⊆-⊆-r : Γ₁ ⊆ Δ₁ ∣ Γ₂ ⊆ Δ₂ by k
       → Γ₂ ⊆ Δ₂
⊆⊆-⊆-r (⊆⊆-Z ext) = ext
⊆⊆-⊆-r (⊆-S^^ exts) = evar (⊆⊆-⊆-r exts)
⊆⊆-⊆-r (⊆-S∙∙ exts) = uvar (⊆⊆-⊆-r exts)
⊆⊆-⊆-r (⊆-S== exts regA)
  with ext ← ⊆⊆-⊆-ll exts = svar (⊆⊆-⊆-r exts) (⊆-⊢r regA ext)
⊆⊆-⊆-r (⊆-S^= exts regA)
  with ext ← ⊆⊆-⊆-ll exts = svar (⊆⊆-⊆-r exts) (⊆-⊢r regA ext)

⊆⊆-inst : [ A / X ] Γ₁ ⟹ Γ₂
        → Γ₁ ⊆ Δ₁ ∣ Γ₂ ⊆ Δ₂ by k
        → X #< k
        → [ A / X ] Δ₁ ⟹ Δ₂
⊆⊆-inst (⟹^0 up regA env) (⊆-S^= exts regA₁) (s≤s lt)
  with refl ← ⊆⊆-one-input exts
  with ext ← ⊆⊆-⊆-l exts = ⟹^0 up (⊆-⊢r regA ext) (⊆-sregular' ext)
⊆⊆-inst (⟹^S inst up1) (⊆-S^^ exts) (s≤s lt) = ⟹^S (⊆⊆-inst inst exts lt) up1
⊆⊆-inst (⟹∙S inst up1) (⊆-S∙∙ exts) (s≤s lt) = ⟹∙S (⊆⊆-inst inst exts lt) up1
⊆⊆-inst (⟹=S inst up1 regB) (⊆-S== exts regA) (s≤s lt)
  with ext ← ⊆⊆-⊆-l exts = ⟹=S (⊆⊆-inst inst exts lt) up1 (⊆-⊢r regB ext)

⊆⊆-Ω-exist : Γ₁ ⊆ Δ₁ ∣ Γ₂ ⊆ Δ₂ by k
           → Γ₁ ⊆ Ω
           → Ω ⊆ Γ₂
           → ∃[ Ω' ]( (Γ₁ ⊆ Δ₁ ∣ Ω ⊆ Ω' by k) × (Ω ⊆ Ω' ∣ Γ₂ ⊆ Δ₂ by k))
⊆⊆-Ω-exist {Δ₁ = Δ₁} (⊆⊆-Z ext) ext1 ext2
  with refl ← ⊆-antisymm ext1 ext2 = ⟨ Δ₁ , ⟨ ⊆⊆-Z ext , ⊆⊆-Z ext ⟩ ⟩
⊆⊆-Ω-exist (⊆-S^^ exts) (evar ext1) (evar ext2) = ⟨ ⊆⊆-Ω-exist exts ext1 ext2 .proj₁ ,^ ,
                                                   ⟨ ⊆-S^^ (⊆⊆-Ω-exist exts ext1 ext2 .proj₂ .proj₁) ,
                                                   ⊆-S^^ (⊆⊆-Ω-exist exts ext1 ext2 .proj₂ .proj₂) ⟩ ⟩
⊆⊆-Ω-exist (⊆-S∙∙ exts) (uvar ext1) (uvar ext2) = ⟨ ⊆⊆-Ω-exist exts ext1 ext2 .proj₁ ,∙ ,
                                                   ⟨ ⊆-S∙∙ (⊆⊆-Ω-exist exts ext1 ext2 .proj₂ .proj₁) ,
                                                   ⊆-S∙∙ (⊆⊆-Ω-exist exts ext1 ext2 .proj₂ .proj₂) ⟩ ⟩
⊆⊆-Ω-exist (⊆-S== {A = A} exts regA) (svar ext1 regA₁) (svar ext2 regA₂) = ⟨ ⊆⊆-Ω-exist exts ext1 ext2 .proj₁ ,= A ,
                                                                    ⟨ ⊆-S== (⊆⊆-Ω-exist exts ext1 ext2 .proj₂ .proj₁) regA ,
                                                                    ⊆-S== (⊆⊆-Ω-exist exts ext1 ext2 .proj₂ .proj₂) regA₂ ⟩ ⟩
⊆⊆-Ω-exist (⊆-S^= exts regA) (evar ext1) (evar-sol ext2 regA₁)
  with ⟨ Ω' , ⟨ exts1 , exts2 ⟩ ⟩ ← ⊆⊆-Ω-exist exts ext1 ext2 = ⟨ (Ω' ,^) , ⟨ (⊆-S^^ exts1) , ⊆-S^= exts2 (⊆-⊢r regA ext1) ⟩ ⟩
⊆⊆-Ω-exist (⊆-S^= {A = A} exts regA) (evar-sol ext1 regA₁) (svar ext2 regA₂) = ⟨ ⊆⊆-Ω-exist exts ext1 ext2 .proj₁ ,= A ,
                                                                        ⟨ ⊆-S^= (⊆⊆-Ω-exist exts ext1 ext2 .proj₂ .proj₁) regA ,
                                                                        ⊆-S== (⊆⊆-Ω-exist exts ext1 ext2 .proj₂ .proj₂) regA₂ ⟩ ⟩


ss+-⊆-prv-gen : Γ₁ ⊢ A ⌞ ≤⁺ ⌝ B ⊣ Γ₂
              → Γ₁ ∤ k ⊢o A
              → Γ₁ ⊆ Δ₁ ∣ Γ₂ ⊆ Δ₂ by k
              → Δ₁ ⊢ A ⌞ ≤⁺ ⌝ B ⊣ Δ₂

ss--⊆-prv-gen : Γ₁ ⊢ A ⌞ ≤⁻ ⌝ B ⊣ Γ₂
              → Γ₁ ∤ k ⊢o B
              → Γ₁ ⊆ Δ₁ ∣ Γ₂ ⊆ Δ₂ by k
              → Δ₁ ⊢ A ⌞ ≤⁻ ⌝ B ⊣ Δ₂

ss+-⊆-prv-gen (s-int regΓ) opn-int exts
  with refl ← ⊆⊆-one-input exts
  with ext ← ⊆⊆-⊆-l exts = s-int (⊆-sregular' ext)
ss+-⊆-prv-gen (s-var-∙ regΓ inΔ) (opn-var x) exts
  with refl ← ⊆⊆-one-input exts
  with ext ← ⊆⊆-⊆-l exts = s-var-∙ (⊆-sregular' ext) (⊆-∋∙ inΔ ext)
ss+-⊆-prv-gen (s-ex-l^ inst) (opn-var x) exts = s-ex-l^ (⊆⊆-inst inst exts (⊢oˣ-∋^-#< x (inst-∋^ inst)))
ss+-⊆-prv-gen (s-ex-l= regΓ x-in) (opn-var x) exts
  with refl ← ⊆⊆-one-input exts
  with ext ← ⊆⊆-⊆-l exts = s-ex-l= (⊆-sregular' ext) (⊆-∋:= x-in ext)
ss+-⊆-prv-gen (s-arr s s₁) (opn-arr opnA opnA₁) exts
  with ⟨ Ω' , ⟨ exts1 , exts2 ⟩ ⟩ ← ⊆⊆-Ω-exist exts (ss-⊆ s) (ss-⊆ s₁)
  = s-arr (ss--⊆-prv-gen s opnA exts1) (ss+-⊆-prv-gen s₁ (⊢ok-⊆ opnA₁ (ss-⊆ s)) exts2)
ss+-⊆-prv-gen (s-∀ s) (opn-∀ opnA) exts = s-∀ (ss+-⊆-prv-gen s opnA (⊆-S∙∙ exts))
ss+-⊆-prv-gen (s-arr-n s s₁) (opn-arr opnA opnA₁) exts = {!!}

ss--⊆-prv-gen (s-int regΓ) opn-int exts
  with refl ← ⊆⊆-one-input exts
  with ext ← ⊆⊆-⊆-l exts = s-int (⊆-sregular' ext)
ss--⊆-prv-gen (s-var-∙ regΓ inΔ) (opn-var x) exts
  with refl ← ⊆⊆-one-input exts
  with ext ← ⊆⊆-⊆-l exts = s-var-∙ (⊆-sregular' ext) (⊆-∋∙ inΔ ext)
ss--⊆-prv-gen (s-ex-r^ inst) (opn-var x) exts = s-ex-r^ (⊆⊆-inst inst exts (⊢oˣ-∋^-#< x (inst-∋^ inst)))
ss--⊆-prv-gen (s-ex-r= regΓ x-in) (opn-var x) exts
  with refl ← ⊆⊆-one-input exts
  with ext ← ⊆⊆-⊆-l exts = s-ex-r= (⊆-sregular' ext) (⊆-∋:= x-in ext)
ss--⊆-prv-gen (s-arr s s₁) (opn-arr opnA opnA₁) exts
  with ⟨ Ω' , ⟨ exts1 , exts2 ⟩ ⟩ ← ⊆⊆-Ω-exist exts (ss-⊆ s) (ss-⊆ s₁)
  = s-arr (ss+-⊆-prv-gen s opnA exts1) (ss--⊆-prv-gen s₁ (⊢ok-⊆ opnA₁ (ss-⊆ s)) exts2)
ss--⊆-prv-gen (s-∀ s) (opn-∀ opnA) exts = s-∀ (ss--⊆-prv-gen s opnA (⊆-S∙∙ exts))
ss--⊆-prv-gen (s-arr-n s s₁) (opn-arr opnA opnA₁) exts = {!!}

exts-∋^-prv : Γ₁ ∋^ X
            → Γ₁ ⊆ Δ₁ ∣ Γ₂ ⊆ Δ₂ by k
            → X #< k
            → Δ₁ ∋^ X
exts-∋^-prv Z (⊆-S^^ exts) lt = Z
exts-∋^-prv Z (⊆-S^= exts regA) lt = Z
exts-∋^-prv (S∙ inΓ) (⊆-S∙∙ exts) (s≤s lt) = S∙ (exts-∋^-prv inΓ exts lt)
exts-∋^-prv (S= inΓ) (⊆-S== exts regA) (s≤s lt) = S= (exts-∋^-prv inΓ exts lt)
exts-∋^-prv (S^ inΓ) (⊆-S^^ exts) (s≤s lt) = S^ (exts-∋^-prv inΓ exts lt)
exts-∋^-prv (S^ inΓ) (⊆-S^= exts regA) (s≤s lt) = S^ (exts-∋^-prv inΓ exts lt)
exts-∋^-prv (S, inΓ) (⊆⊆-Z ext) ()

exts-open-prv : Γ₁ ⊆ Δ₁ ∣ Γ₂ ⊆ Δ₂ by k
              → Γ₁ ⊢o A
              → Γ₁ ∤ k ⊢o A
              → Δ₁ ⊢o A
exts-open-prv exts (⊢o-var-^ x) (opn-var x₁) = ⊢o-var-^ (exts-∋^-prv x exts (⊢oˣ-∋^-#< x₁ x))
exts-open-prv exts (⊢o-arr-l opnA) (opn-arr opnk opnk₁) = ⊢o-arr-l (exts-open-prv exts opnA opnk)
exts-open-prv exts (⊢o-arr-r opnA) (opn-arr opnk opnk₁) = ⊢o-arr-r (exts-open-prv exts opnA opnk₁)
exts-open-prv exts (⊢o-∀ opnA) (opn-∀ opnk) = ⊢o-∀ (exts-open-prv (⊆-S∙∙ exts) opnA opnk)


s-⊆-prv-gen : Γ₁ ⊢ A ≤⁺ Σ ⊣ Γ₂ ↪ B
            → Γ₁ ∤ k ⊢o A
            → Γ₁ ⊆ Δ₁ ∣ Γ₂ ⊆ Δ₂ by k
            → Δ₁ ⊢ A ≤⁺ Σ ⊣ Δ₂ ↪ B
s-⊆-prv-gen (s-empty regΓ cloA grd) opnA exts
  with ext ← ⊆⊆-⊆-l exts
  with refl ← ⊆⊆-one-input exts
  = s-empty (⊆-sregular' ext) (⊆-⊢c cloA ext) (⊆-⊢c-≫' ext cloA grd)
s-⊆-prv-gen (s-type ss) opnA exts = s-type (ss+-⊆-prv-gen ss opnA exts)
s-⊆-prv-gen (s-term-c ap ⊢e s) (opn-arr opnA opnA₁) exts
  with ext ← ⊆⊆-⊆-l exts
  = s-term-c {!!} (t-irrev-⊆ ⊢e ext) (s-⊆-prv-gen s opnA₁ exts)
s-⊆-prv-gen (s-term-o ⊢e ss s) (opn-arr opnA opnA₂) exts
  with ext ← ⊆⊆-⊆-l exts
  with ⟨ Ω' , ⟨ exts1 , exts2 ⟩ ⟩ ← ⊆⊆-Ω-exist exts (ss-⊆ ss) (s-⊆ s)
  = s-term-o (t-irrev-⊆ ⊢e ext) (ss--⊆-prv-gen ss opnA exts1) (s-⊆-prv-gen s (⊢ok-⊆ opnA₂ (ss-⊆ ss)) exts2)
s-⊆-prv-gen {k = k} (s-∀l s upᶜ upᵉ upC upD) (opn-∀ opnA) exts
  with reg-S= r regA ← s-env-out s
  with ext ← ⊆⊆-⊆-ll exts
  = s-∀l (s-⊆-prv-gen {k = #S k} s (⊢ok-◈0 opnA) (⊆-S^= exts (⊆-⊢r' regA ext))) upᶜ upᵉ upC upD
s-⊆-prv-gen (s-∀l-no s upᶜ upᵉ upC upD) (opn-∀ opnA) exts = s-∀l-no (s-⊆-prv-gen s (⊢ok-◈0 opnA) (⊆-S^^ exts)) upᶜ upᵉ upC upD
s-⊆-prv-gen (s-tapp s upᶜ) (opn-∀ opnA) exts
  with reg-S= r regA ← s-env-in s = s-tapp (s-⊆-prv-gen s (⊢ok-∙⟹0 opnA regA) (⊆-S== exts regA)) upᶜ
s-⊆-prv-gen (s-svar-term x s) (opn-var x₁) exts
  with ext ← ⊆⊆-⊆-l exts
  with refl ← ⊆⊆-one-input exts = s-svar-term (⊆-∋:= x ext) (s-⊆-prv-gen s (⊢r-⊢ok (∋:=-⊢r (s-env-in s) x)) exts)
s-⊆-prv-gen (s-svar-tapp x s) (opn-var x₁) exts
  with ext ← ⊆⊆-⊆-l exts
  with refl ← ⊆⊆-one-input exts = s-svar-tapp (⊆-∋:= x ext) (s-⊆-prv-gen s (⊢r-⊢ok (∋:=-⊢r (s-env-in s) x)) exts)
s-⊆-prv-gen (s-evar-infers infs inst) (opn-var x) exts
  with ext ← ⊆⊆-⊆-l exts = s-evar-infers (infs-irrev-⊆ infs ext) (⊆⊆-inst inst exts (⊢oˣ-∋^-#< x (inst-∋^ inst)))
s-⊆-prv-gen (s-term-c-n s ap ⊢e) opn exts = {!!}
s-⊆-prv-gen (s-term-o-n s ⊢e ss) opn exts = {!!}

s-irrev-⊆ : Γ ⊢ A ≤⁺ Σ ⊣ Γ ↪ B
          → Γ ⊆ Δ
          → Δ ⊢ A ≤⁺ Σ ⊣ Δ ↪ B
s-irrev-⊆ s ext = s-⊆-prv-gen s (⊢c-⊢ok (s-⊢c s)) (⊆⊆-Z ext)
