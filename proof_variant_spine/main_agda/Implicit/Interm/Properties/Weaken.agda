module Implicit.Interm.Properties.Weaken where

open import Implicit.Language.All
open import Implicit.Interm.Base
open import Implicit.Interm.Properties.Regularity
open import Implicit.Interm.Properties.Polarity


s-weaken^ : Γ ⊢ j # A ⌞ ≤ ⌝ B
              → Γ ▶ k ,^⇘ Γ'
              → A ↑ty k ⇘ A'
              → B ↑ty k ⇘ B'
              → j ↑tyʲ k ⇘ j'
              → Γ' ⊢ j' # A' ⌞ ≤ ⌝ B'
s-weaken^ (s-refl regΔ cloA grd) newΓ upA upB ↑tyʲ-Z = s-refl (sregular-weaken^ regΔ newΓ) (⊢c-weaken^ cloA newΓ upA) (≫-weaken^ grd newΓ upA upB)
s-weaken^ (s-int regΔ) newΓ ↑ty-int ↑ty-int ↑tyʲ-∞ = s-int (sregular-weaken^ regΔ newΓ)
s-weaken^ (s-var-∙ regΔ inΔ) newΓ ↑ty-var ↑ty-var ↑tyʲ-∞ = s-var-∙ (sregular-weaken^ regΔ newΓ) (∋∙-weaken^ inΔ newΓ)
s-weaken^ (s-arr₁ s s₁) newΓ (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) ↑tyʲ-∞ = s-arr₁ (s-weaken^ s newΓ upB upA ↑tyʲ-∞) (s-weaken^ s₁ newΓ upA₁ upB₁ ↑tyʲ-∞)
s-weaken^ (s-arr₂ s s₁) newΓ (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) (↑tyʲ-𝕚 upj) = s-arr₂ (s-weaken^ s newΓ upB upA ↑tyʲ-∞) (s-weaken^ s₁ newΓ upA₁ upB₁ upj)
s-weaken^ (s-arr₃ cloA grd s) newΓ (↑ty-arr upA upA₁) (↑ty-arr upB upB₁) (↑tyʲ-𝕔 upj) = s-arr₃ (⊢c-weaken^ cloA newΓ upA) (≫-weaken^ grd newΓ upA upB) (s-weaken^ s newΓ upA₁ upB₁ upj)
s-weaken^ (s-∀ s) newΓ (↑ty-∀ upA) (↑ty-∀ upB) ↑tyʲ-∞ = s-∀ (s-weaken^ s (▶S∙ newΓ) upA upB ↑tyʲ-∞)
s-weaken^ {k = k} {j' = j₁} (s-∀l-new {B = B} s ic fd upC upD upj₁) newΓ (↑ty-∀ upA) (↑ty-arr {A' = A₁} {B' = B₁} upB upB₁) upj
  with ⟨ A₁' , upA₂ ⟩ ← ↑ty0-total A₁
  with ⟨ B₁' , upB₂ ⟩ ← ↑ty0-total B₁
  with ⟨ j₁' , upj₂ ⟩ ← ↑tyʲ0-total j₁
  with ⟨ B' , upB₃ ⟩ ← ↑ty-total B k
  = s-∀l-new (s-weaken^ s (▶S= newΓ upB₃) upA
         (↑ty-arr (↑ty-comm0' upB upA₂ upC) (↑ty-comm0' upB₁ upB₂ upD)) (↑tyʲ-comm0' upj upj₂ upj₁)) (𝕚𝕔-↑tyʲ ic upj)
                              (↑ty-find0 fd upA (↑tyʲ-comm0' upj upj₂ upj₁)) upA₂ upB₂ upj₂
s-weaken^ {k = k} {j' = j₁} (s-∀l-peek {B = B} s ic pk upC upD upj₁) newΓ (↑ty-∀ upA) (↑ty-arr {A' = A₁} {B' = B₁} upB upB₁) upj
  with ⟨ A₁' , upA₂ ⟩ ← ↑ty0-total A₁
  with ⟨ B₁' , upB₂ ⟩ ← ↑ty0-total B₁
  with ⟨ j₁' , upj₂ ⟩ ← ↑tyʲ0-total j₁
  with ⟨ B' , upB₃ ⟩ ← ↑ty-total B k
  = s-∀l-peek (s-weaken^ s (▶S= newΓ upB₃) upA (↑ty-arr (↑ty-comm0' upB upA₂ upC) (↑ty-comm0' upB₁ upB₂ upD)) (↑tyʲ-comm0' upj upj₂ upj₁))
              (𝕚𝕔-↑tyʲ ic upj) (↑ty-peek0 pk upA (↑tyʲ-comm0' upj upj₂ upj₁)) upA₂ upB₂ upj₂
s-weaken^ {k = k} {j' = j₁} (s-∀l-no-appear s ic fd upC upD upj₁) newΓ (↑ty-∀ upA) (↑ty-arr {A' = A₁} {B' = B₁} upB upB₁) upj
  with ⟨ A₁' , upA₂ ⟩ ← ↑ty0-total A₁
  with ⟨ B₁' , upB₂ ⟩ ← ↑ty0-total B₁
  with ⟨ j₁' , upj₂ ⟩ ← ↑tyʲ0-total j₁
  = s-∀l-no-appear (s-weaken^ s (▶S^ newΓ) upA (↑ty-arr (↑ty-comm0' upB upA₂ upC) (↑ty-comm0' upB₁ upB₂ upD))
                              (↑tyʲ-comm0' upj upj₂ upj₁)) (𝕚𝕔-↑tyʲ ic upj) (¬ε-↑ty0' fd upA) upA₂ upB₂ upj₂
s-weaken^ (s-tapp s upj₁) newΓ (↑ty-∀ upA) (↑ty-∀ upB) (↑tyʲ-𝕥 {j' = j₁} upj upA₁)
  with ⟨ j₁' , upj₂ ⟩ ← ↑tyʲ0-total j₁
  = s-tapp (s-weaken^ s (▶S= newΓ upA₁) upA upB (↑tyʲ-comm0' upj upj₂ upj₁)) upj₂
s-weaken^ (s-svar-l x inΔ) newΓ ↑ty-var upB ↑tyʲ-∞ = s-svar-l (sregular-weaken^ x newΓ) (∋:=-weaken^ inΔ upB newΓ)
s-weaken^ (s-svar-r x inΔ) newΓ upA ↑ty-var ↑tyʲ-∞ = s-svar-r (sregular-weaken^ x newΓ) (∋:=-weaken^ inΔ upA newΓ)
s-weaken^ {k = k} (s-svar-𝕚 {C = C} x s) newΓ ↑ty-var (↑ty-arr upB upB₁) (↑tyʲ-𝕚 upj)
  with ⟨ C' , upC ⟩ ← ↑ty-total C k
  = s-svar-𝕚 (∋:=-weaken^ x upC newΓ) (s-weaken^ s newΓ upC (↑ty-arr upB upB₁) (↑tyʲ-𝕚 upj))
s-weaken^ {k = k} (s-svar-𝕔 {C = C} x s) newΓ ↑ty-var (↑ty-arr upB upB₁) (↑tyʲ-𝕔 upj)
  with ⟨ C' , upC ⟩ ← ↑ty-total C k
  = s-svar-𝕔 (∋:=-weaken^ x upC newΓ) (s-weaken^ s newΓ upC (↑ty-arr upB upB₁) (↑tyʲ-𝕔 upj))
s-weaken^ {k = k} (s-svar-𝕥 {B = B} x s) newΓ ↑ty-var (↑ty-∀ upB) (↑tyʲ-𝕥 upj upA₁)
  with ⟨ B' , upB₁ ⟩ ← ↑ty-total B k
  = s-svar-𝕥 (∋:=-weaken^ x upB₁ newΓ) (s-weaken^ s newΓ upB₁ (↑ty-∀ upB) (↑tyʲ-𝕥 upj upA₁))

t-weaken^ : Γ ⊢ j # e ⦂ A
            → Γ ▶ k ,^⇘ Γ'
              → e ↑tyᵉ k ⇘ e'
              → A ↑ty k ⇘ A'
              → j ↑tyʲ k ⇘ j'
                → Γ' ⊢ j' # e' ⦂ A'
t-weaken^ (⊢lit regΓ) new ↑tyᵉ-lit ↑ty-int ↑tyʲ-Z = ⊢lit (tregular-weaken^ regΓ new)
t-weaken^ (⊢var regΓ x∈Γ) new ↑tyᵉ-var upA ↑tyʲ-Z = ⊢var (tregular-weaken^ regΓ new) (∋⦂-weaken^ x∈Γ new upA)
t-weaken^ (⊢ann ⊢e) new (↑tyᵉ-⦂ upe up) upA ↑tyʲ-Z
  with refl ← ↑ty-unique up upA
  = ⊢ann (t-weaken^ ⊢e new upe up ↑tyʲ-∞)
t-weaken^ (⊢lam₁ ⊢e) new (↑tyᵉ-ƛ upe) (↑ty-arr upA upA₁) ↑tyʲ-∞ = ⊢lam₁ (t-weaken^ ⊢e (▶S, new upA) upe upA₁ ↑tyʲ-∞)
t-weaken^ (⊢lam₂ ⊢e) new (↑tyᵉ-ƛ upe) (↑ty-arr upA upA₁) (↑tyʲ-𝕚 upj) = ⊢lam₂ (t-weaken^ ⊢e (▶S, new upA) upe upA₁ upj)
t-weaken^ {k = k} (⊢app₁ {A = A} ⊢e ⊢e₁) new (↑tyᵉ-app upe upe₁) upA upj
  with ⟨ A' , upA₁ ⟩ ← ↑ty-total A k
  = ⊢app₁ (t-weaken^ ⊢e new upe (↑ty-arr upA₁ upA) (↑tyʲ-𝕔 upj)) (t-weaken^ ⊢e₁ new upe₁ upA₁ ↑tyʲ-∞)
t-weaken^ {k = k} (⊢app₂ {A = A} ⊢e ⊢e₁) new (↑tyᵉ-app upe upe₁) upA upj
  with ⟨ A' , upA₁ ⟩ ← ↑ty-total A k
  = ⊢app₂ (t-weaken^ ⊢e new upe (↑ty-arr upA₁ upA) (↑tyʲ-𝕚 upj)) (t-weaken^ ⊢e₁ new upe₁ upA₁ ↑tyʲ-Z)
t-weaken^ {k = k} (⊢sub {A = A} ⊢e B≤A gc j≢Z) new upe upA upj
  with ⟨ A' , upA₁ ⟩ ← ↑ty-total A k
  = ⊢sub (t-weaken^ ⊢e new upe upA₁ ↑tyʲ-Z) (s-weaken^ B≤A (▶S⋈ new) upA₁ upA upj) (gc-↑tyᵉ gc upe) (nonz-↑tyʲ j≢Z upj)
t-weaken^ (⊢tabs ⊢e) new (↑tyᵉ-Λ upe) (↑ty-∀ upA) ↑tyʲ-Z = ⊢tabs (t-weaken^ ⊢e (▶S∙ new) upe upA ↑tyʲ-Z)
t-weaken^ (⊢tabs-∞ ⊢e) new (↑tyᵉ-Λ upe) (↑ty-∀ upA) ↑tyʲ-∞ = ⊢tabs-∞ (t-weaken^ ⊢e (▶S∙ new) upe upA ↑tyʲ-∞)
t-weaken^ {A' = A₁} (⊢tapp ⊢e upB) new (↑tyᵉ-⓪ upe upA₁) upA upj
  with ⟨ A₁' , upA₂ ⟩ ← ↑ty0-total A₁
  = ⊢tapp (t-weaken^ ⊢e new upe (↑ty-∀ (↑ty-comm0' upA upA₂ upB)) (↑tyʲ-𝕥 upj upA₁)) upA₂
