module Implicit.Language.EnvOps.InsertTVar where

open import Implicit.Language.Base
open import Implicit.Language.Shift.All
open import Implicit.Language.Lookup.All
open import Implicit.Language.Regular.All
open import Implicit.Language.OpenClose.Base
open import Implicit.Language.Ground.Base
open import Implicit.Language.EnvOps.Base
open import Implicit.Language.EnvOps.Inst

-- insert into typing env
infix 3 _▶_,_⇘_
data _▶_,_⇘_ : Env n m → Fin (1 + n) → Type m → Env (1 + n) m → Set where
  ▶Z  : (regA : Γ ⊢r A)
      → Γ ▶ #0 , A ⇘ Γ , A
  ▶S, : Γ ▶ k , A ⇘ Γ'
      → (Γ , B) ▶ #S k , A ⇘ Γ' , B
  ▶S^ : Γ ▶ k , A ⇘ Γ'
      → ↑ty0 A ⇘ A'
      → (Γ ,^) ▶ k , A' ⇘ Γ' ,^
  ▶S∙ : Γ ▶ k , A ⇘ Γ'
      → ↑ty0 A ⇘ A'
      → (Γ ,∙) ▶ k , A' ⇘ Γ' ,∙
  ▶S= : Γ ▶ k , A  ⇘ Γ'
      → ↑ty0 A ⇘ A'
      → (Γ ,= B) ▶ k , A' ⇘ Γ' ,= B

-- insert into subtyping env
infix 3 _▶s_,_⇘_
data _▶s_,_⇘_ : Env n m → Fin (1 + n) → Type m → Env (1 + n) m → Set where
  ▶sS⋈ : Γ ▶ k , A ⇘ Γ'
      → Γ ⋈ ▶s k , A ⇘ Γ' ⋈
  ▶sS, : Γ ▶s k , A ⇘ Γ'
      → (Γ , B) ▶s #S k , A ⇘ Γ' , B
  ▶sS^ : Γ ▶s k , A ⇘ Γ'
      → ↑ty0 A ⇘ A'
      → (Γ ,^) ▶s k , A' ⇘ Γ' ,^
  ▶sS∙ : Γ ▶s k , A ⇘ Γ'
      → ↑ty0 A ⇘ A'
      → (Γ ,∙) ▶s k , A' ⇘ Γ' ,∙
  ▶sS= : Γ ▶s k , A  ⇘ Γ'
      → ↑ty0 A ⇘ A'
      → (Γ ,= B) ▶s k , A' ⇘ Γ' ,= B

infix 3 _⨟_▶_,_⇘_⨟_
data _⨟_▶_,_⇘_⨟_ : Env n m → Env n m → Fin (1 + n) → Type m → Env (1 + n) m → Env (1 + n) m → Set where
  ▶Z  : (regA : Γ ⊢r T)
      → Γ ⨟ Δ ▶ #0 , T ⇘ Γ , T ⨟ Δ , T
  ▶S, : Γ ⨟ Δ ▶ k , T ⇘ Γ' ⨟ Δ'
      → Γ , A ⨟ Δ , A ▶ #S k , T ⇘ Γ' , A ⨟ Δ' , A
  ▶S^ : Γ ⨟ Δ ▶ k , T ⇘ Γ' ⨟ Δ'
      → ↑ty0 T ⇘ T'
      → Γ ,^ ⨟ Δ ,^ ▶ k , T' ⇘ Γ' ,^ ⨟ Δ' ,^
  ▶S∙ : Γ ⨟ Δ ▶ k , T ⇘ Γ' ⨟ Δ'
      → ↑ty0 T ⇘ T'
      → Γ ,∙ ⨟ Δ ,∙ ▶ k , T' ⇘ Γ' ,∙ ⨟ Δ' ,∙
  ▶S= : Γ ⨟ Δ ▶ k , T  ⇘ Γ' ⨟ Δ'
      → ↑ty0 T ⇘ T'
      → Γ ,= A ⨟ Δ ,= A ▶ k , T' ⇘ Γ' ,= A ⨟ Δ' ,= A
  ▶S^= : Γ ⨟ Δ ▶ k , T  ⇘ Γ' ⨟ Δ'
      → ↑ty0 T ⇘ T'
      → Γ ,^ ⨟ Δ ,= A ▶ k , T' ⇘ Γ' ,^ ⨟ Δ' ,= A

infix 3 _⨟_▶s_,_⇘_⨟_
data _⨟_▶s_,_⇘_⨟_ : Env n m → Env n m → Fin (1 + n) → Type m → Env (1 + n) m → Env (1 + n) m → Set where
  ▶sS⋈  : Γ ⨟ Δ ▶ k , T  ⇘ Γ' ⨟ Δ'
      → Γ ⋈ ⨟ Δ ⋈ ▶s k , T ⇘ Γ' ⋈ ⨟ Δ' ⋈
  ▶sS, : Γ ⨟ Δ ▶s k , T ⇘ Γ' ⨟ Δ'
      → Γ , A ⨟ Δ , A ▶s #S k , T ⇘ Γ' , A ⨟ Δ' , A
  ▶sS^ : Γ ⨟ Δ ▶s k , T ⇘ Γ' ⨟ Δ'
      → ↑ty0 T ⇘ T'
      → Γ ,^ ⨟ Δ ,^ ▶s k , T' ⇘ Γ' ,^ ⨟ Δ' ,^
  ▶sS∙ : Γ ⨟ Δ ▶s k , T ⇘ Γ' ⨟ Δ'
      → ↑ty0 T ⇘ T'
      → Γ ,∙ ⨟ Δ ,∙ ▶s k , T' ⇘ Γ' ,∙ ⨟ Δ' ,∙
  ▶sS= : Γ ⨟ Δ ▶s k , T  ⇘ Γ' ⨟ Δ'
      → ↑ty0 T ⇘ T'
      → Γ ,= A ⨟ Δ ,= A ▶s k , T' ⇘ Γ' ,= A ⨟ Δ' ,= A
  ▶sS^= : Γ ⨟ Δ ▶s k , T  ⇘ Γ' ⨟ Δ'
      → ↑ty0 T ⇘ T'
      → Γ ,^ ⨟ Δ ,= A ▶s k , T' ⇘ Γ' ,^ ⨟ Δ' ,= A

▶⨟,-unique : Γ ⨟ Γ ▶ k , T ⇘ Γ' ⨟ Δ'
           → Γ' ≡ Δ'
▶⨟,-unique (▶Z regA) = refl
▶⨟,-unique (▶S, new) rewrite ▶⨟,-unique new = refl
▶⨟,-unique (▶S^ new x) rewrite ▶⨟,-unique new = refl
▶⨟,-unique (▶S∙ new x) rewrite ▶⨟,-unique new = refl
▶⨟,-unique (▶S= new x) rewrite ▶⨟,-unique new = refl


▶s⨟,-unique : Γ ⨟ Γ ▶s k , T ⇘ Γ' ⨟ Δ'
           → Γ' ≡ Δ'
▶s⨟,-unique (▶sS⋈ new) rewrite ▶⨟,-unique new = refl
▶s⨟,-unique (▶sS, new) rewrite ▶s⨟,-unique new = refl
▶s⨟,-unique (▶sS^ new x) rewrite ▶s⨟,-unique new = refl
▶s⨟,-unique (▶sS∙ new x) rewrite ▶s⨟,-unique new = refl
▶s⨟,-unique (▶sS= new x) rewrite ▶s⨟,-unique new = refl


▶⨟,-▶,-l : Γ ⨟ Δ ▶ k , T ⇘ Γ' ⨟ Δ'
         → Γ ▶ k , T ⇘ Γ'
▶⨟,-▶,-l (▶Z regA) = ▶Z regA
▶⨟,-▶,-l (▶S, new) = ▶S, (▶⨟,-▶,-l new)
▶⨟,-▶,-l (▶S^ new x) = ▶S^ (▶⨟,-▶,-l new) x
▶⨟,-▶,-l (▶S∙ new x) = ▶S∙ (▶⨟,-▶,-l new) x
▶⨟,-▶,-l (▶S= new x) = ▶S= (▶⨟,-▶,-l new) x
▶⨟,-▶,-l (▶S^= new x) = ▶S^ (▶⨟,-▶,-l new) x

▶s⨟,-▶s,-l : Γ ⨟ Δ ▶s k , T ⇘ Γ' ⨟ Δ'
           → Γ ▶s k , T ⇘ Γ'
▶s⨟,-▶s,-l (▶sS⋈ x) = ▶sS⋈ (▶⨟,-▶,-l x)
▶s⨟,-▶s,-l (▶sS, new) = ▶sS, (▶s⨟,-▶s,-l new)
▶s⨟,-▶s,-l (▶sS^ new x) = ▶sS^ (▶s⨟,-▶s,-l new) x
▶s⨟,-▶s,-l (▶sS∙ new x) = ▶sS∙ (▶s⨟,-▶s,-l new) x
▶s⨟,-▶s,-l (▶sS= new x) = ▶sS= (▶s⨟,-▶s,-l new) x
▶s⨟,-▶s,-l (▶sS^= new x) = ▶sS^ (▶s⨟,-▶s,-l new) x

▶,-▶⨟, : Γ ▶ k , T ⇘ Γ'
       → Γ ⨟ Γ ▶ k , T ⇘ Γ' ⨟ Γ'
▶,-▶⨟, (▶Z regA) = ▶Z regA
▶,-▶⨟, (▶S, new) = ▶S, (▶,-▶⨟, new)
▶,-▶⨟, (▶S^ new x) = ▶S^ (▶,-▶⨟, new) x
▶,-▶⨟, (▶S∙ new x) = ▶S∙ (▶,-▶⨟, new) x
▶,-▶⨟, (▶S= new x) = ▶S= (▶,-▶⨟, new) x

▶,-𝕣 : Γ ▶ k , T ⇘ Γ'
     → 𝕣 Γ ▶ k , T ⇘ 𝕣 Γ'
▶,-𝕣 (▶Z regA) = ▶Z (⊢r-𝕣' regA)
▶,-𝕣 (▶S, new) = ▶S, (▶,-𝕣 new)
▶,-𝕣 (▶S^ new x) = ▶S^ (▶,-𝕣 new) x
▶,-𝕣 (▶S∙ new x) = ▶S∙ (▶,-𝕣 new) x
▶,-𝕣 (▶S= new x) = ▶S= (▶,-𝕣 new) x

▶,-▶s,-𝕣 : Γ ▶s k , T ⇘ Γ'
         → 𝕣 Γ ▶ k , T ⇘ 𝕣 Γ'
▶,-▶s,-𝕣 (▶sS⋈ x) = x
▶,-▶s,-𝕣 (▶sS, new) = ▶S, (▶,-▶s,-𝕣 new)
▶,-▶s,-𝕣 (▶sS^ new x) = ▶S^ (▶,-▶s,-𝕣 new) x
▶,-▶s,-𝕣 (▶sS∙ new x) = ▶S∙ (▶,-▶s,-𝕣 new) x
▶,-▶s,-𝕣 (▶sS= new x) = ▶S= (▶,-▶s,-𝕣 new) x


∋∙-weaken, : Γ ∋∙ X
           → Γ ▶ k , T ⇘ Γ'
           → Γ' ∋∙ X
∋∙-weaken, Z (▶Z regA) = S, Z
∋∙-weaken, Z (▶S∙ new x) = Z
∋∙-weaken, (S, inΓ) (▶Z regA) = S, (S, inΓ)
∋∙-weaken, (S, inΓ) (▶S, new) = S, (∋∙-weaken, inΓ new)
∋∙-weaken, (S∙ inΓ) (▶Z regA) = S, (S∙ inΓ)
∋∙-weaken, (S∙ inΓ) (▶S∙ new x) = S∙ (∋∙-weaken, inΓ new)
∋∙-weaken, (S= inΓ) (▶Z regA) = S, (S= inΓ)
∋∙-weaken, (S= inΓ) (▶S= new x) = S= (∋∙-weaken, inΓ new)
∋∙-weaken, (S^ inΓ) (▶Z regA) = S, (S^ inΓ)
∋∙-weaken, (S^ inΓ) (▶S^ new x) = S^ (∋∙-weaken, inΓ new)
∋∙-weaken, (S⋈ inΓ) (▶Z regA) = S, (S⋈ inΓ)

∋∙-weaken,s : Γ ∋∙ X
           → Γ ▶s k , T ⇘ Γ'
           → Γ' ∋∙ X
∋∙-weaken,s Z (▶sS∙ new x) = Z
∋∙-weaken,s (S, inΓ) (▶sS, new) = S, (∋∙-weaken,s inΓ new)
∋∙-weaken,s (S∙ inΓ) (▶sS∙ new x) = S∙ (∋∙-weaken,s inΓ new)
∋∙-weaken,s (S= inΓ) (▶sS= new x) = S= (∋∙-weaken,s inΓ new)
∋∙-weaken,s (S^ inΓ) (▶sS^ new x) = S^ (∋∙-weaken,s inΓ new)
∋∙-weaken,s (S⋈ inΓ) (▶sS⋈ x) = S⋈ (∋∙-weaken, inΓ x)


∋=-weaken, : Γ ∋= X
           → Γ ▶ k , T ⇘ Γ'
           → Γ' ∋= X
∋=-weaken, Z (▶Z regA) = S, Z
∋=-weaken, Z (▶S= new x) = Z
∋=-weaken, (S∙ inΓ) (▶Z regA) = S, (S∙ inΓ)
∋=-weaken, (S∙ inΓ) (▶S∙ new x) = S∙ (∋=-weaken, inΓ new)
∋=-weaken, (S^ inΓ) (▶Z regA) = S, (S^ inΓ)
∋=-weaken, (S^ inΓ) (▶S^ new x) = S^ (∋=-weaken, inΓ new)
∋=-weaken, (S= inΓ) (▶Z regA) = S, (S= inΓ)
∋=-weaken, (S= inΓ) (▶S= new x) = S= (∋=-weaken, inΓ new)
∋=-weaken, (S, inΓ) (▶Z regA) = S, (S, inΓ)
∋=-weaken, (S, inΓ) (▶S, new) = S, (∋=-weaken, inΓ new)

∋=-weaken,s : Γ ∋= X
           → Γ ▶s k , T ⇘ Γ'
           → Γ' ∋= X
∋=-weaken,s Z (▶sS= new x) = Z
∋=-weaken,s (S∙ inΓ) (▶sS∙ new x) = S∙ (∋=-weaken,s inΓ new)
∋=-weaken,s (S^ inΓ) (▶sS^ new x) = S^ (∋=-weaken,s inΓ new)
∋=-weaken,s (S= inΓ) (▶sS= new x) = S= (∋=-weaken,s inΓ new)
∋=-weaken,s (S, inΓ) (▶sS, new) = S, (∋=-weaken,s inΓ new)


∋:=-weaken, : Γ ∋ X := A
            → Γ ▶ k , T ⇘ Γ'
            → Γ' ∋ X := A
∋:=-weaken, (Z up) (▶Z regA) = S, (Z up)
∋:=-weaken, (Z up) (▶S= new x) = Z up
∋:=-weaken, (S∙ inΓ up) (▶Z regA) = S, (S∙ inΓ up)
∋:=-weaken, (S∙ inΓ up) (▶S∙ new x) = S∙ (∋:=-weaken, inΓ new) up
∋:=-weaken, (S^ inΓ up) (▶Z regA) = S, (S^ inΓ up)
∋:=-weaken, (S^ inΓ up) (▶S^ new x) = S^ (∋:=-weaken, inΓ new) up
∋:=-weaken, (S= inΓ up) (▶Z regA) = S, (S= inΓ up)
∋:=-weaken, (S= inΓ up) (▶S= new x) = S= (∋:=-weaken, inΓ new) up
∋:=-weaken, (S, inΓ) (▶Z regA) = S, (S, inΓ)
∋:=-weaken, (S, inΓ) (▶S, new) = S, (∋:=-weaken, inΓ new)


∋:=-weaken,s : Γ ∋ X := A
            → Γ ▶s k , T ⇘ Γ'
            → Γ' ∋ X := A
∋:=-weaken,s (Z up) (▶sS= new x) = Z up
∋:=-weaken,s (S∙ inΓ up) (▶sS∙ new x) = S∙ (∋:=-weaken,s inΓ new) up
∋:=-weaken,s (S^ inΓ up) (▶sS^ new x) = S^ (∋:=-weaken,s inΓ new) up
∋:=-weaken,s (S= inΓ up) (▶sS= new x) = S= (∋:=-weaken,s inΓ new) up
∋:=-weaken,s (S, inΓ) (▶sS, new) = S, (∋:=-weaken,s inΓ new)



∋⦂-weaken, : Γ ∋ x ⦂ A
           → Γ ▶ k , T ⇘ Γ'
           → Γ' ∋ punchIn k x ⦂ A
∋⦂-weaken, Z (▶Z regA) = S, Z
∋⦂-weaken, Z (▶S, new) = Z
∋⦂-weaken, (S, inΓ) (▶Z regA) = S, (S, inΓ)
∋⦂-weaken, (S, inΓ) (▶S, new) = S, (∋⦂-weaken, inΓ new)
∋⦂-weaken, (S∙ inΓ up) (▶Z regA) = S, (S∙ inΓ up)
∋⦂-weaken, (S∙ inΓ up) (▶S∙ new x) = S∙ (∋⦂-weaken, inΓ new) up
∋⦂-weaken, (S^ inΓ up) (▶Z regA) = S, (S^ inΓ up)
∋⦂-weaken, (S^ inΓ up) (▶S^ new x) = S^ (∋⦂-weaken, inΓ new) up
∋⦂-weaken, (S= inΓ up) (▶Z regA) = S, (S= inΓ up)
∋⦂-weaken, (S= inΓ up) (▶S= new x) = S= (∋⦂-weaken, inΓ new) up


∋^-weaken, : Γ ∋^ X
           → Γ ▶ k , T ⇘ Γ'
           → Γ' ∋^ X
∋^-weaken, Z (▶Z regA) = S, Z
∋^-weaken, Z (▶S^ new x) = Z
∋^-weaken, (S∙ inΓ) (▶Z regA) = S, (S∙ inΓ)
∋^-weaken, (S∙ inΓ) (▶S∙ new x) = S∙ (∋^-weaken, inΓ new)
∋^-weaken, (S= inΓ) (▶Z regA) = S, (S= inΓ)
∋^-weaken, (S= inΓ) (▶S= new x) = S= (∋^-weaken, inΓ new)
∋^-weaken, (S^ inΓ) (▶Z regA) = S, (S^ inΓ)
∋^-weaken, (S^ inΓ) (▶S^ new x) = S^ (∋^-weaken, inΓ new)
∋^-weaken, (S, inΓ) (▶Z regA) = S, (S, inΓ)
∋^-weaken, (S, inΓ) (▶S, new) = S, (∋^-weaken, inΓ new)

∋^-weaken,s : Γ ∋^ X
           → Γ ▶s k , T ⇘ Γ'
           → Γ' ∋^ X
∋^-weaken,s Z (▶sS^ new x) = Z
∋^-weaken,s (S∙ inΓ) (▶sS∙ new x) = S∙ (∋^-weaken,s inΓ new)
∋^-weaken,s (S= inΓ) (▶sS= new x) = S= (∋^-weaken,s inΓ new)
∋^-weaken,s (S^ inΓ) (▶sS^ new x) = S^ (∋^-weaken,s inΓ new)
∋^-weaken,s (S, inΓ) (▶sS, new) = S, (∋^-weaken,s inΓ new)

⊢r-weaken, : Γ ⊢r A
           → Γ ▶ k , T ⇘ Γ'
           → Γ' ⊢r A
⊢r-weaken, ⊢r-int new = ⊢r-int
⊢r-weaken, (⊢r-var-∙ inΓ) new = ⊢r-var-∙ (∋∙-weaken, inΓ new)
⊢r-weaken, (⊢r-arr regA regA₁) new = ⊢r-arr (⊢r-weaken, regA new) (⊢r-weaken, regA₁ new)
⊢r-weaken, {T = T} (⊢r-∀ regA) new
  with ⟨ T' , upT ⟩ ← ↑ty0-total T = ⊢r-∀ (⊢r-weaken, regA (▶S∙ new upT))


⊢r-weaken,s : Γ ⊢r A
            → Γ ▶s k , T ⇘ Γ'
            → Γ' ⊢r A
⊢r-weaken,s ⊢r-int new = ⊢r-int
⊢r-weaken,s (⊢r-var-∙ inΓ) new = ⊢r-var-∙ (∋∙-weaken,s inΓ new)
⊢r-weaken,s (⊢r-arr regA regA₁) new = ⊢r-arr (⊢r-weaken,s regA new) (⊢r-weaken,s regA₁ new)
⊢r-weaken,s {T = T} (⊢r-∀ regA) new
  with ⟨ T' , upT ⟩ ← ↑ty0-total T = ⊢r-∀ (⊢r-weaken,s regA (▶sS∙ new upT))

⊢c-weaken, : Γ ⊢c A
           → Γ ▶ k , T ⇘ Γ'
           → Γ' ⊢c A
⊢c-weaken, ⊢c-int new = ⊢c-int
⊢c-weaken, (⊢c-var-∙ inΔ) new = ⊢c-var-∙ (∋∙-weaken, inΔ new)
⊢c-weaken, (⊢c-var-= inΔ) new = ⊢c-var-= (∋=-weaken, inΔ new)
⊢c-weaken, (⊢c-arr cloA cloA₁) new = ⊢c-arr (⊢c-weaken, cloA new) (⊢c-weaken, cloA₁ new)
⊢c-weaken, {T = T} (⊢c-∀ cloA) new
  with ⟨ T' , upT ⟩ ← ↑ty0-total T = ⊢c-∀ (⊢c-weaken, cloA (▶S∙ new upT))

⊢o-weaken, : Γ ⊢o A
           → Γ ▶ k , T ⇘ Γ'
           → Γ' ⊢o A
⊢o-weaken, (⊢o-var-^ x) new = ⊢o-var-^ (∋^-weaken, x new)
⊢o-weaken, (⊢o-arr-l opnA) new = ⊢o-arr-l (⊢o-weaken, opnA new)
⊢o-weaken, (⊢o-arr-r opnA) new = ⊢o-arr-r (⊢o-weaken, opnA new)
⊢o-weaken, {T = T} (⊢o-∀ opnA) new
  with ⟨ T' , upT ⟩ ← ↑ty0-total T = ⊢o-∀ (⊢o-weaken, opnA (▶S∙ new upT))


⊢c-weaken,s : Γ ⊢c A
           → Γ ▶s k , T ⇘ Γ'
           → Γ' ⊢c A
⊢c-weaken,s ⊢c-int new = ⊢c-int
⊢c-weaken,s (⊢c-var-∙ inΔ) new = ⊢c-var-∙ (∋∙-weaken,s inΔ new)
⊢c-weaken,s (⊢c-var-= inΔ) new = ⊢c-var-= (∋=-weaken,s inΔ new)
⊢c-weaken,s (⊢c-arr cloA cloA₁) new = ⊢c-arr (⊢c-weaken,s cloA new) (⊢c-weaken,s cloA₁ new)
⊢c-weaken,s {T = T} (⊢c-∀ cloA) new
  with ⟨ T' , upT ⟩ ← ↑ty0-total T = ⊢c-∀ (⊢c-weaken,s cloA (▶sS∙ new upT))


⊢o-weaken,s : Γ ⊢o A
           → Γ ▶s k , T ⇘ Γ'
           → Γ' ⊢o A
⊢o-weaken,s (⊢o-var-^ x) new = ⊢o-var-^ (∋^-weaken,s x new)
⊢o-weaken,s (⊢o-arr-l opnA) new = ⊢o-arr-l (⊢o-weaken,s opnA new)
⊢o-weaken,s (⊢o-arr-r opnA) new = ⊢o-arr-r (⊢o-weaken,s opnA new)
⊢o-weaken,s {T = T} (⊢o-∀ opnA) new
  with ⟨ T' , upT ⟩ ← ↑ty0-total T = ⊢o-∀ (⊢o-weaken,s opnA (▶sS∙ new upT))


tregular-weaken, : TRegular Γ
                 → Γ ▶ k , T ⇘ Γ'
                 → TRegular Γ'
tregular-weaken, reg-Z (▶Z regA) = reg-S, reg-Z regA
tregular-weaken, (reg-S, regΓ regA) (▶Z regA₁) = reg-S, (reg-S, regΓ regA) regA₁
tregular-weaken, (reg-S, regΓ regA) (▶S, new) = reg-S, (tregular-weaken, regΓ new) (⊢r-weaken, regA new)
tregular-weaken, (reg-S∙ regΓ) (▶Z regA) = reg-S, (reg-S∙ regΓ) regA
tregular-weaken, (reg-S∙ regΓ) (▶S∙ new x) = reg-S∙ (tregular-weaken, regΓ new)
tregular-weaken, (reg-S^ regΓ) (▶Z regA) = reg-S, (reg-S^ regΓ) regA
tregular-weaken, (reg-S^ regΓ) (▶S^ new x) = reg-S^ (tregular-weaken, regΓ new)
tregular-weaken, (reg-S= regΓ regA) (▶Z regA₁) = reg-S, (reg-S= regΓ regA) regA₁
tregular-weaken, (reg-S= regΓ regA) (▶S= new x) = reg-S= (tregular-weaken, regΓ new) (⊢r-weaken, regA new)

sregular-weaken,s : SRegular Γ
                 → Γ ▶s k , T ⇘ Γ'
                 → SRegular Γ'
sregular-weaken,s (reg-Z regΓ) (▶sS⋈ x) = reg-Z (tregular-weaken, regΓ x)
sregular-weaken,s (reg-S∙ regΓ) (▶sS∙ new x) = reg-S∙ (sregular-weaken,s regΓ new)
sregular-weaken,s (reg-S^ regΓ) (▶sS^ new x) = reg-S^ (sregular-weaken,s regΓ new)
sregular-weaken,s (reg-S= regΓ regA) (▶sS= new x) = reg-S= (sregular-weaken,s regΓ new) (⊢r-weaken,s regA new)



≫-weaken,s : Γ ≫ A ⇘ B
          → Γ ▶s k , T ⇘ Γ'
          → Γ' ≫ A ⇘ B
≫-weaken,s grd-int new = grd-int
≫-weaken,s (grd-var= x) new = grd-var= (∋:=-weaken,s x new)
≫-weaken,s (grd-var∙ x) new = grd-var∙ (∋∙-weaken,s x new)
≫-weaken,s (grd-arr grd grd₁) new = grd-arr (≫-weaken,s grd new) (≫-weaken,s grd₁ new)
≫-weaken,s {T = T} (grd-∀ grd) new
  with ⟨ T' , upT ⟩ ← ↑ty0-total T = grd-∀ (≫-weaken,s grd (▶sS∙ new upT))

inst-weaken,s : [ A / X ] Γ ⟹ Δ
             → Γ ⨟ Δ ▶s k , T ⇘ Γ' ⨟ Δ'
             → [ A / X ] Γ' ⟹ Δ'
inst-weaken,s (⟹^0 up regA env) (▶sS^= new x)
  with refl ← ▶s⨟,-unique new = ⟹^0 up (⊢r-weaken,s regA (▶s⨟,-▶s,-l new)) (sregular-weaken,s env (▶s⨟,-▶s,-l new))
inst-weaken,s (⟹^S inst up1) (▶sS^ new x) = ⟹^S (inst-weaken,s inst new) up1
inst-weaken,s (⟹∙S inst up1) (▶sS∙ new x) = ⟹∙S (inst-weaken,s inst new) up1
inst-weaken,s (⟹=S inst up1 regB) (▶sS= new x) = ⟹=S (inst-weaken,s inst new) up1 (⊢r-weaken,s regB (▶s⨟,-▶s,-l new))
