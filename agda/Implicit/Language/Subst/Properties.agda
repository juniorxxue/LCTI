module Implicit.Language.Subst.Properties where

open import Implicit.Language.Base
open import Implicit.Language.Subst.Base
open import Implicit.Language.Shift

stx-unique : ⟦ k / A ⟧ˣ X ⇘ B₁
           → ⟦ k / A ⟧ˣ X ⇘ B₂
           → B₁ ≡ B₂
stx-unique stx-eq stx-eq = refl
stx-unique stx-eq (stx-neq ¬p) = ⊥-elim (¬p refl)
stx-unique (stx-neq ¬p) stx-eq = ⊥-elim (¬p refl)
stx-unique (stx-neq ¬p) (stx-neq ¬p₁) = refl

st-unique :
    ⟦ k / A ⟧ B ⇘ B₁
  → ⟦ k / A ⟧ B ⇘ B₂
  → B₁ ≡ B₂
st-unique st-int st-int = refl
st-unique (st-var stx1) (st-var stx2) = stx-unique stx1 stx2
st-unique (st-arr st1 st3) (st-arr st2 st4) rewrite st-unique st1 st2 | st-unique st3 st4 = refl
st-unique (st-∀ up st1) (st-∀ up₁ st2) rewrite ↑ty-unique up up₁ | st-unique st1 st2 = refl

stx-total : ∀ (A : Type m) k X
  → ∃[ A* ](⟦ k / A ⟧ˣ X ⇘ A*)
stx-total A k X with k #≟ X
... | yes refl = ⟨ A , stx-eq ⟩
... | no ¬p = ⟨ (‶ punchOut {i = k} {j = X} ¬p) , stx-neq ¬p ⟩

st-total : ∀ (A : Type m) k B → ∃[ B* ](⟦ k / A ⟧ B ⇘ B*)
st-total A k Int = ⟨ Int , st-int ⟩
st-total A k (‶ X) with stx-total A k X
... | ⟨ A' , stx ⟩ = ⟨ A' , st-var stx ⟩
st-total A k (B `→ B₁) = ⟨ st-total A k B .proj₁ `→ st-total A k B₁ .proj₁ ,
                          st-arr (st-total A k B .proj₂) (st-total A k B₁ .proj₂) ⟩
st-total A k (`∀ B) with ↑ty0-total A
... | ⟨ A' , upA ⟩ with st-total A' (#S k) B
... | ⟨ B* , stB ⟩ = ⟨ `∀ B* , st-∀ upA stB ⟩

st0-total : ∀ (A : Type m) B → ∃[ B* ](⟦ A ⟧ B ⇘ B*)
st0-total A B = st-total A #0 B

st0-unique :
    ⟦ A ⟧ B ⇘ B₁
  → ⟦ A ⟧ B ⇘ B₂
  → B₁ ≡ B₂
st0-unique st1 st2 = st-unique st1 st2

↑ty-stx-eq : ⟦ k / T ⟧ˣ Y ⇘ B
           → Y ≡ punchIn k X
           → ‶ X ≡ B
↑ty-stx-eq {k = k} {Y = Y} {X = X} stx-eq eq = ⊥-elim ((punchInᵢ≢i k X) (sym eq))
↑ty-stx-eq {k = k} (stx-neq ¬p) refl = cong ‶_ (sym (punchOut-punchIn k))

↑ty-st-eq :
    A ↑ty k ⇘ A'
  → ⟦ k / T ⟧ A' ⇘ B
  → A ≡ B
↑ty-st-eq ↑ty-int st-int = refl
↑ty-st-eq {k = k} (↑ty-var {X = X}) (st-var stx) = ↑ty-stx-eq stx refl
↑ty-st-eq (↑ty-arr up up₁) (st-arr st st₁) rewrite ↑ty-st-eq up st | ↑ty-st-eq up₁ st₁ = refl
↑ty-st-eq (↑ty-∀ up) (st-∀ up₁ st) = cong `∀_ (↑ty-st-eq up st)

↑ty-st :
    A ↑ty k ⇘ A'
  → ⟦ k / T ⟧ A' ⇘ A
↑ty-st {A = A} {k} {A'} {T = T} up with st-total T k A'
... | ⟨ A* , st ⟩ rewrite ↑ty-st-eq up st = st

{-
-- this is a wrong lemma, say T is Int, k is 0, A' is 0
st-↑ty : ⟦ k / T ⟧ A' ⇘ A
       → A ↑ty k ⇘ A'
st-↑ty st-int = ↑ty-int
st-↑ty {k = k} {T = T} (st-var {X = X}) = {!!}
st-↑ty (st-arr st st₁) = ↑ty-arr (st-↑ty st) (st-↑ty st₁)
st-↑ty (st-∀ up st) = ↑ty-∀ (st-↑ty st)
-}

↑tyᵉ-st-eq :
    e ↑tyᵉ k ⇘ e'
  → ⟦ k / T ⟧ᵉ e' ⇘ e*
  → e ≡ e*
↑tyᵉ-st-eq ↑tyᵉ-lit st-lit = refl
↑tyᵉ-st-eq ↑tyᵉ-var st-var = refl
↑tyᵉ-st-eq (↑tyᵉ-ƛ up) (st-ƛ st) = cong ƛ_ (↑tyᵉ-st-eq up st)
↑tyᵉ-st-eq (↑tyᵉ-app up up₁) (st-· st st₁) rewrite ↑tyᵉ-st-eq up st | ↑tyᵉ-st-eq up₁ st₁ = refl
↑tyᵉ-st-eq (↑tyᵉ-⦂ up x) (st-⦂ st x₁) rewrite ↑tyᵉ-st-eq up st | ↑ty-st-eq x x₁ = refl
↑tyᵉ-st-eq (↑tyᵉ-Λ up) (st-Λ st up') = cong Λ_ (↑tyᵉ-st-eq up st)

↑tyᵉ-st :
    e ↑tyᵉ k ⇘ e'
  → ⟦ k / T ⟧ᵉ e' ⇘ e
↑tyᵉ-st ↑tyᵉ-lit = st-lit
↑tyᵉ-st ↑tyᵉ-var = st-var
↑tyᵉ-st (↑tyᵉ-ƛ up) = st-ƛ (↑tyᵉ-st up)
↑tyᵉ-st (↑tyᵉ-app up up₁) = st-· (↑tyᵉ-st up) (↑tyᵉ-st up₁)
↑tyᵉ-st (↑tyᵉ-⦂ up up₁) = st-⦂ (↑tyᵉ-st up) (↑ty-st up₁)
↑tyᵉ-st {T = T} (↑tyᵉ-Λ up) = st-Λ (↑tyᵉ-st up) (proj₂ (↑ty0-total T))

st-total-rev : ∀ k B → ∃[ A ](⟦ k / T ⟧ A ⇘ B)
st-total-rev k B = let ⟨ B* , up ⟩ = ↑ty-total B k in ⟨ B* , ↑ty-st up ⟩

st0-total-rev : ∀ B → ∃[ A ](⟦ T ⟧ A ⇘ B)
st0-total-rev = st-total-rev #0




-- a corollary of ↑ty-comm and ↑ty-st
{-
↑ty-st-comm : k₂ #≤ k₁
            → A ↑ty (inject₁ k₁) ⇘ A'
            → T ↑ty k₁ ⇘ T'
            → ⟦ #S k₂ / T' ⟧ A' ⇘ A*'
            ---------------
            → A* ↑ty k₁ ⇘ A*'
            → ⟦ k₂ / T ⟧ A ⇘ A*
-}

punchIn-punchOut' : ∀ {k₂ : Fin (1 + m)}
  → (¬p : k₁ ≢ X)
  → (sm : k₁ #≤ k₂)
  → punchOut {i = inject₁ k₁} {j = punchIn (#S k₂) X} (punchIn-inject-neq (s≤s sm) ¬p) ≡ punchIn k₂ (punchOut ¬p)
punchIn-punchOut' {k₁ = #0} {#0} {k₂ = k₂} ¬p sm = ⊥-elim (¬p refl)
punchIn-punchOut' {k₁ = #S #0} {#0} {k₂ = #S k₂} ¬p sm = refl
punchIn-punchOut' {k₁ = #S (#S k₁)} {#0} {k₂ = #S k₂} ¬p sm = refl
punchIn-punchOut' {k₁ = #0} {#S X} {k₂ = #0} ¬p sm = refl
punchIn-punchOut' {k₁ = #0} {#S X} {k₂ = #S k₂} ¬p sm = refl
punchIn-punchOut' {m = suc m} {k₁ = #S k₁} {X = #S X} {k₂ = #S k₂} ¬p (s≤s sm) = cong #S (punchIn-punchOut' (λ x → ¬p (cong #S x)) sm)

↑ty-stx-comm : k₁ #≤ k₂
             → ⟦ k₁ / B ⟧ˣ X ⇘ A*
             ----------------------
             → B ↑ty k₂ ⇘ B'
             → A* ↑ty k₂ ⇘ A*'
             ------------------
             → ⟦ inject₁ k₁ / B' ⟧ˣ punchIn (#S k₂) X ⇘ A*'
↑ty-stx-comm {k₁ = k₁} {k₂} {B = B} k₁≤k₂ stx-eq up1 up2
  rewrite sym (punchIn-inject {X = k₁} {k = #S k₂} (s≤s k₁≤k₂)) rewrite ↑ty-unique up1 up2 = stx-eq
↑ty-stx-comm {k₁ = k₁} {k₂} {X = X} k₁≤k₂ (stx-neq ¬p) up1 ↑ty-var rewrite sym (punchIn-punchOut' ¬p k₁≤k₂) = stx-neq (punchIn-inject-neq (s≤s k₁≤k₂) ¬p)

↑ty-st-comm : k₁ #≤ k₂
            → ⟦ k₁ / B ⟧ A ⇘ A*
            --------------------
            → A ↑ty (#S k₂) ⇘ A'
            → B ↑ty k₂ ⇘ B'
            → A* ↑ty k₂ ⇘ A*'
            ----------------------
            → ⟦ (inject₁ k₁) / B' ⟧ A' ⇘ A*'
↑ty-st-comm k₁≤k₂ st-int ↑ty-int up2 ↑ty-int = st-int
↑ty-st-comm k₁≤k₂ (st-var stx) ↑ty-var up2 up3 = st-var (↑ty-stx-comm k₁≤k₂ stx up2 up3)
↑ty-st-comm k₁≤k₂ (st-arr st st₁) (↑ty-arr up1 up4) up2 (↑ty-arr up3 up5) =
  st-arr (↑ty-st-comm k₁≤k₂ st up1 up2 up3) (↑ty-st-comm k₁≤k₂ st₁ up4 up2 up5)
↑ty-st-comm {B' = B'} k₁≤k₂ (st-∀ up st) (↑ty-∀ up1) up2 (↑ty-∀ up3) with ↑ty0-total B'
... | ⟨ nB' , upB' ⟩ = st-∀ upB' (↑ty-st-comm (s≤s k₁≤k₂) st up1 (↑ty-comm0' up2 upB' up) up3)

↑ty-st-comm0 : ⟦ B ⟧ C ⇘ C*
             → B ↑ty k ⇘ B'
             → C ↑ty #S k ⇘ C'
             → C* ↑ty k ⇘ C*'
             → ⟦ B' ⟧ C' ⇘ C*'
↑ty-st-comm0 up1 st1 up2 up3 = ↑ty-st-comm {k₁ = #0} z≤n up1 up2 st1 up3

#≤-inject : ∀ {k₁ : Fin (1 + m)} {k₂ : Fin (1 + m)}
          → k₁ #≤ k₂
          → inject₁ k₁ #≤ k₂
#≤-inject {k₁ = #0} {k₂} lt = lt
#≤-inject {m = suc m} {k₁ = #S k₁} {#S k₂} (s≤s lt) = s≤s (#≤-inject lt)

postulate
  ↑ty-stx-comm1 : k₁ #≤ k₂
                → ⟦ k₂ / T ⟧ˣ X ⇘ A*
                -----------------------
                → T ↑ty k₁ ⇘ T'
                -----------------------
                → ⟦ #S k₂ / T' ⟧ˣ punchIn (inject₁ k₁) X ⇘ A*'
                → A* ↑ty k₁ ⇘ A*'
{-
↑ty-stx-comm1 {k₁ = k₁} {k₂} lt stx-eq upT stX rewrite punchIn-≤ {k₁ = k₂} {k₂ = inject₁ k₁} (#≤-inject lt) with stX
... | stx-eq = upT
... | stx-neq ¬p = ⊥-elim (¬p refl)
↑ty-stx-comm1 {m} {k₁ = #0} {k₂} {X = X} lt (stx-neq ¬p) upT stx-eq = ⊥-elim (¬p refl)
↑ty-stx-comm1 {m} {k₁ = #0} {k₂} {X = X} lt (stx-neq ¬p) upT (stx-neq ¬p₁) = ↑ty-var
↑ty-stx-comm1 {m} {k₁ = #S k₁} {k₂} {X = #0} lt (stx-neq ¬p) upT (stx-neq ¬p₁) = {!!}
↑ty-stx-comm1 {m} {k₁ = #S k₁} {k₂} {X = #S X} lt (stx-neq ¬p) upT stx-eq = {!!}
↑ty-stx-comm1 {m} {k₁ = #S k₁} {k₂} {X = #S X} lt (stx-neq ¬p) upT (stx-neq ¬p₁) = {!!}
-}


↑ty-st-comm1 : k₁ #≤ k₂
             --------------------
             → ⟦ k₂ / T ⟧ A ⇘ A*
             --------------------
             → T ↑ty k₁ ⇘ T'
             → A ↑ty (inject₁ k₁) ⇘ A'
             → ⟦ #S k₂ / T' ⟧ A' ⇘ A*'
             --------------------
             → A* ↑ty k₁ ⇘ A*'
↑ty-st-comm1 lt st-int upT ↑ty-int st-int = ↑ty-int
↑ty-st-comm1 lt (st-var stx) upT ↑ty-var (st-var stx₁) = ↑ty-stx-comm1 lt stx upT stx₁
↑ty-st-comm1 lt (st-arr stA stA₁) upT (↑ty-arr upA upA₁) (st-arr stA' stA'') =
  ↑ty-arr (↑ty-st-comm1 lt stA upT upA stA') (↑ty-st-comm1 lt stA₁ upT upA₁ stA'')
↑ty-st-comm1 lt (st-∀ up stA) upT (↑ty-∀ upA) (st-∀ up₁ stA') = ↑ty-∀ (↑ty-st-comm1 (s≤s lt) stA (↑ty-comm0' upT up₁ up) upA stA')

postulate
  ↑ty-st-comm1' : k₁ #≤ k₂
                --------------------
                → ⟦ k₂ / T ⟧ A ⇘ A*
                --------------------
                → T ↑ty k₁ ⇘ T'
                → A ↑ty (inject₁ k₁) ⇘ A'
                → A* ↑ty k₁ ⇘ A*'
                --------------------
                → ⟦ #S k₂ / T' ⟧ A' ⇘ A*'


postulate
  st-st-comm : ∀ {k₁ : Fin (1 + m)} {k₂ T U U* U** U*₂ V T* V'}
             → k₁ #≤ k₂
             → ⟦ (inject₁ k₁) / U ⟧ T ⇘ U*
             → ⟦ k₂ / V ⟧ U* ⇘ U**
             ------------------------
             → V ↑ty k₁ ⇘ V'
             → ⟦ #S k₂ / V' ⟧ T ⇘ T*
             → ⟦ k₂ / V ⟧ U ⇘ U*₂
             → ⟦ k₁ / U*₂ ⟧ T* ⇘ U**
