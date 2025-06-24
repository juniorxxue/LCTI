module Implicit.Interm2Algo2.FVClose where

open import Implicit.Language.All
open import Implicit.AuxLemmas

data HClosed : Env n m → HitMis m → Set where
  hclo-Z : HClosed ∅ ∅
  hclo-S, : HClosed Γ H
          → HClosed (Γ , A) H
  hclo-S^ : HClosed Γ H
          → HClosed (Γ ,^) (mis H)
  hclo-S∙-hit : HClosed Γ H
              → HClosed (Γ ,∙) (hit H)
  hclo-S∙-mis : HClosed Γ H
              → HClosed (Γ ,∙) (mis H)
  hclo-S=-hit : HClosed Γ H
              → HClosed (Γ ,= A) (hit H)
  hclo-S=-mis : HClosed Γ H
              → HClosed (Γ ,= A) (mis H)
  hclo-S⋈ : HClosed Γ H
            → HClosed (Γ ⋈) H


data FClose (Γ : Env n m) (A : Type m) : Set where
  f-close : ∀ {H}
         → (fv : A 𝕗𝕧 H)
         → (hclo : HClosed Γ H)
         → FClose Γ A


mkMis-hclose : ∀ {m} {Γ : Env n m}
             → HClosed Γ mkMis
mkMis-hclose {m = zero} {Γ = ∅} = hclo-Z
mkMis-hclose {m = zero} {Γ = Γ , A} = hclo-S, mkMis-hclose
mkMis-hclose {m = zero} {Γ = Γ ⋈} = hclo-S⋈ mkMis-hclose
mkMis-hclose {m = suc m} {Γ = Γ , A} = hclo-S, mkMis-hclose
mkMis-hclose {m = suc m} {Γ = Γ ,^} = hclo-S^ mkMis-hclose
mkMis-hclose {m = suc m} {Γ = Γ ,∙} = hclo-S∙-mis mkMis-hclose
mkMis-hclose {m = suc m} {Γ = Γ ,= A} = hclo-S=-mis mkMis-hclose
mkMis-hclose {m = suc m} {Γ = Γ ⋈} = hclo-S⋈ mkMis-hclose

∋∙-hclose : Γ ∋∙ X
          → HClosed Γ (mkHit X)
∋∙-hclose Z = hclo-S∙-hit mkMis-hclose
∋∙-hclose (S, inΓ) = hclo-S, (∋∙-hclose inΓ)
∋∙-hclose (S∙ inΓ) = hclo-S∙-mis (∋∙-hclose inΓ)
∋∙-hclose (S= inΓ) = hclo-S=-mis (∋∙-hclose inΓ)
∋∙-hclose (S^ inΓ) = hclo-S^ (∋∙-hclose inΓ)
∋∙-hclose (S⋈ inΓ) = hclo-S⋈ (∋∙-hclose inΓ)

∋=-hclose : Γ ∋= X
          → HClosed Γ (mkHit X)
∋=-hclose Z = hclo-S=-hit mkMis-hclose
∋=-hclose (S∙ inΓ) = hclo-S∙-mis (∋=-hclose inΓ)
∋=-hclose (S^ inΓ) = hclo-S^ (∋=-hclose inΓ)
∋=-hclose (S= inΓ) = hclo-S=-mis (∋=-hclose inΓ)
∋=-hclose (S, inΓ) = hclo-S, (∋=-hclose inΓ)

orHit-hclose : HClosed Γ H₁
             → HClosed Γ H₂
             → orHit H₁ H₂ H
             → HClosed Γ H
orHit-hclose hclo-Z hclo-Z Z = hclo-Z
orHit-hclose (hclo-S, hclo1) (hclo-S, hclo2) Z = hclo-S, hclo1
orHit-hclose (hclo-S⋈ hclo1) (hclo-S⋈ hclo2) Z = hclo-S⋈ hclo1
orHit-hclose (hclo-S, hclo1) (hclo-S, hclo2) (S-hm orh) = hclo-S, (orHit-hclose hclo1 hclo2 (S-hm orh))
orHit-hclose (hclo-S∙-hit hclo1) (hclo-S∙-mis hclo2) (S-hm orh) = hclo-S∙-hit (orHit-hclose hclo1 hclo2 orh)
orHit-hclose (hclo-S=-hit hclo1) (hclo-S=-mis hclo2) (S-hm orh) = hclo-S=-hit (orHit-hclose hclo1 hclo2 orh)
orHit-hclose (hclo-S⋈ hclo1) (hclo-S⋈ hclo2) (S-hm orh) = hclo-S⋈ (orHit-hclose hclo1 hclo2 (S-hm orh))
orHit-hclose (hclo-S, hclo1) (hclo-S, hclo2) (S-mh orh) = hclo-S, (orHit-hclose hclo1 hclo2 (S-mh orh))
orHit-hclose (hclo-S∙-mis hclo1) (hclo-S∙-hit hclo2) (S-mh orh) = hclo-S∙-hit (orHit-hclose hclo1 hclo2 orh)
orHit-hclose (hclo-S=-mis hclo1) (hclo-S=-hit hclo2) (S-mh orh) = hclo-S=-hit (orHit-hclose hclo1 hclo2 orh)
orHit-hclose (hclo-S⋈ hclo1) (hclo-S⋈ hclo2) (S-mh orh) = hclo-S⋈ (orHit-hclose hclo1 hclo2 (S-mh orh))
orHit-hclose (hclo-S, hclo1) (hclo-S, hclo2) (S-hh orh) = hclo-S, (orHit-hclose hclo1 hclo2 (S-hh orh))
orHit-hclose (hclo-S∙-hit hclo1) (hclo-S∙-hit hclo2) (S-hh orh) = hclo-S∙-hit (orHit-hclose hclo1 hclo2 orh)
orHit-hclose (hclo-S=-hit hclo1) (hclo-S=-hit hclo2) (S-hh orh) = hclo-S=-hit (orHit-hclose hclo1 hclo2 orh)
orHit-hclose (hclo-S⋈ hclo1) (hclo-S⋈ hclo2) (S-hh orh) = hclo-S⋈ (orHit-hclose hclo1 hclo2 (S-hh orh))
orHit-hclose (hclo-S, hclo1) (hclo-S, hclo2) (s-mm orh) = hclo-S, (orHit-hclose hclo1 hclo2 (s-mm orh))
orHit-hclose (hclo-S^ hclo1) (hclo-S^ hclo2) (s-mm orh) = hclo-S^ (orHit-hclose hclo1 hclo2 orh)
orHit-hclose (hclo-S∙-mis hclo1) (hclo-S∙-mis hclo2) (s-mm orh) = hclo-S∙-mis (orHit-hclose hclo1 hclo2 orh)
orHit-hclose (hclo-S=-mis hclo1) (hclo-S=-mis hclo2) (s-mm orh) = hclo-S=-mis (orHit-hclose hclo1 hclo2 orh)
orHit-hclose (hclo-S⋈ hclo1) (hclo-S⋈ hclo2) (s-mm orh) = hclo-S⋈ (orHit-hclose hclo1 hclo2 (s-mm orh))

⊢c-fclose : Γ ⊢c A → FClose Γ A
⊢c-fclose ⊢c-int = f-close fv-Int mkMis-hclose
⊢c-fclose (⊢c-var-∙ inΔ) = f-close fv-var (∋∙-hclose inΔ)
⊢c-fclose (⊢c-var-= inΔ) = f-close fv-var (∋=-hclose inΔ)
⊢c-fclose (⊢c-arr cloA cloA₁) with ⊢c-fclose cloA | ⊢c-fclose cloA₁
... | f-close {H = H₁} fv1 hclo1 | f-close {H = H₂} fv2 hclo2
  with ⟨ H' , or-hit ⟩ ← orHit-total H₁ H₂ = f-close (fv-arr fv1 fv2 or-hit) (orHit-hclose hclo1 hclo2 or-hit)
⊢c-fclose (⊢c-∀ cloA) with ⊢c-fclose cloA
... | f-close fv (hclo-S∙-hit hclo) = f-close (fv-∀-h fv) hclo
... | f-close fv (hclo-S∙-mis hclo) = f-close (fv-∀-m fv) hclo
