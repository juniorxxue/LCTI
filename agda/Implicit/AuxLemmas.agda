module Implicit.AuxLemmas where

open import Implicit.Language.All


-- could be proved via a inst-total
-- however, the total requires a condition: B is shifted k times, which is a tricky to define in well-scoped settings: finite nubmers
inst-exist : [ B / k ] Δ =⟹ Δ'
           → Ω ⊆ Δ
           → Ω ∋= k
           → ∃[ Ω' ]( [ B / k ] Ω =⟹ Ω')
inst-exist (=⟹=0  {A = A} up) (svar {Γ = Γ} ext regA) Z = ⟨ Γ ,= A , =⟹=0 up ⟩
inst-exist (=⟹^S inst up1) (evar ext) (S^ inΩ) = ⟨ inst-exist inst ext inΩ .proj₁ ,^ ,
                                                  =⟹^S (inst-exist inst ext inΩ .proj₂) up1 ⟩
inst-exist (=⟹∙S inst up1) (uvar ext) (S∙ inΩ) = ⟨ inst-exist inst ext inΩ .proj₁ ,∙ ,
                                                  =⟹∙S (inst-exist inst ext inΩ .proj₂) up1 ⟩
inst-exist (=⟹=S inst up1) (evar-sol ext regA) (S^ inΩ) = ⟨ inst-exist inst ext inΩ .proj₁ ,^ ,
                                                           =⟹^S (inst-exist inst ext inΩ .proj₂) up1 ⟩
inst-exist (=⟹=S inst up1) (svar {A = A} ext regA) (S= inΩ) = ⟨ inst-exist inst ext inΩ .proj₁ ,= A ,
                                                       =⟹=S (inst-exist inst ext inΩ .proj₂) up1 ⟩
