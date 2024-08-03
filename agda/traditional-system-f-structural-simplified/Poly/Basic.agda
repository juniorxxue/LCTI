module Poly.Basic where

open import Poly.Common

_/ˣ_ : Env (1 + n) m → Fin (1 + n) → Env n m
(Γ , A) /ˣ #0 = Γ
_/ˣ_ {suc n} (Γ , A) (#S k) = (Γ /ˣ k) , A
(Γ ,∙) /ˣ k = (Γ /ˣ k) ,∙
