open import Data.Nat public
open import Data.Nat.Properties public

variable
  m n m' : ℕ

data explicit-guarantee : (m : ℕ) → (n : ℕ) → (p : m ≤ n) → Set where
  case-one : explicit-guarantee 0 1 z≤n
  case-two : explicit-guarantee 0 2 z≤n
  case-three : explicit-guarantee 1 4 (s≤s z≤n)
  
data implicit-guarantee : (m : ℕ) → (m' + m : ℕ) → Set where
  case-one : implicit-guarantee 0 1
  
