module Heap where

open import Data.List
open import Data.Nat
open import Data.Bool
open import Relation.Nullary
open import Data.Nat.Properties
open import Data.Sum
open import Data.Empty
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Maybe
open import Function
open import Sort

data Heap (A : Set) : Set where
    E : Heap A
    ∧ : A → Heap A → Heap A → Heap A

mergeHeap : Heap ℕ → Heap ℕ → Heap ℕ
mergeHeap E y = y
mergeHeap x E = x
mergeHeap x@(∧ n rx lx) y@(∧ m ry ly) with n ≤? m
... | yes n≤m = ∧ n (mergeHeap y lx) rx
... | no n≰m  = ∧ m (mergeHeap x ly) ry


insertHeap : ℕ → Heap ℕ → Heap ℕ
insertHeap n h = mergeHeap (∧ n E E) h

makeHeap : List ℕ → Heap ℕ
makeHeap = foldr insertHeap E

deleteMin : Heap ℕ → Maybe (ℕ × Heap ℕ)
deleteMin E = nothing
deleteMin (∧ x r l) = just (x , mergeHeap r l)

fromHeap : ℕ → Heap ℕ → List ℕ
fromHeap n = unfold (λ n → Heap ℕ) (λ {n} → deleteMin) {n}

hsort : List ℕ → List ℕ
hsort xs = (fromHeap (suc (length xs))) (makeHeap xs)

test1 : hsort (5 ∷ 4 ∷ 3 ∷ 2 ∷ 1 ∷ []) ≡ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])
test1 = refl
