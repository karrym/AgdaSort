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

open ≡-Reasoning

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
fromHeap zero x = []
fromHeap (suc n) E = []
fromHeap (suc n) (∧ x l r) = x ∷ fromHeap n (mergeHeap l r)

heapSize : {A : Set} → Heap A → ℕ
heapSize E = zero
heapSize (∧ x l r) = suc (heapSize l + heapSize r)

hsort : List ℕ → List ℕ
hsort xs = fromHeap (heapSize h) h
    where h = makeHeap xs

test1 : hsort (5 ∷ 4 ∷ 3 ∷ 2 ∷ 1 ∷ []) ≡ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])
test1 = refl

step-insert≥ : {n x : ℕ}{rx lx : Heap ℕ} → ¬ (n ≤ x) → insertHeap n (∧ x rx lx) ≡ ∧ x (mergeHeap (∧ n E E) lx) rx
step-insert≥ {n}{x}{rx}{lx} n≰x with n ≤? x
... | yes n≤x = ⊥-elim (n≰x n≤x)
... | no n≰x′ = refl

step-insert≤ : {n x : ℕ}{rx lx : Heap ℕ} → n ≤ x → insertHeap n (∧ x rx lx) ≡ ∧ n (∧ x rx lx) E
step-insert≤ {n}{x}{rx}{lx} n≤x with n ≤? x
... | yes n≤x′ = refl
... | no n≰x  = ⊥-elim (n≰x n≤x)

step-merge≤ : {x y : ℕ}{lx rx ly ry : Heap ℕ} → x ≤ y
        → mergeHeap (∧ x lx rx) (∧ y ly ry) ≡ (∧ x (mergeHeap (∧ y ly ry) rx) lx)
step-merge≤ {x}{y} x≤y with x ≤? y
... | yes x≤y′ = refl
... | no x≰y  = ⊥-elim (x≰y x≤y)

step-merge≥ : {x y : ℕ}{lx rx ly ry : Heap ℕ} → ¬ (x ≤ y)
        → mergeHeap (∧ x lx rx) (∧ y ly ry) ≡ (∧ y (mergeHeap (∧ x lx rx) ry) ly)
step-merge≥ {x}{y} x≰y with x ≤? y
... | yes x≤y = ⊥-elim (x≰y x≤y)
... | no x≰y′  = refl
