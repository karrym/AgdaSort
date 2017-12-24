module Insert where

open import Data.List
open import Data.Nat
open import Data.Bool
open import Relation.Nullary
open import Data.Nat.Properties
open import Data.Sum
open import Data.Empty
open import Relation.Binary.PropositionalEquality

open import Sort

insert : ℕ → List ℕ → List ℕ
insert x [] = x ∷ []
insert x (y ∷ ys) with x ≤? y
... | yes _ = x ∷ y ∷ ys
... | no _  = y ∷ insert x ys

step-insert : {x y : ℕ}{ys : List ℕ} → ¬ (x ≤ y) → insert x (y ∷ ys) ≡ y ∷ insert x ys
step-insert {x} {y} {ys} x≰y with x ≤? y
... | yes x≤y = ⊥-elim (x≰y x≤y)
... | no x≰y₁ = refl

lem-isorted : (x : ℕ) → (xs : List ℕ) → Sorted xs → Sorted (insert x xs)
lem-isorted x [] s = scons1
lem-isorted x (y ∷ ys) s with x ≤? y
... | yes x≤y = scons x≤y s
lem-isorted x (y ∷ []) scons1 | no x≰y = scons (lem-≤ x≰y) scons1
lem-isorted x (y ∷ (z ∷ zs)) (scons y≤z s) | no x≰y with x ≤? z
...     | yes x≤z = scons (lem-≤ x≰y) (scons x≤z s)
...     | no x≰z  = scons y≤z (subst Sorted (step-insert x≰z) (lem-isorted x (z ∷ zs) s))

isort : List ℕ → List ℕ
isort [] = []
isort (x ∷ xs) = insert x (isort xs)

iSorted : (xs : List ℕ) → Sorted (isort xs)
iSorted [] = snull
iSorted (x ∷ xs) = lem-isorted x (isort xs) (iSorted xs)

lem-iperm : (x : ℕ) (xs : List ℕ) → Permutation (x ∷ xs) (insert x xs)
lem-iperm x [] = pskip pnull
lem-iperm x (y ∷ []) with x ≤? y
... | yes x≤y = pskip (pskip pnull)
... | no x≰y  = pswap
lem-iperm x (y ∷ z ∷ zs) with x ≤? y
... | yes x≤y = ptrans pswap pswap
... | no x≰y with x ≤? z
...     | yes x≤z = pswap
...     | no x≰z  = ptrans pswap (pskip (subst (Permutation (x ∷ z ∷ zs)) (step-insert x≰z) (lem-iperm x (z ∷ zs))))

perm-isort : (xs : List ℕ) → Permutation xs (isort xs)
perm-isort [] = pnull
perm-isort (x ∷ xs) = ptrans (pskip (perm-isort xs)) (lem-iperm x (isort xs))
