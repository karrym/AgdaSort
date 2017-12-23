module Merge where

open import Data.List
open import Data.Nat
open import Data.Bool
open import Relation.Nullary
open import Data.Nat.Properties
open import Data.Sum
open import Data.Empty
open import Relation.Binary.PropositionalEquality

open import Sort

merge : List ℕ → List ℕ → List ℕ
merge [] ys = ys
merge (x ∷ xs) [] = x ∷ xs
merge (x ∷ xs) (y ∷ ys) with x ≤? y
... | yes _ = x ∷ y ∷ merge xs ys
... | no _  = y ∷ x ∷ merge xs ys

lem-msort : (xs ys : List ℕ) → Sorted xs → Sorted ys → Sorted (merge xs ys)
lem-msort .[] ys snull sy = sy
lem-msort .(_ ∷ []) .[] scons1 snull = scons1
lem-msort (x ∷ []) (y ∷ []) scons1 scons1 with x ≤? y
... | yes x≤y = scons x≤y scons1
... | no x≰y  = scons (lem-≤ x≰y) scons1
lem-msort (x ∷ []) (y ∷ z ∷ zs) scons1 (scons y≤z sy) with x ≤? y
... | yes x≤y = scons x≤y (scons y≤z sy)
... | no x≰y with x ≤? z
...     | yes x≤z = scons (lem-≤ x≰y) (scons x≤z sy)
...     | no x≰z  = {!   !}
lem-msort .(_ ∷ _ ∷ _) ys (scons x₁ sx) sy = {!   !}
