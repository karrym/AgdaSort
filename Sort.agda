module Sort where

open import Data.List
open import Data.Nat
open import Data.Bool
open import Relation.Nullary
open import Data.Nat.Properties
open import Data.Sum
open import Data.Empty
open import Relation.Binary.PropositionalEquality

data Sorted : List ℕ → Set where
    snull : Sorted []
    scons1 : {x : ℕ} → Sorted (x ∷ [])
    scons : {x y : ℕ} {ys : List ℕ} → x ≤ y → Sorted (y ∷ ys) → Sorted (x ∷ y ∷ ys)

lem-≤ : {x y : ℕ} → ¬ (x ≤ y) → y ≤ x
lem-≤ {x} {y} x≰y with ≤-total x y
... | inj₁ x≤y = ⊥-elim (x≰y x≤y)
... | inj₂ y≤x = y≤x

data Permutation {A} : List A → List A → Set where
    pnull : Permutation [] []
    pskip : {x : A} {xs ys : List A} → Permutation xs ys → Permutation (x ∷ xs) (x ∷ ys)
    pswap : {x y : A} {xs : List A} → Permutation (x ∷ y ∷ xs) (y ∷ x ∷ xs)
    ptrans : {xs ys zs : List A} → Permutation xs ys → Permutation ys zs → Permutation xs zs
