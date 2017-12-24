module Merge where

open import Data.List
open import Data.Nat
open import Data.Bool
open import Relation.Nullary
open import Data.Nat.Properties
open import Data.Sum
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Induction.WellFounded
open import Induction.Nat
open import Relation.Binary
import Level
open import Function
open import Data.Product

open import Sort

merge : List ℕ → List ℕ → List ℕ
merge [] ys = ys
merge (x ∷ xs) [] = x ∷ xs
merge (x ∷ xs) (y ∷ ys) with x ≤? y
... | yes _ = x ∷ merge xs (y ∷ ys)
... | no _  = y ∷ merge (x ∷ xs) ys

step-mergeL : {x y : ℕ}{xs ys : List ℕ} → x ≤ y → merge (x ∷ xs) (y ∷ ys) ≡ x ∷ merge xs (y ∷ ys)
step-mergeL {x}{y}{xs}{ys} x≤y with x ≤? y
... | yes _  = refl
... | no x≰y = ⊥-elim (x≰y x≤y)

step-mergeR : {x y : ℕ}{xs ys : List ℕ} → ¬ (x ≤ y) → merge (x ∷ xs) (y ∷ ys) ≡ y ∷ merge (x ∷ xs) ys
step-mergeR {x}{y}{xs}{ys} x≰y with x ≤? y
... | yes x≤y = ⊥-elim (x≰y x≤y)
... | no _    = refl

lem-msort : (xs ys : List ℕ) → Sorted xs → Sorted ys → Sorted (merge xs ys)
lem-msort [] ys snull sy = sy
lem-msort (x ∷ []) [] scons1 snull = scons1
lem-msort (x ∷ []) (y ∷ []) scons1 scons1 with x ≤? y
... | yes x≤y = scons x≤y scons1
... | no x≰y  = scons (lem-≤ x≰y) scons1
lem-msort (x ∷ []) (y ∷ w ∷ ws) scons1 (scons y≤w sy) with x ≤? y
... | yes x≤y = scons x≤y (scons y≤w sy)
... | no x≰y with x ≤? w
...     | yes x≤w = scons (lem-≤ x≰y) (scons x≤w sy)
...     | no x≰w  = scons y≤w (subst Sorted (step-mergeR x≰w) (lem-msort (x ∷ []) (w ∷ ws) scons1 sy))
lem-msort (x ∷ z ∷ zs) [] (scons x≤z sx) snull = scons x≤z sx
lem-msort (x ∷ z ∷ zs) (y ∷ []) (scons x≤z sx) scons1 with x ≤? y
... | yes x≤y with z ≤? y
...     | yes z≤y = scons x≤z (subst Sorted (step-mergeL z≤y) (lem-msort (z ∷ zs) (y ∷ []) sx scons1))
...     | no z≰y  = scons x≤y (scons (lem-≤ z≰y) sx)
lem-msort (x ∷ z ∷ zs) (y ∷ []) (scons x≤z sx) scons1
    | no x≰y  = scons (lem-≤ x≰y) (scons x≤z sx)
lem-msort (x ∷ z ∷ zs) (y ∷ w ∷ ws) (scons x≤z sx) (scons y≤w sy) with x ≤? y
... | yes x≤y with z ≤? y
...     | yes z≤y = scons x≤z (subst Sorted (step-mergeL z≤y) (lem-msort (z ∷ zs) (y ∷ w ∷ ws) sx (scons y≤w sy)))
...     | no z≰y with z ≤? w
...         | yes z≤w = scons x≤y (scons (lem-≤ z≰y) (subst Sorted (step-mergeL z≤w) (lem-msort (z ∷ zs) (w ∷ ws) sx sy)))
...         | no z≰w  = scons x≤y (scons y≤w (subst Sorted (step-mergeR z≰w) (lem-msort (z ∷ zs) (w ∷ ws) sx sy)))
lem-msort (x ∷ z ∷ zs) (y ∷ w ∷ ws) (scons x≤z sx) (scons y≤w sy)
    | no x≰y with x ≤? w
...     | yes x≤w with z ≤? w
...         | yes z≤w = scons (lem-≤ x≰y) (scons x≤z (subst Sorted (step-mergeL z≤w) (lem-msort (z ∷ zs) (w ∷ ws) sx sy)))
...         | no z≰w  = scons (lem-≤ x≰y) (scons x≤w (subst Sorted (step-mergeR z≰w) (lem-msort (z ∷ zs) (w ∷ ws) sx sy)))
lem-msort (x ∷ z ∷ zs) (y ∷ w ∷ ws) (scons x≤z sx) (scons y≤w sy)
    | no x≰y
        | no x≰w  = scons y≤w (subst Sorted (step-mergeR x≰w) (lem-msort (x ∷ z ∷ zs) (w ∷ ws) (scons x≤z sx) sy))

xs++[]≡xs : {A : Set} {xs : List A} → xs ++ [] ≡ xs
xs++[]≡xs {A} {[]} = refl
xs++[]≡xs {A} {x ∷ xs} = cong (_∷_ x) xs++[]≡xs

++-stepR : {A : Set} {y : A} {xs ys : List A} → Permutation (xs ++ (y ∷ ys)) (y ∷ (xs ++ ys))
++-stepR {A} {y} {[]} {ys} = perm-refl
++-stepR {A} {y} {x ∷ xs} {ys} = ptrans (pskip (++-stepR {y = y} {xs = xs} {ys = ys})) pswap

lem-mperm : (xs ys : List ℕ) → Permutation (xs ++ ys) (merge xs ys)
lem-mperm [] ys = perm-refl
lem-mperm (x ∷ xs) [] rewrite xs++[]≡xs {xs = xs} = perm-refl
lem-mperm (x ∷ xs) (y ∷ ys) with x ≤? y
... | yes x≤y = pskip (lem-mperm xs (y ∷ ys))
... | no x≰y  = ptrans (++-stepR {y = y} {xs = x ∷ xs} {ys = ys}) (pskip (lem-mperm (x ∷ xs) ys))

_⟪_ : {A : Set} → Rel (List A) Level.zero
_⟪_ = _<_ on length

⟪-well-founded : {A : Set} → Well-founded (_⟪_ {A})
⟪-well-founded = Inverse-image.well-founded length <-well-founded

module _ {ℓ} {A : Set} where
  open All (⟪-well-founded {A}) ℓ public
    renaming ( wfRec-builder to ⟪-rec-builder
             ; wfRec to ⟪-rec
             )

split : {A : Set} → List A → List A × List A
split xs = splitAt ⌊ (length xs) /2⌋ xs
