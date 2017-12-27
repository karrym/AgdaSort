module HeapProp.HeapMerge where

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
open import Heap

data IsHeap : Heap ℕ → Set where
    h[] : IsHeap E
    h[n] : (n : ℕ) → IsHeap (∧ n E E)
    hE← : {x y : ℕ} {rx lx : Heap ℕ} → IsHeap (∧ x rx lx)
        → y ≤ x → IsHeap (∧ y E (∧ x rx lx))
    hE→ : {x y : ℕ} {rx lx : Heap ℕ} → IsHeap (∧ x rx lx)
        → y ≤ x → IsHeap (∧ y (∧ x rx lx) E)
    h∧ : {x y z : ℕ} {rx lx ry ly : Heap ℕ}
        → IsHeap (∧ x rx lx) → IsHeap (∧ y ry ly)
        → z ≤ x × z ≤ y → IsHeap (∧ z (∧ x rx lx) (∧ y ry ly))

lem-insertHeap : (n : ℕ) → (x : Heap ℕ) → IsHeap x → IsHeap (insertHeap n x)
lem-insertHeap n .E h[] = h[n] n
lem-insertHeap n .(∧ x E E) (h[n] x) with n ≤? x
... | yes n≤x = hE→ (h[n] x) n≤x
... | no n≰x  = hE→ (h[n] n) (lem-≤ n≰x)
lem-insertHeap n (∧ x E (∧ y ry ly)) (hE← hy x≤y) with n ≤? x
... | yes n≤x = hE→ (hE← hy x≤y) n≤x
... | no n≰x with n ≤? y
...     | yes n≤y = hE→ (subst IsHeap (step-insert≤ n≤y) (lem-insertHeap n (∧ y ry ly) hy)) (lem-≤ n≰x)
...     | no n≰y  = hE→ (subst IsHeap (step-insert≥ n≰y) (lem-insertHeap n (∧ y ry ly) hy)) x≤y
lem-insertHeap n (∧ x (∧ y ry ly) E) (hE→ hy x≤y) with n ≤? x
... | yes n≤x = hE→ (hE→ hy x≤y) n≤x
... | no n≰x  = h∧ (h[n] n) hy (lem-≤ n≰x , x≤y)
lem-insertHeap n (∧ x (∧ y ry ly) (∧ z rz lz)) (h∧ hy hz (x≤y , x≤z)) with n ≤? x
... | yes n≤x = hE→ (h∧ hy hz (x≤y , x≤z)) n≤x
... | no n≰x with n ≤? z
...     | yes n≤z = h∧ (subst IsHeap (step-insert≤ n≤z) (lem-insertHeap n (∧ z rz lz) hz)) hy (lem-≤ n≰x , x≤y)
...     | no n≰z  = h∧ (subst IsHeap (step-insert≥ n≰z) (lem-insertHeap n (∧ z rz lz) hz)) hy (x≤z , x≤y)

lem-makeHeap : (xs : List ℕ) → IsHeap (makeHeap xs)
lem-makeHeap [] = h[]
lem-makeHeap (x ∷ xs) = lem-insertHeap x (makeHeap xs) (lem-makeHeap xs)

lem-mergeHeap : (x y : Heap ℕ) → IsHeap x → IsHeap y → IsHeap (mergeHeap x y)
lem-mergeHeap .E y h[] hy = hy
lem-mergeHeap .(∧ n E E) y (h[n] n) hy = lem-insertHeap n y hy
lem-mergeHeap (∧ x E (∧ z lz rz)) .E (hE← hx x≤z) h[] = hE← hx x≤z
lem-mergeHeap (∧ x E (∧ z lz rz)) .(∧ n E E) (hE← hz x≤z) (h[n] n) with x ≤? n
... | no x≰n  = hE→ (hE← hz x≤z) (lem-≤ x≰n)
... | yes x≤n with n ≤? z
...     | yes n≤z = hE→ (hE→ hz n≤z) x≤n
...     | no n≰z  = hE→ (subst IsHeap (step-insert≥ n≰z) (lem-insertHeap n (∧ z lz rz) hz)) x≤z
lem-mergeHeap (∧ x E (∧ z lz rz)) h@(∧ y E (∧ w lw rw))
        (hE← hz x≤z) hy@(hE← hw y≤w) with x ≤? y
... | yes x≤y with y ≤? z
...     | no y≰z  = hE→ (subst IsHeap (step-merge≤ (lem-≤ y≰z)) (lem-mergeHeap (∧ z lz rz) h hz hy)) x≤z
...     | yes y≤z with z ≤? w
...         | yes z≤w = hE→ (subst IsHeap (trans (step-merge≤ y≤z) (cong (λ e → ∧ y e E) (step-merge≤ z≤w))) (lem-mergeHeap h (∧ z lz rz) hy hz)) x≤y
...         | no z≰w  = hE→ (subst IsHeap (trans (step-merge≤ y≤z) (cong (λ e → ∧ y e E) (step-merge≥ z≰w))) (lem-mergeHeap h (∧ z lz rz) hy hz)) x≤y
lem-mergeHeap h@(∧ x E (∧ z lz rz)) (∧ y E (∧ w lw rw)) hx@(hE← hz x≤z) (hE← hw y≤w)
    | no x≰y with x ≤? w
...     | no x≰w  = hE→ (subst IsHeap (step-merge≥ x≰w) (lem-mergeHeap h (∧ w lw rw) hx hw)) y≤w
...     | yes x≤w with w ≤? z
...         | yes w≤z = hE→ (subst IsHeap (trans (step-merge≤ x≤w) (cong (λ e → ∧ x e E) (step-merge≤ w≤z))) (lem-mergeHeap h (∧ w lw rw) hx hw)) (lem-≤ x≰y)
...         | no w≰z  = hE→ (subst IsHeap (trans (step-merge≤ x≤w) (cong (λ e → ∧ x e E) (step-merge≥ w≰z))) (lem-mergeHeap h (∧ w lw rw) hx hw)) (lem-≤ x≰y)
lem-mergeHeap (∧ x E (∧ z lz rz)) h@(∧ y (∧ w lw rw) E) (hE← hz x≤z) hy@(hE→ hw y≤w) with x ≤? y
... | no x≰y  = h∧ (hE← hz x≤z) hw (lem-≤ x≰y , y≤w)
... | yes x≤y with y ≤? z
...     | yes y≤z = hE→ (h∧ hz hw (y≤z , y≤w)) x≤y
...     | no y≰z  = hE→ (subst IsHeap (step-merge≥ y≰z) (lem-mergeHeap h (∧ z lz rz) hy hz)) x≤z
lem-mergeHeap (∧ x E (∧ z lz rz)) h@(∧ y (∧ y₁ l₁ r₁) (∧ y₂ l₂ r₂))
    (hE← hz x≤z) hy@(h∧ h₁ h₂ (y≤y₁ , y≤y₂)) with x ≤? y
... | yes x≤y with y ≤? z
...     | no y≰z  = hE→ (subst IsHeap (step-merge≥ y≰z) (lem-mergeHeap h (∧ z lz rz) hy hz)) x≤z
...     | yes y≤z with z ≤? y₂
...         | yes z≤y₂ = hE→ (h∧ (subst IsHeap (step-merge≤ z≤y₂) (lem-mergeHeap (∧ z lz rz) (∧ y₂ l₂ r₂) hz h₂)) h₁ (y≤z , y≤y₁)) x≤y
...         | no z≰y₂  = hE→ (h∧ (subst IsHeap (step-merge≥ z≰y₂) (lem-mergeHeap (∧ z lz rz) (∧ y₂ l₂ r₂) hz h₂)) h₁ (y≤y₂ , y≤y₁)) x≤y
lem-mergeHeap h@(∧ x E (∧ z lz rz)) (∧ y (∧ y₁ l₁ r₁) (∧ y₂ l₂ r₂))
    hx@(hE← hz x≤z) (h∧ h₁ h₂ (y≤y₁ , y≤y₂))
    | no x≰y with x ≤? y₂
...     | no x≰y₂  = h∧ (subst IsHeap (step-merge≥ x≰y₂) (lem-mergeHeap h (∧ y₂ l₂ r₂) hx h₂)) h₁ (y≤y₂ , y≤y₁)
...     | yes x≤y₂ with y₂ ≤? z
...         | yes y₂≤z = h∧ (hE→ (subst IsHeap (step-merge≤ y₂≤z) (lem-mergeHeap (∧ y₂ l₂ r₂) (∧ z lz rz) h₂ hz)) x≤y₂) h₁ (lem-≤ x≰y , y≤y₁)
...         | no y₂≰z  = h∧ (hE→ (subst IsHeap (step-merge≥ y₂≰z) (lem-mergeHeap (∧ y₂ l₂ r₂) (∧ z lz rz) h₂ hz)) x≤z) h₁ (lem-≤ x≰y , y≤y₁)
lem-mergeHeap (∧ x (∧ z lz rz) E) .E (hE→ hz x≤z) h[] = hE→ hz x≤z
lem-mergeHeap (∧ x (∧ z lz rz) E) .(∧ n E E) (hE→ hz x≤z) (h[n] n) with x ≤? n
... | yes x≤n = h∧ (h[n] n) hz (x≤n , x≤z)
... | no x≰n  = hE→ (hE→ hz x≤z) (lem-≤ x≰n)
lem-mergeHeap h@(∧ x (∧ z lz rz) E) (∧ y E (∧ w lw rw)) hx@(hE→ hz x≤z) (hE← hw y≤w) with x ≤? y
... | yes x≤y = h∧ (hE← hw y≤w) hz (x≤y , x≤z)
... | no x≰y with x ≤? w
...     | yes x≤w = hE→ (h∧ hw hz (x≤w , x≤z)) (lem-≤ x≰y)
...     | no x≰w  = hE→ (subst IsHeap (step-merge≥ x≰w) (lem-mergeHeap h (∧ w lw rw) hx hw)) y≤w
lem-mergeHeap (∧ x (∧ z lz rz) E) (∧ y (∧ w lw rw) E) (hE→ hz x≤z) (hE→ hw y≤w) with x ≤? y
... | yes x≤y = h∧ (hE→ hw y≤w) hz (x≤y , x≤z)
... | no x≰y  = h∧ (hE→ hz x≤z) hw (lem-≤ x≰y , y≤w)
lem-mergeHeap h@(∧ x (∧ z lz rz) E) (∧ y (∧ y₁ l₁ r₁) (∧ y₂ l₂ r₂))
    hx@(hE→ hz x≤z) (h∧ h₁ h₂ (y≤y₁ , y≤y₂)) with x ≤? y
... | yes x≤y = h∧ (h∧ h₁ h₂ (y≤y₁ , y≤y₂)) hz (x≤y , x≤z)
... | no x≰y with x ≤? y₂
...     | yes x≤y₂ = h∧ (h∧ h₂ hz (x≤y₂ , x≤z)) h₁ (lem-≤ x≰y , y≤y₁)
...     | no x≰y₂  = h∧ (subst IsHeap (step-merge≥ x≰y₂) (lem-mergeHeap h (∧ y₂ l₂ r₂) hx h₂)) h₁ (y≤y₂ , y≤y₁)
lem-mergeHeap (∧ x (∧ x₁ l₁ r₁) (∧ x₂ l₂ r₂)) .E (h∧ h₁ h₂ (x≤x₁ , x≤x₂)) h[] = h∧ h₁ h₂ (x≤x₁ , x≤x₂)
lem-mergeHeap (∧ x (∧ x₁ l₁ r₁) (∧ x₂ l₂ r₂)) .(∧ n E E)
    (h∧ h₁ h₂ (x≤x₁ , x≤x₂)) (h[n] n) with x ≤? n
... | no x≰n  = hE→ (h∧ h₁ h₂ (x≤x₁ , x≤x₂)) (lem-≤ x≰n)
... | yes x≤n with n ≤? x₂
...     | yes n≤x₂ = h∧ (hE→ h₂ n≤x₂) h₁ (x≤n , x≤x₁)
...     | no n≰x₂  = h∧ (subst IsHeap (step-merge≥ n≰x₂) (lem-mergeHeap (∧ n E E) (∧ x₂ l₂ r₂) (h[n] n) h₂)) h₁ (x≤x₂ , x≤x₁)
lem-mergeHeap (∧ x (∧ x₁ l₁ r₁) (∧ x₂ l₂ r₂)) h@(∧ y E (∧ w lw rw))
    (h∧ h₁ h₂ (x≤x₁ , x≤x₂)) hy@(hE← hw y≤w) with x ≤? y
... | yes x≤y with y ≤? x₂
...     | no y≰x₂  = h∧ (subst IsHeap (step-merge≥ y≰x₂) (lem-mergeHeap h (∧ x₂ l₂ r₂) hy h₂)) h₁ (x≤x₂ , x≤x₁)
...     | yes y≤x₂ with x₂ ≤? w
...         | yes x₂≤w = h∧ (hE→ (subst IsHeap (step-merge≤ x₂≤w) (lem-mergeHeap (∧ x₂ l₂ r₂) (∧ w lw rw) h₂ hw)) y≤x₂) h₁ (x≤y , x≤x₁)
...         | no x₂≰w  = h∧ (hE→ (subst IsHeap (step-merge≥ x₂≰w) (lem-mergeHeap (∧ x₂ l₂ r₂) (∧ w lw rw) h₂ hw)) y≤w) h₁ (x≤y , x≤x₁)
lem-mergeHeap h@(∧ x (∧ x₁ l₁ r₁) (∧ x₂ l₂ r₂)) (∧ y E (∧ w lw rw))
    hx@(h∧ h₁ h₂ (x≤x₁ , x≤x₂)) (hE← hw y≤w)
    | no x≰y with x ≤? w
...     | no x≰w  = hE→ (subst IsHeap (step-merge≥ x≰w) (lem-mergeHeap h (∧ w lw rw) hx hw)) y≤w
...     | yes x≤w with w ≤? x₂
...         | yes w≤x₂ = hE→ (h∧ (subst IsHeap (step-merge≤ w≤x₂) (lem-mergeHeap (∧ w lw rw) (∧ x₂ l₂ r₂) hw h₂)) h₁ (x≤w , x≤x₁)) (lem-≤ x≰y)
...         | no w≰x₂  = hE→ (h∧ (subst IsHeap (step-merge≥ w≰x₂) (lem-mergeHeap (∧ w lw rw) (∧ x₂ l₂ r₂) hw h₂)) h₁ (x≤x₂ , x≤x₁)) (lem-≤ x≰y)
lem-mergeHeap (∧ x (∧ x₁ l₁ r₁) (∧ x₂ l₂ r₂)) h@(∧ y (∧ w lw rw) E)
    (h∧ h₁ h₂ (x≤x₁ , x≤x₂)) hy@(hE→ hw y≤w) with x ≤? y
... | no x≰y  = h∧ (h∧ h₁ h₂ (x≤x₁ , x≤x₂)) hw (lem-≤ x≰y , y≤w)
... | yes x≤y with y ≤? x₂
...     | yes y≤x₂ = h∧ (h∧ h₂ hw (y≤x₂ , y≤w)) h₁ (x≤y , x≤x₁)
...     | no y≰x₂  = h∧ (subst IsHeap (step-merge≥ y≰x₂) (lem-mergeHeap h (∧ x₂ l₂ r₂) hy h₂)) h₁ (x≤x₂ , x≤x₁)
lem-mergeHeap tx@(∧ x (∧ x₁ l₁ r₁) (∧ x₂ l₂ r₂)) ty@(∧ y (∧ z lz rz) (∧ w lw rw))
    hx@(h∧ h₁ h₂ (x≤x₁ , x≤x₂)) hy@(h∧ hz hw (y≤z , y≤w)) with x ≤? y
... | yes x≤y with y ≤? x₂
...     | no y≰x₂  = h∧ (subst IsHeap (step-merge≥ y≰x₂) (lem-mergeHeap ty (∧ x₂ l₂ r₂) hy h₂)) h₁ (x≤x₂ , x≤x₁)
...     | yes y≤x₂ with x₂ ≤? w
...         | yes x₂≤w = h∧ (h∧ (subst IsHeap (step-merge≤ x₂≤w) (lem-mergeHeap (∧ x₂ l₂ r₂) (∧ w lw rw) h₂ hw)) hz (y≤x₂ , y≤z)) h₁ (x≤y , x≤x₁)
...         | no x₂≰w  = h∧ (h∧ (subst IsHeap (step-merge≥ x₂≰w) (lem-mergeHeap (∧ x₂ l₂ r₂) (∧ w lw rw) h₂ hw)) hz (y≤w , y≤z)) h₁ (x≤y , x≤x₁)
lem-mergeHeap tx@(∧ x (∧ x₁ l₁ r₁) (∧ x₂ l₂ r₂)) ty@(∧ y (∧ z lz rz) (∧ w lw rw))
    hx@(h∧ h₁ h₂ (x≤x₁ , x≤x₂)) hy@(h∧ hz hw (y≤z , y≤w))
    | no x≰y with x ≤? w
...     | no x≰w  = h∧ (subst IsHeap (step-merge≥ x≰w) (lem-mergeHeap tx (∧ w lw rw) hx hw)) hz (y≤w , y≤z)
...     | yes x≤w with w ≤? x₂
...         | yes w≤x₂ = h∧ (h∧ (subst IsHeap (step-merge≤ w≤x₂) (lem-mergeHeap (∧ w lw rw) (∧ x₂ l₂ r₂) hw h₂)) h₁ (x≤w , x≤x₁)) hz (lem-≤ x≰y , y≤z)
...         | no w≰x₂  = h∧ (h∧ (subst IsHeap (step-merge≥ w≰x₂) (lem-mergeHeap (∧ w lw rw) (∧ x₂ l₂ r₂) hw h₂)) h₁ (x≤x₂ , x≤x₁)) hz (lem-≤ x≰y , y≤z)
