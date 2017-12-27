module HeapProp.HeapSorted where

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
open import HeapProp.HeapMerge
open import Induction.WellFounded as WF
open import Induction.Nat
import Level
open import Relation.Binary

open ≡-Reasoning

mergeSize : {x y : Heap ℕ} → heapSize (mergeHeap x y) ≡ heapSize x + heapSize y
mergeSize {E} {y} = refl
mergeSize {∧ x l₁ r₁} {E} = cong suc (sym (+-identityʳ (heapSize l₁ + heapSize r₁)))
mergeSize {∧ x l₁ r₁} {∧ y l₂ r₂} with x ≤? y
... | yes x≤y = cong suc (
            heapSize (mergeHeap (∧ y l₂ r₂) r₁) + heapSize l₁
        ≡⟨ cong (λ e → e + heapSize l₁) (mergeSize {∧ y l₂ r₂} {r₁}) ⟩
            suc (heapSize l₂ + heapSize r₂ + heapSize r₁ + heapSize l₁)
        ≡⟨ cong suc (+-assoc (heapSize l₂ + heapSize r₂) (heapSize r₁) (heapSize l₁)) ⟩
            suc (heapSize l₂ + heapSize r₂ + (heapSize r₁ + heapSize l₁))
        ≡⟨ cong suc (+-comm (heapSize l₂ + heapSize r₂) (heapSize r₁ + heapSize l₁)) ⟩
            suc (heapSize r₁ + heapSize l₁ + (heapSize l₂ + heapSize r₂))
        ≡⟨ cong (λ e → suc (e + (heapSize l₂ + heapSize r₂))) (+-comm (heapSize r₁) (heapSize l₁)) ⟩
            suc (heapSize l₁ + heapSize r₁ + (heapSize l₂ + heapSize r₂))
        ≡⟨ sym (+-suc (heapSize l₁ + heapSize r₁) (heapSize l₂ + heapSize r₂)) ⟩
            heapSize l₁ + heapSize r₁ + suc (heapSize l₂ + heapSize r₂)
        ∎)
... | no x≰y  = cong suc (
            heapSize (mergeHeap (∧ x l₁ r₁) r₂) + heapSize l₂
        ≡⟨ cong (λ e → e + heapSize l₂) (mergeSize {∧ x l₁ r₁} {r₂}) ⟩
            suc (heapSize l₁ + heapSize r₁ + heapSize r₂ + heapSize l₂)
        ≡⟨ cong suc (+-assoc (heapSize l₁ + heapSize r₁) (heapSize r₂) (heapSize l₂)) ⟩
            suc (heapSize l₁ + heapSize r₁ + (heapSize r₂ + heapSize l₂))
        ≡⟨ cong (λ e → suc (heapSize l₁ + heapSize r₁ + e)) (+-comm (heapSize r₂) (heapSize l₂)) ⟩
            suc (heapSize l₁ + heapSize r₁ + (heapSize l₂ + heapSize r₂))
        ≡⟨ sym (+-suc (heapSize l₁ + heapSize r₁) (heapSize l₂ + heapSize r₂)) ⟩
            heapSize l₁ + heapSize r₁ + suc (heapSize l₂ + heapSize r₂)
        ∎)

mergeSize< : {x : ℕ}{l r : Heap ℕ} → heapSize (mergeHeap l r) < heapSize (∧ x l r)
mergeSize< {x}{l}{r} rewrite mergeSize {l}{r} = s≤s ≤-refl

_⟪_ : {A : Set} → Rel (Heap A) Level.zero
_⟪_ = _<_ on heapSize

⟪-well-founded : {A : Set} → Well-founded (_⟪_ {A})
⟪-well-founded = Inverse-image.well-founded heapSize <-well-founded

module _ {ℓ} {A : Set} where
  open WF.All (⟪-well-founded {A}) ℓ public
    renaming ( wfRec-builder to ⟪-rec-builder
             ; wfRec to ⟪-rec
             )

P : ∀ x → Set
P x = IsHeap x → Sorted (fromHeap (heapSize x) x)

step : ∀ x → (∀ y → y ⟪ x → P y) → P x
step .E rec h[] = s[]
step .(∧ n E E) rec (h[n] n) = s[n]
step (∧ x E (∧ y l r)) rec (hE← h x≤y) = s∷ x≤y (rec (∧ y l r) (s≤s (s≤s ≤-refl)) h)
step (∧ x (∧ y l r) E) rec (hE→ h x≤y) = s∷ x≤y (subst Sorted (cong
    (λ e → y ∷ fromHeap e (mergeHeap l r)) (sym (+-identityʳ (heapSize l + heapSize r))))
    (rec (∧ y l r) (s≤s (s≤s (m≤m+n (heapSize l + heapSize r) zero))) h))
step (∧ x t₁@(∧ x₁ l₁ r₁) t₂@(∧ x₂ l₂ r₂)) rec (h∧ h₁ h₂ (x≤x₁ , x≤x₂))
    with x₁ ≤? x₂
... | yes x₁≤x₂ = s∷ x≤x₁ (subst Sorted (
            fromHeap
            (heapSize (mergeHeap (∧ x₁ l₁ r₁) (∧ x₂ l₂ r₂)))
            (mergeHeap (∧ x₁ l₁ r₁) (∧ x₂ l₂ r₂))
        ≡⟨ cong₂ (λ e₁ e₂ → fromHeap (heapSize e₁) e₂) (step-merge≤ x₁≤x₂) (step-merge≤ x₁≤x₂) ⟩
            x₁ ∷ fromHeap
            (heapSize (mergeHeap (∧ x₂ l₂ r₂) r₁) + heapSize l₁)
            (mergeHeap (mergeHeap (∧ x₂ l₂ r₂) r₁) l₁)
        ≡⟨ cong
            (λ e → x₁ ∷ fromHeap e (mergeHeap (mergeHeap (∧ x₂ l₂ r₂) r₁) l₁))
            (   (heapSize (mergeHeap (∧ x₂ l₂ r₂) r₁) + heapSize l₁)
            ≡⟨ cong (λ e → e + heapSize l₁) (mergeSize {t₂}{r₁}) ⟩
                suc (heapSize l₂ + heapSize r₂ + heapSize r₁ + heapSize l₁)
            ≡⟨ cong suc (+-assoc (heapSize l₂ + heapSize r₂) (heapSize r₁) (heapSize l₁)) ⟩
                suc (heapSize l₂ + heapSize r₂ + (heapSize r₁ + heapSize l₁))
            ≡⟨ cong (λ e → suc (heapSize l₂ + heapSize r₂ + e)) (+-comm (heapSize r₁) (heapSize l₁)) ⟩
                suc (heapSize l₂ + heapSize r₂ + (heapSize l₁ + heapSize r₁))
            ≡⟨ cong suc (+-comm (heapSize l₂ + heapSize r₂) (heapSize l₁ + heapSize r₁)) ⟩
                suc ((heapSize l₁ + heapSize r₁) + (heapSize l₂ + heapSize r₂))
            ≡⟨ sym (+-suc (heapSize l₁ + heapSize r₁) (heapSize l₂ + heapSize r₂)) ⟩
                heapSize l₁ + heapSize r₁ + suc (heapSize l₂ + heapSize r₂)
            ∎) ⟩
            x₁ ∷ fromHeap (heapSize l₁ + heapSize r₁ + suc (heapSize l₂ + heapSize r₂))
            (mergeHeap (mergeHeap (∧ x₂ l₂ r₂) r₁) l₁)
        ∎) (rec (mergeHeap t₁ t₂) (mergeSize< {x}{t₁}{t₂}) (lem-mergeHeap t₁ t₂ h₁ h₂)))
... | no x₁≰x₂  = s∷ x≤x₂ (subst Sorted (
            fromHeap
            (heapSize (mergeHeap (∧ x₁ l₁ r₁) (∧ x₂ l₂ r₂)))
            (mergeHeap (∧ x₁ l₁ r₁) (∧ x₂ l₂ r₂))
        ≡⟨ cong₂ (λ e₁ e₂ → fromHeap (heapSize e₁) e₂) (step-merge≥ x₁≰x₂) (step-merge≥ x₁≰x₂) ⟩
            x₂ ∷ fromHeap
            (heapSize (mergeHeap t₁ r₂) + heapSize l₂)
            (mergeHeap (mergeHeap t₁ r₂) l₂)
        ≡⟨ cong (λ e → x₂ ∷ fromHeap e (mergeHeap (mergeHeap t₁ r₂) l₂)) (
                heapSize (mergeHeap t₁ r₂) + heapSize l₂
            ≡⟨ cong (λ e → e + heapSize l₂) (mergeSize {t₁}{r₂}) ⟩
                suc (heapSize l₁ + heapSize r₁ + heapSize r₂ + heapSize l₂)
            ≡⟨ cong suc (+-assoc (heapSize l₁ + heapSize r₁) (heapSize r₂) (heapSize l₂)) ⟩
                suc (heapSize l₁ + heapSize r₁ + (heapSize r₂ + heapSize l₂))
            ≡⟨ cong (λ e → suc (heapSize l₁ + heapSize r₁ + e)) (+-comm (heapSize r₂) (heapSize l₂)) ⟩
                suc (heapSize l₁ + heapSize r₁ + (heapSize l₂ + heapSize r₂))
            ≡⟨ sym (+-suc (heapSize l₁ + heapSize r₁) (heapSize l₂ + heapSize r₂)) ⟩
                heapSize l₁ + heapSize r₁ + suc (heapSize l₂ + heapSize r₂)
            ∎) ⟩
            x₂ ∷ fromHeap
            (heapSize l₁ + heapSize r₁ + suc (heapSize l₂ + heapSize r₂))
            (mergeHeap (mergeHeap (∧ x₁ l₁ r₁) r₂) l₂)
        ∎)(rec (mergeHeap t₁ t₂) (mergeSize< {x}{t₁}{t₂}) (lem-mergeHeap t₁ t₂ h₁ h₂)))

lem-fromHeap : (x : Heap ℕ) → IsHeap x → Sorted (fromHeap (heapSize x) x)
lem-fromHeap x h = ⟪-rec P step x h

hSorted : (xs : List ℕ) → Sorted (hsort xs)
hSorted xs = lem-fromHeap (makeHeap xs) (lem-makeHeap xs)
