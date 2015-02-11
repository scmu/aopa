module Examples.Optimisation.ActivitySelection.Spec where

import Data.Nat
import Data.Nat.Properties as NatProp
open import Function            using (id; _∘_; _$_)
open import Data.List           using (List; _∷_; []; length; foldr)
open import Data.Product        using (Σ; _,_; _×_; proj₁; proj₂; uncurry; ∃)
open import Data.Sum            using (_⊎_; inj₁; inj₂)
open import Relation.Binary  using (module DecTotalOrder)
open import Relation.Binary.PropositionalEquality
                             using (_≡_; inspect; _with-≡_; 
                                    refl; cong; sym; subst; trans)
open import Sets                using (ℙ; ⊆-refl; _⊇_; _⊆_)
open import Relations        using (_←_; _○_; fun;  _˘; _⊔_; _⊑_; _⊒_; _≑_; 
                                       _⨉_; idR; ⊑-refl; ⊑-trans; _⊓_; _₁∘_; ℰ; Λ)
open import Relations.Coreflexive 
                                using (_¿)
open import Relations.Minimum   using (max)
open import Data.List.Utilities using (All; check)
open import Data.List.Fold      using (foldR; nil; cons)

abstract

  open Data.Nat using (ℕ; _<_; _≤_; _≤?_)
  Activity : Set
  Activity = Σ (ℕ × ℕ) (λ p → proj₁ p < proj₂ p)

  Act = Activity -- Abbreviation

  start : Act → ℕ
  start = proj₁ ∘ proj₁

  finish : Act → ℕ
  finish = proj₂ ∘ proj₁

  start<finish : {a : Act} → start a < finish a
  start<finish {a} = proj₂ a

-- Utility function
outr : {A B : Set} → B ← (A × B)
outr = fun proj₂
  
disjoint : Act ← Act
disjoint a x = finish x ≤ start a  ⊎  finish a ≤ start x

  -- Check that a is disjoint from all xs
compatible : ℙ (Act × List Act)
compatible (a , xs ) = All (disjoint a) xs

mutex : List Act ← List Act
mutex = check (compatible ¿)

lessfin : Act ← Act
lessfin a x = finish x ≤ finish a

fin-ubound : ℙ (Act × List Act)
fin-ubound (a , xs) = All (lessfin a) xs

fin-ordered : List Act ← List Act
fin-ordered = check (fin-ubound ¿)

subseq : {A : Set} → List A ← List A
subseq = foldR (outr ⊔ cons) nil

module SimpleOrderings where
  open Data.Nat    using (ℕ; zero; suc; _≤_; _<_; 
                          decTotalOrder) -- hiding (_⊔_; _⊓_)
  open NatProp using (≤-step)
  ≤-refl : {x : ℕ} → x ≤ x
  ≤-refl = DecTotalOrder.refl decTotalOrder

  ≤-trans : {x y z : ℕ} → x ≤ y → y ≤ z → x ≤ z
  ≤-trans = DecTotalOrder.trans decTotalOrder

  x<y⇒x≤y : {x y : ℕ} → x < y → x ≤ y
  x<y⇒x≤y x<y = ≤-trans (≤-step ≤-refl) x<y

  _≤ℓ_ : {A : Set} → List A ← List A
  xs ≤ℓ ys = length xs ≤ length ys

  _<ℓ_ : {A : Set} → List A ← List A
  xs <ℓ ys = length xs < length ys

  <ℓ⊑≤ℓ : {A : Set} → _<ℓ_ {A} ⊑ _≤ℓ_
  <ℓ⊑≤ℓ xs ys = x<y⇒x≤y

  _≡ℓ_ : {A : Set} → List A ← List A
  xs ≡ℓ ys = length xs ≡ length ys

  ≡ℓ⊑≤ℓ : {A : Set} → _≡ℓ_ {A} ⊑ _≤ℓ_
  ≡ℓ⊑≤ℓ xs ys len-ys≡len-xs = subst (λ z → length xs ≤ z) len-ys≡len-xs ≤-refl

open SimpleOrderings using (_≤ℓ_; _≡ℓ_; ≤-trans; x<y⇒x≤y)

act-sel-spec : List Act ← List Act
act-sel-spec =  (max _≤ℓ_ ₁∘ Λ(mutex ○ subseq)) ○ fin-ordered