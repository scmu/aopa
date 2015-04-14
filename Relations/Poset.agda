{-# OPTIONS --universe-polymorphism #-}

module Relations.Poset where

open import Level renaming (_⊔_ to _⊔ℓ_)
open import Relation.Binary
open import Data.Product

open import Relations

≑-isEquivalence : ∀ {i j k A B} → IsEquivalence (_≑_ {i} {j} {k} {A} {B})
≑-isEquivalence = 
  record { refl = ≑-refl ; sym = ≑-sym ; trans = ≑-trans }

⊑-refl-≑ :  ∀ {i j k A B} → (_≑_ {i} {j} {k} {A} {B}) ⇒ _⊑_
⊑-refl-≑ (R⊑S , S⊑R) = R⊑S

⊑-isPreorder :  ∀ {i j k A B} 
                → IsPreorder (_≑_ {i} {j} {k} {A} {B}) (_⊑_ {i} {j} {k} {A} {B})
⊑-isPreorder = record { isEquivalence = ≑-isEquivalence ; 
                        reflexive     = ⊑-refl-≑ ; 
                        trans         = ⊑-trans }

⊑-Preorder : ∀ {i j k} → Set i → Set j 
             → Preorder (suc k ⊔ℓ (j ⊔ℓ i)) (k ⊔ℓ (j ⊔ℓ i)) (k ⊔ℓ (j ⊔ℓ i))
⊑-Preorder {k = k} A B = 
  record { Carrier = A ← B ⊣ k ; _≈_ = _≑_ ; _∼_ = _⊑_ ; isPreorder = ⊑-isPreorder }

⊑-isPartialOrder : ∀ {i j k A B} 
                   → IsPartialOrder (_≑_ {i} {j} {k} {A} {B}) (_⊑_ {i} {j} {k} {A} {B})
⊑-isPartialOrder = record { isPreorder = ⊑-isPreorder ; 
                            antisym    = ⊑-antisym }

⊑-Poset : ∀ {i j k} → Set i → Set j 
                 → Poset (suc k ⊔ℓ (j ⊔ℓ i)) (k ⊔ℓ (j ⊔ℓ i)) (k ⊔ℓ (j ⊔ℓ i))
⊑-Poset {k = k} A B = record { Carrier = A ← B ⊣ k ; 
                               _≈_ = _≑_ ; 
                               _≤_ = _⊑_ ; 
                               isPartialOrder = ⊑-isPartialOrder }

⊒-refl-≑ :  ∀ {i j k A B} → (_≑_ {i} {j} {k} {A} {B}) ⇒ _⊒_
⊒-refl-≑ (R⊑S , S⊑R) = S⊑R

⊒-isPreorder :  ∀ {i j k A B} 
                → IsPreorder (_≑_ {i} {j} {k} {A} {B}) (_⊒_ {i} {j} {k} {A} {B})
⊒-isPreorder = record { isEquivalence = ≑-isEquivalence ; 
                        reflexive     = ⊒-refl-≑ ; 
                        trans         = ⊒-trans }

⊒-Preorder : ∀ {i j k} → Set i → Set j 
             → Preorder (suc k ⊔ℓ (j ⊔ℓ i)) (k ⊔ℓ (j ⊔ℓ i)) (k ⊔ℓ (j ⊔ℓ i))
⊒-Preorder {k = k} A B = 
  record { Carrier = A ← B ⊣ k ; _≈_ = _≑_ ; _∼_ = _⊒_ ; isPreorder = ⊒-isPreorder }

⊒-isPartialOrder : ∀ {i j k A B} 
                   → IsPartialOrder (_≑_ {i} {j} {k} {A} {B}) (_⊒_ {i} {j} {k} {A} {B})
⊒-isPartialOrder = record { isPreorder = ⊒-isPreorder ; 
                            antisym    = ⊒-antisym }

⊒-Poset : ∀ {i j k} → Set i → Set j 
                 → Poset (suc k ⊔ℓ (j ⊔ℓ i)) (k ⊔ℓ (j ⊔ℓ i)) (k ⊔ℓ (j ⊔ℓ i))
⊒-Poset {k = k} A B = record { Carrier = A ← B ⊣ k ; 
                               _≈_ = _≑_ ; 
                               _≤_ = _⊒_ ; 
                               isPartialOrder = ⊒-isPartialOrder }
