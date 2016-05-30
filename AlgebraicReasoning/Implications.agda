{-# OPTIONS --universe-polymorphism #-}

module AlgebraicReasoning.Implications where

open import Level
open import Data.Product
open import Function
open import Relation.Binary renaming (_⇒_ to _⇒′_)

import Relation.Binary.PreorderReasoning as PreR
import Relation.Binary.EqReasoning as EqR

infixr 5 _⇒_ _⇐_

_⇒_ : ∀ {i} → Set i → Set i → Set i
A ⇒ B = A → B

⇒-refl : ∀ {i} {A : Set i} → A ⇒ A
⇒-refl = id

⇒-trans : ∀ {i} {A B C : Set i} → (A ⇒ B) → (B ⇒ C) → (A ⇒ C)
⇒-trans g f = λ x → f (g x) -- flip _∘_

_⇐_ : ∀ {i} → Set i → Set i → Set i
A ⇐ B = B → A

⇐-refl : ∀ {i} {A : Set i} → A ⇐ A
⇐-refl = id

⇐-trans : ∀ {i} {A B C : Set i} → (A ⇐ B) → (B ⇐ C) → (A ⇐ C)
⇐-trans = flip ⇒-trans  -- _∘_


infixr 5 _⇔_

_⇔_ : ∀ {i} → Set i → Set i → Set i
A ⇔ B = A ⇒ B × A ⇐ B

⇔-refl : ∀ {i} {A : Set i} → A ⇔ A
⇔-refl = (id , id)

⇔-trans : ∀ {i} {A B C : Set i} → (A ⇔ B) → (B ⇔ C) → (A ⇔ C)
⇔-trans (A⇒B , A⇐B) (B⇒C , B⇐C) = (B⇒C ∘ A⇒B  , A⇐B ∘ B⇐C)

⇔-sym : ∀ {i} {A B : Set i} → (A ⇔ B) → (B ⇔ A)
⇔-sym (A⇒B , A⇐B) = A⇐B , A⇒B

⇒-antisym : ∀ {i} {A B : Set i} → (A ⇒ B) → (B ⇒ A) → (A ⇔ B)
⇒-antisym A⇒B B⇒A = A⇒B , B⇒A

⇐-antisym : ∀ {i} {A B : Set i} → (A ⇐ B) → (B ⇐ A) → (A ⇔ B)
⇐-antisym A⇐B B⇐A = B⇐A , A⇐B

⇔-isEquivalence : ∀ {i} → IsEquivalence (_⇔_ {i})
⇔-isEquivalence =
  record { refl = ⇔-refl ; sym = ⇔-sym ; trans = ⇔-trans }

⇔-Setoid : ∀ {i} → Setoid (suc i) i
⇔-Setoid {i} =
  record { Carrier = Set i ; _≈_ = _⇔_ ; isEquivalence = ⇔-isEquivalence }

⇒-refl-⇔ : ∀ {i} → (_⇔_ {i}) ⇒′ _⇒_
⇒-refl-⇔ (A⇒B , A⇐B) = A⇒B

⇒-isPreorder : ∀ {i} → IsPreorder (_⇔_ {i}) (_⇒_ {i})
⇒-isPreorder = record { isEquivalence = ⇔-isEquivalence ;
                        reflexive = ⇒-refl-⇔ ;
                        trans = ⇒-trans }

⇒-Preorder : ∀ {i} → Preorder (suc i) i i
⇒-Preorder {i} =
  record { Carrier = Set i ; _≈_ = _⇔_ ; _∼_ = _⇒_ ; isPreorder = ⇒-isPreorder }

⇒-isPartialOrder : ∀ {i} → IsPartialOrder (_⇔_ {i}) (_⇒_ {i})
⇒-isPartialOrder =
  record { isPreorder = ⇒-isPreorder ; antisym = ⇒-antisym }

⇒-Poset : ∀ {i} → Poset (suc i) i i
⇒-Poset {i} = record { Carrier = Set i ;
                       _≈_ = _⇔_ ;
                       _≤_ = _⇒_ ;
                       isPartialOrder = ⇒-isPartialOrder }

⇐-refl-⇔ : ∀ {i} → (_⇔_ {i}) ⇒′ _⇐_
⇐-refl-⇔ (A⇒B , A⇐B) = A⇐B

⇐-isPreorder : ∀ {i} → IsPreorder (_⇔_ {i}) (_⇐_ {i})
⇐-isPreorder = record { isEquivalence = ⇔-isEquivalence ;
                        reflexive = ⇐-refl-⇔ ;
                        trans = ⇐-trans }

⇐-Preorder : ∀ {i} → Preorder (suc i) i i
⇐-Preorder {i} =
  record { Carrier = Set i ; _≈_ = _⇔_ ; _∼_ = _⇐_ ; isPreorder = ⇐-isPreorder }

⇐-isPartialOrder : ∀ {i} → IsPartialOrder (_⇔_ {i}) (_⇐_ {i})
⇐-isPartialOrder =
  record { isPreorder = ⇐-isPreorder ; antisym = ⇐-antisym }

⇐-Poset : ∀ {i} → Poset (suc i) i i
⇐-Poset {i} = record { Carrier = Set i ;
                       _≈_ = _⇔_ ;
                       _≤_ = _⇐_ ;
                       isPartialOrder = ⇐-isPartialOrder }

module ⇒-reasoning {i} = PreR (⇒-Preorder {i})
  renaming (begin_ to ⇒-begin_ ; _∼⟨_⟩_ to _⇒⟨_⟩_ ; _∎ to _⇒∎)
open ⇒-reasoning public hiding (_IsRelatedTo_; _≈⟨_⟩_; _≈⟨⟩_)

module ⇐-reasoning {i} = PreR (⇐-Preorder {i})
  renaming (begin_ to ⇐-begin_ ; _∼⟨_⟩_ to _⇐⟨_⟩_ ; _∎ to _⇐∎)
open ⇐-reasoning public hiding (_IsRelatedTo_; _≈⟨_⟩_; _≈⟨⟩_)

module ⇔-reasoning {i} = EqR (⇔-Setoid {i})
  renaming (begin_ to ⇔-begin_ ; _≈⟨_⟩_ to _⇔⟨_⟩_ ; _∎ to _⇔∎)
open ⇔-reasoning public hiding (_IsRelatedTo_ ; _≡⟨_⟩_; _≡⟨⟩_)
