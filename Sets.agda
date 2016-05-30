{-# OPTIONS --universe-polymorphism #-}

module Sets where

open import Data.Empty   using (⊥)
open import Relation.Unary public 
  using (_∪_; _∩_)
  renaming (_⊆′_ to _⊆_;
            _⊇′_ to _⊇_)
open import Relation.Binary.PropositionalEquality 
  public -- re-export these (often used)
                          using  (_≡_; refl; sym; trans; subst; cong)
open import Relation.Binary
open import Data.Sum     using (_⊎_)
open import Data.Product using (_×_; _,_)
open import Level

ℙ : ∀ {ℓ : Level} → Set ℓ → Set (suc ℓ)
ℙ {ℓ} A = A → Set ℓ

⊆-refl : ∀ {ℓ} {A : Set ℓ} → {r : ℙ A} → r ⊆ r
⊆-refl _ ra = ra

⊆-trans : ∀ {ℓ} {A : Set ℓ} → {r s t : ℙ A} →
            r ⊆ s → s ⊆ t → r ⊆ t
⊆-trans r⊆s s⊆t a a∈r = s⊆t a (r⊆s a a∈r)


⊇-refl : ∀ {ℓ} {A : Set ℓ} → {r : ℙ A} → r ⊇ r
⊇-refl = ⊆-refl

⊇-trans : ∀ {ℓ} {A : Set ℓ} → {r s t : ℙ A} →
            r ⊇ s → s ⊇ t → r ⊇ t
⊇-trans r⊇s s⊇t = ⊆-trans s⊇t r⊇s


infix 4 _≗_

_≗_ : ∀ {ℓ} {A : Set ℓ} → ℙ A → ℙ A → Set ℓ
r ≗ s = r ⊆ s × s ⊆ r

≗-refl : ∀ {ℓ} {A : Set ℓ} {r : ℙ A} → r ≗ r
≗-refl = ⊆-refl , ⊆-refl

≗-sym : ∀ {ℓ} {A : Set ℓ} {r s : ℙ A}
      → r ≗ s → s ≗ r
≗-sym (r⊆s , s⊆r) = s⊆r , r⊆s

≗-trans : ∀ {ℓ} {A : Set ℓ} {r s t : ℙ A}
        → r ≗ s → s ≗ t → r ≗ t
≗-trans (r⊆s , s⊆r) (s⊆t , t⊆s) = ⊆-trans r⊆s s⊆t , ⊇-trans s⊆r t⊆s

⊆-antisym : ∀ {ℓ} {A : Set ℓ} {r s : ℙ A}
          → r ⊆ s → s ⊆ r → r ≗ s
⊆-antisym r⊆s s⊆r = r⊆s , s⊆r

⊇-antisym : ∀ {ℓ} {A : Set ℓ} {r s : ℙ A}
          → r ⊇ s → s ⊇ r → r ≗ s
⊇-antisym r⊇s s⊇r = s⊇r , r⊇s


≗-isEquivalence : ∀ {ℓ A} → IsEquivalence (_≗_ {ℓ} {A})
≗-isEquivalence =
  record { refl = ≗-refl ; sym = ≗-sym ; trans = ≗-trans }

≗-Setoid : ∀ {ℓ} → Set ℓ → Setoid (suc ℓ) ℓ
≗-Setoid A =
  record { Carrier = ℙ A ; _≈_ = _≗_ ; isEquivalence = ≗-isEquivalence }

⊆-refl-≗ : ∀ {ℓ A} → (_≗_ {ℓ} {A}) ⇒ _⊆_
⊆-refl-≗ (r⊆s , s⊆r) = r⊆s

⊆-isPreorder : ∀ {ℓ A} → IsPreorder (_≗_ {ℓ} {A}) (_⊆_ {ℓ} {A})
⊆-isPreorder = record { isEquivalence = ≗-isEquivalence ;
                        reflexive = ⊆-refl-≗ ;
                        trans = ⊆-trans }

⊆-Preorder : ∀ {ℓ} → Set ℓ → Preorder (suc ℓ) ℓ ℓ
⊆-Preorder A =
  record { Carrier = ℙ A ; _≈_ = _≗_ ; _∼_ = _⊆_ ; isPreorder = ⊆-isPreorder }

⊆-isPartialOrder : ∀ {ℓ A} → IsPartialOrder (_≗_ {ℓ} {A}) (_⊆_ {ℓ} {A})
⊆-isPartialOrder = record { isPreorder = ⊆-isPreorder ;
                            antisym = ⊆-antisym }

⊆-Poset : ∀ {ℓ} → Set ℓ → Poset (suc ℓ) ℓ ℓ
⊆-Poset A = record { Carrier = ℙ A ;
                     _≈_ = _≗_ ;
                     _≤_ = _⊆_ ;
                     isPartialOrder = ⊆-isPartialOrder }

⊇-refl-≗ : ∀ {ℓ A} → (_≗_ {ℓ} {A}) ⇒ _⊇_
⊇-refl-≗ (r⊆s , s⊆r) = s⊆r

⊇-isPreorder : ∀ {ℓ A} → IsPreorder (_≗_ {ℓ} {A}) (_⊇_ {ℓ} {A})
⊇-isPreorder = record { isEquivalence = ≗-isEquivalence ;
                        reflexive = ⊇-refl-≗ ;
                        trans = ⊇-trans }

⊇-Preorder : ∀ {ℓ} → Set ℓ → Preorder (suc ℓ) ℓ ℓ
⊇-Preorder A =
  record { Carrier = ℙ A ; _≈_ = _≗_ ; _∼_ = _⊇_ ; isPreorder = ⊇-isPreorder }

⊇-isPartialOrder : ∀ {ℓ A} → IsPartialOrder (_≗_ {ℓ} {A}) (_⊇_ {ℓ} {A})
⊇-isPartialOrder = record { isPreorder = ⊇-isPreorder ;
                            antisym = ⊇-antisym }

⊇-Poset : ∀ {ℓ} → Set ℓ → Poset (suc ℓ) ℓ ℓ
⊇-Poset A = record { Carrier = ℙ A ;
                     _≈_ = _≗_ ;
                     _≤_ = _⊇_ ;
                     isPartialOrder = ⊇-isPartialOrder }

-- Primitive Sets

∅ : {A : Set} → ℙ A
∅ _ = ⊥

singleton : ∀ {ℓ} {A : Set ℓ} → A → ℙ A
singleton a = λ b → a ≡ b

comap : ∀ {ℓ} {A B : Set ℓ} → (A → B) → ℙ B → ℙ A
comap f s = λ a → s (f a)
