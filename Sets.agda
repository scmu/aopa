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

open import Data.Sum     using (_⊎_)
open import Data.Product using (_×_)
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

-- Primitive Sets

∅ : {A : Set} → ℙ A
∅ _ = ⊥

singleton : ∀ {ℓ} {A : Set ℓ} → A → ℙ A
singleton a = λ b → a ≡ b

comap : ∀ {ℓ} {A B : Set ℓ} → (A → B) → ℙ B → ℙ A
comap f s = λ a → s (f a)
