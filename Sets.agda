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
{-                          renaming (refl  to ≡-refl; 
                                    sym   to ≡-sym; 
                                    trans to ≡-trans; 
                                    subst to ≡-subst; 
                                    cong  to ≡-cong) -}
open import Data.Sum     using (_⊎_)
open import Data.Product using (_×_)
open import Level

ℙ : ∀ {ℓ : Level} → Set ℓ → Set (suc ℓ)
ℙ {ℓ} A = A → Set ℓ

{-
ℙ₁ : Set1 → Set1
ℙ₁ A = A → Set
-}
{-
infixr 3 _∩_
infixr 2 _∪_

_∪_ : {A : Set} → ℙ A → ℙ A → ℙ A
r ∪ s = λ a → r a ⊎ s a

_∩_ : {A : Set} → ℙ A → ℙ A → ℙ A
r ∩ s = λ a → r a × s a

-- set inclusion

infixr 2 _⊆_ _⊇_

-- ⊆ is a partial order

_⊆_ : {A : Set} → ℙ A → ℙ A → Set
r ⊆ s = ∀ a → r a → s a
-}

⊆-refl : ∀ {ℓ} {A : Set ℓ} → {r : ℙ A} → r ⊆ r
⊆-refl _ ra = ra

⊆-trans : ∀ {ℓ} {A : Set ℓ} → {r s t : ℙ A} →
            r ⊆ s → s ⊆ t → r ⊆ t
⊆-trans r⊆s s⊆t a a∈r = s⊆t a (r⊆s a a∈r)

{-
_⊇_ : {A : Set} → ℙ A → ℙ A → Set
r ⊇ s = s ⊆ r
-}

⊇-refl : ∀ {ℓ} {A : Set ℓ} → {r : ℙ A} → r ⊇ r
⊇-refl = ⊆-refl

⊇-trans : ∀ {ℓ} {A : Set ℓ} → {r s t : ℙ A} →
            r ⊇ s → s ⊇ t → r ⊇ t
⊇-trans r⊇s s⊇t = ⊆-trans s⊇t r⊇s

{-
_₁⊆_ : {A : Set1} → ℙ₁ A → ℙ₁ A → Set1
r ₁⊆ s = ∀ a → r a → s a

₁⊆-refl : {A : Set1} → {r : ℙ₁ A} → r ₁⊆ r
₁⊆-refl _ ra = ra

₁⊆-trans : {A : Set1} → {r s t : ℙ₁ A} →
            r ₁⊆ s → s ₁⊆ t → r ₁⊆ t
₁⊆-trans r⊆s s⊆t a a∈r = s⊆t a (r⊆s a a∈r)

_₁⊇_ : {A : Set1} → ℙ₁ A → ℙ₁ A → Set1
r ₁⊇ s = s ₁⊆ r
-}
-- Primitive Sets

∅ : {A : Set} → ℙ A
∅ _ = ⊥

singleton : ∀ {ℓ} {A : Set ℓ} → A → ℙ A
singleton a = λ b → a ≡ b

comap : ∀ {ℓ} {A B : Set ℓ} → (A → B) → ℙ B → ℙ A
comap f s = λ a → s (f a)

{-
-- How close to a monad is ℙ?
kleisli : {A B C : Set} → (B → ℙ C) → (A → ℙ B) → (A → ℙ C)
kleisli f g a = {! !}

ℙ₁ : Set1 → Set2
ℙ₁ A = A → Set1

join : {A : Set} → ℙ₁ (ℙ A) → ℙ A
join ppa = λ a → ∃ (λ pa → pa a ×₁ ppa pa)

-}
