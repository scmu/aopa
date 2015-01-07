{-# OPTIONS --type-in-type #-}
module Sets where

open import Data.Empty   using (⊥)
open import Relation.Binary.PropositionalEquality 
  public -- re-export these (often used)
                          using  (_≡_)
                          renaming (refl  to ≡-refl; 
                                    sym   to ≡-sym; 
                                    trans to ≡-trans; 
                                    subst to ≡-subst; 
                                    cong  to ≡-cong)
open import Data.Sum     using (_⊎_)
open import Data.Product using (_×_)

ℙ : Set -> Set1
ℙ A = A -> Set

infixr 3 _∩_
infixr 2 _∪_

_∪_ : {A : Set} -> ℙ A -> ℙ A -> ℙ A
r ∪ s = \a -> r a ⊎ s a

_∩_ : {A : Set} -> ℙ A -> ℙ A -> ℙ A
r ∩ s = \a -> r a × s a

-- set inclusion

infixr 2 _⊆_ _⊇_

-- ⊆ is a partial order

_⊆_ : {A : Set} -> ℙ A -> ℙ A -> Set
r ⊆ s = forall a -> r a -> s a

⊆-refl : {A : Set} -> {r : ℙ A} -> r ⊆ r
⊆-refl _ ra = ra

⊆-trans : {A : Set} -> {r s t : ℙ A} ->
            r ⊆ s -> s ⊆ t -> r ⊆ t
⊆-trans r⊆s s⊆t a a∈r = s⊆t a (r⊆s a a∈r)

_⊇_ : {A : Set} -> ℙ A -> ℙ A -> Set
r ⊇ s = s ⊆ r

⊇-refl : {A : Set} -> {r : ℙ A} -> r ⊇ r
⊇-refl = ⊆-refl

⊇-trans : {A : Set} -> {r s t : ℙ A} ->
            r ⊇ s -> s ⊇ t -> r ⊇ t
⊇-trans r⊇s s⊇t = ⊆-trans s⊇t r⊇s

-- Primitive Sets

∅ : {A : Set} -> ℙ A
∅ _ = ⊥

singleton : {A : Set} -> A -> ℙ A
singleton a = \b -> a ≡ b

comap : {A B : Set} -> (A -> B) -> ℙ B -> ℙ A
comap f s = \a -> s (f a)
