{-# OPTIONS --universe-polymorphism #-}

module AlgebraicReasoning.Equivalence where

open import Level
open import Data.Product
open import Relation.Binary hiding (_⇒_)
open import Function
open import AlgebraicReasoning.Implications 

import AlgebraicReasoning.MonoPreorderReasoning as MPR

infixr 5 _⇔_ 


_⇔_ : ∀ {i} → Set i → Set i → Set i
A ⇔ B = A ⇒ B × A ⇐ B

⇔-refl : ∀ {i} {A : Set i} → A ⇔ A
⇔-refl = (id , id) 

⇔-trans : ∀ {i} {A B C : Set i} → (A ⇔ B) → (B ⇔ C) → (A ⇔ C)
⇔-trans (A⇒B , A⇐B) (B⇒C , B⇐C) = (B⇒C ∘ A⇒B  , A⇐B ∘ B⇐C) 

module ⇔-reasoning {i : Level} = MPR.Mono {suc i} {i} _⇔_ ⇔-refl ⇔-trans
   renaming (begin_ to ⇔-begin_ ; _∼⟨_⟩_ to _⇔⟨_⟩_ ; _∎ to _⇔∎)
open ⇔-reasoning public hiding (byDef) 

indirect-equality : 
  ∀ {i j k} {A : Set i} (_≈_ : Rel A j) (_≤_ : Rel A k)
  → (∀ {x} → x ≤ x)
  → Antisymmetric _≈_ _≤_
  → {x y : A}
  → (∀ {z} → (z ≤ x ⇔ z ≤ y)) → x ≈ y
indirect-equality _≈_ _≤_ reflx antisym {x} {y} inde with
    proj₁ (inde {x}) (reflx {x}) | proj₂ (inde {y}) (reflx {y}) 
... | x≤y | y≤x = antisym x≤y y≤x

indirect-equality' :
  ∀ {i j k} → (poset : Poset i j k)
  → let open Poset poset
    in ∀ {x y} → (∀ {z} → (z ≤ x) ⇔ (z ≤ y)) → (x ≈ y)
indirect-equality' poset = 
    indirect-equality _≈_ _≤_ (reflexive (IsEquivalence.refl isEquivalence)) antisym
  where open Poset poset
