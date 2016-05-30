{-# OPTIONS --universe-polymorphism #-}

module AlgebraicReasoning.Equivalence where

open import Level
open import Data.Product
open import Relation.Binary hiding (_⇒_)
open import Function
open import AlgebraicReasoning.Implications

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
