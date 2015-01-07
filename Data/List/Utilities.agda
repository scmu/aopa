module Data.List.Utilities where

open import Data.List using (List; []; _∷_)
open import Data.Unit
open import Data.Product

open import Sets using (⊆-refl)
open import Relations
open import Relations.Product
open import Data.List.Fold using (foldR; nil; cons; corefl-foldR)


All : {A : Set} → (A → Set) → (List A → Set)
All p []       = ⊤
All p (a ∷ as) = p a × All p as

check : {A : Set} → 
   ((A × List A) ← (A × List A)) → (List A ← List A)
check {A} C = foldR (cons ○ C) nil

-- Simple corollary of corefl-foldR

corefl-check : {A : Set} {C : (A × List A) ← (A × List A)} →
  C ⊑ idR  →  check C ⊑ idR
corefl-check C⊑idR = corefl-foldR C⊑idR ⊆-refl
