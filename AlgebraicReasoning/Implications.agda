{-# OPTIONS --universe-polymorphism #-}

module AlgebraicReasoning.Implications where

open import Level
open import Data.Product
open import Function

import AlgebraicReasoning.MonoPreorderReasoning as MPR

infixr 5 _⇒_ _⇐_

_⇒_ : ∀ {i} → Set i → Set i → Set i
A ⇒ B = A → B

⇒-refl : ∀ {i} {A : Set i} → A ⇒ A
⇒-refl = id

⇒-trans : ∀ {i} {A B C : Set i} → (A ⇒ B) → (B ⇒ C) → (A ⇒ C)
⇒-trans g f = λ x → f (g x) -- flip _∘_

module ⇒-reasoning {i : Level} = MPR.Mono {suc i} {i}  _⇒_ ⇒-refl ⇒-trans
   renaming (begin_ to ⇒-begin_ ; _∼⟨_⟩_ to _⇒⟨_⟩_ ; _∎ to _⇒∎) 
open ⇒-reasoning public hiding (byDef) 

_⇐_ : ∀ {i} → Set i → Set i → Set i
A ⇐ B = B → A

⇐-refl : ∀ {i} {A : Set i} → A ⇐ A
⇐-refl = id

⇐-trans : ∀ {i} {A B C : Set i} → (A ⇐ B) → (B ⇐ C) → (A ⇐ C)
⇐-trans = flip ⇒-trans  -- _∘_

module ⇐-reasoning {i : Level} = MPR.Mono {suc i} {i} _⇐_ ⇐-refl ⇐-trans
   renaming (begin_ to ⇐-begin_ ; _∼⟨_⟩_ to _⇐⟨_⟩_ ; _∎ to _⇐∎) 
open ⇐-reasoning public hiding (byDef) 