{-# OPTIONS --universe-polymorphism #-}

module AlgebraicReasoning.Implications where

open import Level
open import Data.Product
open import Function

import AlgebraicReasoning.MonoPreorderReasoning as MPR

infixr 5 _⇒_ _⇐_ _⇔_ -- _⇒₁_

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

_⇔_ : ∀ {i} → Set i → Set i → Set i
A ⇔ B = A ⇒ B × A ⇐ B

⇔-refl : ∀ {i} {A : Set i} → A ⇔ A
⇔-refl = (id , id) 

⇔-trans : ∀ {i} {A B C : Set i} → (A ⇔ B) → (B ⇔ C) → (A ⇔ C)
⇔-trans (A⇒B , A⇐B) (B⇒C , B⇐C) = (B⇒C ∘ A⇒B  , A⇐B ∘ B⇐C) 

module ⇔-reasoning {i : Level} = MPR.Mono {suc i} {i} _⇔_ ⇔-refl ⇔-trans
   renaming (begin_ to ⇔-begin_ ; _∼⟨_⟩_ to _⇔⟨_⟩_ ; _∎ to _⇔∎)
open ⇔-reasoning public hiding (byDef) 

{-
_⇒₁_ : Set1 → Set1 → Set1
A ⇒₁ B = A → B

⇒₁-refl : {A : Set1} → A ⇒₁ A
⇒₁-refl x = x

⇒₁-trans : {A B C : Set1} → (A ⇒₁ B) → (B ⇒₁ C) → (A ⇒₁ C)
⇒₁-trans f g x = g (f x)

module ⇒₁-reasoning = MPR.Sets1 _⇒₁_ ⇒₁-refl ⇒₁-trans
   renaming (begin_ to ⇒₁-begin_ ; _∼⟨_⟩_ to _⇒₁⟨_⟩_ ; _∎ to _⇒₁∎)
open ⇒₁-reasoning public

-}