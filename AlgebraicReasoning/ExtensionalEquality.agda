module AlgebraicReasoning.ExtensionalEquality where

open import Sets
     using (_≡_; refl; sym; subst)

import AlgebraicReasoning.PolyPreorderReasoning as PPR

infix 4 _≐_

_≐_ : {A B : Set} → (A → B) → (A → B) → Set
f ≐ g = forall a → f a ≡ g a

≐-refl : {A B : Set}{f : A → B} → f ≐ f
≐-refl {A} {B} {f} a = refl 

≐-sym : {A B : Set}{f g : A → B} → f ≐ g → g ≐ f
≐-sym f≐g a = sym (f≐g a) 

≐-trans : {A B : Set}{f g h : A → B} → f ≐ g → g ≐ h → f ≐ h
≐-trans {A} {B} {f} {g} {h} f≐g g≐h a = 
    subst (λ b → f a ≡ b) (g≐h a) (f≐g a) 

module ≐-reasoning = PPR.BinaryCarrier (λ A B → A → B) 
  _≐_ ≐-refl ≐-trans
  renaming (begin_ to ≐-begin_ ; _∼⟨_⟩_ to _≐⟨_⟩_ ; _∎ to _≐∎)
open ≐-reasoning public