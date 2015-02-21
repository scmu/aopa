module AlgebraicReasoning.ExtensionalEquality where

open import Sets
     using (_≡_; refl; sym; subst)
open import Level renaming (_⊔_ to _⊔ℓ_)

import AlgebraicReasoning.PolyPreorderReasoning as PPR

infix 4 _≐_

_≐_ : ∀ {i j} {A : Set i} {B : Set j} → (A → B) → (A → B) → Set (i ⊔ℓ j)
f ≐ g = forall a → f a ≡ g a

≐-refl : ∀ {i j} {A : Set i} {B : Set j} {f : A → B} → f ≐ f
≐-refl {A} {B} {f} a = refl 

≐-sym : ∀ {i j} {A : Set i} {B : Set j} {f g : A → B} → f ≐ g → g ≐ f
≐-sym f≐g a = sym (f≐g a) 

≐-trans : ∀ {i j} {A : Set i} {B : Set j} {f g h : A → B} → f ≐ g → g ≐ h → f ≐ h
≐-trans {f = f} f≐g g≐h a =
  subst (λ b → f a ≡ b) (g≐h a) (f≐g a) 

module ≐-reasoning {i j} = PPR.BinaryCarrier {i} {j} (λ A B → A → B) 
  _≐_ ≐-refl ≐-trans
  renaming (begin_ to ≐-begin_ ; _∼⟨_⟩_ to _≐⟨_⟩_ ; _∎ to _≐∎)
open ≐-reasoning public
