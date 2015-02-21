module AlgebraicReasoning.ExtensionalEquality where

open import Function using (_∘_; id)

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

≐-trans' : ∀ {i j} {A : Set i} {B : Set j} {f g h : A → B} → f ≐ g → h ≐ f → h ≐ g
≐-trans' f≐g h≐f = ≐-trans h≐f f≐g 

pre-∘-cong : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k} 
             → (f : B → C) → {g h : A → B} → g ≐ h → f ∘ g ≐ f ∘ h
pre-∘-cong f g≐h a rewrite g≐h a = refl

post-∘-cong : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k} 
              → (f : A → B) → {g h : B → C} → g ≐ h → g ∘ f ≐ h ∘ f
post-∘-cong f g≐h a = g≐h (f a)

module ≐-reasoning {i j} = PPR.BinaryCarrier {i} {j} (λ A B → A → B) 
  _≐_ ≐-refl ≐-trans
  renaming (begin_ to ≐-begin_ ; _∼⟨_⟩_ to _≐⟨_⟩_ ; _∎ to _≐∎)
open ≐-reasoning public
