module AlgebraicReasoning.ExtensionalEquality where

open import Function using (_∘_; id)

open import Sets
     using (_≡_; refl; sym; subst)
open import Relations.Function
open import Level renaming (_⊔_ to _⊔ℓ_)

import AlgebraicReasoning.PolyPreorderReasoning as PPR


module ≐-reasoning {i j} = PPR.BinaryCarrier {i} {j} (λ A B → A → B) 
  _≐_ ≐-refl ≐-trans
  renaming (begin_ to ≐-begin_ ; _∼⟨_⟩_ to _≐⟨_⟩_ ; _∎ to _≐∎)
open ≐-reasoning public
