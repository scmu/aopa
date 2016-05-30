module AlgebraicReasoning.ExtensionalEquality where

open import Function using (_∘_; id)

open import Sets
     using (_≡_; refl; sym; subst)
open import Relations.Function
open import Level renaming (_⊔_ to _⊔ℓ_)

import Relation.Binary.EqReasoning as EqR

module ≐-reasoning {i j A B} = EqR (≐-Setoid {i} {j} A B)
  renaming (begin_ to ≐-begin_ ; _≈⟨_⟩_ to _≐⟨_⟩_ ; _∎ to _≐∎)
open ≐-reasoning public hiding (_IsRelatedTo_ ; _≡⟨_⟩_; _≡⟨⟩_)
