module AlgebraicReasoning.Sets where

open import Level
open import Relation.Binary
open import Data.Product
open import Sets  {- using (ℙ; _⊆_; ⊆-refl; ⊆-trans;
                           _⊇_; ⊇-refl; ⊇-trans;
                           _≗_; ≗-refl; ≗-trans; ≗-sym) -}
import Relation.Binary.PreorderReasoning as PreR

module ⊆-reasoning {ℓ A} = PreR (⊆-Preorder {ℓ} A)
  renaming (begin_ to ⊆-begin_; _∼⟨_⟩_ to _⊆⟨_⟩_; _∎ to _⊆∎)
open ⊆-reasoning public  hiding (_IsRelatedTo_; _≈⟨_⟩_; _≈⟨⟩_)

module ⊇-reasoning {ℓ A} = PreR (⊇-Preorder {ℓ} A)
  renaming (begin_ to ⊇-begin_; _∼⟨_⟩_ to _⊇⟨_⟩_; _∎ to _⊇∎)
open ⊇-reasoning public  hiding (_IsRelatedTo_; _≈⟨_⟩_; _≈⟨⟩_)
