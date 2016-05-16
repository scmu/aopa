module AlgebraicReasoning.Relations where

open import Level renaming (_⊔_ to _⊔ℓ_)
open import Relations using
     (_←_;  _⊑_;  ⊑-refl;  ⊑-trans;
            _⊒_;  ⊒-refl;  ⊒-trans;
            _≑_;  ≑-refl;  ≑-trans)
open import Relations.Poset

import Relation.Binary.PreorderReasoning as PreR
import Relation.Binary.EqReasoning as EqR

module ⊑-reasoning {i j k A B} = PreR (⊑-Preorder {i}{j}{k} A B)
   renaming (begin_ to ⊑-begin_ ; _∼⟨_⟩_ to _⊑⟨_⟩_ ; _∎ to _⊑∎)
open ⊑-reasoning public  hiding (_IsRelatedTo_; _≈⟨_⟩_; _≈⟨⟩_)

module ⊒-reasoning {i j k A B} = PreR (⊒-Preorder {i}{j}{k} A B)
   renaming (begin_ to ⊒-begin_ ; _∼⟨_⟩_ to _⊒⟨_⟩_ ; _∎ to _⊒∎)
open ⊒-reasoning public  hiding (_IsRelatedTo_; _≈⟨_⟩_; _≈⟨⟩_)

module ≑-reasoning {i j k A B} = EqR (≑-Setoid {i}{j}{k} A B)
   renaming (begin_ to ≑-begin_; _≈⟨_⟩_ to _≑⟨_⟩_; _∎ to _≑∎)
open ≑-reasoning public hiding (_IsRelatedTo_ ; _≡⟨_⟩_; _≡⟨⟩_)
