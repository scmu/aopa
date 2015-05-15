module Data.Generic where

open import Sets
open import Data.Empty
open import Data.Unit using (⊤)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; ∃; _×_; _,_; proj₁; proj₂)
open import Function using (_∘_; id)
open import Level renaming (_⊔_ to _⊔ℓ_)

open import Relations
open import Relations.Factor
open import Relations.Function
open import Relations.Converse
open import Relations.CompChain
open import Relations.Poset
open import FixedPoint
open import AlgebraicReasoning.ExtensionalEquality 
            using (_≐_; ≐-refl; ≐-sym; ≐-trans; ≐-trans'; 
                   pre-∘-cong; post-∘-cong)
open import AlgebraicReasoning.Implications
open import AlgebraicReasoning.Relations

open import Data.Generic.Core public
open import Data.Generic.Fold public
open import Data.Generic.Hylo public

