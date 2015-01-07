module AlgebraicReasoning.Sets where

open import Level
open import Sets using (ℙ; _⊆_; ⊆-refl; ⊆-trans;
                           _⊇_; ⊇-refl; ⊇-trans )

import AlgebraicReasoning.PolyPreorderReasoning as PPR

  -- Shall we make it more level-polymorphic?

module ⊆-reasoning = PPR.UnaryCarrier {zero} {suc zero} ℙ _⊆_ ⊆-refl ⊆-trans
   renaming (begin_ to ⊆-begin_ ; _∼⟨_⟩_ to _⊆⟨_⟩_ ; _∎ to _⊆∎)
open ⊆-reasoning public  hiding (byDef)

module ⊇-reasoning = PPR.UnaryCarrier {zero} {suc zero} ℙ _⊇_ ⊇-refl ⊇-trans
   renaming (begin_ to ⊇-begin_ ; _∼⟨_⟩_ to _⊇⟨_⟩_ ; _∎ to _⊇∎)
open ⊇-reasoning public hiding (byDef)


