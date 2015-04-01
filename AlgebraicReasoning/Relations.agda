module AlgebraicReasoning.Relations where

open import Level renaming (_⊔_ to _⊔ℓ_)
open import Relations using
     (_←_;  _⊑_;  ⊑-refl;  ⊑-trans;
            _⊒_;  ⊒-refl;  ⊒-trans)

import AlgebraicReasoning.PolyPreorderReasoning as PPR

module ⊑-reasoning {i j k : Level} = 
    PPR.BinaryCarrier {i} {j} {suc k ⊔ℓ (j ⊔ℓ i)} 
                      (_←_ {i}{j}{k}) _⊑_ ⊑-refl ⊑-trans
   renaming (begin_ to ⊑-begin_ ; _∼⟨_⟩_ to _⊑⟨_⟩_ ; _∎ to _⊑∎)
open ⊑-reasoning public  hiding (byDef)

module ⊒-reasoning {i j k : Level} = 
      PPR.BinaryCarrier {i} {j} {suc k ⊔ℓ (j ⊔ℓ i)} 
                        (_←_ {i}{j}{k}) _⊒_ ⊒-refl ⊒-trans
   renaming (begin_ to ⊒-begin_ ; _∼⟨_⟩_ to _⊒⟨_⟩_ ; _∎ to _⊒∎)
open ⊒-reasoning public  hiding (byDef)
