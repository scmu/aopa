module AlgebraicReasoning.Relations where

open import Level renaming (_⊔_ to _⊔l_)
open import Relations using
     (_←_;  _⊑_;  ⊑-refl;  ⊑-trans;
            _⊒_;  ⊒-refl;  ⊒-trans)
--      _←₁_; _⊑₁_; ⊑₁-refl; ⊑₁-trans;
--            _⊒₁_; ⊒₁-refl; ⊒₁-trans)

import AlgebraicReasoning.PolyPreorderReasoning as PPR

module ⊑-reasoning {i j : Level} = PPR.BinaryCarrier {i} {j} _←_ _⊑_ ⊑-refl ⊑-trans
   renaming (begin_ to ⊑-begin_ ; _∼⟨_⟩_ to _⊑⟨_⟩_ ; _∎ to _⊑∎)
open ⊑-reasoning public  hiding (byDef)

module ⊒-reasoning {i j : Level} = PPR.BinaryCarrier {i} {j} _←_ _⊒_ ⊒-refl ⊒-trans
   renaming (begin_ to ⊒-begin_ ; _∼⟨_⟩_ to _⊒⟨_⟩_ ; _∎ to _⊒∎)
open ⊒-reasoning public  hiding (byDef)

{-
module ⊑₁-reasoning = PPR.BinaryCarrier₁ _←₁_ _⊑₁_ ⊑₁-refl ⊑₁-trans
   renaming (begin_ to ⊑₁-begin_ ; _∼⟨_⟩_ to _⊑₁⟨_⟩_ ; _∎ to _⊑₁∎)
open ⊑₁-reasoning public  hiding (byDef)

module ⊒₁-reasoning = PPR.BinaryCarrier₁ _←₁_ _⊒₁_ ⊒₁-refl ⊒₁-trans
   renaming (begin_ to ⊒₁-begin_ ; _∼⟨_⟩_ to _⊒₁⟨_⟩_ ; _∎ to _⊒₁∎)
open ⊒₁-reasoning public  hiding (byDef)
-}