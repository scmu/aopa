module Examples.GC.TakeWhile where

open import Data.Empty
open import Data.Unit using (⊤)
open import Data.Product using (_×_; _,_; uncurry; ∃; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂; _⊎_)
open import Function
open import Relation.Binary
open import Level renaming (_⊔_ to _⊔ℓ_)
open import Sets
open import Relations
open import Relations.Factor
open import Relations.Shrink
open import Relations.Galois
open import Relations.Converse
open import Relations.Coreflexive using (_¿)
open import Relations.CompChain
open import Data.Generic
open import AlgebraicReasoning.Relations
open import AlgebraicReasoning.Implications
open import Examples.GC.Relations
open import Examples.GC.List


fuse-cond-⊒ : {A : Set} → (p : ℙ A)
            → [ nil , (nil ○ !) ⊔ (cons ○ bimapR (arg₁ ⊗ arg₂) (p ¿) idR) ] ○ bimapR ListF idR (mapR (p ¿))
                ⊑ mapR (p ¿) ○ [ nil , (nil ○ !) ⊔ cons ]
fuse-cond-⊒ p =
  ⊑-begin
    [ nil , (nil ○ !) ⊔ (cons ○ bimapR (arg₁ ⊗ arg₂) (p ¿) idR) ] ○ bimapR ListF idR (mapR (p ¿))
  ⊑⟨ [,]-⊕-absorption-⊑ ⟩
    [ nil ○ bimapR one idR (mapR (p ¿)) , ((nil ○ !) ⊔ (cons ○ bimapR (arg₁ ⊗ arg₂) (p ¿) idR)) ○ bimapR (arg₁ ⊗ arg₂) idR (mapR (p ¿)) ]
  ⊑⟨ [,]-monotonic (○-monotonic-r bimapR-one⊑idR) ⊑-refl ⟩
    [ nil ○ idR , ((nil ○ !) ⊔ (cons ○ bimapR (arg₁ ⊗ arg₂) (p ¿) idR)) ○ bimapR (arg₁ ⊗ arg₂) idR (mapR (p ¿)) ]
  ⊑⟨ [,]-monotonic id-intro-r ○-⊔-distr-r-⊑ ⟩
    [ nil , ((nil ○ !) ○ bimapR (arg₁ ⊗ arg₂) idR (mapR (p ¿))) ⊔ ((cons ○ bimapR (arg₁ ⊗ arg₂) (p ¿) idR) ○ bimapR (arg₁ ⊗ arg₂) idR (mapR (p ¿))) ]
  ⊑⟨ [,]-monotonic ⊑-refl (⊔-monotonic ○-assocr ○-assocr) ⟩
    [ nil , (nil ○ ! ○ bimapR (arg₁ ⊗ arg₂) idR (mapR (p ¿))) ⊔ (cons ○ bimapR (arg₁ ⊗ arg₂) (p ¿) idR ○ bimapR (arg₁ ⊗ arg₂) idR (mapR (p ¿))) ]
  ⊑⟨ [,]-monotonic ⊑-refl (⊔-monotonic (○-monotonic-r !-fusion-⊑) (○-monotonic-r (bimapR-functor-⊑ (arg₁ ⊗ arg₂)))) ⟩
    [ nil , (nil ○ !) ⊔ (cons ○ bimapR (arg₁ ⊗ arg₂) ((p ¿) ○ idR) (idR ○ (mapR (p ¿)))) ]
  ⊑⟨ [,]-monotonic ⊑-refl (⊔-monotonic ⊑-refl (○-monotonic-r (bimapR-monotonic-⊑ (arg₁ ⊗ arg₂) id-intro-r id-intro-l))) ⟩
    [ nil , (nil ○ !) ⊔ (cons ○ bimapR (arg₁ ⊗ arg₂) (p ¿) (mapR (p ¿))) ]
  ⊑⟨ [,]-monotonic mapR-computation-nil-⊒ (⊔-monotonic (⇦-mono-l (nil ‥) (mapR (p ¿) ● nil ‥) mapR-computation-nil-⊒) mapR-computation-cons-⊒) ⟩
    [ mapR (p ¿) ○ nil , (mapR (p ¿) ○ nil ○ !) ⊔ (mapR (p ¿) ○ cons) ]
  ⊑⟨ [,]-monotonic ⊑-refl ○-⊔-distr-l-⊒ ⟩
    [ mapR (p ¿) ○ nil , mapR (p ¿) ○ ((nil ○ !) ⊔ cons) ]
  ⊑⟨ ○-[,]-distr-⊒ ⟩
    mapR (p ¿) ○ [ nil , (nil ○ !) ⊔ cons ]
  ⊑∎


mono-cond : {A : Set} → (p : ℙ A) → [ nil , (nil ○ !) ⊔ (cons ○ bimapR (arg₁ ⊗ arg₂) (p ¿) idR) ] ○ bimapR ListF idR _≼_
                                  ⊑ _≼_ ○ [ nil , (nil ○ !) ⊔ (cons ○ bimapR (arg₁ ⊗ arg₂) (p ¿) idR) ]
mono-cond p =
  ⊑-begin
    [ nil , (nil ○ !) ⊔ (cons ○ bimapR (arg₁ ⊗ arg₂) (p ¿) idR) ] ○ bimapR ListF idR _≼_
  ⊑⟨ [,]-⊕-absorption-⊑ ⟩
    [ nil ○ bimapR one idR _≼_ , ((nil ○ !) ⊔ (cons ○ bimapR (arg₁ ⊗ arg₂) (p ¿) idR)) ○ bimapR (arg₁ ⊗ arg₂) idR _≼_ ]
  ⊑⟨ [,]-monotonic (○-monotonic-r bimapR-one⊑idR) ○-⊔-distr-r-⊑ ⟩
    [ nil ○ idR , ((nil ○ !) ○ bimapR (arg₁ ⊗ arg₂) idR _≼_) ⊔ ((cons ○ bimapR (arg₁ ⊗ arg₂) (p ¿) idR) ○ bimapR (arg₁ ⊗ arg₂) idR _≼_) ]
  ⊑⟨ [,]-monotonic id-intro-r (⊔-monotonic ○-assocr ○-assocr) ⟩
    [ nil , (nil ○ ! ○ bimapR (arg₁ ⊗ arg₂) idR _≼_) ⊔ (cons ○ bimapR (arg₁ ⊗ arg₂) (p ¿) idR ○ bimapR (arg₁ ⊗ arg₂) idR _≼_) ]
  ⊑⟨ [,]-monotonic ⊑-refl (⊔-monotonic (○-monotonic-r !-fusion-⊑) (○-monotonic-r (bimapR-functor-⊑ (arg₁ ⊗ arg₂)))) ⟩
    [ nil , (nil ○ !) ⊔ (cons ○ bimapR (arg₁ ⊗ arg₂) ((p ¿) ○ idR) (idR ○ _≼_)) ]
  ⊑⟨ [,]-monotonic ⊑-refl (⊔-monotonic ⊑-refl (○-monotonic-r (bimapR-monotonic-⊑ (arg₁ ⊗ arg₂) id-intro-r id-intro-l))) ⟩
    [ nil , (nil ○ !) ⊔ (cons ○ bimapR (arg₁ ⊗ arg₂) (p ¿) _≼_) ]
  ⊑⟨ [,]-monotonic ⊑-refl (⊔-monotonic ⊑-refl (○-monotonic-r (bimapR-monotonic-⊑ (arg₁ ⊗ arg₂) id-elim-l id-elim-r))) ⟩
    [ nil , (nil ○ !) ⊔ (cons ○ bimapR (arg₁ ⊗ arg₂) (idR ○ p ¿) (_≼_ ○ idR)) ]
  ⊑⟨ [,]-monotonic ⊑-refl (⊔-monotonic ⊑-refl (○-monotonic-r (bimapR-functor-⊒ (arg₁ ⊗ arg₂)))) ⟩
    [ nil , (nil ○ !) ⊔ (cons ○ bimapR (arg₁ ⊗ arg₂) idR _≼_ ○ bimapR (arg₁ ⊗ arg₂) (p ¿) idR) ]
  ⊑⟨ [,]-monotonic ≼-computation-nil-⊒ (⊔-monotonic (⇦-mono-l (nil ‥) (_≼_ ● nil ‥) ≼-computation-nil-⊒) (⇦-mono-l (cons ● bimapR (arg₁ ⊗ arg₂) idR _≼_ ‥) (_≼_ ● cons ‥) cons○bimap⊑≼○cons)) ⟩
    [ _≼_ ○ nil , (_≼_ ○ nil ○ !) ⊔ (_≼_ ○ cons ○ bimapR (arg₁ ⊗ arg₂) (p ¿) idR) ]
  ⊑⟨ [,]-monotonic ⊑-refl ○-⊔-distr-l-⊒ ⟩
    [ _≼_ ○ nil , _≼_ ○ ((nil ○ !) ⊔ (cons ○ bimapR (arg₁ ⊗ arg₂) (p ¿) idR)) ]
  ⊑⟨ ○-[,]-distr-⊒ ⟩
    _≼_ ○ [ nil , (nil ○ !) ⊔ (cons ○ bimapR (arg₁ ⊗ arg₂) (p ¿) idR) ]
  ⊑∎
 where
   cons○bimap⊑≼○cons : cons ○ bimapR (arg₁ ⊗ arg₂) idR _≼_ ⊑ _≼_ ○ cons
   cons○bimap⊑≼○cons =
     (⇐-begin
        cons ○ bimapR (arg₁ ⊗ arg₂) idR _≼_ ⊑ _≼_ ○ cons
      ⇐⟨ proj₂ ∘ ⊔-universal-⇒ ⟩
        (((nil ○ !) ○ bimapR (arg₁ ⊗ arg₂) idR _≼_ ) ⊔ (cons ○ bimapR (arg₁ ⊗ arg₂) idR _≼_)) ⊑ _≼_ ○ cons
      ⇐⟨ ⊑-trans ○-⊔-distr-r-⊒ ⟩
        ((nil ○ !) ⊔ cons) ○ bimapR (arg₁ ⊗ arg₂) idR _≼_ ⊑ _≼_ ○ cons
      ⇐∎) ≼-computation-cons-⊒


takeWhile-der : {A : Set} → (p : ℙ A) → foldR ListF ([ nil , (nil ○ !) ⊔ (cons ○ bimapR (arg₁ ⊗ arg₂) (p ¿) idR) ] ↾ _≽_) ⊑ (mapR (p ¿) ○ _≼_) ↾ _≽_
takeWhile-der p =
  ⊒-begin
    (mapR (p ¿) ○ _≼_) ↾ _≽_
  ⊒⟨ ⊒-refl ⟩
    (mapR (p ¿) ○ _≼_) ⊓ (_≽_ / (mapR (p ¿) ○ _≼_) ˘)
  ⊒⟨ ⊓-monotonic map○≼-foldR-⊒ ⊑-refl ⟩
    (foldR ListF [ nil , (nil ○ !) ⊔ (cons ○ bimapR (arg₁ ⊗ arg₂) (p ¿) idR) ]) ⊓ (_≽_ / (mapR (p ¿) ○ _≼_) ˘)
  ⊒⟨ ⊓-monotonic ⊑-refl (/-anti-monotonic (˘-monotonic-⇐ map○≼-foldR-⊑)) ⟩
    (foldR ListF [ nil , (nil ○ !) ⊔ (cons ○ bimapR (arg₁ ⊗ arg₂) (p ¿) idR) ]) ⊓ (_≽_ / (foldR ListF [ nil , (nil ○ !) ⊔ (cons ○ bimapR (arg₁ ⊗ arg₂) (p ¿) idR) ]) ˘)
  ⊒⟨ ⊒-refl ⟩
    (foldR ListF [ nil , (nil ○ !) ⊔ (cons ○ bimapR (arg₁ ⊗ arg₂) (p ¿) idR) ]) ↾ _≽_
  ⊒⟨ foldR-↾-absorption ListF ≽-isPreorder (mono-cond p) ⟩
    foldR ListF ([ nil , (nil ○ !) ⊔ (cons ○ bimapR (arg₁ ⊗ arg₂) (p ¿) idR) ] ↾ _≽_)
  ⊒∎
 where
   map○≼-foldR-⊑ : mapR (p ¿) ○ _≼_ ⊑ foldR ListF [ nil , (nil ○ !) ⊔ (cons ○ bimapR (arg₁ ⊗ arg₂) (p ¿) idR) ]
   map○≼-foldR-⊑ = {!!}
   map○≼-foldR-⊒ : mapR (p ¿) ○ _≼_ ⊒ foldR ListF [ nil , (nil ○ !) ⊔ (cons ○ bimapR (arg₁ ⊗ arg₂) (p ¿) idR) ]
   map○≼-foldR-⊒ = foldR-fusion-⊒ ListF (mapR (p ¿)) [ nil , (nil ○ !) ⊔ cons ] [ nil , (nil ○ !) ⊔ (cons ○ bimapR (arg₁ ⊗ arg₂) (p ¿) idR) ] (fuse-cond-⊒ p)
