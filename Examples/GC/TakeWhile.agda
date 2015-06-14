module Examples.GC.TakeWhile where

open import Data.Empty
open import Data.Unit using (⊤)
open import Data.Bool
open import Data.Product using (_×_; _,_; uncurry; ∃; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂; _⊎_)
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (inspect) renaming ([_] to [_]')
open import Level renaming (_⊔_ to _⊔ℓ_)
open import Sets
open import Relations hiding (_⨉_) -- overridden by our definition here.
open import Relations.Factor
open import Relations.Shrink
open import Relations.Galois
open import Relations.Converse
open import Relations.Coreflexive
open import Relations.CompChain
open import Data.Generic
open import Data.Generic.Greedy
open import AlgebraicReasoning.Relations
open import AlgebraicReasoning.Implications
open import Examples.GC.Relations
open import Examples.GC.List

-- an abbreviation, overridding the one defined in Relations

private
  _⨉_ : ∀ {i j k l} {A : Set i} {B : Set j} {C : Set k} {D : Set l}
       → (B ← A) → (D ← C) → ⟦ arg₁ ⊗ arg₂ ⟧ B D ← ⟦ arg₁ ⊗ arg₂ ⟧ A C
  (R ⨉ S) = bimapR (arg₁ ⊗ arg₂) R S

map○≼-foldR-⊑ : {A : Set} → {p : ℙ A} → mapR (p ¿) ○ _≼_ ⊑ foldR ListF [ nil , (nil ○ !) ⊔ (cons ○ (p ¿ ⨉ idR)) ]
map○≼-foldR-⊑ {p = p} =
  (⇐-begin
     mapR (p ¿) ○ _≼_ ⊑ foldR ListF [ nil , (nil ○ !) ⊔ (cons ○ (p ¿ ⨉ idR)) ]
   ⇐⟨ foldR-universal-⇐-⊑ ListF (mapR (p ¿) ○ _≼_) [ nil , (nil ○ !) ⊔ (cons ○ (p ¿ ⨉ idR)) ] ⟩
     (mapR (p ¿) ○ _≼_) ○ fun In ⊑ [ nil , (nil ○ !) ⊔ (cons ○ (p ¿ ⨉ idR)) ] ○ fmapR ListF (mapR (p ¿) ○ _≼_)
   ⇐⟨ ⊑-trans ○-assocr ⟩
     mapR (p ¿) ○ _≼_ ○ fun In ⊑ [ nil , (nil ○ !) ⊔ (cons ○ (p ¿ ⨉ idR)) ] ○ fmapR ListF (mapR (p ¿) ○ _≼_)
   ⇐⟨ ⊑-trans (○-monotonic-r (foldR-computation-⊑ [ nil , (nil ○ !) ⊔ cons ])) ⟩
     mapR (p ¿) ○ [ nil , (nil ○ !) ⊔ cons ] ○ fmapR ListF _≼_ ⊑ [ nil , (nil ○ !) ⊔ (cons ○ (p ¿ ⨉ idR)) ] ○ fmapR ListF (mapR (p ¿) ○ _≼_)
   ⇐∎) cond
 where
   cond : mapR (p ¿) ○ [ nil , (nil ○ !) ⊔ cons ] ○ fmapR ListF _≼_
            ⊑ [ nil , (nil ○ !) ⊔ (cons ○ (p ¿ ⨉ idR)) ] ○ fmapR ListF (mapR (p ¿) ○ _≼_)
   cond =
     ⊑-begin
       mapR (p ¿) ○ [ nil , (nil ○ !) ⊔ cons ] ○ fmapR ListF _≼_
     ⊑⟨ ○-assocl ⟩
       (mapR (p ¿) ○ [ nil , (nil ○ !) ⊔ cons ]) ○ fmapR ListF _≼_
     ⊑⟨ ○-monotonic-l ○-[,]-distr-⊑ ⟩
       [ mapR (p ¿) ○ nil , mapR (p ¿) ○ ((nil ○ !) ⊔ cons) ] ○ fmapR ListF _≼_
     ⊑⟨ ○-monotonic-l ([,]-monotonic mapR-computation-nil-⊑ ○-⊔-distr-l-⊑) ⟩
       [ nil , (mapR (p ¿) ○ nil ○ !) ⊔ (mapR (p ¿) ○ cons) ] ○ fmapR ListF _≼_
     ⊑⟨ ○-monotonic-l ([,]-monotonic ⊑-refl (⊔-monotonic ○-assocl mapR-computation-cons-⊑)) ⟩
       [ nil , ((mapR (p ¿) ○ nil) ○ !) ⊔ (cons ○ (p ¿ ⨉ mapR (p ¿))) ] ○ fmapR ListF _≼_
     ⊑⟨ ○-monotonic-l ([,]-monotonic ⊑-refl (⊔-monotonic (○-monotonic-l mapR-computation-nil-⊑) ⊑-refl)) ⟩
       [ nil , (nil ○ !) ⊔ (cons ○ (p ¿ ⨉ mapR (p ¿))) ] ○ fmapR ListF _≼_
     ⊑⟨ [,]-⊕-absorption-⊑ ⟩
       [ nil ○ bimapR one idR _≼_ , ((nil ○ !) ⊔ (cons ○ (p ¿ ⨉ mapR (p ¿)))) ○ (idR ⨉ _≼_) ]
     ⊑⟨ [,]-monotonic (○-monotonic-r bimapR-one⊑idR) ○-⊔-distr-r-⊑ ⟩
       [ nil ○ idR , ((nil ○ !) ○ (idR ⨉ _≼_)) ⊔ ((cons ○ (p ¿ ⨉ mapR (p ¿))) ○ (idR ⨉ _≼_)) ]
     ⊑⟨ [,]-monotonic id-intro-r (⊔-monotonic ⊑-refl ○-assocr) ⟩
       [ nil , ((nil ○ !) ○ (idR ⨉ _≼_)) ⊔ (cons ○ (p ¿ ⨉ mapR (p ¿)) ○ (idR ⨉ _≼_)) ]
     ⊑⟨ [,]-monotonic ⊑-refl (⊔-monotonic ⊑-refl (○-monotonic-r (bimapR-functor-⊑ (arg₁ ⊗ arg₂)))) ⟩
       [ nil , ((nil ○ !) ○ (idR ⨉ _≼_)) ⊔ (cons ○ ((p ¿ ○ idR) ⨉ (mapR (p ¿) ○ _≼_))) ]
     ⊑⟨ [,]-monotonic ⊑-refl (⊔-monotonic ⊑-refl (○-monotonic-r (bimapR-monotonic (arg₁ ⊗ arg₂) ⊑-refl id-elim-l))) ⟩
       [ nil , ((nil ○ !) ○ (idR ⨉ _≼_)) ⊔ (cons ○ ((p ¿ ○ idR) ⨉ (idR ○ (mapR (p ¿) ○ _≼_)))) ]
     ⊑⟨ [,]-monotonic ⊑-refl (⊔-monotonic ⊑-refl (○-monotonic-r (bimapR-functor-⊒ (arg₁ ⊗ arg₂)))) ⟩
       [ nil , ((nil ○ !) ○ (idR ⨉ _≼_)) ⊔ (cons ○ (p ¿ ⨉ idR) ○ (idR ⨉ (mapR (p ¿) ○ _≼_))) ]
     ⊑⟨ [,]-monotonic id-elim-r (⊔-monotonic nil≼⊑nilmap≼ ○-assocl) ⟩
       [ nil ○ idR , ((nil ○ !) ○ (idR ⨉ (mapR (p ¿) ○ _≼_))) ⊔ ((cons ○ (p ¿ ⨉ idR)) ○ (idR ⨉ (mapR (p ¿) ○ _≼_))) ]
     ⊑⟨ [,]-monotonic (○-monotonic-r bimapR-one⊒idR) ○-⊔-distr-r-⊒ ⟩
       [ nil ○ bimapR one idR (mapR (p ¿) ○ _≼_) , ((nil ○ !) ⊔ ((cons ○ (p ¿ ⨉ idR))) ○ (idR ⨉ (mapR (p ¿) ○ _≼_))) ]
     ⊑⟨ [,]-⊕-absorption-⊒ ⟩
       [ nil , (nil ○ !) ⊔ (cons ○ (p ¿ ⨉ idR)) ] ○ fmapR ListF (mapR (p ¿) ○ _≼_)
     ⊑∎
    where
      nil≼⊑nilmap≼ : (nil ○ !) ○ (idR ⨉ _≼_) ⊑ (nil ○ !) ○ (idR ⨉ (mapR (p ¿) ○ _≼_))
      nil≼⊑nilmap≼ (In (inj₁ tt)) (fst x , snd xs) _ =
        ((fst x , snd []) ,
         (refl , [] , ≼-universal₁ , inj₁ tt , Data.Unit.tt , (inj₁ (tt , refl , []-nil))) ,
         (tt , refl , []-nil))
      nil≼⊑nilmap≼ (In (inj₂ ys)) xs (_ , _ , tt , _ , .(inj₂ ys) , () , refl)

map○≼-foldR-⊒ : {A : Set} → {p : ℙ A} → mapR (p ¿) ○ _≼_ ⊒ foldR ListF [ nil , (nil ○ !) ⊔ (cons ○ (p ¿ ⨉ idR)) ]
map○≼-foldR-⊒ {p = p} = foldR-fusion-⊒ ListF (mapR (p ¿)) [ nil , (nil ○ !) ⊔ cons ] [ nil , (nil ○ !) ⊔ (cons ○ (p ¿ ⨉ idR)) ] fuse-cond
  where
    fuse-cond : [ nil , (nil ○ !) ⊔ (cons ○ (p ¿ ⨉ idR)) ] ○ fmapR ListF (mapR (p ¿))
                  ⊑ mapR (p ¿) ○ [ nil , (nil ○ !) ⊔ cons ]
    fuse-cond =
      ⊑-begin
        [ nil , (nil ○ !) ⊔ (cons ○ (p ¿ ⨉ idR)) ] ○ fmapR ListF (mapR (p ¿))
      ⊑⟨ [,]-⊕-absorption-⊑ ⟩
        [ nil ○ bimapR one idR (mapR (p ¿)) , ((nil ○ !) ⊔ (cons ○ (p ¿ ⨉ idR))) ○ (idR ⨉ mapR (p ¿)) ]
      ⊑⟨ [,]-monotonic (○-monotonic-r bimapR-one⊑idR) ⊑-refl ⟩
        [ nil ○ idR , ((nil ○ !) ⊔ (cons ○ (p ¿ ⨉ idR))) ○ (idR ⨉ mapR (p ¿)) ]
      ⊑⟨ [,]-monotonic id-intro-r ○-⊔-distr-r-⊑ ⟩
        [ nil , ((nil ○ !) ○ (idR ⨉ mapR (p ¿))) ⊔ ((cons ○ (p ¿ ⨉ idR)) ○ (idR ⨉ mapR (p ¿))) ]
      ⊑⟨ [,]-monotonic ⊑-refl (⊔-monotonic ○-assocr ○-assocr) ⟩
        [ nil , (nil ○ ! ○ (idR ⨉ mapR (p ¿))) ⊔ (cons ○ (p ¿ ⨉ idR) ○ (idR ⨉ mapR (p ¿))) ]
      ⊑⟨ [,]-monotonic ⊑-refl (⊔-monotonic (○-monotonic-r !-fusion-⊑) (○-monotonic-r (bimapR-functor-⊑ (arg₁ ⊗ arg₂)))) ⟩
        [ nil , (nil ○ !) ⊔ (cons ○ ((p ¿ ○ idR) ⨉ (idR ○ (mapR (p ¿))))) ]
      ⊑⟨ [,]-monotonic ⊑-refl (⊔-monotonic ⊑-refl (○-monotonic-r (bimapR-monotonic (arg₁ ⊗ arg₂) id-intro-r id-intro-l))) ⟩
        [ nil , (nil ○ !) ⊔ (cons ○ (p ¿ ⨉ mapR (p ¿))) ]
      ⊑⟨ [,]-monotonic mapR-computation-nil-⊒ (⊔-monotonic (⇦-mono-l (nil ‥) (mapR (p ¿) ● nil ‥) mapR-computation-nil-⊒) mapR-computation-cons-⊒) ⟩
        [ mapR (p ¿) ○ nil , (mapR (p ¿) ○ nil ○ !) ⊔ (mapR (p ¿) ○ cons) ]
      ⊑⟨ [,]-monotonic ⊑-refl ○-⊔-distr-l-⊒ ⟩
        [ mapR (p ¿) ○ nil , mapR (p ¿) ○ ((nil ○ !) ⊔ cons) ]
      ⊑⟨ ○-[,]-distr-⊒ ⟩
        mapR (p ¿) ○ [ nil , (nil ○ !) ⊔ cons ]
      ⊑∎

map○≼≑foldR : {A : Set} → {p : ℙ A}
  → mapR (p ¿) ○ _≼_ ≑ foldR ListF [ nil , (nil ○ !) ⊔ (cons ○ (p ¿ ⨉ idR)) ]
map○≼≑foldR = (map○≼-foldR-⊑ , map○≼-foldR-⊒)

mono-cond : {A : Set} → (p : ℙ A)
         → [ nil , (nil ○ !) ⊔ (cons ○ (p ¿ ⨉ idR)) ] ○ fmapR ListF _≼_
             ⊑ _≼_ ○ [ nil , (nil ○ !) ⊔ (cons ○ (p ¿ ⨉ idR)) ]
mono-cond p =
  ⊑-begin
    [ nil , (nil ○ !) ⊔ (cons ○ (p ¿ ⨉ idR)) ] ○ fmapR ListF _≼_
  ⊑⟨ [,]-⊕-absorption-⊑ ⟩
    [ nil ○ bimapR one idR _≼_ , ((nil ○ !) ⊔ (cons ○ (p ¿ ⨉ idR))) ○ (idR ⨉ _≼_) ]
  ⊑⟨ [,]-monotonic (○-monotonic-r bimapR-one⊑idR) ○-⊔-distr-r-⊑ ⟩
    [ nil ○ idR , ((nil ○ !) ○ (idR ⨉ _≼_)) ⊔ ((cons ○ (p ¿ ⨉ idR)) ○ (idR ⨉ _≼_)) ]
  ⊑⟨ [,]-monotonic id-intro-r (⊔-monotonic ○-assocr ○-assocr) ⟩
    [ nil , (nil ○ ! ○ (idR ⨉ _≼_)) ⊔ (cons ○ (p ¿ ⨉ idR) ○ (idR ⨉ _≼_)) ]
  ⊑⟨ [,]-monotonic ⊑-refl (⊔-monotonic (○-monotonic-r !-fusion-⊑) (○-monotonic-r (bimapR-functor-⊑ (arg₁ ⊗ arg₂)))) ⟩
    [ nil , (nil ○ !) ⊔ (cons ○ ((p ¿ ○ idR) ⨉ (idR ○ _≼_))) ]
  ⊑⟨ [,]-monotonic ⊑-refl (⊔-monotonic ⊑-refl (○-monotonic-r (bimapR-monotonic (arg₁ ⊗ arg₂) id-intro-r id-intro-l))) ⟩
    [ nil , (nil ○ !) ⊔ (cons ○ (p ¿ ⨉ _≼_)) ]
  ⊑⟨ [,]-monotonic ⊑-refl (⊔-monotonic ⊑-refl (○-monotonic-r (bimapR-monotonic (arg₁ ⊗ arg₂) id-elim-l id-elim-r))) ⟩
    [ nil , (nil ○ !) ⊔ (cons ○ ((idR ○ p ¿) ⨉ (_≼_ ○ idR))) ]
  ⊑⟨ [,]-monotonic ⊑-refl (⊔-monotonic ⊑-refl (○-monotonic-r (bimapR-functor-⊒ (arg₁ ⊗ arg₂)))) ⟩
    [ nil , (nil ○ !) ⊔ (cons ○ (idR ⨉ _≼_) ○ (p ¿ ⨉ idR)) ]
  ⊑⟨ [,]-monotonic ≼-computation-nil-⊒ (⊔-monotonic (⇦-mono-l (nil ‥) (_≼_ ● nil ‥) ≼-computation-nil-⊒) (⇦-mono-l (cons ● (idR ⨉ _≼_) ‥) (_≼_ ● cons ‥) cons○bimap⊑≼○cons)) ⟩
    [ _≼_ ○ nil , (_≼_ ○ nil ○ !) ⊔ (_≼_ ○ cons ○ (p ¿ ⨉ idR)) ]
  ⊑⟨ [,]-monotonic ⊑-refl ○-⊔-distr-l-⊒ ⟩
    [ _≼_ ○ nil , _≼_ ○ ((nil ○ !) ⊔ (cons ○ (p ¿ ⨉ idR))) ]
  ⊑⟨ ○-[,]-distr-⊒ ⟩
    _≼_ ○ [ nil , (nil ○ !) ⊔ (cons ○ (p ¿ ⨉ idR)) ]
  ⊑∎
 where
   cons○bimap⊑≼○cons : cons ○ (idR ⨉ _≼_) ⊑ _≼_ ○ cons
   cons○bimap⊑≼○cons =
     (⇐-begin
        cons ○ (idR ⨉ _≼_) ⊑ _≼_ ○ cons
      ⇐⟨ proj₂ ∘ ⊔-universal-⇒ ⟩
        (((nil ○ !) ○ (idR ⨉ _≼_) ) ⊔ (cons ○ (idR ⨉ _≼_))) ⊑ _≼_ ○ cons
      ⇐⟨ ⊑-trans ○-⊔-distr-r-⊒ ⟩
        ((nil ○ !) ⊔ cons) ○ (idR ⨉ _≼_) ⊑ _≼_ ○ cons
      ⇐∎) ≼-computation-cons-⊒


takeWhile-der : {A : Set} → (p : A → Bool) → ∃ (λ f → fun f ⊑ (mapR ((p ♯) ¿) ○ _≼_) ↾ _≽_)
takeWhile-der {A} p = _ ,
  (⊒-begin
     (mapR ((p ♯) ¿) ○ _≼_) ↾ _≽_
   ⊒⟨ proj₂ (↾-subst (mapR ((p ♯) ¿) ○ _≼_) _ _≽_ map○≼≑foldR) ⟩
     (⦇ [ nil , (nil ○ !) ⊔ (cons ○ ((p ♯) ¿ ⨉ idR)) ] ⦈) ↾ _≽_
   ⊒⟨ greedy-cata ListF ≽-isPreorder (mono-cond (p ♯)) ⟩
     ⦇ ([ nil , (nil ○ !) ⊔ (cons ○ ((p ♯) ¿ ⨉ idR)) ] ↾ _≽_) ⦈
   ⊒⟨ foldR-fold ListF pcons _ pcons⊑S↾≽ ⟩
     fun (fold ListF pcons)
   ⊒∎)
 where
   pcons : ⟦ ListF ⟧ A (List A) → List A
   pcons (inj₁ tt) = []
   pcons (inj₂ (fst x , snd xs)) with p x
   ... | true = x ∷ xs
   ... | false = []


   pcons⊑S : fun pcons ⊑ [ nil , (nil ○ !) ⊔ (cons ○ ((p ♯) ¿ ⨉ idR)) ]
   pcons⊑S .(In (inj₁ tt)) (inj₁ tt) refl = inj₁ (tt , refl , []-nil)
   pcons⊑S ys (inj₂ (fst x , snd xs)) eq with p x | inspect p x
   pcons⊑S ._ (inj₂ (fst x , snd xs)) refl | true | [ px≡true ]' = inj₂ (_ , refl , inj₂ ((fst x , snd xs) , ((refl , px≡true) , refl) , ∷-cons))
   pcons⊑S ._ (inj₂ (fst x , snd xs)) refl | false | [ _ ]' = inj₂ (_ , refl , inj₁ (tt , refl , []-nil))

   pconsS˘⊒≽ : fun pcons ○ [ nil , (nil ○ !) ⊔ (cons ○ ((p ♯) ¿ ⨉ idR)) ] ˘ ⊑ _≽_
   pconsS˘⊒≽ .(In (inj₁ tt)) .(In (inj₁ tt)) (.(inj₁ tt) , inj₁ (tt , refl , .(inj₁ tt) , refl , refl) , refl) = ≽-refl refl
   pconsS˘⊒≽ ys .(In (inj₁ tt)) (.(inj₂ (fst x , snd xs)) , inj₂ ((fst x , snd xs) , refl , inj₁ (tt , refl , .(inj₁ tt) , refl , refl)) , eq) = ≼-universal₁
   pconsS˘⊒≽ ._ .(In (inj₂ (fst x , snd xs))) (.(inj₂ (fst x , snd xs)) , inj₂ ((fst x , snd xs) , refl , inj₂ ((fst .x , snd .xs) , ((refl , px≡true) , refl) , .(inj₂ (fst x , snd xs)) , refl , refl)) , refl) rewrite px≡true = ≽-refl refl


   pcons⊑S↾≽ : fun pcons ⊑ [ nil , (nil ○ !) ⊔ (cons ○ ((p ♯) ¿ ⨉ idR)) ] ↾ _≽_
   pcons⊑S↾≽ = ↾-universal-⇐ (pcons⊑S , pconsS˘⊒≽)
