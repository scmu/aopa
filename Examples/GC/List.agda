module Examples.GC.List where

open import Data.Unit using (⊤)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂; _⊎_)
open import Relation.Binary
open import Level renaming (_⊔_ to _⊔ℓ_)
open import Sets
open import Relations
open import Relations.CompChain
open import Data.Generic
open import AlgebraicReasoning.Relations
open import AlgebraicReasoning.Implications
open import Examples.GC.Relations


ListF : PolyF
ListF = one ⊕ (arg₁ ⊗ arg₂)

List : ∀ {i} → (A : Set i) → Set i
List A = μ ListF A

[] : ∀ {i} {A : Set i} → List A
[] = In (inj₁ tt)

_∷_ : ∀ {i} {A : Set i} → A → List A → List A
x ∷ xs = In (inj₂ (fst x , snd xs))

nil : ∀ {i} {A : Set i} → (List A ← One {i})
nil = (fun In) ○ (fun inj₁)

cons : ∀ {i} {A : Set i} → (List A ← ⟦ arg₁ ⊗ arg₂ ⟧ A (List A))
cons = (fun In) ○ (fun inj₂)


[]-nil : ∀ {i} {A : Set i} → nil {A = A} [] tt
[]-nil = (inj₁ tt , refl , refl)

∷-cons : ∀ {i} {A : Set i} {x : A} {xs : List A} → cons (x ∷ xs) (fst x , snd xs)
∷-cons = (inj₂ _ , refl , refl)

{-
[nil,cons]⊑In : ∀ {i} {A : Set i} → [ nil {A = A} , cons ] ⊑ fun In
[nil,cons]⊑In (In (inj₁ tt)) .(inj₁ tt) (inj₁ (tt , refl , _)) = refl
[nil,cons]⊑In (In (inj₂ a)) .(inj₁ tt) (inj₁ (tt , refl , .(inj₁ tt) , refl , ()))
[nil,cons]⊑In (In (inj₁ tt)) .(inj₂ as) (inj₂ (as , refl , .(inj₂ as) , refl , ()))
[nil,cons]⊑In (In (inj₂ a)) .(inj₂ a) (inj₂ (.a , refl , .(inj₂ a) , refl , refl)) = refl

[nil,cons]⊒In : ∀ {i} {A : Set i} → fun In ⊑ [ nil {A = A} , cons ]
[nil,cons]⊒In (In .(inj₁ tt)) (inj₁ tt) refl = inj₁ (tt , refl , (inj₁ tt) , refl , refl)
[nil,cons]⊒In (In .(inj₂ a)) (inj₂ a) refl = inj₂ (a , refl , (inj₂ a) , refl , refl)
-}


-- prefix operator

_≼_ : {A : Set} → (List A ← List A)
_≼_ = foldR ListF [ nil , (nil ○ !) ⊔ cons ]

_≽_ : {A : Set} → (List A ← List A)
ys ≽ xs = xs ≼ ys

≼-universal₁ : ∀ {A} {xs : List A} → [] ≼ xs
≼-universal₁ {xs = In (inj₁ tt)} = (inj₁ tt , Data.Unit.tt , inj₁ (tt , refl , []-nil))
≼-universal₁ {xs = In (inj₂ (fst x , snd xs))} = (inj₂ (fst x , snd []) , (refl , ≼-universal₁) , inj₂ (_ , refl , inj₁ (tt , refl , []-nil)))

≼-universal₂ : ∀ {A} {x : A} {xs ys : List A} → xs ≼ ys → (x ∷ xs) ≼ (x ∷ ys)
≼-universal₂ {x = x} {xs} xs≼ys = (inj₂ (fst x , snd xs) , (refl , xs≼ys) , inj₂ (_ , refl , inj₂ ∷-cons))



≼-computation-⊑ : {A : Set} → _≼_ {A} ○ fun In ⊑ [ nil , ((nil ○ !) ⊔ cons) ○ bimapR (arg₁ ⊗ arg₂) idR _≼_ ]
≼-computation-⊑ =
  ⊑-begin
    _≼_ ○ fun In
  ⊑⟨ foldR-computation-⊑ ListF [ nil , (nil ○ !) ⊔ cons ] ⟩
    [ nil , (nil ○ !) ⊔ cons ] ○ bimapR ListF idR _≼_
  ⊑⟨ [,]-⊕-absorption-⊑ ⟩
    [ nil ○ bimapR one idR _≼_ , ((nil ○ !) ⊔ cons) ○ bimapR (arg₁ ⊗ arg₂) idR _≼_ ]
  ⊑⟨ [,]-monotonic (○-monotonic-r bimapR-one⊑idR) ⊑-refl ⟩
    [ nil ○ idR , ((nil ○ !) ⊔ cons) ○ bimapR (arg₁ ⊗ arg₂) idR _≼_ ]
  ⊑⟨ [,]-monotonic id-intro-r ⊑-refl ⟩
    [ nil , ((nil ○ !) ⊔ cons) ○ bimapR (arg₁ ⊗ arg₂) idR _≼_ ]
  ⊑∎

≼-computation-⊒ : {A : Set} → _≼_ {A} ○ fun In ⊒ [ nil , ((nil ○ !) ⊔ cons) ○ bimapR (arg₁ ⊗ arg₂) idR _≼_ ]
≼-computation-⊒ =
  ⊑-begin
    [ nil , ((nil ○ !) ⊔ cons) ○ bimapR (arg₁ ⊗ arg₂) idR _≼_ ]
  ⊑⟨ [,]-monotonic id-elim-r ⊑-refl ⟩
    [ nil ○ idR , ((nil ○ !) ⊔ cons) ○ bimapR (arg₁ ⊗ arg₂) idR _≼_ ]
  ⊑⟨ [,]-monotonic (○-monotonic-r bimapR-one⊒idR) ⊑-refl ⟩
    [ nil ○ bimapR one idR _≼_ , ((nil ○ !) ⊔ cons) ○ bimapR (arg₁ ⊗ arg₂) idR _≼_ ]
  ⊑⟨ [,]-⊕-absorption-⊒ ⟩
    [ nil , (nil ○ !) ⊔ cons ] ○ bimapR ListF idR _≼_
  ⊑⟨ foldR-computation-⊒ ListF [ nil , (nil ○ !) ⊔ cons ] ⟩
    _≼_ ○ fun In
  ⊑∎

≼-computation-nil-⊑ : {A : Set} → _≼_ {A} ○ nil ⊑ nil
≼-computation-nil-⊑ =
  ⊑-begin
    _≼_ ○ nil
  ⊑⟨ ⊑-refl ⟩
    _≼_ ○ (fun In ○ fun inj₁)
  ⊑⟨ ⇦-mono-l (_≼_ ● fun In ‥) ([ nil , ((nil ○ !) ⊔ cons) ○ bimapR (arg₁ ⊗ arg₂) idR _≼_ ] ‥) ≼-computation-⊑ ⟩
    [ nil , ((nil ○ !) ⊔ cons) ○ bimapR (arg₁ ⊗ arg₂) idR _≼_ ] ○ fun inj₁
  ⊑⟨ [,]-universal-l-⊑ ⟩
    nil
  ⊑∎

≼-computation-nil-⊒ : {A : Set} → _≼_ {A} ○ nil ⊒ nil
≼-computation-nil-⊒ =
  ⊑-begin
    nil
  ⊑⟨ [,]-universal-l-⊒ ⟩
    [ nil , ((nil ○ !) ⊔ cons) ○ bimapR (arg₁ ⊗ arg₂) idR _≼_ ] ○ fun inj₁
  ⊑⟨ ○-monotonic-l ≼-computation-⊒ ⟩
    (_≼_ ○ fun In) ○ fun inj₁
  ⊑⟨ ○-assocr ⟩
    _≼_ ○ nil
  ⊑∎

≼-computation-cons-⊑ : {A : Set} → _≼_ {A} ○ cons ⊑ ((nil ○ !) ⊔ cons) ○ bimapR (arg₁ ⊗ arg₂) idR _≼_
≼-computation-cons-⊑ =
  ⊑-begin
    _≼_ ○ cons
  ⊑⟨ ⊑-refl ⟩
    _≼_ ○ (fun In ○ fun inj₂)
  ⊑⟨ ⇦-mono-l (_≼_ ● fun In ‥) ([ nil , ((nil ○ !) ⊔ cons) ○ bimapR (arg₁ ⊗ arg₂) idR _≼_ ] ‥) ≼-computation-⊑ ⟩
    [ nil , ((nil ○ !) ⊔ cons) ○ bimapR (arg₁ ⊗ arg₂) idR _≼_ ] ○ fun inj₂
  ⊑⟨ [,]-universal-r-⊑ ⟩
    ((nil ○ !) ⊔ cons) ○ bimapR (arg₁ ⊗ arg₂) idR _≼_
  ⊑∎

≼-computation-cons-⊒ : {A : Set} → _≼_ {A} ○ cons ⊒ ((nil ○ !) ⊔ cons) ○ bimapR (arg₁ ⊗ arg₂) idR _≼_
≼-computation-cons-⊒ =
  ⊑-begin
    ((nil ○ !) ⊔ cons) ○ bimapR (arg₁ ⊗ arg₂) idR _≼_
  ⊑⟨ [,]-universal-r-⊒ ⟩
    [ nil , ((nil ○ !) ⊔ cons) ○ bimapR (arg₁ ⊗ arg₂) idR _≼_ ] ○ fun inj₂
  ⊑⟨ ○-monotonic-l ≼-computation-⊒ ⟩
    (_≼_ ○ fun In) ○ fun inj₂
  ⊑⟨ ○-assocr ⟩
    _≼_ ○ cons
  ⊑∎


≼-refl : ∀ {A : Set} {xs ys : List A} → xs ≡ ys → xs ≼ ys
≼-refl {xs = In (inj₁ tt)} refl = (inj₁ tt , Data.Unit.tt , (inj₁ (tt , refl , []-nil)))
≼-refl {xs = In (inj₂ (fst x , snd xs))} refl = (inj₂ (fst x , snd xs) , (refl , ≼-refl refl) , inj₂ (_ , refl , inj₂ ∷-cons))

≼-trans : ∀ {A : Set} {xs ys zs : List A} → xs ≼ ys → ys ≼ zs → xs ≼ zs
≼-trans {xs = xs} {ys} {zs} xs≼ys ys≼zs = foldR-fusion-⊑ ListF _≼_ [ nil , (nil ○ !) ⊔ cons ] [ nil , (nil ○ !) ⊔ cons ] fuse-cond xs zs (ys , ys≼zs , xs≼ys)
  where
    fuse-cond : _≼_ ○ [ nil , (nil ○ !) ⊔ cons ] ⊑ [ nil , (nil ○ !) ⊔ cons ] ○ bimapR ListF idR _≼_
    fuse-cond =
      ⊑-begin
        _≼_ ○ [ nil , (nil ○ !) ⊔ cons ]
      ⊑⟨ ○-[,]-distr-⊑ ⟩
        [ _≼_ ○ nil , _≼_ ○ ((nil ○ !) ⊔ cons) ]
      ⊑⟨ [,]-monotonic ≼-computation-nil-⊑ ○-⊔-distr-l-⊑ ⟩
        [ nil , (_≼_ ○ (nil ○ !)) ⊔ (_≼_ ○ cons) ]
      ⊑⟨ [,]-monotonic ⊑-refl (⊔-monotonic ○-assocl ≼-computation-cons-⊑) ⟩
        [ nil , ((_≼_ ○ nil) ○ !) ⊔ (((nil ○ !) ⊔ cons) ○ bimapR (arg₁ ⊗ arg₂) idR _≼_) ]
      ⊑⟨ [,]-monotonic ⊑-refl (⊔-monotonic (○-monotonic-l ≼-computation-nil-⊑) ○-⊔-distr-r-⊑) ⟩
        [ nil , (nil ○ !) ⊔ (((nil ○ !) ○ bimapR (arg₁ ⊗ arg₂) idR _≼_) ⊔ (cons ○ bimapR (arg₁ ⊗ arg₂) idR _≼_)) ]
      ⊑⟨ [,]-monotonic ⊑-refl (⊔-monotonic (○-monotonic-r (!-fusion-⊒ bimapR-entire)) ⊑-refl) ⟩
        [ nil , (nil ○ ! ○ bimapR (arg₁ ⊗ arg₂) idR _≼_) ⊔ (((nil ○ !) ○ bimapR (arg₁ ⊗ arg₂) idR _≼_) ⊔ (cons ○ bimapR (arg₁ ⊗ arg₂) idR _≼_)) ]
      ⊑⟨ [,]-monotonic ⊑-refl (⊔-monotonic ○-assocl ⊑-refl) ⟩
        [ nil , ((nil ○ !) ○ bimapR (arg₁ ⊗ arg₂) idR _≼_) ⊔ (((nil ○ !) ○ bimapR (arg₁ ⊗ arg₂) idR _≼_) ⊔ (cons ○ bimapR (arg₁ ⊗ arg₂) idR _≼_)) ]
      ⊑⟨ [,]-monotonic ⊑-refl (⊔-universal-⇐ ((λ _ _ → inj₁) , ⊑-refl)) ⟩
        [ nil , ((nil ○ !) ○ bimapR (arg₁ ⊗ arg₂) idR _≼_) ⊔ (cons ○ bimapR (arg₁ ⊗ arg₂) idR _≼_) ]
      ⊑⟨ [,]-monotonic id-elim-r ○-⊔-distr-r-⊒ ⟩
        [ nil ○ idR , ((nil ○ !) ⊔ cons) ○ bimapR (arg₁ ⊗ arg₂) idR _≼_ ]
      ⊑⟨ [,]-monotonic (○-monotonic-r bimapR-one⊒idR) ⊑-refl ⟩
        [ nil ○ bimapR one idR _≼_ , ((nil ○ !) ⊔ cons) ○ bimapR (arg₁ ⊗ arg₂) idR _≼_ ]
      ⊑⟨ [,]-⊕-absorption-⊒ ⟩
        [ nil , (nil ○ !) ⊔ cons ] ○ bimapR ListF idR _≼_
      ⊑∎
     where
       bimapR-entire : idR ⊑ (bimapR (arg₁ ⊗ arg₂) idR _≼_ ˘) ○ bimapR (arg₁ ⊗ arg₂) idR _≼_
       bimapR-entire (fst a , snd as) ._ refl = ((fst a , snd as) , (refl , (≼-refl refl)) , (refl , (≼-refl refl)))

≽-refl : ∀ {A} {xs ys : List A} → xs ≡ ys → xs ≽ ys
≽-refl {xs = xs} refl = ≼-refl refl

≽-trans : ∀ {A} {xs ys zs : List A} → xs ≽ ys → ys ≽ zs → xs ≽ zs
≽-trans xs≽ys ys≽zs = ≼-trans ys≽zs xs≽ys

≽-isPreorder : ∀ {A} → IsPreorder (_≡_) (_≽_ {A})
≽-isPreorder = record
  { isEquivalence = record { refl = refl ; sym = sym ; trans = trans } ;
    reflexive = ≽-refl ;
    trans = ≽-trans }


-- relational map on list

mapR : {A B : Set} → (R : B ← A) → (List B ← List A)
mapR R = foldR ListF [ nil , cons ○ bimapR (arg₁ ⊗ arg₂) R idR ]

mapR-computation-⊑ : {A B : Set} {R : B ← A ⊣ zero}
                   → mapR R ○ fun In ⊑ [ nil , cons ○ bimapR (arg₁ ⊗ arg₂) R (mapR R) ]
mapR-computation-⊑ {R = R} =
  ⊑-begin
    mapR R ○ fun In
  ⊑⟨ foldR-computation-⊑ ListF [ nil , cons ○ bimapR (arg₁ ⊗ arg₂) R idR ] ⟩
    [ nil , cons ○ bimapR (arg₁ ⊗ arg₂) R idR ] ○ bimapR ListF idR (mapR R)
  ⊑⟨ [,]-⊕-absorption-⊑ ⟩
    [ nil ○ bimapR one idR (mapR R) , (cons ○ bimapR (arg₁ ⊗ arg₂) R idR) ○ bimapR (arg₁ ⊗ arg₂) idR (mapR R) ]
  ⊑⟨ [,]-monotonic (○-monotonic-r bimapR-one⊑idR) ○-assocr ⟩
    [ nil ○ idR , cons ○ (bimapR (arg₁ ⊗ arg₂) R idR ○ bimapR (arg₁ ⊗ arg₂) idR (mapR R)) ]
  ⊑⟨ [,]-monotonic id-intro-r (○-monotonic-r (bimapR-functor-⊑ (arg₁ ⊗ arg₂))) ⟩
    [ nil , cons ○ (bimapR (arg₁ ⊗ arg₂) (R ○ idR) (idR ○ mapR R)) ]
  ⊑⟨ [,]-monotonic ⊑-refl (○-monotonic-r (bimapR-monotonic-⊑ (arg₁ ⊗ arg₂) id-intro-r id-intro-l)) ⟩
    [ nil , cons ○ bimapR (arg₁ ⊗ arg₂) R (mapR R) ]
  ⊑∎

mapR-computation-⊒ : {A B : Set} {R : B ← A}
                   → mapR R ○ fun In ⊒ [ nil , cons ○ bimapR (arg₁ ⊗ arg₂) R (mapR R) ]
mapR-computation-⊒ {R = R} =
  ⊑-begin
    [ nil , cons ○ bimapR (arg₁ ⊗ arg₂) R (mapR R) ]
  ⊑⟨ [,]-monotonic ⊑-refl (○-monotonic-r (bimapR-monotonic-⊑ (arg₁ ⊗ arg₂) id-elim-r id-elim-l)) ⟩
    [ nil , cons ○ bimapR (arg₁ ⊗ arg₂) (R ○ idR) (idR ○ mapR R) ]
  ⊑⟨ [,]-monotonic id-elim-r (○-monotonic-r (bimapR-functor-⊒ (arg₁ ⊗ arg₂))) ⟩
    [ nil ○ idR , cons ○ (bimapR (arg₁ ⊗ arg₂) R idR ○ bimapR (arg₁ ⊗ arg₂) idR (mapR R)) ]
  ⊑⟨ [,]-monotonic (○-monotonic-r bimapR-one⊒idR) ○-assocl ⟩
    [ nil ○ bimapR one idR (mapR R) , (cons ○ bimapR (arg₁ ⊗ arg₂) R idR) ○ bimapR (arg₁ ⊗ arg₂) idR (mapR R) ]
  ⊑⟨ [,]-⊕-absorption-⊒ ⟩
    [ nil , cons ○ bimapR (arg₁ ⊗ arg₂) R idR ] ○ bimapR ListF idR (mapR R)
  ⊑⟨ foldR-computation-⊒ ListF [ nil , cons ○ bimapR (arg₁ ⊗ arg₂) R idR ] ⟩
    mapR R ○ fun In
  ⊑∎

mapR-computation-nil-⊑ : {A B : Set} {R : B ← A} → mapR R ○ nil ⊑ nil
mapR-computation-nil-⊑ {R = R} =
  ⊑-begin
    mapR R ○ nil
  ⊑⟨ ⊑-refl ⟩
    mapR R ○ (fun In ○ fun inj₁)
  ⊑⟨ ⇦-mono-l (mapR R ● fun In ‥) ([ nil , cons ○ bimapR (arg₁ ⊗ arg₂) R (mapR R) ] ‥) mapR-computation-⊑ ⟩
    [ nil , cons ○ bimapR (arg₁ ⊗ arg₂) R (mapR R) ] ○ fun inj₁
  ⊑⟨ [,]-universal-l-⊑ ⟩
    nil
  ⊑∎

mapR-computation-nil-⊒ : {A B : Set} {R : B ← A} → nil ⊑ mapR R ○ nil
mapR-computation-nil-⊒ {R = R} =
  ⊑-begin
    nil
  ⊑⟨ [,]-universal-l-⊒ ⟩
    [ nil , cons ○ bimapR (arg₁ ⊗ arg₂) R (mapR R) ] ○ fun inj₁
  ⊑⟨ ○-monotonic-l mapR-computation-⊒ ⟩
    (mapR R ○ fun In) ○ fun inj₁
  ⊑⟨ ○-assocr ⟩
    mapR R ○ nil
  ⊑∎

mapR-computation-cons-⊑ : {A B : Set} {R : B ← A}
                        → mapR R ○ cons ⊑ cons ○ bimapR (arg₁ ⊗ arg₂) R (mapR R)
mapR-computation-cons-⊑ {R = R} =
  ⊑-begin
    mapR R ○ cons
  ⊑⟨ ⊑-refl ⟩
    mapR R ○ (fun In ○ fun inj₂)
  ⊑⟨ ⇦-mono-l (mapR R ● fun In ‥) ([ nil , cons ○ bimapR (arg₁ ⊗ arg₂) R (mapR R) ] ‥) mapR-computation-⊑ ⟩
    [ nil , cons ○ bimapR (arg₁ ⊗ arg₂) R (mapR R) ] ○ fun inj₂
  ⊑⟨ [,]-universal-r-⊑ ⟩
    cons ○ bimapR (arg₁ ⊗ arg₂) R (mapR R)
  ⊑∎

mapR-computation-cons-⊒ : {A B : Set} {R : B ← A}
                       → cons ○ bimapR (arg₁ ⊗ arg₂) R (mapR R) ⊑ (mapR R) ○ cons
mapR-computation-cons-⊒ {R = R} =
  ⊑-begin
    cons ○ bimapR (arg₁ ⊗ arg₂) R (mapR R)
  ⊑⟨ [,]-universal-r-⊒ ⟩
    [ nil , cons ○ bimapR (arg₁ ⊗ arg₂) R (mapR R) ] ○ fun inj₂
  ⊑⟨ ○-monotonic-l mapR-computation-⊒ ⟩
    (mapR R ○ fun In) ○ fun inj₂
  ⊑⟨ ○-assocr ⟩
    mapR R ○ cons
  ⊑∎
