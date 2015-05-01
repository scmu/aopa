module Examples.GC.TakeWhile where

open import Data.Empty
open import Data.Unit using (⊤)
open import Data.Product using (_×_; _,_; uncurry; ∃; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂; _⊎_)
open import Function
open import Level renaming (_⊔_ to _⊔ℓ_)
open import Sets
open import Relations
open import Relations.Shrink
open import Relations.Galois
open import Relations.Coreflexive using (_¿)
open import Relations.CompChain
open import Data.Generic
open import AlgebraicReasoning.Relations
open import AlgebraicReasoning.Implications

-- List

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


[_,_] : ∀ {i} {A B C : Set i}
        → (C ← A ⊣ i) → (C ← B ⊣ i) → (C ← A ⊎ B ⊣ i)
[ R , S ] = (R ○ (fun inj₁ ˘)) ⊔ (S ○ (fun inj₂ ˘))


[,]-universal-l-⊑ : ∀ {i} {A B C : Set i} {R : C ← A} {S : C ← B}
                  → [ R , S ] ○ fun inj₁ ⊑ R
[,]-universal-l-⊑ c a (.(inj₁ a) , refl , inj₁ (.a , refl , cRa)) = cRa
[,]-universal-l-⊑ c a (.(inj₁ a) , refl , inj₂ (_ , () , _))

[,]-universal-l-⊒ : ∀ {i} {A B C : Set i} {R : C ← A} {S : C ← B}
                  → [ R , S ] ○ fun inj₁ ⊒ R
[,]-universal-l-⊒ c a cRa = (inj₁ a , refl , inj₁ (a , refl , cRa))

[,]-universal-r-⊑ : ∀ {i} {A B C : Set i} {R : C ← A} {S : C ← B}
                  → [ R , S ] ○ fun inj₂ ⊑ S
[,]-universal-r-⊑ c b (.(inj₂ b) , refl , inj₁ (_ , () , _))
[,]-universal-r-⊑ c b (.(inj₂ b) , refl , inj₂ (.b , refl , cSb)) = cSb

[,]-universal-r-⊒ : ∀ {i} {A B C : Set i} {R : C ← A} {S : C ← B}
                  → [ R , S ] ○ fun inj₂ ⊒ S
[,]-universal-r-⊒ c b cSb = (inj₂ b , refl , inj₂ (b , refl , cSb))


[,]-monotonic : ∀ {i} {A B C : Set i}
                  {R T : C ← A} {S U : C ← B}
                → R ⊑ T → S ⊑ U → [ R , S ] ⊑ [ T , U ]
[,]-monotonic {R = R} {T} {S} {U} R⊑T S⊑U =
   ⊑-begin
     [ R , S ]
   ⊑⟨ ⊑-refl ⟩
     (R ○ (fun inj₁ ˘)) ⊔ (S ○ (fun inj₂ ˘))
   ⊑⟨ ⊔-monotonic (○-monotonic-l R⊑T) (○-monotonic-l S⊑U) ⟩
     (T ○ (fun inj₁ ˘)) ⊔ (U ○ (fun inj₂ ˘))
   ⊑⟨ ⊑-refl ⟩
     [ T , U ]
   ⊑∎

[,]-⊕-absorption-⊑ : {F₁ F₂ : PolyF} {A B C D E : Set} {R : E ← ⟦ F₁ ⟧ C D} {S : E ← ⟦ F₂ ⟧ C D} {T : C ← A} {U : D ← B}
                    → [ R , S ] ○ bimapR (F₁ ⊕ F₂) T U ⊑ [ R ○ bimapR F₁ T U , S ○ bimapR F₂ T U ]
[,]-⊕-absorption-⊑ {F₁} {F₂} {R = R} {S} {T} {U} =
   ⊑-begin
     [ R , S ] ○ bimapR (F₁ ⊕ F₂) T U
   ⊑⟨ ○-monotonic-l ⊑-refl ⟩
     ((R ○ (fun inj₁ ˘)) ⊔ (S ○ (fun inj₂ ˘))) ○ bimapR (F₁ ⊕ F₂) T U
   ⊑⟨ ○-⊔-distr-r-⊑ ⟩
     ((R ○ (fun inj₁ ˘)) ○ bimapR (F₁ ⊕ F₂) T U) ⊔ ((S ○ (fun inj₂ ˘)) ○ bimapR (F₁ ⊕ F₂) T U)
   ⊑⟨ ⊔-monotonic ○-assocr ○-assocr ⟩
     (R ○ (fun inj₁ ˘) ○ bimapR (F₁ ⊕ F₂) T U) ⊔ (S ○ (fun inj₂ ˘) ○ bimapR (F₁ ⊕ F₂) T U)
   ⊑⟨ ⊔-monotonic (○-monotonic-r inj₁˘F₁F₂⊑F₁inj₁) (○-monotonic-r inj₂˘F₁F₂⊑F₂inj₂) ⟩
     (R ○ bimapR F₁ T U ○ (fun inj₁ ˘)) ⊔ (S ○ bimapR F₂ T U ○ (fun inj₂ ˘))
   ⊑⟨ ⊔-monotonic ○-assocl ○-assocl ⟩
     ((R ○ bimapR F₁ T U) ○ (fun inj₁ ˘)) ⊔ ((S ○ bimapR F₂ T U) ○ (fun inj₂ ˘))
   ⊑⟨ ⊑-refl ⟩
     [ R ○ bimapR F₁ T U , S ○ bimapR F₂ T U ]
   ⊑∎
 where
   inj₁˘F₁F₂⊑F₁inj₁ : (fun inj₁ ˘) ○ bimapR (F₁ ⊕ F₂) T U ⊑ bimapR F₁ T U ○ (fun inj₁ ˘)
   inj₁˘F₁F₂⊑F₁inj₁ x (inj₁ y) (.(inj₁ x) , bmp , refl) = (y , refl , bmp)
   inj₁˘F₁F₂⊑F₁inj₁ x (inj₂ y) (inj₁ _ , () , _)
   inj₁˘F₁F₂⊑F₁inj₁ x (inj₂ y) (inj₂ _ , _ , ())

   inj₂˘F₁F₂⊑F₂inj₂ : (fun inj₂ ˘) ○ bimapR (F₁ ⊕ F₂) T U ⊑ bimapR F₂ T U ○ (fun inj₂ ˘)
   inj₂˘F₁F₂⊑F₂inj₂ x (inj₁ y) (inj₁ _ , _ , ())
   inj₂˘F₁F₂⊑F₂inj₂ x (inj₁ y) (inj₂ _ , () , _)
   inj₂˘F₁F₂⊑F₂inj₂ x (inj₂ y) (.(inj₂ x) , bmp , refl) = (y , refl , bmp)


[,]-⊕-absorption-⊒ : {F₁ F₂ : PolyF} {A B C D E : Set} {R : E ← ⟦ F₁ ⟧ C D} {S : E ← ⟦ F₂ ⟧ C D} {T : C ← A} {U : D ← B}
                    → [ R , S ] ○ bimapR (F₁ ⊕ F₂) T U ⊒ [ R ○ bimapR F₁ T U , S ○ bimapR F₂ T U ]
[,]-⊕-absorption-⊒ {F₁} {F₂} {R = R} {S} {T} {U} =
  ⊑-begin
    [ R ○ bimapR F₁ T U , S ○ bimapR F₂ T U ]
  ⊑⟨ ⊑-refl ⟩
    ((R ○ bimapR F₁ T U) ○ (fun inj₁ ˘)) ⊔ ((S ○ bimapR F₂ T U) ○ (fun inj₂ ˘))
  ⊑⟨ ⊔-monotonic ○-assocr ○-assocr ⟩
    (R ○ bimapR F₁ T U ○ (fun inj₁ ˘)) ⊔ (S ○ bimapR F₂ T U ○ (fun inj₂ ˘))
  ⊑⟨ ⊔-monotonic (○-monotonic-r F₁inj₁˘⊑inj₁˘F₁F₂) (○-monotonic-r F₂inj₂˘⊑inj₂˘F₁F₂) ⟩
    (R ○ (fun inj₁ ˘) ○ bimapR (F₁ ⊕ F₂) T U) ⊔ (S ○ (fun inj₂ ˘) ○ bimapR (F₁ ⊕ F₂) T U)
  ⊑⟨ ⊔-monotonic ○-assocl ○-assocl ⟩
    ((R ○ (fun inj₁ ˘)) ○ bimapR (F₁ ⊕ F₂) T U) ⊔ ((S ○ (fun inj₂ ˘)) ○ bimapR (F₁ ⊕ F₂) T U)
  ⊑⟨ ○-⊔-distr-r-⊒ ⟩
    [ R , S ] ○ bimapR (F₁ ⊕ F₂) T U
  ⊑∎
 where
   F₁inj₁˘⊑inj₁˘F₁F₂ : bimapR F₁ T U ○ (fun inj₁ ˘) ⊑ (fun inj₁ ˘) ○ bimapR (F₁ ⊕ F₂) T U
   F₁inj₁˘⊑inj₁˘F₁F₂ x (inj₁ y) (.y , refl , bmp) = (inj₁ x , bmp , refl)
   F₁inj₁˘⊑inj₁˘F₁F₂ x (inj₂ y) (_ , () , _)

   F₂inj₂˘⊑inj₂˘F₁F₂ : bimapR F₂ T U ○ (fun inj₂ ˘) ⊑ (fun inj₂ ˘) ○ bimapR (F₁ ⊕ F₂) T U
   F₂inj₂˘⊑inj₂˘F₁F₂ x (inj₁ y) (_ , () , _)
   F₂inj₂˘⊑inj₂˘F₁F₂ x (inj₂ y) (.y , refl , bmp) = (inj₂ x , bmp , refl)
  
○-[,]-distr-⊑ : ∀ {i} {A B C D : Set i} {R : D ← C ⊣ i} {S : C ← A} {T : C ← B}
                → R ○ [ S , T ] ⊑ [ R ○ S , R ○ T ]
○-[,]-distr-⊑ {R = R}{S}{T} =
  ⊑-begin
    R ○ [ S , T ]
  ⊑⟨ ○-monotonic-r ⊑-refl ⟩
    R ○ ((S ○ (fun inj₁ ˘) ) ⊔ (T ○ (fun inj₂ ˘)))
  ⊑⟨ ○-⊔-distr-l-⊑ ⟩
    (R ○ S ○ (fun inj₁ ˘)) ⊔ (R ○ T ○ (fun inj₂ ˘))
  ⊑⟨ ⊔-monotonic ○-assocl ○-assocl ⟩
    ((R ○ S) ○ (fun inj₁ ˘)) ⊔ ((R ○ T) ○ (fun inj₂ ˘))
  ⊑⟨ ⊑-refl ⟩
    [ R ○ S , R ○ T ]
  ⊑∎

○-[,]-distr-⊒ : ∀ {i} {A B C D : Set i} {R : D ← C ⊣ i} {S : C ← A} {T : C ← B}
                → R ○ [ S , T ] ⊒ [ R ○ S , R ○ T ]
○-[,]-distr-⊒ {R = R}{S}{T} =
  ⊑-begin
    [ R ○ S , R ○ T ]
  ⊑⟨ ⊑-refl ⟩
    ((R ○ S) ○ (fun inj₁ ˘)) ⊔ ((R ○ T) ○ (fun inj₂ ˘))
  ⊑⟨ ⊔-monotonic ○-assocr ○-assocr ⟩
    (R ○ S ○ (fun inj₁ ˘)) ⊔ (R ○ T ○ (fun inj₂ ˘))
  ⊑⟨ ○-⊔-distr-l-⊒ ⟩
    R ○ ((S ○ (fun inj₁ ˘) ) ⊔ (T ○ (fun inj₂ ˘)))
  ⊑⟨ ⊑-refl ⟩
    R ○ [ S , T ]
  ⊑∎


! : ∀ {i} {A : Set i} → (One {i} ← A)
! = fun (λ _ → tt)

!-fusion : ∀ {i} {A B : Set i} {R : A ← B ⊣ i}
           → ! ○ R ⊑ !
!-fusion tt b (a , bRa , refl) = refl

bimapR-one⊑idR : {A₁ B₁ A₂ B₂ : Set} {R : B₁ ← A₁} {S : B₂ ← A₂}
                → bimapR one R S ⊑ idR
bimapR-one⊑idR tt tt _ = refl

bimapR-one⊒idR : {A₁ B₁ A₂ B₂ : Set} {R : B₁ ← A₁} {S : B₂ ← A₂}
                → bimapR one R S ⊒ idR
bimapR-one⊒idR tt tt _ = Data.Unit.tt


-- prefix operator

_≼_ : {A : Set} → (List A ← List A)
_≼_ = foldR ListF [ nil , (nil ○ !) ⊔ cons ]

_≽_ : {A : Set} → (List A ← List A)
ys ≽ xs = xs ≼ ys


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


fuse-cond : {A : Set} → (p : ℙ A) → [ nil , (nil ○ !) ⊔ (cons ○ bimapR (arg₁ ⊗ arg₂) (p ¿) idR) ] ○ bimapR ListF idR (mapR (p ¿)) ⊑ mapR (p ¿) ○ [ nil , (nil ○ !) ⊔ cons ]
fuse-cond p =
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
  ⊑⟨ [,]-monotonic ⊑-refl (⊔-monotonic (○-monotonic-r !-fusion) (○-monotonic-r (bimapR-functor-⊑ (arg₁ ⊗ arg₂)))) ⟩
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
  ⊑⟨ [,]-monotonic ⊑-refl (⊔-monotonic (○-monotonic-r !-fusion) (○-monotonic-r (bimapR-functor-⊑ (arg₁ ⊗ arg₂)))) ⟩
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


takeWhile-der : {A : Set} → (p : ℙ A) → foldR ListF [ nil , (nil ○ !) ⊔ (cons ○ bimapR (arg₁ ⊗ arg₂) (p ¿) idR) ] ⊑ (mapR (p ¿) ○ _≼_) ↾ _≽_
takeWhile-der = {!!}

