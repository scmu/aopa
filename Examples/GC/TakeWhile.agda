module Examples.GC.TakeWhile where

open import Data.Empty
open import Data.Unit using (⊤)
open import Data.Product using (_×_; _,_; uncurry)
open import Data.Sum using (inj₁; inj₂; _⊎_)
open import Level renaming (_⊔_ to _⊔ℓ_)
open import Sets
open import Relations
open import Relations.Shrink
open import Relations.Galois
open import Relations.Coreflexive using (_¿)
open import Relations.CompChain
open import Data.Generic
open import AlgebraicReasoning.Relations

-- List

ListF : PolyF
ListF = one ⊕ (arg₁ ⊗ arg₂)

List : ∀ {i} → (A : Set i) → Set i
List A = μ ListF A

[] : ∀ {i} {A : Set i} → List A
[] = In (inj₁ tt)

_∷_ : ∀ {i} {A : Set i} → A → List A → List A
x ∷ xs = In (inj₂ (fst x , snd xs))

nil : ∀ {i j} {A : Set i} → (List A ← One {j})
nil = fun (λ _ → [])

cons : ∀ {i} {A : Set i} → (List A ← ⟦ arg₁ ⊗ arg₂ ⟧ A (List A))
cons ys (fst x , snd xs) = (x ∷ xs) ≡ ys


[_,_] : ∀ {i} {A B C : Set i}
        → (C ← A ⊣ i) → (C ← B ⊣ i) → (C ← A ⊎ B ⊣ i)
[ R , S ] = (R ○ (fun inj₁ ˘)) ⊔ (S ○ (fun inj₂ ˘))


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


-- prefix operator

_≼_ : {A : Set} → (List A ← List A)
_≼_ = foldR ListF [ nil , (nil ○ !) ⊔ cons ]

_≽_ : {A : Set} → (List A ← List A)
ys ≽ xs = xs ≼ ys

{-
mapR : {A B : Set} → (R : B ← A) → (List B ← List A)
mapR R = foldR ListF [ nil , cons ○ bimapR (arg₁ ⊗ arg₂) R idR ]
-}
mapR : ∀ {i} {A B : Set i} → (R : B ← A ⊣ zero) → (List B ← List A)
mapR R (In (inj₁ tt)) (In (inj₁ tt)) = ⊤
mapR R (In (inj₁ tt)) (In (inj₂ _)) = ⊥
mapR R (In (inj₂ (fst y , snd ys))) (In (inj₁ _)) = ⊥
mapR R (In (inj₂ (fst y , snd ys))) (In (inj₂ (fst x , snd xs))) = R y x × mapR R ys xs


mapR-computation-nil-⊑ : ∀ {i} {A B : Set} {R : B ← A ⊣ zero} → mapR R ○ nil ⊑ nil {j = i}
mapR-computation-nil-⊑ (In (inj₁ tt)) tt (In .(inj₁ tt) , refl , Data.Unit.tt) = refl
mapR-computation-nil-⊑ (In (inj₂ (fst x , snd xs))) tt (In .(inj₁ tt) , refl , ())

mapR-computation-nil-⊒ : ∀{i} {A B : Set} {R : B ← A ⊣ zero} → nil {j = i} ⊑ mapR R ○ nil
mapR-computation-nil-⊒ .(In (inj₁ tt)) tt refl = (In (inj₁ tt) , refl , Data.Unit.tt)

mapR-computation-cons-⊑ : {A B : Set} {R : B ← A}
               → (mapR R) ○ cons ⊑ cons ○ bimapR (arg₁ ⊗ arg₂) R (mapR R)
mapR-computation-cons-⊑ (In (inj₁ tt)) (fst x , snd xs) (In (inj₁ tt) , () , _)
mapR-computation-cons-⊑ (In (inj₁ tt)) (fst x , snd xs) (In (inj₂ _) , _ , ())
mapR-computation-cons-⊑ (In (inj₂ (fst y , snd ys))) (fst x , snd xs) (.(In (inj₂ (fst x , snd xs))) , refl , ysmapRxs)
  = ((fst y , snd ys) , ysmapRxs , refl)

mapR-computation-cons-⊒ : {A B : Set} {R : B ← A}
                         → cons ○ bimapR (arg₁ ⊗ arg₂) R (mapR R) ⊑ (mapR R) ○ cons
mapR-computation-cons-⊒ (In (inj₁ tt)) xs ((fst _ , snd _) , _ , ())
mapR-computation-cons-⊒ (In (inj₂ (fst y , snd ys))) (fst x , snd xs) ((fst .y , snd .ys) , ysmapRxs , refl)
  = (In (inj₂ (fst x , snd xs)) , refl , ysmapRxs)

fuse-cond : {A : Set} → (p : ℙ A) → [ nil , (nil ○ !) ⊔ (cons ○ bimapR (arg₁ ⊗ arg₂) (p ¿) idR) ] ○ bimapR ListF idR (mapR (p ¿)) ⊑ mapR (p ¿) ○ [ nil , (nil ○ !) ⊔ cons ]
fuse-cond p =
  ⊑-begin
    [ nil , (nil ○ !) ⊔ (cons ○ bimapR (arg₁ ⊗ arg₂) (p ¿) idR) ] ○ bimapR ListF idR (mapR (p ¿))
  ⊑⟨ [,]-⊕-absorption-⊑ ⟩
    [ nil ○ bimapR one idR (mapR (p ¿)) , ((nil ○ !) ⊔ (cons ○ bimapR (arg₁ ⊗ arg₂) (p ¿) idR)) ○ bimapR (arg₁ ⊗ arg₂) idR (mapR (p ¿)) ]
  ⊑⟨ [,]-monotonic nil-bimap⊑nil ⊑-refl ⟩
    [ nil , ((nil ○ !) ⊔ (cons ○ bimapR (arg₁ ⊗ arg₂) (p ¿) idR)) ○ bimapR (arg₁ ⊗ arg₂) idR (mapR (p ¿)) ]
  ⊑⟨ [,]-monotonic ⊑-refl ○-⊔-distr-r-⊑ ⟩
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
 where nil-bimap⊑nil : nil ○ bimapR one idR (mapR (p ¿)) ⊑ nil
       nil-bimap⊑nil (In (inj₁ tt)) tt (tt , Data.Unit.tt , refl) = refl
       nil-bimap⊑nil (In (inj₂ xs)) tt (_ , _ , ())


takeWhile-der : {A : Set} → (p : ℙ A) → foldR ListF [ nil , (nil ○ !) ⊔ (cons ○ bimapR (arg₁ ⊗ arg₂) (p ¿) idR) ] ⊑ (mapR (p ¿) ○ _≼_) ↾ _≽_
takeWhile-der = {!!}

