module Examples.GC.Relations where

open import Data.Unit using (⊤)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂; _⊎_)
open import Sets
open import Relations
open import Data.Generic
open import AlgebraicReasoning.Relations


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

bimapR-one⊑idR : {A₁ B₁ A₂ B₂ : Set} {R : B₁ ← A₁} {S : B₂ ← A₂}
                → bimapR one R S ⊑ idR
bimapR-one⊑idR tt tt _ = refl

bimapR-one⊒idR : {A₁ B₁ A₂ B₂ : Set} {R : B₁ ← A₁} {S : B₂ ← A₂}
                → bimapR one R S ⊒ idR
bimapR-one⊒idR tt tt _ = Data.Unit.tt


! : ∀ {i} {A : Set i} → (One {i} ← A)
! = fun (λ _ → tt)

!-fusion-⊑ : ∀ {i} {A B : Set i} {R : A ← B ⊣ i}
           → ! ○ R ⊑ !
!-fusion-⊑ tt b (a , bRa , refl) = refl

!-fusion-⊒ : ∀ {i} {A B : Set i} {R : A ← B ⊣ i}
           → idR ⊑ (R ˘) ○ R → ! ⊑ ! ○ R
!-fusion-⊒ R-entire tt b refl with R-entire b b refl
... | (a , aRb , _) = (a , aRb , refl)
