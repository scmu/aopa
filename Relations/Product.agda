{-# OPTIONS --universe-polymorphism #-}

module Relations.Product where

open import Level
open import Data.Sum      using (_⊎_)
open import Data.Product  using (Σ; _×_; _,_; proj₁ ; proj₂) 
                       renaming (map to map-×)
open import Function using (_∘_; id)

open import Sets
open import Relations

open import AlgebraicReasoning.Relations
     using (⊑-begin_; _⊑⟨_⟩_; _⊑∎)

⨉-functor-⊒ : ∀ {i j k l} {A : Set} {B : Set i} {C : Set} {D : Set j}
                         {E : Set k} {F : Set l} 
              → {R : B ← A} {S : D ← C} {T : A ← E} {U : C ← F}
              → (R ⨉ S) ○ (T ⨉ U) ⊒ ((R ○ T) ⨉ (S ○ U)) 
⨉-functor-⊒ (e , f) (b , d) ((a , aTe , bRa) , (c , cUf , dSc)) = 
    ((a , c) , (aTe , cUf) , (bRa , dSc))

⨉-functor-⊑ : ∀ {i j k l} {A : Set} {B : Set i} {C : Set} {D : Set j}
                         {E : Set k} {F : Set l}
              → {R : B ← A} {S : D ← C} {T : A ← E} {U : C ← F} 
              → (R ⨉ S) ○ (T ⨉ U) ⊑ ((R ○ T) ⨉ (S ○ U))
⨉-functor-⊑ (e , f) (b , d) ((a , c) , (aTe , cUf) , (bRa , dSc)) = 
     ((a , aTe , bRa) , (c , cUf , dSc))

⨉3-functor-⊒ : {A B C D E F G H I : Set} →
  {R : B ← A} {S : D ← C} {T : F ← E} {U : A ← G} →
      {V : C ← H} → {W : E ← I} →
        (R ⨉ S ⨉ T) ○ (U ⨉ V ⨉ W) ⊒ ((R ○ U) ⨉ (S ○ V) ⨉ (T ○ W))
⨉3-functor-⊒ (g , h , i) (b , d , f) 
  ((a , aUg , bRa) , (c , cVh , dSc) , (e , eWi , fTe)) = 
    ((a , c , e) , (aUg , cVh , eWi) , (bRa , dSc , fTe))

⨉3-functor-⊑ : {A B C D E F G H I : Set} →
  {R : B ← A} {S : D ← C} {T : F ← E} {U : A ← G} →
      {V : C ← H} → {W : E ← I} →
        (R ⨉ S ⨉ T) ○ (U ⨉ V ⨉ W) ⊑ ((R ○ U) ⨉ (S ○ V) ⨉ (T ○ W))
⨉3-functor-⊑ (g , h , i) (b , d , f) 
  ((a , c , e) , (aUg , cVh , eWi) , (bRa , dSc , fTe)) =
    ((a , aUg , bRa) , (c , cVh , dSc) , (e , eWi , fTe)) 

⨉-id-⊑ : {A B : Set} → (idR ⨉ idR) ⊑ idR {A × B} 
⨉-id-⊑ (a , b) (a' , b') (p , q) with p | q
⨉-id-⊑ (a , b) (.a , .b) (p , q) | refl | refl = refl

{-
⨉₁-functor : {A B : Set} {C : Set1} {D E : Set}
  (R : B ← A) → (T : E ← D) → (U : D ←₁ C) → 
     (R ⨉₁ (T ○₁ U)) ⊑₁ (R ⨉ T) ○₁ (idR ⨉₁ U)
⨉₁-functor _ _ _ (b , e) (a ,₁ c) (bRa , (d , dUc , eTd)) = 
        ((a , d) , ({!!} , dUc) , (bRa , eTd)) -}

⨉-monotonic : {A B C D : Set} -- ∀ {i j k l} {A : Set i} {B : Set j} {C : Set k} {D : Set l}
              → {R S : B ← A} {T U : D ← C}
              → R ⊑ S → T ⊑ U → (R ⨉ T) ⊑ (S ⨉ U)
⨉-monotonic R⊑S T⊑U (b , d) (a , c) (bRa , dTc) 
  = (R⊑S b a bRa , T⊑U d c dTc) 

⨉3-id-⊑ : {A B C : Set} → (idR ⨉ idR ⨉ idR) ⊑ idR {A × B × C} 
⨉3-id-⊑ {A} {B} {C} = 
   ⊑-begin
       (idR ⨉ idR ⨉ idR)
   ⊑⟨ ⨉-monotonic {R = idR} ⊑-refl ⨉-id-⊑ ⟩
       (idR ⨉ idR)
   ⊑⟨ ⨉-id-⊑ ⟩
       idR
   ⊑∎ 

-- identical to Relations.Converse.˘-⨉-distr-⊒
˘-dist-⨉ : ∀ {i j k l} {A : Set i} {B : Set j} {C : Set k} {D : Set l} {R : B ← A} {S : D ← C} →
   (R ˘ ⨉ S ˘) ⊑ (R ⨉ S)˘ 
˘-dist-⨉ (b , d) (a , c) (bRa , dSc) = (bRa , dSc) 

-- The rules below are simply identity functions. Thus
-- Agda can derive them itself and they are not really necessary.

Λ⨉-absorption-⊆ : ∀ {i} {A : Set} {B : Set i} {C : Set} (T : C ← (A × C)) (X : C ← B) →
               (a : A) → (b : B) →
               Λ (T ○ (idR ⨉ ∈)) (a , Λ X b)
             ⊆ Λ (T ○ (idR ⨉ X)) (a , b)
Λ⨉-absorption-⊆ T X a b c ((a' , c') , pf) =  ((a' , c') , pf)

Λ⨉-absorption-⊇ : ∀ {i} {A : Set} {B : Set i} {C : Set} (T : C ← (A × C)) (X : C ← B) →
               (a : A) → (b : B) →
               Λ (T ○ (idR ⨉ ∈)) (a , Λ X b)
             ⊇ Λ (T ○ (idR ⨉ X)) (a , b)
Λ⨉-absorption-⊇ T X a b c ((a' , c') , pf) = ((a' , c') , pf) 
{-
Λ₁⨉₁-absorption : {A B C : Set} (T : C ← (A × C)) (X : C ←₁ ℙ B) →
               (a : A) → (bs : ℙ B) →
               Λ₁(T ○₁ (idR ⨉₁ ∈)) (a ,₁ Λ₁ X bs)
             ⊆ Λ₁(T ○₁ (idR ⨉₁ X)) (a ,₁ bs)
Λ₁⨉₁-absorption T X a bs c ((a' , c') , pf) = ((a' , c') , pf)
-}

Λ⨉⨉-absorption-⊆ : {A B C D E F : Set} (T : F ← (A × D × E)) →
     (X : D ← B) → (Y : E ← C) → 
         (a : A) → (b : B) → (c : C) →
               Λ (T ○ (idR ⨉ ∈ ⨉ ∈)) (a , Λ X b , Λ Y c)
             ⊆ Λ (T ○ (idR ⨉ X ⨉ Y)) (a , b , c)
Λ⨉⨉-absorption-⊆ T X Y a b c f ((a' , d , e) , pf) = 
        ((a' , d , e) , pf)  

Λ⨉⨉-absorption-⊇ : {A B C D E F : Set} (T : F ← (A × D × E)) →
     (X : D ← B) → (Y : E ← C) → 
         (a : A) → (b : B) → (c : C) →
               Λ (T ○ (idR ⨉ ∈ ⨉ ∈)) (a , Λ X b , Λ Y c)
             ⊇ Λ (T ○ (idR ⨉ X ⨉ Y)) (a , b , c)
Λ⨉⨉-absorption-⊇ T X Y a b c f ((a' , d , e) , pf) = 
        ((a' , d , e) , pf)  

-- These rules should be decomposed into more primitive lemmas.

Λ⨉-monotonic : {A B C : Set} {s t : ℙ B} (T : C ← (A × B)) → s ⊆ t →
               forall a →    Λ (T ○ (idR ⨉ ∈)) (a , s)
                            ⊆ Λ (T ○ (idR ⨉ ∈)) (a , t)
Λ⨉-monotonic _ s⊆t a x 
     ((a' , b') , (a≡a' ,        sb') , T<a',b'>x) =
       ((a' , b') , (a≡a' , s⊆t b' sb') , T<a',b'>x)

Λ⨉⨉-monotonic : {A B C D : Set}{s t : ℙ B}{u v : ℙ C}
       (T : D ← (A × B × C)) → s ⊆ t → u ⊆ v →
               forall a →    Λ (T ○ (idR ⨉ ∈ ⨉ ∈)) (a , s , u)
                            ⊆ Λ (T ○ (idR ⨉ ∈ ⨉ ∈)) (a , t , v)
Λ⨉⨉-monotonic _ s⊆t u⊆v a x 
     ((a' , b' , c') , (a≡a' , b'∈s , c'∈u) , xT<a'b'c'>)
   =  ((a' , b' , c') , (a≡a' , s⊆t b' b'∈s , u⊆v c' c'∈u) , xT<a'b'c'>) 
