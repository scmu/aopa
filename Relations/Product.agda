{-# OPTIONS --universe-polymorphism #-}

module Relations.Product where

open import Level renaming (_⊔_ to _⊔ℓ_)
open import Data.Sum      using (_⊎_)
open import Data.Product  using (Σ; _×_; _,_; proj₁ ; proj₂) 
                       renaming (map to map-×)
open import Function using (_∘_; id)

open import Sets
open import Relations

open import AlgebraicReasoning.Relations
     using (⊑-begin_; _⊑⟨_⟩_; _⊑∎)

⨉-functor-⊒ : ∀ {i j k l m n o p} {A : Set} {B : Set i} {C : Set} 
                {D : Set j} {E : Set k} {F : Set l} 
              → {R : B ← A ⊣ m} {S : D ← C ⊣ n} {T : A ← E ⊣ o} {U : C ← F ⊣ p}
              → (R ⨉ S) ○ (T ⨉ U) ⊒ ((R ○ T) ⨉ (S ○ U)) 
⨉-functor-⊒ (e , f) (b , d) ((a , aTe , bRa) , (c , cUf , dSc)) = 
    ((a , c) , (aTe , cUf) , (bRa , dSc))

⨉-functor-⊑ : ∀ {i j k l m n o p} {A : Set} {B : Set i} {C : Set} 
                {D : Set j} {E : Set k} {F : Set l}
              → {R : B ← A ⊣ m} {S : D ← C ⊣ n} {T : A ← E ⊣ o} {U : C ← F ⊣ p} 
              → (R ⨉ S) ○ (T ⨉ U) ⊑ ((R ○ T) ⨉ (S ○ U))
⨉-functor-⊑ (e , f) (b , d) ((a , c) , (aTe , cUf) , (bRa , dSc)) = 
     ((a , aTe , bRa) , (c , cUf , dSc))

⨉3-functor-⊒ : ∀ {l₀ l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃ l₁₄}  
                 {A : Set l₀} {B : Set l₁} {C : Set l₂} {D : Set l₃} {E : Set l₄} 
                 {F : Set l₅} {G : Set l₆} {H : Set l₇} {I : Set l₈} →
                 {R : B ← A ⊣ l₉} {S : D ← C ⊣ l₁₀} {T : F ← E ⊣ l₁₁} {U : A ← G ⊣ l₁₂} →
                 {V : C ← H ⊣ l₁₃} {W : E ← I ⊣ l₁₄} →
               (R ⨉ S ⨉ T) ○ (U ⨉ V ⨉ W) ⊒ ((R ○ U) ⨉ (S ○ V) ⨉ (T ○ W))
⨉3-functor-⊒ (g , h , i) (b , d , f) 
  ((a , aUg , bRa) , (c , cVh , dSc) , (e , eWi , fTe)) = 
    ((a , c , e) , (aUg , cVh , eWi) , (bRa , dSc , fTe))

⨉3-functor-⊑ : ∀ {l₀ l₁ l₂ l₃ l₄ l₅ l₆ l₇ l₈ l₉ l₁₀ l₁₁ l₁₂ l₁₃ l₁₄}  
                 {A : Set l₀} {B : Set l₁} {C : Set l₂} {D : Set l₃} {E : Set l₄} 
                 {F : Set l₅} {G : Set l₆} {H : Set l₇} {I : Set l₈} →
                 {R : B ← A ⊣ l₉} {S : D ← C ⊣ l₁₀} {T : F ← E ⊣ l₁₁} {U : A ← G ⊣ l₁₂} →
                 {V : C ← H ⊣ l₁₃} {W : E ← I ⊣ l₁₄} →
               (R ⨉ S ⨉ T) ○ (U ⨉ V ⨉ W) ⊑ ((R ○ U) ⨉ (S ○ V) ⨉ (T ○ W))
⨉3-functor-⊑ (g , h , i) (b , d , f) 
  ((a , c , e) , (aUg , cVh , eWi) , (bRa , dSc , fTe)) =
    ((a , aUg , bRa) , (c , cVh , dSc) , (e , eWi , fTe)) 

⨉-id-⊑ : ∀ {i j} {A : Set i} {B : Set j} → (idR ⨉ idR) ⊑ idR {A = A × B} 
⨉-id-⊑ (a , b) (a' , b') (p , q) with p | q
⨉-id-⊑ (a , b) (.a , .b) (p , q) | refl | refl = refl

⨉-monotonic : ∀ {i j k l m n} {A : Set i} {B : Set j} {C : Set k} {D : Set l}
              → {R S : B ← A ⊣ m} {T U : D ← C ⊣ n}
              → R ⊑ S → T ⊑ U → (R ⨉ T) ⊑ (S ⨉ U)
⨉-monotonic R⊑S T⊑U (b , d) (a , c) (bRa , dTc) 
  = (R⊑S b a bRa , T⊑U d c dTc) 

⨉3-id-⊑ : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k} 
          → (idR ⨉ idR ⨉ idR) ⊑ idR {A = A × B × C} 
⨉3-id-⊑ {i} {j} {k} {A} {B} {C} = 
   ⊑-begin
       (idR {i} ⨉ idR {j} ⨉ idR {k})
   ⊑⟨ ⨉-monotonic {R = idR} (⊑-refl {i}{i}{i}) ⨉-id-⊑ ⟩
       (idR {i} ⨉ idR {j ⊔ℓ k})
   ⊑⟨ ⨉-id-⊑ ⟩
       idR
   ⊑∎ 

-- identical to Relations.Converse.˘-⨉-distr-⊒
˘-dist-⨉ : ∀ {i j k l m n} {A : Set i} {B : Set j} {C : Set k} {D : Set l} 
             {R : B ← A ⊣ m} {S : D ← C ⊣ n} →
           (R ˘ ⨉ S ˘) ⊑ (R ⨉ S)˘ 
˘-dist-⨉ (b , d) (a , c) (bRa , dSc) = (bRa , dSc) 

-- The rules below are simply identity functions. Thus
-- Agda can derive them itself and they are not really necessary.

Λ⨉-absorption-⊆ : ∀ {i j} {A : Set i} {B : Set j} {C : Set i} 
                  → (T : C ← (A × C) ⊣ i) (X : C ← B) 
                  → (a : A) → (b : B) 
                  →   Λ (T ○ (idR ⨉ ∈)) (a , Λ X b)
                    ⊆ Λ (T ○ (idR ⨉ X)) (a , b)
Λ⨉-absorption-⊆ T X a b c ((a' , c') , pf) =  ((a' , c') , pf)

Λ⨉-absorption-⊇ : ∀ {i j} {A : Set i} {B : Set j} {C : Set i} 
                  → (T : C ← (A × C) ⊣ i) (X : C ← B) 
                  → (a : A) → (b : B) 
                  →   Λ (T ○ (idR ⨉ ∈)) (a , Λ X b)
                    ⊇ Λ (T ○ (idR ⨉ X)) (a , b)
Λ⨉-absorption-⊇ T X a b c ((a' , c') , pf) = ((a' , c') , pf) 

Λ⨉⨉-absorption-⊆ : ∀ {i j} {A : Set i} {B C : Set j} {D E F : Set i} 
                   → (T : F ← (A × D × E) ⊣ i) → (X : D ← B) → (Y : E ← C) 
                   → (a : A) → (b : B) → (c : C) 
                   →   Λ (T ○ (idR ⨉ ∈ ⨉ ∈)) (a , Λ X b , Λ Y c)
                     ⊆ Λ (T ○ (idR ⨉ X ⨉ Y)) (a , b , c)
Λ⨉⨉-absorption-⊆ T X Y a b c f ((a' , d , e) , pf) = 
        ((a' , d , e) , pf)  

Λ⨉⨉-absorption-⊇ : ∀ {i j} {A : Set i} {B C : Set j} {D E F : Set i} 
                   → (T : F ← (A × D × E) ⊣ i) → (X : D ← B) → (Y : E ← C) 
                   → (a : A) → (b : B) → (c : C) 
                   →   Λ (T ○ (idR ⨉ ∈ ⨉ ∈)) (a , Λ X b , Λ Y c)
                     ⊇ Λ (T ○ (idR ⨉ X ⨉ Y)) (a , b , c)
Λ⨉⨉-absorption-⊇ T X Y a b c f ((a' , d , e) , pf) = 
        ((a' , d , e) , pf)  

-- These rules should be decomposed into more primitive lemmas.

Λ⨉-monotonic : ∀ {i} {A B C : Set i}
               → {s t : ℙ B} (T : C ← (A × B) ⊣ i) → s ⊆ t →
               forall a →    Λ (T ○ (idR ⨉ ∈)) (a , s)
                            ⊆ Λ (T ○ (idR ⨉ ∈)) (a , t)
Λ⨉-monotonic _ s⊆t a x 
     ((a' , b') , (a≡a' ,        sb') , T<a',b'>x) =
       ((a' , b') , (a≡a' , s⊆t b' sb') , T<a',b'>x)

Λ⨉⨉-monotonic : ∀ {i} {A B C D : Set i}{s t : ℙ B}{u v : ℙ C}
       (T : D ← (A × B × C) ⊣ i) → s ⊆ t → u ⊆ v →
               forall a →    Λ (T ○ (idR ⨉ ∈ ⨉ ∈)) (a , s , u)
                            ⊆ Λ (T ○ (idR ⨉ ∈ ⨉ ∈)) (a , t , v)
Λ⨉⨉-monotonic _ s⊆t u⊆v a x 
     ((a' , b' , c') , (a≡a' , b'∈s , c'∈u) , xT<a'b'c'>)
   =  ((a' , b' , c') , (a≡a' , s⊆t b' b'∈s , u⊆v c' c'∈u) , xT<a'b'c'>) 
