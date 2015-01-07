{-# OPTIONS --universe-polymorphism #-}

module Relations.PowerTrans where

open import Level renaming (_⊔_ to _⊔l_)
open import Data.Sum      using (_⊎_)
open import Data.Product  using (_×_; _,_)
open import Function using (_∘_; id)

open import Sets
open import Relations

open import AlgebraicReasoning.Sets
     using (⊆-begin_; _⊆⟨_⟩_; _⊆∎;
            ⊇-begin_; _⊇⟨_⟩_; _⊇∎)

Λ∈-galois-1 : {A B : Set} {R : A → ℙ B} {S : B ← A} →
              ∈ ₁∘ R ⊑ S → R ⊑ Λ S
Λ∈-galois-1 R⊑S a b bRa = R⊑S b a bRa 

Λ∈-galois-2 : {A B : Set} {R : A → ℙ B} {S : B ← A} →
               R ⊑ Λ S → ∈ ₁∘ R ⊑ S
Λ∈-galois-2 R⊑S a b bRa = R⊑S b a bRa 

Λ∈-cancelation : {A B : Set} → (r : A → ℙ B) → 
                 Λ(∈ ₁∘ r) ⊑ r
Λ∈-cancelation _ _ _ aRb = aRb

∈Λ-cancelation : {A B : Set} → (R : B ← A) → (∈ ₁∘ (Λ R) ⊑ R)
∈Λ-cancelation _ _ _ aRb = aRb

Λ-monotonic : ∀ {i} {A : Set i} {B : Set} {R S : B ← A} →
    (R ⊑ S) →  (Λ R ⊑ Λ S)
Λ-monotonic R⊑S a b bRa = R⊑S b a bRa  
{-
Λ-monotonic : {A : Set1} {B : Set} {R S : B ← A} →
    (R ⊑ S) →  (Λ R ⊑ Λ S)
Λ-monotonic R⊑S a b bRa = R⊑S b a bRa  -}

ℰΛ-absorption-⊇ : {A : Set1} {B C : Set} → 
   (R : C ← B) → (S : B ← A) →
     (a : A) → Λ(R ○ S) a ⊆ ℰ R (Λ S a)
ℰΛ-absorption-⊇ _ _ _ _ c∈ΛR○Sa = c∈ΛR○Sa

ℰΛ-absorption-⊆ : {A : Set1} {B C : Set} → 
   (R : C ← B) → (S : B ← A) →
      (a : A) → ℰ R (Λ S a) ⊆ Λ(R ○ S) a
ℰΛ-absorption-⊆ _ _ _ _ c∈ΛR○Sa = c∈ΛR○Sa

ℰ-monotonic : {A B : Set} {R S : B ← A} →
    (R ⊑ S) →  (ℰ R ⊑ ℰ S)
ℰ-monotonic {A}{B}{R}{S} R⊑S = Λ-monotonic R∈⊑S∈
  where R∈⊑S∈ : R ○ ∈ ⊑ S ○ ∈
        R∈⊑S∈ = ○-monotonic-l R⊑S

ℰ-monotonic' : {A B : Set} {R : B ← A} {s t : ℙ A} →
    (s ⊆ t) →  (ℰ R s ⊆ ℰ R t)
ℰ-monotonic' s⊆t b (a , a∈s , bRa) = (a , s⊆t a a∈s , bRa) 

ℰ-functor-⊆ : {A B C : Set} → {R : B ← A} →
      {S : C ← B} → ∀ {a} →
         ℰ S (ℰ R a) ⊆ ℰ (S ○ R) a 
ℰ-functor-⊆ {R = R} {S} {a} =
   ⊆-begin
       ℰ S (ℰ R a)
   ⊆⟨ ⊆-refl ⟩
       ℰ S (Λ (R ○ ∈) a)
   ⊆⟨ ℰΛ-absorption-⊆ S (R ○ ∈) a ⟩
       Λ (S ○ (R ○ ∈)) a
   ⊆⟨ Λ-monotonic (○-assocl {T = ∈}) a ⟩
       Λ ((S ○ R) ○ ∈) a
   ⊆⟨ ⊆-refl ⟩
       ℰ (S ○ R) a
   ⊆∎

ℰ-functor-⊇ : {A B C : Set} → {R : B ← A} →
      {S : C ← B} → ∀ {a} →
         ℰ S (ℰ R a) ⊇ ℰ (S ○ R) a 
ℰ-functor-⊇ {R = R} {S} {a} =
   ⊇-begin
       ℰ S (ℰ R a)
   ⊇⟨ ⊇-refl ⟩
       ℰ S (Λ (R ○ ∈) a)
   ⊇⟨ ℰΛ-absorption-⊇ S (R ○ ∈) a ⟩
       Λ (S ○ (R ○ ∈)) a
   ⊇⟨ Λ-monotonic (○-assocr {T = ∈}) a ⟩
       Λ ((S ○ R) ○ ∈) a
   ⊇⟨ ⊇-refl ⟩
       ℰ (S ○ R) a
   ⊇∎
