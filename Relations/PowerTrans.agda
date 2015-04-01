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

Λ∈-galois-1 : ∀ {i j} {A : Set i} {B : Set j} 
              → {R : A → ℙ B} {S : B ← A}
              → ∈ ₁∘ R ⊑ S → R ⊑ Λ S
Λ∈-galois-1 R⊑S a b bRa = R⊑S b a bRa 

Λ∈-galois-2 : ∀ {i j} {A : Set i} {B : Set j} 
              → {R : A → ℙ B} {S : B ← A}
              → R ⊑ Λ S → ∈ ₁∘ R ⊑ S
Λ∈-galois-2 R⊑S a b bRa = R⊑S b a bRa 

Λ∈-cancelation : ∀ {i j} {A : Set i} {B : Set j} 
                 → (r : A → ℙ B)
                 → Λ(∈ ₁∘ r) ⊑ r
Λ∈-cancelation _ _ _ aRb = aRb

∈Λ-cancelation : ∀ {i j} {A : Set i} {B : Set j}
                 → (R : B ← A) → (∈ ₁∘ (Λ R) ⊑ R)
∈Λ-cancelation _ _ _ aRb = aRb

Λ-monotonic : ∀ {i j} {A : Set i} {B : Set j} {R S : B ← A} 
              → (R ⊑ S) → (Λ R ⊑ Λ S)
Λ-monotonic R⊑S a b bRa = R⊑S b a bRa  

ℰΛ-absorption-⊇ : ∀ {i j} {A : Set i} {B C : Set j} 
                  → (R : C ← B ⊣ j) (S : B ← A) →
     (a : A) → Λ(R ○ S) a ⊆ ℰ R (Λ S a)
ℰΛ-absorption-⊇ _ _ _ _ c∈ΛR○Sa = c∈ΛR○Sa

ℰΛ-absorption-⊆ : ∀ {i j} {A : Set i} {B C : Set j} 
                  → (R : C ← B ⊣ j) (S : B ← A) 
                  → (a : A) → ℰ R (Λ S a) ⊆ Λ(R ○ S) a
ℰΛ-absorption-⊆ _ _ _ _ c∈ΛR○Sa = c∈ΛR○Sa

ℰ-monotonic : ∀ {i} {A B : Set i} {R S : B ← A ⊣ i} →
    (R ⊑ S) →  (ℰ R ⊑ ℰ S)
ℰ-monotonic {R = R}{S} R⊑S = Λ-monotonic R∈⊑S∈
  where R∈⊑S∈ : R ○ ∈ ⊑ S ○ ∈
        R∈⊑S∈ = ○-monotonic-l R⊑S

ℰ-monotonic' : ∀ {i} {A B : Set i} {R : B ← A ⊣ i} {s t : ℙ A} →
    (s ⊆ t) →  (ℰ R s ⊆ ℰ R t)
ℰ-monotonic' s⊆t b (a , a∈s , bRa) = (a , s⊆t a a∈s , bRa) 

ℰ-functor-⊆ : ∀ {i} {A B C : Set i} → {R : B ← A ⊣ i} →
      {S : C ← B} → ∀ {a : ℙ A} →
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

ℰ-functor-⊇ : ∀ {i} {A B C : Set i} → {R : B ← A ⊣ i} →
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
