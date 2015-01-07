{-# OPTIONS --universe-polymorphism #-}

module Relations.Factor where

open import Level
open import Data.Product  using (_×_; _,_)

open import Sets
open import Relations
open import AlgebraicReasoning.Implications using (_⇔_; ⇐-begin_; _⇐⟨_⟩_; _⇐∎)

_/_ : ∀ {j k} {A : Set} {B : Set j} {C : Set k} → (B ← A) → (C ← A) → (B ← C) 
(R / S) b c = ∀ a → S c a → R b a

-- /-universal : R ○ S ⊑ T  ⇔  R ⊑ T / S

/-universal-⇒ : ∀ {i} {A : Set} {B : Set} {C : Set i} → 
   {R : C ← B} {S : B ← A} {T : C ← A} →
      R ○ S ⊑ T → R ⊑ T / S
/-universal-⇒ RS⊑T c b cRb a bSa = RS⊑T c a (b , bSa , cRb)

/-universal-⇐ : ∀ {i} {A : Set} {B : Set} {C : Set i} → 
   {R : C ← B} {S : B ← A} {T : C ← A} →
      R ⊑ T / S →  R ○ S ⊑ T 
/-universal-⇐ R⊑T/S c a (b , bSa , cRb) = R⊑T/S c b cRb a bSa

/-universal : ∀ {i} {A : Set} {B : Set} {C : Set i} → 
   {R : C ← B} {S : B ← A} {T : C ← A} →
      R ○ S ⊑ T  ⇔  R ⊑ T / S
/-universal = (/-universal-⇒ , /-universal-⇐)

/-monotonic : ∀ {i} {A B : Set} {C : Set i}
  {R S : C ← A} {T : B ← A} → R ⊑ S → R / T ⊑ S / T
/-monotonic {R = R} {S} {T} =
  ⇐-begin
    R / T ⊑ S / T
  ⇐⟨ /-universal-⇒ ⟩
    (R / T) ○ T ⊑ S
  ⇐⟨ ⊑-trans {R = (R / T) ○ T} (/-universal-⇐ {R = R / T} ⊑-refl) ⟩
    R ⊑ S
  ⇐∎

/-anti-monotonic : {A B C : Set}
  {R S : B ← A} {T : C ← A} → R ⊑ S → T / R ⊒ T / S
/-anti-monotonic {R = R} {S} {T} R⊑S =
 (⇐-begin
    T / S ⊑ T / R
  ⇐⟨ /-universal-⇒ ⟩
    (T / S) ○ R ⊑ T
  ⇐⟨ ⊑-trans (○-monotonic-r R⊑S) ⟩
    (T / S) ○ S ⊑ T
  ⇐⟨ ⊑-trans (/-universal-⇐ ⊑-refl) ⟩
    T ⊑ T
  ⇐∎) ⊑-refl

_﹨_ : ∀ {i j} {A : Set i} {B : Set} {C : Set j} → (B ← A) → (B ← C) → (A ← C)
R ﹨ S = ((S ˘) / (R ˘)) ˘

{-
-- (B ₁← A) / (C ← A)

_₁/_ : {A : Set}{B : Set1}{C : Set} → (B ₁← A) → (C ← A) → (B ₁← C) 
(R ₁/ S) b c = ∀ a → S c a → R b a

-- ₁/-universal-⇒ : R ₁○ S ₁⊑ T ⇔ R ₁⊑ T ₁/ S

₁/-universal-⇒ : {A B : Set}{C : Set1} → 
   {R : C ₁← B} {S : B ← A} {T : C ₁← A} →
      R ₁○ S ₁⊑ T → R ₁⊑ T ₁/ S
₁/-universal-⇒ RS⊑T c b cRb a bSa = RS⊑T c a (b , bSa , cRb)

₁/-universal-⇐ : {A B : Set}{C : Set1} → 
   {R : C ₁← B} {S : B ← A} {T : C ₁← A} →
      R ₁⊑ T ₁/ S →  R ₁○ S ₁⊑ T 
₁/-universal-⇐ R⊑T/S c a (b , bSa , cRb) = R⊑T/S c b cRb a bSa
-}

{-- I cannot define universal properties for the next few divisions,
    because I cannot talk about things like.
      R ○ S ⊑ T
    The LHS has kind Set1, while the RHS has kind Set --}

-- (B ← A) / (C ₁← A)
{-
_/₁_ : {A B : Set} {C : Set1} → (B ← A) → (C ₁← A) → (B ←₁ C) 
(R /₁ S) b c = ∀ a → S c a → R b a
-}
{-
_₁﹨_ : {A : Set1} {B C : Set} → (B ←₁ A) → (B ← C) → (A ₁← C) 
(R ₁﹨ S) = ((S ˘) /₁ (R ˘₁)) ˘₁
-}

/∋○Λ-cancelation-⊒ : {A B C : Set} → (R : B ← A) → (S : A ← C) →
     R / ∋ ₁∘ Λ S ⊒ R / S ˘
/∋○Λ-cancelation-⊒ R S b c aSc⇒bRa aSc = aSc⇒bRa aSc 

/∋○Λ-cancelation-⊑ : {A B C : Set} → (R : B ← A) → (S : A ← C) →
     R / ∋ ₁∘ Λ S ⊑ R / S ˘
/∋○Λ-cancelation-⊑ R S b c aSc⇒bRa aSc = aSc⇒bRa aSc


{-
-- (B ₁← A) / (C ₁← A) 

_₁/₁_ : {A : Set}{B C : Set1} → (B ₁← A) → (C ₁← A) → (B ₁←₁ C)
(R ₁/₁ S) b c = ∀ a → S c a → R b a

_₁﹨₁_ : {A : Set1}{B : Set}{C : Set1} →(B ←₁ A) → (B ←₁ C) → (A ₁←₁ C)
R ₁﹨₁ S = ((S ˘₁) ₁/₁ (R ˘₁)) ₁˘₁
-}