{-# OPTIONS --universe-polymorphism #-}

module Relations.Factor where

open import Level
open import Data.Product  using (_×_; _,_)

open import Sets
open import Relations
open import AlgebraicReasoning.Implications using (_⇔_; ⇐-begin_; _⇐⟨_⟩_; _⇐∎)

_/_ : ∀ {i j k l m} {A : Set i} {B : Set j} {C : Set k} 
      → (B ← A ⊣ l) → (C ← A ⊣ m) → (B ← C) 
(R / S) b c = ∀ a → S c a → R b a

-- /-universal : R ○ S ⊑ T  ⇔  R ⊑ T / S

/-universal-⇒ : ∀ {i j} {A B : Set i} {C : Set j}
                → {R : C ← B ⊣ i} {S : B ← A ⊣ i} {T : C ← A}
                → R ○ S ⊑ T → R ⊑ T / S
/-universal-⇒ RS⊑T c b cRb a bSa = RS⊑T c a (b , bSa , cRb)

/-universal-⇐ : ∀ {i j} {A B : Set i} {C : Set j}
                → {R : C ← B ⊣ i} {S : B ← A ⊣ i} {T : C ← A}
                → R ⊑ T / S →  R ○ S ⊑ T 
/-universal-⇐ R⊑T/S c a (b , bSa , cRb) = R⊑T/S c b cRb a bSa

/-universal : ∀ {i j} {A B : Set i} {C : Set j}
              → {R : C ← B ⊣ i} {S : B ← A ⊣ i} {T : C ← A}
              → R ○ S ⊑ T  ⇔  R ⊑ T / S
/-universal = (/-universal-⇒ , /-universal-⇐)

/-monotonic : ∀ {i j} {A B : Set i} {C : Set j}
              → {R S : C ← A ⊣ i} {T : B ← A ⊣ i} 
              → R ⊑ S → R / T ⊑ S / T
/-monotonic {R = R} {S} {T} =
  ⇐-begin
    R / T ⊑ S / T
  ⇐⟨ /-universal-⇒ ⟩
    (R / T) ○ T ⊑ S
  ⇐⟨ ⊑-trans {R = (R / T) ○ T} (/-universal-⇐ {R = R / T} ⊑-refl) ⟩
    R ⊑ S
  ⇐∎

/-anti-monotonic : ∀ {i j} {A B : Set i} {C : Set j}
                   → {R S : B ← A ⊣ i} {T : C ← A ⊣ i} 
                   → R ⊑ S → T / R ⊒ T / S
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

_﹨_ : ∀ {i j k l m} {A : Set i} {B : Set j} {C : Set k} 
      → (B ← A ⊣ l) → (B ← C ⊣ m) → (A ← C)
R ﹨ S = ((S ˘) / (R ˘)) ˘

/∋○Λ-cancelation-⊒ : ∀ {i j k l} {A : Set i} {B : Set j} {C : Set k} 
                     → (R : B ← A ⊣ l) → (S : A ← C ⊣ i)
                     → R / ∋ ₁∘ Λ S ⊒ R / S ˘
/∋○Λ-cancelation-⊒ R S b c aSc⇒bRa aSc = aSc⇒bRa aSc 

/∋○Λ-cancelation-⊑ : ∀ {i j k l} {A : Set i} {B : Set j} {C : Set k} 
                     → (R : B ← A ⊣ l) → (S : A ← C ⊣ i) 
                     → R / ∋ ₁∘ Λ S ⊑ R / S ˘
/∋○Λ-cancelation-⊑ R S b c aSc⇒bRa aSc = aSc⇒bRa aSc
