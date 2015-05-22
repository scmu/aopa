-- Two "monotype factors", suggested by Doornbos and Backhouse, et al.

module Relations.MonoFactor where

open import Level renaming (_⊔_ to _⊔ℓ_)
open import Data.Product  using (_×_; _,_; ∃; Σ)

open import Sets
open import Relations
open import Relations.Coreflexive
open import AlgebraicReasoning.Equivalence using (_⇔_)
open import AlgebraicReasoning.Implications
       using (⇐-begin_; _⇐⟨_⟩_; _⇐∎;
              ⇒-begin_; _⇒⟨_⟩_; _⇒∎ )

-- ranges.

ran : ∀ {i} {A B : Set i}
      → (B ← A ⊣ i) → ℙ B
ran R b = ∃ (λ a → R b a)

ran-universal-⇒ : ∀ {i} {A B : Set i}
                → (R : B ← A ⊣ i) → (P : ℙ B)
                → ran R ⊆ P → R ⊑ P ¿ ○ R
ran-universal-⇒ R P <R⊆P b a bRa = b , bRa , refl , <R⊆P b (a , bRa)

ran-universal-⇐ : ∀ {i} {A B : Set i}
                → (R : B ← A ⊣ i) → (P : ℙ B)
                → R ⊑ P ¿ ○ R → ran R ⊆ P 
ran-universal-⇐ R P R⊑PR b (a , bRa) with R⊑PR b a bRa 
ran-universal-⇐ R P R⊑PR b (a , bRa) | ._ , _ , refl , Pb = Pb

ran-universal : ∀ {i} {A B : Set i}
                → (R : B ← A ⊣ i) → (P : ℙ B)
                → (ran R ⊆ P) ⇔ (R ⊑ P ¿ ○ R)
ran-universal R P = (ran-universal-⇒ R P , ran-universal-⇐ R P)

ran-cancellation : ∀ {i} {A B : Set i}
                 → (R : B ← A ⊣ i)
                 → R ⊑ (ran R) ¿ ○ R
ran-cancellation R = ran-universal-⇒ R (ran R) ⊆-refl                 
                 
-- monotype factor.

_⍀_ : ∀ {i}{A B : Set i}
      → (B ← A ⊣ i) → ℙ B → ℙ A
(R ⍀ P) a = ∀ b → R b a → P b

-- universal property:
--   Q ⊆ R ⍀ P  ≡ ran (R ∘ Q) ⊆ P

⍀-universal-⇒ : ∀ {i} {A B : Set i}
                → (R : B ← A ⊣ i) → (Q : ℙ A) → (P : ℙ B)
                → Q ⊆ R ⍀ P → ran (R ○ Q ¿) ⊆ P
⍀-universal-⇒ R Q P Q⊆R⍀P b (a , ._ , (refl , Qa) , bRa) = Q⊆R⍀P a Qa b bRa                

⍀-universal-⇐ : ∀ {i} {A B : Set i}
                → (R : B ← A ⊣ i) → (Q : ℙ A) → (P : ℙ B)
                → ran (R ○ Q ¿) ⊆ P → Q ⊆ R ⍀ P
⍀-universal-⇐ R Q P <RQ⊆P a Qa b bRa = <RQ⊆P b (a , a , (refl , Qa) , bRa)

⍀-universal : ∀ {i} {A B : Set i}
              → (R : B ← A ⊣ i) → (Q : ℙ A) → (P : ℙ B)
              → (Q ⊆ R ⍀ P) ⇔ (ran (R ○ Q ¿) ⊆ P)
⍀-universal R Q P = ⍀-universal-⇒ R Q P , ⍀-universal-⇐ R Q P

⍀-cancellation : ∀ {i} {A B : Set i}
                 → (R : B ← A ⊣ i) → (P : ℙ B)
                 → R ○ (R ⍀ P) ¿ ⊑ P ¿ ○ R
⍀-cancellation R P =
      (⇒-begin
         ran (R ○ (R ⍀ P) ¿) ⊆ P
       ⇒⟨ ran-universal-⇒ (R ○ (R ⍀ P) ¿) P ⟩
         R ○ (R ⍀ P) ¿ ⊑ P ¿ ○ R ○ (R ⍀ P) ¿
       ⇒⟨ ⊒-trans (○-monotonic-r (corefl-intro-r (set-corefl⊑idR _))) ⟩
         R ○ (R ⍀ P) ¿ ⊑ P ¿ ○ R
       ⇒∎) (⍀-universal-⇒ R (R ⍀ P) P ⊆-refl)

-- The "second factor", defined in Doornbos and Backhouse 1995.

_⋱_ : ∀ {i} {A B : Set i}
      → (B ← A ⊣ i) → (B ← A ⊣ i) → ℙ A
(R ⋱ S) a = ∀ b → R b a → S b a

⋱-universal-⇒ : ∀ {i} {A B : Set i}
               → (P : ℙ A) → (R S : B ← A ⊣ i)
               → P ⊆ R ⋱ S → R ○ P ¿ ⊑ S
⋱-universal-⇒ P R S P⊆R⋱S b a (._ , (refl , Pa) , bRa) = P⊆R⋱S a Pa b bRa

⋱-universal-⇐ : ∀ {i} {A B : Set i}
               → (P : ℙ A) → (R S : B ← A ⊣ i)
               → R ○ P ¿ ⊑ S → P ⊆ R ⋱ S 
⋱-universal-⇐ P R S RP⊑S a Pa b bRa = RP⊑S b a (a , (refl , Pa) , bRa)

⋱-universal : ∀ {i} {A B : Set i}
             → (P : ℙ A) → (R S : B ← A ⊣ i)
             → (P ⊆ R ⋱ S) ⇔ (R ○ P ¿ ⊑ S)
⋱-universal P R S = (⋱-universal-⇒ P R S , ⋱-universal-⇐ P R S)               

⋱-cancellation : ∀ {i} {A B : Set i}
                → (R S : B ← A ⊣ i) 
                → R ○ (R ⋱ S) ¿ ⊑ S
⋱-cancellation R S = ⋱-universal-⇒ (R ⋱ S) R S ⊆-refl

