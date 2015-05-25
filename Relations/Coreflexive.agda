module Relations.Coreflexive where

open import Level
open import Data.Product
open import Sets
open import Relations
open import AlgebraicReasoning.Relations

-- coreflexives built from sets

_¿ : ∀ {i} {A : Set i} → ℙ A → (A ← A)
(p ¿) b a = (a ≡ b) × p a

set-corefl⊑idR : ∀ {i} {A : Set i} → (s : ℙ A) → s ¿ ⊑ idR
set-corefl⊑idR s b a (a≡b , bRa) = a≡b

-- coreflexives are idempotent: C ○ C ≑ C

corefl-idempotent-⊒ : ∀ {i} {A : Set i} {C : A ← A} → C ⊑ idR → C ○ C ⊒ C
corefl-idempotent-⊒ C⊑idR x y yCx with C⊑idR x y yCx
corefl-idempotent-⊒ C⊑idR x .x xCx | refl = x , xCx , xCx

corefl-idempotent-⊑ : ∀ {i} {A : Set i} {C : A ← A} → C ⊑ idR → C ○ C ⊑ C
corefl-idempotent-⊑ C⊑idR y x (z , zCx , yCz) with C⊑idR z x zCx | C⊑idR y z yCz
corefl-idempotent-⊑ C⊑idR x .x (.x , xCx , xCx') | refl | refl = xCx

-- Introducing a coreflexive relation. Sometimes
-- help to shorten the proof.

corefl-intro-r : ∀ {i j} {A : Set i} {B : Set j} {C : A ← A} {R : B ← A ⊣ i}
               → C ⊑ idR → R ○ C ⊑ R
corefl-intro-r {C = C} {R} C⊑idR =
  ⊑-begin
    R ○ C
  ⊑⟨ ○-monotonic-r C⊑idR ⟩
    R ○ idR
  ⊑⟨ id-intro-r ⟩
    R
  ⊑∎

corefl-intro-l : ∀ {i j} {A : Set i} {B : Set j} {C : B ← B} {R : B ← A ⊣ j}
               → C ⊑ idR → C ○ R ⊑ R
corefl-intro-l {C = C} {R} C⊑idR =
  ⊑-begin
    C ○ R 
  ⊑⟨ ○-monotonic-l C⊑idR ⟩
    idR ○ R
  ⊑⟨ id-intro-l ⟩
    R
  ⊑∎

-- Eliminating a reflexive relation

refl-elim-r : ∀ {i j} {A : Set i} {B : Set j} {C : A ← A} {R : B ← A ⊣ i}
              → idR ⊑ C → R ⊑ R ○ C
refl-elim-r {C = C} {R} id⊑C =
  ⊑-begin
    R 
  ⊑⟨ id-elim-r ⟩
    R ○ idR
  ⊑⟨ ○-monotonic-r id⊑C ⟩
    R ○ C
  ⊑∎

refl-elim-l : ∀ {i j} {A : Set i} {B : Set j} {C : B ← B} {R : B ← A ⊣ j}
              → idR ⊑ C → R ⊑ C ○ R
refl-elim-l {C = C} {R} id⊑C =
  ⊑-begin
    R 
  ⊑⟨ id-elim-l ⟩
    idR ○ R
  ⊑⟨ ○-monotonic-l id⊑C ⟩
    C ○ R
  ⊑∎

total-pred : ∀ {i} {A : Set i} {P : A → Set i}
             → (∀ x → P x)
             → idR ⊑ P ¿ 
total-pred P-total x ._ refl = refl , P-total x

open import Data.List using (List)
open import Data.List.Utilities using (check; corefl-check)

check-idempotent : ∀ {A : Set} → (p : ℙ (A × List A)) → 
                   check (p ¿) ○ check (p ¿) ⊒ check (p ¿)
check-idempotent p = corefl-idempotent-⊒ (corefl-check (set-corefl⊑idR p))

-- Coref as a datatype

Coref : ∀ {i} (A : Set i) → Set (suc i)
Coref A = Σ (A ← A) (λ R → R ⊑ idR)

