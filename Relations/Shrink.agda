module Relations.Shrink where

open import Level renaming (_⊔_ to _⊔ℓ_)
open import Function using (_∘_; id)
open import Data.Product renaming (map to ×-map)

open import Relations
open import Relations.Factor
open import Relations.Product
open import Relations.Converse
open import Relations.CompChain
open import Relations.Galois
open import Relations.Function

open import AlgebraicReasoning.Equivalence
open import AlgebraicReasoning.Implications
open import AlgebraicReasoning.Relations
open import Relation.Binary using (IsPreorder; Transitive)
open import Relation.Binary.PropositionalEquality


infixr 7 _↾_

_↾_ : ∀ {i j} {A : Set i} {B : Set j}
      → (S : A ← B ⊣ (i ⊔ℓ j)) → (R : A ← A ⊣ (i ⊔ℓ j))
      → (A ← B ⊣ (i ⊔ℓ j))
S ↾ R = S ⊓ (R / S ˘)

-- Universal properties.

↾-universal-⇒₁ : ∀ {i j} {A : Set i} {B : Set j}
                 → {X S : A ← B} {R : A ← A}
                 → X ⊑ S ↾ R 
                 → X ⊑ S
↾-universal-⇒₁ X⊑S↾R = proj₁ (⊓-universal-⇒ X⊑S↾R)

↾-universal-⇒₂ : ∀ {i j} {A : Set i} {B : Set j}
                 → {X S : A ← B} {R : A ← A}
                 → X ⊑ S ↾ R 
                 → X ○ S ˘ ⊑ R 
↾-universal-⇒₂ {X = X} {S} {R} = 
  ⇒-begin 
    X ⊑ S ↾ R 
  ⇒⟨ proj₂ ∘ ⊓-universal-⇒ ⟩ 
    X ⊑ R / S ˘ 
  ⇒⟨ /-universal-⇒ ⟩ 
    X ○ S ˘ ⊑ R 
  ⇒∎

↾-universal-⇒ : ∀ {i j} {A : Set i} {B : Set j}
                 → {X S : A ← B} {R : A ← A}
                 → X ⊑ S ↾ R 
                 → (X ⊑ S) × (X ○ S ˘ ⊑ R)
↾-universal-⇒ X⊑S↾R = (↾-universal-⇒₁ X⊑S↾R , ↾-universal-⇒₂ X⊑S↾R)

↾-universal-⇐ : ∀ {i j} {A : Set i} {B : Set j}
                 → {X S : A ← B} {R : A ← A}
                 → (X ⊑ S) × (X ○ S ˘ ⊑ R)
                 → X ⊑ S ↾ R 
↾-universal-⇐ {X = X} {S} {R} (X⊑S , XS˘⊑R) = 
  (⇐-begin 
     X ⊑ S ↾ R 
   ⇐⟨ id ⟩ 
     X ⊑ S ⊓ (R / (S ˘)) 
   ⇐⟨ ⊓-universal-⇐ ⟩ 
     (X ⊑ S × X ⊑ R / (S ˘)) 
   ⇐⟨ ×-map id /-universal-⇐ ⟩
     (X ⊑ S × X ○ S ˘ ⊑ R) 
   ⇐∎) (X⊑S , XS˘⊑R)

↾-universal : ∀ {i j} {A : Set i} {B : Set j}
              → {X S : A ← B} {R : A ← A}
              → X ⊑ S ↾ R ⇔
                ((X ⊑ S) × (X ○ S ˘ ⊑ R))
↾-universal {R = R} = ↾-universal-⇒ , ↾-universal-⇐

-- Derived inclusion properties.

S↾R⊑S : ∀ {i j} {A : Set i} {B : Set j}
        → {S : A ← B} {R : A ← A}
        → S ↾ R ⊑ S
S↾R⊑S = ↾-universal-⇒₁ ⊑-refl

S↾RS˘⊑R : ∀ {i j} {A : Set i} {B : Set j}
        → {S : A ← B} {R : A ← A}
        → (S ↾ R) ○ S ˘ ⊑ R 
S↾RS˘⊑R = ↾-universal-⇒₂ ⊑-refl

-- Absorption rule.

↾-simple-absorption : ∀ {i} {A : Set i} {B : Set i} {C : Set i}
   → (S : A ← B) (T : B ← C) (R : A ← A)
   → (T ○ T ˘ ⊑ idR) 
   → (S ↾ R) ○ T ⊑ (S ○ T) ↾ R
↾-simple-absorption S T R T-simple = ↾-universal-⇐ (S↾RT⊑ST , S↾RTST˘⊑R)
  where S↾RT⊑ST : (S ↾ R) ○ T ⊑ S ○ T
        S↾RT⊑ST = ⊑-begin
                    (S ↾ R) ○ T
                  ⊑⟨ ○-monotonic-l S↾R⊑S ⟩
                    S ○ T
                  ⊑∎
        S↾RTST˘⊑R : ((S ↾ R) ○ T) ○ (S ○ T) ˘ ⊑ R
        S↾RTST˘⊑R =
          ⊑-begin
            ((S ↾ R) ○ T) ○ (S ○ T) ˘
          ⊑⟨ ○-monotonic-r (˘-○-distr-⊑ _ _) ⟩
            ((S ↾ R) ○ T) ○ T ˘ ○ S ˘
          ⊑⟨ ○-assocr ⟩
            (S ↾ R) ○ T ○ T ˘ ○ S ˘            
          ⊑⟨ ⇦-mono ((S ↾ R) ‥) (T ● (T ˘) ‥) (idR ‥) T-simple ⟩
            (S ↾ R) ○ idR ○ S ˘
          ⊑⟨ ○-monotonic-r (id-intro-l {R = S ˘}) ⟩
            (S ↾ R) ○ S ˘
          ⊑⟨ S↾RS˘⊑R ⟩
            R
          ⊑∎

↾-fun-absorption : ∀ {i} {A : Set i} {B : Set i} {C : Set i}
   → (S : A ← B) (f : C → B) (R : A ← A)
   → (S ↾ R) ○ fun f ⊑ (S ○ fun f) ↾ R
↾-fun-absorption S f R = ↾-simple-absorption S (fun f) R fun-simple

-- Monotonicity.

-- Certainly, if the ordering is more "liberal", a shrunk relation
-- is allowed to return more.

↾-ord-monotonic :  ∀ {i j} {A : Set i} {B : Set j} 
   → (S : A ← B) (R T : A ← A)
   → (R ⊑ T) 
   → S ↾ R ⊑ S ↾ T
↾-ord-monotonic S R T R⊑T = ↾-universal-⇐ (S↾R⊑S , S↾RS˘⊑T)   
  where S↾RS˘⊑T : (S ↾ R) ○ S ˘ ⊑ T
        S↾RS˘⊑T = ⊑-begin
                    (S ↾ R) ○ S ˘
                  ⊑⟨ S↾RS˘⊑R ⟩
                    R
                  ⊑⟨ R⊑T ⟩
                    T
                  ⊑∎

-- In general, S ↾ R is not monotonic in S --- 
-- with S ⊑ T, it is not always the case that S ↾ R ⊑ T ↾ R.
-- One situation where the latter holds is when T does not
-- introduce solutions "better" than those given by S. That is,  
-- when S ○ T ˘ ⊑ R.

↾-gen-monotonic :  ∀ {i} {A : Set i} {B : Set i} {C : Set i}
   → (S T : A ← B) (R : A ← A)
   → (S ⊑ T) → S ○ T ˘ ⊑ R
   → S ↾ R ⊑ T ↾ R
↾-gen-monotonic S T R S⊑T ST˘⊑R = ↾-universal-⇐ (S↾R⊑T , S↾RT˘⊑R)   
  where S↾R⊑T : S ↾ R ⊑ T
        S↾R⊑T = ⊑-begin
                  S ↾ R
                ⊑⟨ S↾R⊑S ⟩
                  S
                ⊑⟨ S⊑T ⟩
                  T
                ⊑∎
        
        S↾RT˘⊑R : (S ↾ R) ○ T ˘ ⊑ R
        S↾RT˘⊑R = (⇐-begin 
                    (S ↾ R) ○ T ˘ ⊑ R
                   ⇐⟨ ⊒-trans ST˘⊑R ⟩
                    (S ↾ R) ○ T ˘ ⊑ S ○ T ˘
                   ⇐⟨ ○-monotonic-l ⟩
                    S ↾ R ⊑ S
                   ⇐∎ ) S↾R⊑S

-- Relationship to Galois connection.

galois-shrink : ∀ {i} {A B : Set i}
         → (f : A → B) (g : B → A)
         → (R : B ← B ⊣ i) (S : A ← A ⊣ i)
         → IsPreorder (_≡_) S
         → galois f g R S
         → fun g ⊑ ((fun f)˘ ○ R) ↾ (S ˘)
galois-shrink f g R S isPre gal = ↾-universal-⇐ (g⊑f˘R , gR˘f⊑S˘)
  where g⊑f˘R : fun g ⊑ (fun f ˘ ○ R)
        g⊑f˘R = galois-easy-⇒ {S = S} isPre gal

        gR˘f⊑S˘ : fun g ○ ((fun f ˘ ○ R)) ˘ ⊑ S ˘ 
        gR˘f⊑S˘ = galois-hard-⇒ gal
