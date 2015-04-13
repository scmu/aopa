module Relations.Shrink where

open import Level renaming (_⊔_ to _⊔ℓ_)
open import Function using (_∘_; id)
open import Data.Product renaming (map to ×-map)

open import Relations
open import Relations.Factor
open import Relations.Product
open import Relations.Galois
open import AlgebraicReasoning.Implications
open import Relation.Binary.PropositionalEquality

infixr 7 _↾_

_↾_ : ∀ {i j} {A : Set i} {B : Set j}
      → (R : A ← B ⊣ (i ⊔ℓ j)) → (S : A ← A ⊣ (i ⊔ℓ j))
      → (A ← B ⊣ (i ⊔ℓ j))
R ↾ S = R ⊓ (S / R ˘)

↾-universal-⇒₁ : ∀ {i j} {A : Set i} {B : Set j}
                 → {X R : A ← B} {S : A ← A}
                 → X ⊑ R ↾ S 
                 → X ⊑ R
↾-universal-⇒₁ X⊑R↾S = proj₁ (⊓-universal-⇒ X⊑R↾S)

↾-universal-⇒₂ : ∀ {i j} {A : Set i} {B : Set j}
                 → {X R : A ← B} {S : A ← A}
                 → X ⊑ R ↾ S 
                 → X ○ R ˘ ⊑ S 
↾-universal-⇒₂ {X = X} {R} {S} = 
  ⇒-begin 
    X ⊑ R ↾ S 
  ⇒⟨ proj₂ ∘ ⊓-universal-⇒ ⟩ 
    X ⊑ S / R ˘ 
  ⇒⟨ /-universal-⇒ ⟩ 
    X ○ R ˘ ⊑ S 
  ⇒∎

↾-universal-⇒ : ∀ {i j} {A : Set i} {B : Set j}
                 → {X R : A ← B} {S : A ← A}
                 → X ⊑ R ↾ S 
                 → (X ⊑ R) × (X ○ R ˘ ⊑ S)
↾-universal-⇒ X⊑R↾S = (↾-universal-⇒₁ X⊑R↾S , ↾-universal-⇒₂ X⊑R↾S)

↾-universal-⇐ : ∀ {i j} {A : Set i} {B : Set j}
                 → {X R : A ← B} {S : A ← A}
                 → (X ⊑ R) × (X ○ R ˘ ⊑ S)
                 → X ⊑ R ↾ S 
↾-universal-⇐ {X = X} {R} {S} (X⊑R , XR˘⊑S) = 
  (⇐-begin 
     X ⊑ R ↾ S 
   ⇐⟨ id ⟩ 
     X ⊑ R ⊓ (S / (R ˘)) 
   ⇐⟨ ⊓-universal-⇐ ⟩ 
     (X ⊑ R × X ⊑ S / (R ˘)) 
   ⇐⟨ ×-map id /-universal-⇐ ⟩
     (X ⊑ R × X ○ R ˘ ⊑ S) 
   ⇐∎) (X⊑R , XR˘⊑S)

↾-universal : ∀ {i j} {A : Set i} {B : Set j}
              → {X R : A ← B} {S : A ← A}
              → X ⊑ R ↾ S ⇔
                ((X ⊑ R) × (X ○ R ˘ ⊑ S))
↾-universal {S = S} = ↾-universal-⇒ , ↾-universal-⇐

galois-shrink : ∀ {i} {A B : Set i}
         → (f : A → B) (g : B → A)
         → (R : B ← B ⊣ i) (S : A ← A  ⊣ i)
         → galois f g R S
         → fun g ⊑ ((fun f)˘ ○ R) ↾ (S ˘)
galois-shrink = {!!}
