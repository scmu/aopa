module Relations.Galois where

open import Level renaming (_⊔_ to _⊔ℓ_)
open import Relations
open import Data.Product
open import AlgebraicReasoning.Implications
open import Relations.CompChain
open import Relation.Binary using (IsPreorder; Transitive)
open import Relation.Binary.PropositionalEquality

-- Galois connection, as often seen in literatures.

galois : ∀ {i k} {A B : Set i}
         → (f : A → B) (g : B → A)
         → (_≼_ : B ← B ⊣ k) (_⊴_ : A ← A  ⊣ k) → Set (i ⊔ℓ k)
galois f g _≼_ _⊴_ = ∀ x y → f x ≼ y ⇔ x ⊴ g y

-- a point-free formulation of Galois connection.

galois-○ : ∀ {i k} {A B : Set i}
         → (f : A → B) (g : B → A)
         → (_≼_ : B ← B ⊣ k) (_⊴_ : A ← A ⊣ k) → Set (i ⊔ℓ k)
galois-○ f g R S = (fun f)˘ ○ R ≑ S ○ fun g

galois-equiv-⇐ : ∀ {i k} {A B : Set i}
                 → (f : A → B) (g : B → A)
                 → (R : B ← B ⊣ k) (S : A ← A ⊣ k)
                 → galois-○ f g R S → galois f g R S
galois-equiv-⇐ f g _≼_ _⊴_ (f∘≼→⊴∘g , ⊴∘g→f∘≼) x y = (f≼→⊴g , ⊴g→f≼)
  where f≼→⊴g : f x ≼ y ⇒ x ⊴ g y 
        f≼→⊴g fx≼y with f∘≼→⊴∘g x y (f x , fx≼y , refl)
        ... | (._ , refl , gy⊴b) = gy⊴b

        ⊴g→f≼ : x ⊴ g y → f x ≼ y
        ⊴g→f≼ x⊴gy with ⊴∘g→f∘≼ x y (g y , (refl , x⊴gy))
        ... | (._ , fx≼y , refl) = fx≼y

{- to be proved
galois-equiv-⇒ : ∀ {i k} {A B : Set i}
                 → (f : A → B) (g : B → A)
                 → (R : B ← B ⊣ k) (S : A ← A ⊣ k)
                 → galois f g R S → galois-○ f g R S
galois-equiv-⇒ f g R S = {!!}
-}

transitive-○ : ∀ {i} {A : Set i} {R : A ← A ⊣ i} → IsPreorder (_≡_) R 
               → R ○ R ⊑ R
transitive-○ {R = R} isPre a₀ a₂ (a₁ , a₁Ra₂ , a₀Ra₁) = R-trans a₀Ra₁ a₁Ra₂
  where R-trans : Transitive R
        R-trans = Relation.Binary.IsPreorder.trans isPre

galois-easy : ∀ {i} {A B : Set i}
              → (f : A → B) (g : B → A)
              → (R : B ← B ⊣ i) (S : A ← A ⊣ i)
              → IsPreorder (_≡_) R 
              → S ○ (fun f)˘ ⊑ (fun f)˘ ○ R
              → fun g ⊑ (fun f)˘ ○ R
              → S ○ fun g ⊑ (fun f)˘ ○ R
galois-easy f g R S isPre Sf˘⊑f˘R = 
   ⇒-begin 
     fun g ⊑ fun f ˘ ○ R 
   ⇒⟨ ○-monotonic-r ⟩ 
     S ○ fun g ⊑ S ○ fun f ˘ ○ R 
   ⇒⟨ ⊒-trans (⇦-mono-l (S ● (fun f ˘) ‥) (fun f ˘ ● R ‥) Sf˘⊑f˘R) ⟩ 
     S ○ fun g ⊑ fun f ˘ ○ R ○ R 
   ⇒⟨ ⊒-trans (○-monotonic-r (transitive-○ isPre)) ⟩ 
     S ○ fun g ⊑ fun f ˘ ○ R 
   ⇒∎