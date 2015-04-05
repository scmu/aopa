module Relations.Galois where

open import Level renaming (_⊔_ to _⊔ℓ_)
open import Relations
open import Data.Product
open import AlgebraicReasoning.Implications
open import Relations.CompChain
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

galois-equiv-⇒ : ∀ {i k} {A B : Set i}
                 → (f : A → B) (g : B → A)
                 → (R : B ← B ⊣ k) (S : A ← A ⊣ k)
                 → galois f g R S → galois-○ f g R S
galois-equiv-⇒ f g R S = {!!}

galois-easy : ∀ {i} {A B : Set i}
              → (f : A → B) (g : B → A)
              → (R : B ← B ⊣ i) (S : A ← A ⊣ i)
              → S ○ (fun f)˘ ⊑ (fun f)˘ ○ R
              → fun g ⊑ (fun f)˘ ○ R
              → S ○ fun g ⊑ (fun f)˘ ○ R
galois-easy f g R S Sf˘⊑f˘R = 
   ⇒-begin 
     fun g ⊑ fun f ˘ ○ R 
   ⇒⟨ ○-monotonic-r ⟩ 
     S ○ fun g ⊑ S ○ fun f ˘ ○ R 
   ⇒⟨ ⊒-trans (⇦-mono-l (S ● (fun f ˘) ‥) (fun f ˘ ● R ‥) Sf˘⊑f˘R) ⟩ 
     S ○ fun g ⊑ fun f ˘ ○ R ○ R 
   ⇒⟨ {!!} ⟩ 
     S ○ fun g ⊑ fun f ˘ ○ R 
   ⇒∎
