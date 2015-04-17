module Relations.Galois where

open import Level renaming (_⊔_ to _⊔ℓ_)
open import Relations
open import Function using (flip)
open import Data.Product
open import AlgebraicReasoning.Implications
open import AlgebraicReasoning.Equivalence
open import Relations.CompChain
open import Relation.Binary using (IsPreorder; Transitive)
open import Relation.Binary.PropositionalEquality

-- Galois connection, as often seen in literatures.

galois : ∀ {i k} {A B : Set i}
         → (f : A → B) (g : B → A)
         → (_≼_ : B ← B ⊣ k) (_⊴_ : A ← A ⊣ k) → Set (i ⊔ℓ k)
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



monotonic-lower : ∀ {i k} {A B} 
                   → {f : A → B} {g : B → A} → ∀ {_≼_ _⊴_}
                   → IsPreorder (_≡_) _≼_ → IsPreorder (_≡_) _⊴_
                   → galois {i} {k} f g _≼_ _⊴_ → 
                   ∀ {x₀ x₁} → x₀ ⊴ x₁ → f x₀ ≼ f x₁
monotonic-lower {f = f} {g} {_≼_} {_⊴_} ≼-isPre ⊴-isPre gal {x₀ = x₀} {x₁} = 
  ⇒-begin
    x₀ ⊴ x₁
  ⇒⟨ flip (Relation.Binary.IsPreorder.trans ⊴-isPre) x⊴gfx ⟩
    x₀ ⊴ g (f x₁)
  ⇒⟨ proj₂ (gal x₀ (f x₁)) ⟩
    f x₀ ≼ f x₁
  ⇒∎
 where
   x⊴gfx : ∀ {x} → x ⊴ g (f x)
   x⊴gfx {x} = proj₁ (gal x (f x)) (Relation.Binary.IsPreorder.refl ≼-isPre)

monotonic-lower-○ : ∀ {i k} {A B} 
                    → {f : A → B} {g : B → A} → ∀ {_≼_ _⊴_}
                    → IsPreorder (_≡_) _≼_ → IsPreorder (_≡_) _⊴_
                    → galois {i} {k} f g _≼_ _⊴_
                    → _⊴_ ○ (fun f)˘ ⊑ (fun f)˘ ○ _≼_
monotonic-lower-○ {i}{k}{A}{B}{f}{g}{R}{S} gal ≼-isPre ⊴-isPre  x₀ ._ (x₁ , refl , x₀⊴x₁) = 
    _ , monotonic-lower {f = f}{g}{R} gal ≼-isPre ⊴-isPre x₀⊴x₁ , refl


galois-equiv-⇒ : ∀ {i k} {A B : Set i}
                 → (f : A → B) (g : B → A)
                 → (R : B ← B ⊣ k) (S : A ← A ⊣ k)
                 → galois f g R S → galois-○ f g R S
galois-equiv-⇒ f g R S gal = f˘R⊑Sg , Sg⊑f˘R
  where f˘R⊑Sg : fun f ˘ ○ R ⊑ S ○ fun g
        f˘R⊑Sg x y (._ , fxRy , refl) = g y , refl , proj₁ (gal x y) fxRy
        Sg⊑f˘R : S ○ fun g ⊑ fun f ˘ ○ R
        Sg⊑f˘R x y (._ , refl , xSgy) = f x , proj₂ (gal x y) xSgy , refl


transitive-○ : ∀ {i} {A : Set i} {R : A ← A ⊣ i} → IsPreorder (_≡_) R 
               → R ○ R ⊑ R
transitive-○ {R = R} isPre a₀ a₂ (a₁ , a₁Ra₂ , a₀Ra₁) = R-trans a₀Ra₁ a₁Ra₂
  where R-trans : Transitive R
        R-trans = Relation.Binary.IsPreorder.trans isPre

galois-easy-⇐ : ∀ {i} {A B : Set i}
              → (f : A → B) (g : B → A)
              → (R : B ← B ⊣ i) (S : A ← A ⊣ i)
              → IsPreorder (_≡_) R 
              → S ○ (fun f)˘ ⊑ (fun f)˘ ○ R
              → fun g ⊑ (fun f)˘ ○ R
              → S ○ fun g ⊑ (fun f)˘ ○ R
galois-easy-⇐ f g R S isPre Sf˘⊑f˘R = 
   ⇒-begin 
     fun g ⊑ fun f ˘ ○ R 
   ⇒⟨ ○-monotonic-r ⟩ 
     S ○ fun g ⊑ S ○ fun f ˘ ○ R 
   ⇒⟨ ⊒-trans (⇦-mono-l (S ● (fun f ˘) ‥) (fun f ˘ ● R ‥) Sf˘⊑f˘R) ⟩ 
     S ○ fun g ⊑ fun f ˘ ○ R ○ R 
   ⇒⟨ ⊒-trans (○-monotonic-r (transitive-○ isPre)) ⟩ 
     S ○ fun g ⊑ fun f ˘ ○ R 
   ⇒∎


galois-easy-⇒ : ∀ {i} {A B : Set i}
                → {f : A → B} {g : B → A}
                → {R : B ← B ⊣ i} {S : A ← A ⊣ i}
                → IsPreorder (_≡_) S
                → galois f g R S 
                → fun g ⊑ (fun f)˘ ○ R
galois-easy-⇒ {f = f} {g} {R} {S} isPre =
   ⇒-begin
     galois f g R S
   ⇒⟨ galois-equiv-⇒ f g R S ⟩
     galois-○ f g R S
   ⇒⟨ proj₂ ⟩
     S ○ fun g ⊑ (fun f)˘ ○ R
   ⇒⟨ ⊑-trans (○-monotonic-l idR⊑S) ⟩
     idR ○ fun g ⊑ (fun f)˘ ○ R
   ⇒⟨ ⊑-trans id-elim-l ⟩
     fun g ⊑ (fun f) ˘ ○ R
   ⇒∎
  where
    idR⊑S : idR ⊑ S
    idR⊑S _ ._ refl = Relation.Binary.IsPreorder.refl isPre


galois-hard-⇒ : ∀ {i} {A B : Set i}
                → {f : A → B} {g : B → A}
                → {R : B ← B ⊣ i} {S : A ← A ⊣ i}
                → galois f g R S 
                → fun g ○ ((fun f ˘ ○ R)) ˘ ⊑ S ˘ 
galois-hard-⇒ {f = f} {g} {R} {S} =
   ⇒-begin
     galois f g R S
   ⇒⟨ galois-equiv-⇒ f g R S ⟩
     galois-○ f g R S
   ⇒⟨ proj₁ ⟩
     fun f ˘ ○ R ⊑ S ○ fun g
   ⇒⟨ ˘-monotonic ⟩
     (fun f ˘ ○ R) ˘ ⊑ (S ○ fun g) ˘
   ⇒⟨ ⊒-trans ˘-○-distr-⊑ ⟩
     (fun f ˘ ○ R) ˘ ⊑ (fun g) ˘ ○ S ˘
   ⇒⟨ shunting-l-⇐ ⟩
     fun g ○ ((fun f ˘ ○ R)) ˘ ⊑ S ˘
   ⇒∎
