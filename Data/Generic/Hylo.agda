module Data.Generic.Hylo where

open import Level renaming (_⊔_ to _⊔ℓ_)
open import Function using (_∘_; id)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; ∃; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Relations
open import Relations.WellFound

open import Data.Generic


-- membership relation defined for polynomial functors

ε : (F : PolyF) → ∀ {i} {A : Set i} {X : Set} → (X ← ⟦ F ⟧ A X ⊣ zero) 
ε zer _ _ = ⊥
ε one _ _ = ⊥
ε arg₁ _ _ = ⊥
ε arg₂ x₀ (snd x₁) = x₀ ≡ x₁
ε (F₀ ⊕ F₁) x (inj₁ y) = ε F₀ x y
ε (F₀ ⊕ F₁) x (inj₂ y) = ε F₁ x y
ε (F₀ ⊗ F₁) x (y₀ , y₁) = ε F₀ x y₀ ⊎ ε F₁ x y₁

data Path (F : PolyF) {i : Level} {A : Set i} {X : Set} (x : ⟦ F ⟧ A X) :
          (G : PolyF) → ⟦ G ⟧ A X → Set i where
  root : Path F x F x
  inj₁  : ∀ {G₁ G₂ y} → Path F x (G₁ ⊕ G₂) (inj₁ y) → Path F x G₁ y
  inj₂  : ∀ {G₁ G₂ y} → Path F x (G₁ ⊕ G₂) (inj₂ y) → Path F x G₂ y
  out₁ : ∀ {G₁ G₂ y₁ y₂} → Path F x (G₁ ⊗ G₂) (y₁ , y₂) → Path F x G₁ y₁
  out₂ : ∀ {G₁ G₂ y₁ y₂} → Path F x (G₁ ⊗ G₂) (y₁ , y₂) → Path F x G₂ y₂


path-to-ε' : ∀ {F G} {i}  {A : Set i} {X : Set} {x : ⟦ F ⟧ A X} {y : ⟦ G ⟧ A X}
             → Path F x G y
             → {z : X} → ε G z y
             → ε F z x           
path-to-ε' root z∈ = z∈
path-to-ε' (inj₁ p) z∈ = path-to-ε' p z∈
path-to-ε' (inj₂ p) z∈ = path-to-ε' p z∈
path-to-ε' (out₁ p) z∈ = path-to-ε' p (inj₁ z∈)
path-to-ε' (out₂ p) z∈ = path-to-ε' p (inj₂ z∈)

path-to-ε : ∀ {F} {i}  {A : Set i} {X : Set} {x : ⟦ F ⟧ A X} {y : X}
             → Path F x arg₂ (snd y) → ε F y x
path-to-ε p = path-to-ε' p refl

hylo-acc : (F : PolyF) → ∀ {j} {A : Set} {B : Set j} {C : Set}
           → (f : ⟦ F ⟧ A B → B) → (g : C → ⟦ F ⟧ A C)
           → (c : C) → Acc (ε F ○ fun g) c → B
hylo-acc F {A = A} {B} {C} f g c (acc .c h) = f (fmap-hylo F (g c) root)
  where fmap-hylo : (G : PolyF)
                  → (y : ⟦ G ⟧ A C)
                  → Path F (g c) G y
                  → ⟦ G ⟧ A B
        fmap-hylo zer ()
        fmap-hylo one tt _ = tt
        fmap-hylo arg₁ (fst x) _ = fst x
        fmap-hylo arg₂ (snd y) p = snd (hylo-acc F f g y (h y (g c , refl , path-to-ε p)))
        fmap-hylo (G₀ ⊕ G₁) (inj₁ y) p = inj₁ (fmap-hylo G₀ y (inj₁ p))
        fmap-hylo (G₀ ⊕ G₁) (inj₂ y) p = inj₂ (fmap-hylo G₁ y (inj₂ p)) 
        fmap-hylo (G₀ ⊗ G₁) (y₀ , y₁) p = fmap-hylo G₀ y₀ (out₁ p) , fmap-hylo G₁ y₁ (out₂ p)

hylo : (F : PolyF) → ∀ {j} {A : Set} {B : Set j} {C : Set}
     → (f : ⟦ F ⟧ A B → B) → (g : C → ⟦ F ⟧ A C)
     → well-found (ε F ○ fun g)
     → C → B
hylo F f g wf c = hylo-acc F f g c (wf c)
