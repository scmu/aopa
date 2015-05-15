module Data.Generic.Membership where

open import Level renaming (_⊔_ to _⊔ℓ_)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; ∃; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Relations
open import Data.Generic.Core


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
