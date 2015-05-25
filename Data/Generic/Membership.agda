module Data.Generic.Membership where

open import Level renaming (_⊔_ to _⊔ℓ_)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; ∃; _×_; _,_; proj₁; proj₂)
open import Relation.Unary using (_∈_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sets
open import Relations
open import Data.Generic.Core
open import Relations.MonoFactor


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


ε-⍀-⊆ : ∀ {A B C : Set} {F : PolyF}
      → (S : ⟦ F ⟧ A B ← C) (P : B → Set) 
      → (ε F ○ S) ⍀ P ⊆ S ⍀ (fmapP F P)
ε-⍀-⊆ {F = zer} S P c c∈εFS⍀P () _
ε-⍀-⊆ {F = one} S P c c∈εFS⍀P tt _ = tt
ε-⍀-⊆ {F = arg₁} S P c c∈εFS⍀P (fst a) _ = tt
ε-⍀-⊆ {F = arg₂} S P c c∈εFS⍀P (snd b) bSc = c∈εFS⍀P b (snd b , bSc , refl)
ε-⍀-⊆ {F = F₀ ⊕ F₁} S P c c∈εFS⍀P (inj₁ x) xSc =
   ε-⍀-⊆ {F = F₀} (fun inj₁ ˘ ○ S) P c c∈εi₁S⍀P x (inj₁ x , xSc , refl)
 where c∈εi₁S⍀P : _∈_ c ((ε F₀ ○ fun inj₁ ˘ ○ S) ⍀ P)
       c∈εi₁S⍀P b (w , (._ , wSc , refl) , b∈w)  =
          c∈εFS⍀P b (inj₁ w , wSc , b∈w)
ε-⍀-⊆ {F = F₀ ⊕ F₁} S P c c∈εFS⍀P (inj₂ y) ySc =
   ε-⍀-⊆ {F = F₁} (fun inj₂ ˘ ○ S) P c c∈εi₂S⍀P y (inj₂ y , ySc , refl)
 where c∈εi₂S⍀P : _∈_ c ((ε F₁ ○ fun inj₂ ˘ ○ S) ⍀ P)
       c∈εi₂S⍀P b (w , (._ , wSc , refl) , b∈w)  =
          c∈εFS⍀P b (inj₂ w , wSc , b∈w)   
ε-⍀-⊆ {F = F₀ ⊗ F₁} S P c c∈εFS⍀P (x₀ , x₁) xSc =
   ε-⍀-⊆ {F = F₀} (fun proj₁ ○ S) P c p₀ x₀ ((x₀ , x₁) , xSc , refl) ,
   ε-⍀-⊆ {F = F₁} (fun proj₂ ○ S) P c p₁ x₁ ((x₀ , x₁) , xSc , refl)
 where p₀ : _∈_ c ((ε F₀ ○ fun (λ r → proj₁ r) ○ S) ⍀ P)
       p₀ b (w₀ , ((._ , w₁) , wSc , refl) , b∈w₀) =
         c∈εFS⍀P b ((w₀ , w₁) , wSc , inj₁ b∈w₀)
       p₁ : _∈_ c ((ε F₁ ○ fun (λ r → proj₂ r) ○ S) ⍀ P)
       p₁ b (w₁ , ((w₀ , ._) , wSc , refl) , b∈w₁) =
         c∈εFS⍀P b ((w₀ , w₁) , wSc , inj₂ b∈w₁)

ε-⍀-⊇ : ∀ {A B C : Set} {F : PolyF}
      → (S : ⟦ F ⟧ A B ← C) (P : B → Set) 
      → (ε F ○ S) ⍀ P ⊇ S ⍀ (fmapP F P)
ε-⍀-⊇ {F = zer} S P _ _ b (() , _)
ε-⍀-⊇ {F = one} S P c c∈ b (tt , _ , ())
ε-⍀-⊇ {F = arg₁} S P c c∈ b (_ , _ , ())
ε-⍀-⊇ {F = arg₂} S P c c∈ b (snd ._ , bSc , refl) = c∈ (snd b) bSc
ε-⍀-⊇ {F = F₀ ⊕ F₁} S P c c∈ b (inj₁ x , xSc , b∈x) =
  ε-⍀-⊇ {F = F₀} (fun inj₁ ˘ ○ S) P c p₀ b (x , (inj₁ x , xSc , refl) , b∈x)
 where p₀ : _∈_ c ((fun inj₁ ˘ ○ S) ⍀ fmapP F₀ P)
       p₀ w (._ , wSc , refl) = c∈ (inj₁ w) wSc
ε-⍀-⊇ {F = F₀ ⊕ F₁} S P c c∈ b (inj₂ x , xSc , b∈x) =
  ε-⍀-⊇ {F = F₁} (fun inj₂ ˘ ○ S) P c p₁ b (x , (inj₂ x , xSc , refl) , b∈x)
 where p₁ : _∈_ c ((fun inj₂ ˘ ○ S) ⍀ fmapP F₁ P)
       p₁ w (._ , wSc , refl) = c∈ (inj₂ w) wSc
ε-⍀-⊇ {F = F₀ ⊗ F₁} S P c c∈ b ((x₀ , x₁) , xSc , inj₁ b∈x₀) =
  ε-⍀-⊇ {F = F₀} (fun proj₁ ○ S) P c p₀ b
     (x₀ , ((x₀ , x₁) , xSc , refl) , b∈x₀)
 where p₀ : _∈_ c ((fun (λ r → proj₁ r) ○ S) ⍀ fmapP F₀ P)
       p₀ w₀ ((._ , w₁) , wSc , refl) = proj₁ (c∈ (w₀ , w₁) wSc)
ε-⍀-⊇ {F = F₀ ⊗ F₁} S P c c∈ b ((x₀ , x₁) , xSc , inj₂ b∈x₁) =
  ε-⍀-⊇ {F = F₁} (fun proj₂ ○ S) P c p₁ b
     (x₁ , ((x₀ , x₁) , xSc , refl) , b∈x₁)
 where p₁ : _∈_ c ((fun (λ r → proj₂ r) ○ S) ⍀ fmapP F₁ P)
       p₁ w₁ ((w₀ , ._) , wSc , refl) = proj₂ (c∈ (w₀ , w₁) wSc)
