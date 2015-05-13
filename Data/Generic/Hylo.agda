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

mutual
 hylo-acc : (F : PolyF) → ∀ {j} {A : Set} {B : Set j} {C : Set}
          → (f : ⟦ F ⟧ A B → B) → (g : C → ⟦ F ⟧ A C)
          → (c : C) → Acc (ε F ○ fun g) c → B
 hylo-acc F {A = A} {B} {C} f g c (acc .c h) =
   f (fmap-hylo f g c h F (g c) root)
  
 fmap-hylo : {F : PolyF} →  ∀ {j} {A : Set} {B : Set j} {C : Set}
           → (f : ⟦ F ⟧ A B → B) → (g : C → ⟦ F ⟧ A C)
           → (c : C) → (∀ z → (ε F ○ fun g) z c → Acc (ε F ○ fun g) z)
           → (G : PolyF) → (y : ⟦ G ⟧ A C)
                  → Path F (g c) G y
                  → ⟦ G ⟧ A B
 fmap-hylo f g c h zer ()
 fmap-hylo f g c h one tt _ = tt
 fmap-hylo f g c h arg₁ (fst x) _ = fst x
 fmap-hylo f g c h arg₂ (snd y) p = snd (hylo-acc _ f g y (h y (g c , refl , path-to-ε p)))
 fmap-hylo f g c h (G₀ ⊕ G₁) (inj₁ y) p = inj₁ (fmap-hylo f g c h G₀ y (inj₁ p))
 fmap-hylo f g c h (G₀ ⊕ G₁) (inj₂ y) p = inj₂ (fmap-hylo f g c h G₁ y (inj₂ p))
 fmap-hylo f g c h (G₀ ⊗ G₁) (y₀ , y₁) p =
   fmap-hylo f g c h G₀ y₀ (out₁ p) ,
   fmap-hylo f g c h G₁ y₁ (out₂ p)

hylo : (F : PolyF) → ∀ {j} {A : Set} {B : Set j} {C : Set}
     → (f : ⟦ F ⟧ A B → B) → (g : C → ⟦ F ⟧ A C)
     → well-found (ε F ○ fun g)
     → C → B
hylo F f g wf c = hylo-acc F f g c (wf c)

unacc : ∀ {A : Set} {R : A → A → Set} {x : A}
        → Acc R x → (∀ y → R y x → Acc R y)
unacc (acc _ h) = h

mutual
 bimapP : (F : PolyF) → ∀ {i j l m} {A₁ : Set i} {A₂ : Set j} {B₁ : Set} {B₂ : Set l}
        → (A₁ → A₂) → (P : B₁ → Set m) → ((z : B₁) → P z → B₂)
        → (x : ⟦ F ⟧ A₁ B₁)
        → (∀ z → ε F z x → P z) → ⟦ F ⟧ A₂ B₂
 bimapP F {A₁ = A₁} {A₂} {B₁} {B₂} f P g x h =
   bimapP' h f g F x root
 
 bimapP' : {F : PolyF} → ∀ {i j l m} {A₁ : Set i} {A₂ : Set j} {B₁ : Set} {B₂ : Set l}
        →  {x : ⟦ F ⟧ A₁ B₁} → {P : B₁ → Set m} → (∀ z → ε F z x → P z)
        → (A₁ → A₂)  → ((z : B₁) → P z → B₂)
        → (G : PolyF)
        → (y : ⟦ G ⟧ A₁ B₁)
        → Path F x G y
        → ⟦ G ⟧ A₂ B₂
 bimapP' h f g zer () p
 bimapP' h f g one tt p = tt
 bimapP' h f g arg₁ (fst w) p = fst (f w)
 bimapP' h f g arg₂ (snd y) p = snd (g y (h y (path-to-ε p)))
 bimapP' h f g (G₀ ⊕ G₁) (inj₁ y) p = inj₁ (bimapP' h f g G₀ y (inj₁ p))
 bimapP' h f g (G₀ ⊕ G₁) (inj₂ y) p = inj₂ (bimapP' h f g G₁ y (inj₂ p))
 bimapP' h f g (G₀ ⊗ G₁) (y₀ , y₁) p =
    bimapP' h f g G₀ y₀ (out₁ p) , bimapP' h f g G₁ y₁ (out₂ p)

{-
hylo-acc-is-hylo : (F : PolyF) → ∀ {j} {A : Set} {B : Set j} {C : Set}
            → (f : ⟦ F ⟧ A B → B) → (g : C → ⟦ F ⟧ A C)
            → (c : C) → (ac : Acc (ε F ○ fun g) c)
            → hylo-acc F f g c ac ≡
               f (bimapP F id (Acc (ε F ○ fun g)) (hylo-acc F f g)
                    (g c) (λ z z∈ → unacc ac z (g c , refl , z∈)))
hylo-acc-is-hylo F f g c (acc .c x) = {!!}
-}

postulate
  hylo-is-hylo : (F : PolyF) → ∀ {j} {A : Set} {B : Set j} {C : Set}
               → (f : ⟦ F ⟧ A B → B) → (g : C → ⟦ F ⟧ A C)
               → (wf : well-found (ε F ○ fun g))
               → (c : C)
               → hylo F f g wf c ≡ (f ∘ bimap F id (hylo F f g wf) ∘ g) c
