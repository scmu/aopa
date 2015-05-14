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
  
 fmap-hylo : {F : PolyF} {j : Level} {A : Set} {B : Set j} {C : Set}
           → (f : ⟦ F ⟧ A B → B) → (g : C → ⟦ F ⟧ A C)
           → (c : C) → (h : ∀ z → (ε F ○ fun g) z c → Acc (ε F ○ fun g) z)
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

mutual
  hylo-acc-irr : (F : PolyF) → ∀ {j} {A : Set} {B : Set j} {C : Set}
               → (f : ⟦ F ⟧ A B → B) → (g : C → ⟦ F ⟧ A C)
               → (c : C)
               → (ac₁ : Acc (ε F ○ fun g) c) → (ac₂ : Acc (ε F ○ fun g) c)
               → hylo-acc F f g c ac₁ ≡ hylo-acc F f g c ac₂
  hylo-acc-irr F f g c (acc ._ h₁) (acc ._ h₂) 
    rewrite fmap-hylo-irr f g c h₁ h₂ F (g c) root = refl

  fmap-hylo-irr : {F : PolyF} {j : Level} {A : Set} {B : Set j} {C : Set}
                → (f : ⟦ F ⟧ A B → B) → (g : C → ⟦ F ⟧ A C)
                → (c : C) → (h₁ : ∀ z → (ε F ○ fun g) z c → Acc (ε F ○ fun g) z)
                → (h₂ : ∀ z → (ε F ○ fun g) z c → Acc (ε F ○ fun g) z)
                → (G : PolyF) → (y : ⟦ G ⟧ A C)
                → (p : Path F (g c) G y)
                → fmap-hylo f g c h₁ G y p ≡ fmap-hylo f g c h₂ G y p 
  fmap-hylo-irr f g c h₁ h₂ zer () p
  fmap-hylo-irr f g c h₁ h₂ one tt p = refl
  fmap-hylo-irr f g c h₁ h₂ arg₁ (fst x) p = refl
  fmap-hylo-irr f g c h₁ h₂ arg₂ (snd y) p
   rewrite hylo-acc-irr _ f g y (h₁ y (g c , refl , path-to-ε p))
                                (h₂ y (g c , refl , path-to-ε p)) = refl
  fmap-hylo-irr f g c h₁ h₂ (G₀ ⊕ G₁) (inj₁ x) p
   rewrite fmap-hylo-irr f g c h₁ h₂ G₀ x (inj₁ p) = refl
  fmap-hylo-irr f g c h₁ h₂ (G₀ ⊕ G₁) (inj₂ y) p
   rewrite fmap-hylo-irr f g c h₁ h₂ G₁ y (inj₂ p) = refl
  fmap-hylo-irr f g c h₁ h₂ (G₀ ⊗ G₁) (y₀ , y₁) p
   rewrite fmap-hylo-irr f g c h₁ h₂ G₀ y₀ (out₁ p)
         | fmap-hylo-irr f g c h₁ h₂ G₁ y₁ (out₂ p) = refl


fmap-hylo-bimap :
           {F : PolyF} {j : Level} {A : Set} {B : Set j} {C : Set}
           → (f : ⟦ F ⟧ A B → B) → (g : C → ⟦ F ⟧ A C) → (wf : well-found (ε F ○ fun g))
           → (c : C)  → (h : ∀ z → (ε F ○ fun g) z c → Acc (ε F ○ fun g) z)
           → (G : PolyF) → (y : ⟦ G ⟧ A C)
           → (p : Path F (g c) G y)
           → fmap-hylo f g c h G y p ≡
               bimap G id (λ d → hylo-acc F f g d (wf d)) y
fmap-hylo-bimap f g wf c h zer () p
fmap-hylo-bimap f g wf c h one tt p = refl
fmap-hylo-bimap f g wf c h arg₁ (fst x) p = refl
fmap-hylo-bimap f g wf c h arg₂ (snd x) p
   rewrite hylo-acc-irr _ f g x (h x (g c , refl , path-to-ε p)) (wf x) = refl
fmap-hylo-bimap f g wf c h (G₀ ⊕ G₁) (inj₁ x) p
   rewrite fmap-hylo-bimap f g wf c h G₀ x (inj₁ p) = refl
fmap-hylo-bimap f g wf c h (G₀ ⊕ G₁) (inj₂ y) p
   rewrite fmap-hylo-bimap f g wf c h G₁ y (inj₂ p) = refl
fmap-hylo-bimap f g wf c h (G₀ ⊗ G₁) (y₀ , y₁) p
   rewrite fmap-hylo-bimap f g wf c h G₀ y₀ (out₁ p)
         | fmap-hylo-bimap f g wf c h G₁ y₁ (out₂ p) = refl

hylo-is-hylo : (F : PolyF) → ∀ {j} {A : Set} {B : Set j} {C : Set}
               → (f : ⟦ F ⟧ A B → B) → (g : C → ⟦ F ⟧ A C)
               → (wf : well-found (ε F ○ fun g))
               → (c : C)
               → hylo F f g wf c ≡ (f ∘ bimap F id (hylo F f g wf) ∘ g) c
hylo-is-hylo F f g wf c with wf c
... | acc ._ h rewrite fmap-hylo-bimap f g wf c h F (g c) root = refl
