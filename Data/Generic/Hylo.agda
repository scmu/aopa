module Data.Generic.Hylo where

open import Level renaming (_⊔_ to _⊔ℓ_)
open import Function using (_∘_; id)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; ∃; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Relations
open import Relations.Converse
open import Relations.Function
open import Relations.Factor
open import Relations.CompChain
open import Relations.WellFound
open import Relations.Poset
open import FixedPoint
open import AlgebraicReasoning.Implications
open import AlgebraicReasoning.Relations

open import Data.Generic.Core
open import Data.Generic.Membership
open import Data.Generic.Fold


hylo-lpfp : {A B C : Set} {F : PolyF} {R : B ← ⟦ F ⟧ A B} {S : C ← ⟦ F ⟧ A C}
          → LeastPrefixedPoint (_⊑_) (λ X → R ○ fmapR F X ○ S ˘) (⦇ R ⦈ ○ ⦇ S ⦈ ˘)
hylo-lpfp {F = F} {R} {S} = (pfp , least)
  where
    pfp : R ○ fmapR F (⦇ R ⦈ ○ ⦇ S ⦈ ˘) ○ S ˘ ⊑ ⦇ R ⦈ ○ ⦇ S ⦈ ˘
    pfp =
      ⊑-begin
        R ○ fmapR F (⦇ R ⦈ ○ ⦇ S ⦈ ˘) ○ S ˘
      ⊑⟨ ○-monotonic-r (○-monotonic-l (bimapR-monotonic-⊑ F id-idempotent-⊒ ⊑-refl)) ⟩
        R ○ bimapR F (idR ○ idR) (⦇ R ⦈ ○ ⦇ S ⦈ ˘) ○ S ˘
      ⊑⟨ ○-monotonic-r (○-monotonic-l (bimapR-functor-⊒ F)) ⟩
        R ○ (fmapR F (⦇ R ⦈) ○ fmapR F (⦇ S ⦈ ˘)) ○ S ˘
      ⊑⟨ ○-monotonic-r ○-assocr ⟩
        R ○ fmapR F (⦇ R ⦈) ○ fmapR F (⦇ S ⦈ ˘) ○ S ˘
      ⊑⟨ ⇦-mono-l (R ● fmapR F (⦇ R ⦈) ‥) (⦇ R ⦈ ● fun In ‥) (foldR-computation-⊒ F R) ⟩
        ⦇ R ⦈ ○ fun In ○ fmapR F (⦇ S ⦈ ˘) ○ S ˘
      ⊑⟨ ○-monotonic-r ˘-idempotent-⊒ ⟩
        ⦇ R ⦈ ○ ((fun In ○ fmapR F (⦇ S ⦈ ˘) ○ S ˘) ˘) ˘
      ⊑⟨ ○-monotonic-r (˘-monotonic-⇐ ˘-○-distr3-⊑) ⟩
        ⦇ R ⦈ ○ (((S ˘) ˘) ○ (fmapR F (⦇ S ⦈ ˘) ˘) ○ (fun In ˘)) ˘
      ⊑⟨ ○-monotonic-r (˘-monotonic-⇐ (○-monotonic-l ˘-idempotent-⊑)) ⟩
        ⦇ R ⦈ ○ (S ○ (fmapR F (⦇ S ⦈ ˘) ˘) ○ (fun In ˘)) ˘
      ⊑⟨ ○-monotonic-r (˘-monotonic-⇐ (○-monotonic-r (○-monotonic-l (bimapR-˘-preservation-⊑ F)))) ⟩
        ⦇ R ⦈ ○ (S ○ (fmapR F ((⦇ S ⦈ ˘) ˘)) ○ (fun In ˘)) ˘
      ⊑⟨ ○-monotonic-r (˘-monotonic-⇐ (○-monotonic-r (○-monotonic-l (bimapR-monotonic-⊑ F ⊑-refl ˘-idempotent-⊑)))) ⟩
        ⦇ R ⦈ ○ (S ○ fmapR F ⦇ S ⦈ ○ (fun In ˘)) ˘
      ⊑⟨ ○-monotonic-r (˘-monotonic-⇐ (⇦-mono-l (S ● fmapR F ⦇ S ⦈ ‥) (⦇ S ⦈ ● fun In ‥) (foldR-computation-⊒ F S))) ⟩
        ⦇ R ⦈ ○ (⦇ S ⦈ ○ (fun In) ○ (fun In ˘)) ˘
      ⊑⟨ ○-monotonic-r (˘-monotonic-⇐ (○-monotonic-r fun-simple)) ⟩
        ⦇ R ⦈ ○ (⦇ S ⦈ ○ idR) ˘
      ⊑⟨ ○-monotonic-r (˘-monotonic-⇐ id-intro-r) ⟩
        ⦇ R ⦈ ○ ⦇ S ⦈ ˘
      ⊑∎

    least : ∀ {X} → R ○ fmapR F X ○ S ˘ ⊑ X → ⦇ R ⦈ ○ ⦇ S ⦈ ˘ ⊑ X
    least {X} =
      ⇐-begin
        ⦇ R ⦈ ○ ⦇ S ⦈ ˘ ⊑ X
      ⇐⟨ /-universal-⇒ ⟩
        ⦇ R ⦈ ⊑ X / ⦇ S ⦈ ˘
      ⇐⟨ foldR-universal-⇐-⊒ F (X / ⦇ S ⦈ ˘) R ⟩
        R ○ fmapR F (X / ⦇ S ⦈ ˘) ⊑ (X / ⦇ S ⦈ ˘) ○ fun In
      ⇐⟨ ⊑-trans id-elim-r ⟩
        (R ○ fmapR F (X / ⦇ S ⦈ ˘)) ○ idR ⊑ (X / ⦇ S ⦈ ˘) ○ fun In
      ⇐⟨ ⊑-trans (○-monotonic-r fun-entire) ⟩
        (R ○ fmapR F (X / ⦇ S ⦈ ˘)) ○ (fun In ˘) ○ (fun In) ⊑ (X / ⦇ S ⦈ ˘) ○ fun In
      ⇐⟨ ⇦-mono-l (R ○ fmapR F (X / ⦇ S ⦈ ˘) ● (fun In ˘) ‥) ((X / ⦇ S ⦈ ˘) ‥) ⟩
        (R ○ fmapR F (X / ⦇ S ⦈ ˘)) ○ (fun In ˘) ⊑ X / ⦇ S ⦈ ˘
      ⇐⟨ /-universal-⇐ ⟩
        ((R ○ fmapR F (X / ⦇ S ⦈ ˘)) ○ (fun In ˘)) ○ ⦇ S ⦈ ˘ ⊑ X
      ⇐⟨ ⊑-trans ○-assocr ⟩
        (R ○ fmapR F (X / ⦇ S ⦈ ˘)) ○ (fun In ˘) ○ ⦇ S ⦈ ˘ ⊑ X
      ⇐⟨ ⊑-trans (○-monotonic-r In˘FS˘⊑FS˘S˘) ⟩
        (R ○ fmapR F (X / ⦇ S ⦈ ˘)) ○ (fmapR F (⦇ S ⦈ ˘)) ○ S ˘ ⊑ X
      ⇐⟨ ⊑-trans ○-assocl ⟩
        ((R ○ fmapR F (X / ⦇ S ⦈ ˘)) ○ fmapR F (⦇ S ⦈ ˘)) ○ S ˘ ⊑ X
      ⇐⟨ ⊑-trans (○-monotonic-l ○-assocr) ⟩
        (R ○ (fmapR F (X / ⦇ S ⦈ ˘)) ○ fmapR F (⦇ S ⦈ ˘)) ○ S ˘ ⊑ X
      ⇐⟨ ⊑-trans (○-monotonic-l (⇦-mono-r (R ‥) (bimapR-functor-⊑ F))) ⟩
        (R ○ bimapR F (idR ○ idR) (X / ⦇ S ⦈ ˘ ○ ⦇ S ⦈ ˘)) ○ S ˘ ⊑ X
      ⇐⟨ ⊑-trans (⇦-mono-l ((R ○ bimapR F (idR ○ idR) (X / ⦇ S ⦈ ˘ ○ ⦇ S ⦈ ˘)) ‥) (R ● fmapR F X ‥) (○-monotonic-r (bimapR-monotonic-⊑ F id-idempotent-⊑ (/-universal-⇒ ⊑-refl)))) ⟩
        R ○ fmapR F X ○ S ˘ ⊑ X
      ⇐∎
     where
       In˘FS˘⊑FS˘S˘ : fun In ˘ ○ ⦇ S ⦈ ˘ ⊑ fmapR F (⦇ S ⦈ ˘) ○ S ˘
       In˘FS˘⊑FS˘S˘ =
         (⇐-begin
            fun In ˘ ○ ⦇ S ⦈ ˘ ⊑ fmapR F (⦇ S ⦈ ˘) ○ S ˘
          ⇐⟨ ⊑-trans (˘-○-distr-⊒ (⦇ S ⦈) (fun In)) ⟩
            (⦇ S ⦈ ○ fun In) ˘ ⊑ fmapR F (⦇ S ⦈ ˘) ○ S ˘
          ⇐⟨ ⊒-trans (○-monotonic-l (bimapR-˘-preservation-⊑ F)) ⟩
            (⦇ S ⦈ ○ fun In) ˘ ⊑ (fmapR F ⦇ S ⦈)˘ ○ S ˘
          ⇐⟨ ⊒-trans (˘-○-distr-⊑ S (fmapR F ⦇ S ⦈)) ⟩
            (⦇ S ⦈ ○ fun In) ˘ ⊑ (S ○ fmapR F ⦇ S ⦈) ˘
          ⇐⟨ ˘-monotonic-⇒ ⟩
            ⦇ S ⦈ ○ fun In ⊑ S ○ fmapR F ⦇ S ⦈
          ⇐∎) (foldR-computation-⊑ F S) 

hylo-lfp : {A B C : Set} {F : PolyF} {R : B ← ⟦ F ⟧ A B} {S : C ← ⟦ F ⟧ A C}
          → LeastFixedPoint (_≑_) (_⊑_) (λ X → R ○ fmapR F X ○ S ˘) (⦇ R ⦈ ○ ⦇ S ⦈ ˘)
hylo-lfp = lpfp⇒lfp _≑_ _⊑_ ⊑-isPartialOrder _ (λ x⊑y → ○-monotonic-r (○-monotonic-l (bimapR-monotonic-⊑ _ ⊑-refl x⊑y))) _ hylo-lpfp


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
