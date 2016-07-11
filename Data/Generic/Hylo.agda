module Data.Generic.Hylo where

open import Level renaming (_⊔_ to _⊔ℓ_)
open import Function using (_∘_; id)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; ∃; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality

open import Sets using (_⊆_; ⊆-trans)
open import Relations
open import Relations.Converse
open import Relations.Coreflexive
open import Relations.Function
open import Relations.Factor
open import Relations.MonoFactor
open import Relations.CompChain
open import Relations.WellFound
open import Relations.Poset
open import FixedPoint
open import AlgebraicReasoning.Implications
open import AlgebraicReasoning.Relations

open import Data.Generic.Core
open import Data.Generic.Membership
open import Data.Generic.Fold

-- ⦇ R ⦈ ○ ⦇ S ⦈ ˘ is a least prefixed point. That is,
--    R ○ fmapR F (⦇ R ⦈ ○ ⦇ S ⦈ ˘) ○ S ˘ ⊑ ⦇ R ⦈ ○ ⦇ S ⦈ ˘     ∧
--    ∀ {X} → R ○ fmapR F X ○ S ˘ ⊑ X → ⦇ R ⦈ ○ ⦇ S ⦈ ˘ ⊑ X


hylo-lpfp : {A B C : Set} {F : PolyF} {R : B ← ⟦ F ⟧ A B} {S : C ← ⟦ F ⟧ A C}
          → LeastPrefixedPoint (_⊑_) (λ X → R ○ fmapR F X ○ S ˘) (⦇ R ⦈ ○ ⦇ S ⦈ ˘)
hylo-lpfp {F = F} {R} {S} = (pfp , least)
  where
    pfp : R ○ fmapR F (⦇ R ⦈ ○ ⦇ S ⦈ ˘) ○ S ˘ ⊑ ⦇ R ⦈ ○ ⦇ S ⦈ ˘
    pfp =
      ⊑-begin
        R ○ fmapR F (⦇ R ⦈ ○ ⦇ S ⦈ ˘) ○ S ˘
      ⊑⟨ ○-monotonic-r (○-monotonic-l (fmapR-functor-⊒ F)) ⟩
        R ○ (fmapR F ⦇ R ⦈ ○ fmapR F (⦇ S ⦈ ˘)) ○ S ˘
      ⊑⟨ ○-monotonic-r ○-assocr ⟩
        R ○ fmapR F ⦇ R ⦈ ○ fmapR F (⦇ S ⦈ ˘) ○ S ˘
      ⊑⟨ ⇦-mono-l (R ● fmapR F ⦇ R ⦈ ‥) (⦇ R ⦈ ● fun In ‥) (foldR-computation-⊒ R) ⟩
        ⦇ R ⦈ ○ fun In ○ fmapR F (⦇ S ⦈ ˘) ○ S ˘
      ⊑⟨ ○-monotonic-r ⦇S⦈˘-computation ⟩
        ⦇ R ⦈ ○ ⦇ S ⦈ ˘
      ⊑∎
     where ⦇S⦈˘-computation : fun In ○ fmapR F (⦇ S ⦈ ˘) ○ S ˘ ⊑ ⦇ S ⦈ ˘
           ⦇S⦈˘-computation =
             ⊒-begin
               ⦇ S ⦈ ˘
             ⊒⟨ ˘-monotonic-⇐ (foldR-computation'-⊒ S) ⟩
               (S ○ fmapR F ⦇ S ⦈ ○ fun In ˘) ˘
             ⊒⟨ ˘-○-distr3-⊒ S _ _ ⟩
               ((fun In) ˘) ˘ ○ (fmapR F ⦇ S ⦈) ˘ ○ S ˘
             ⊒⟨ ○-monotonic-l ˘-idempotent-⊒ ⟩
               fun In ○ fmapR F ⦇ S ⦈ ˘ ○ S ˘
             ⊒⟨ ○-monotonic-r (○-monotonic-l (fmapR-˘-preservation-⊒ F)) ⟩
               fun In ○ fmapR F (⦇ S ⦈ ˘) ○ S ˘
             ⊒∎

    least : ∀ {X} → R ○ fmapR F X ○ S ˘ ⊑ X → ⦇ R ⦈ ○ ⦇ S ⦈ ˘ ⊑ X
    least {X} =
      ⇐-begin
        ⦇ R ⦈ ○ ⦇ S ⦈ ˘ ⊑ X
      ⇐⟨ /-universal-⇒ ⟩
        ⦇ R ⦈ ⊑ X / (⦇ S ⦈ ˘)
      ⇐⟨ foldR-universal-⇐-⊒ F (X / (⦇ S ⦈ ˘)) R ⟩
        R ○ fmapR F (X / (⦇ S ⦈ ˘)) ⊑ (X / (⦇ S ⦈ ˘)) ○ fun In
      ⇐⟨ ⊑-trans id-elim-r ⟩
        (R ○ fmapR F (X / (⦇ S ⦈ ˘))) ○ idR ⊑ (X / (⦇ S ⦈ ˘)) ○ fun In
      ⇐⟨ ⊑-trans (○-monotonic-r fun-entire) ⟩
        (R ○ fmapR F (X / (⦇ S ⦈ ˘))) ○ (fun In ˘) ○ (fun In) ⊑ (X / (⦇ S ⦈ ˘)) ○ fun In
      ⇐⟨ ⇦-mono-l (R ○ fmapR F (X / (⦇ S ⦈ ˘)) ● (fun In ˘) ‥) ((X / (⦇ S ⦈ ˘)) ‥) ⟩
        (R ○ fmapR F (X / (⦇ S ⦈ ˘))) ○ (fun In ˘) ⊑ X / (⦇ S ⦈ ˘)
      ⇐⟨ /-universal-⇐ ⟩
        ((R ○ fmapR F (X / (⦇ S ⦈ ˘))) ○ (fun In ˘)) ○ ⦇ S ⦈ ˘ ⊑ X
      ⇐⟨ ⊑-trans ○-assocr ⟩
        (R ○ fmapR F (X / (⦇ S ⦈ ˘))) ○ (fun In ˘) ○ ⦇ S ⦈ ˘ ⊑ X
      ⇐⟨ ⊑-trans (○-monotonic-r In˘FS˘⊑FS˘S˘) ⟩
        (R ○ fmapR F (X / (⦇ S ⦈ ˘))) ○ (fmapR F (⦇ S ⦈ ˘)) ○ S ˘ ⊑ X
      ⇐⟨ ⊑-trans ○-assocl ⟩
        ((R ○ fmapR F (X / (⦇ S ⦈ ˘))) ○ fmapR F (⦇ S ⦈ ˘)) ○ S ˘ ⊑ X
      ⇐⟨ ⊑-trans (○-monotonic-l ○-assocr) ⟩
        (R ○ (fmapR F (X / (⦇ S ⦈ ˘))) ○ fmapR F (⦇ S ⦈ ˘)) ○ S ˘ ⊑ X
      ⇐⟨ ⊑-trans (○-monotonic-l (⇦-mono-r (R ‥) (fmapR-functor-⊑ F))) ⟩
        (R ○ fmapR F (X / (⦇ S ⦈ ˘) ○ ⦇ S ⦈ ˘)) ○ S ˘ ⊑ X
      ⇐⟨ ⊑-trans (⇦-mono-l ((R ○ fmapR F (X / (⦇ S ⦈ ˘) ○ ⦇ S ⦈ ˘)) ‥) (R ● fmapR F X ‥) (○-monotonic-r (fmapR-monotonic F (/-universal-⇒ ⊑-refl)))) ⟩
        R ○ fmapR F X ○ S ˘ ⊑ X
      ⇐∎
     where
       In˘FS˘⊑FS˘S˘ : fun In ˘ ○ ⦇ S ⦈ ˘ ⊑ fmapR F (⦇ S ⦈ ˘) ○ S ˘
       In˘FS˘⊑FS˘S˘ =
         (⇐-begin
            fun In ˘ ○ ⦇ S ⦈ ˘ ⊑ fmapR F (⦇ S ⦈ ˘) ○ S ˘
          ⇐⟨ ⊑-trans (˘-○-distr-⊒ (⦇ S ⦈) (fun In)) ⟩
            (⦇ S ⦈ ○ fun In) ˘ ⊑ fmapR F (⦇ S ⦈ ˘) ○ S ˘
          ⇐⟨ ⊒-trans (○-monotonic-l (fmapR-˘-preservation-⊑ F)) ⟩
            (⦇ S ⦈ ○ fun In) ˘ ⊑ (fmapR F ⦇ S ⦈)˘ ○ S ˘
          ⇐⟨ ⊒-trans (˘-○-distr-⊑ S (fmapR F ⦇ S ⦈)) ⟩
            (⦇ S ⦈ ○ fun In) ˘ ⊑ (S ○ fmapR F ⦇ S ⦈) ˘
          ⇐⟨ ˘-monotonic-⇒ ⟩
            ⦇ S ⦈ ○ fun In ⊑ S ○ fmapR F ⦇ S ⦈
          ⇐∎) (foldR-computation-⊑ S) 

-- ⦇ R ⦈ ○ ⦇ S ⦈ ˘ is a least fixed point. That is, 
--    R ○ fmapR F (⦇ R ⦈ ○ ⦇ S ⦈ ˘) ○ S ˘ ≑ ⦇ R ⦈ ○ ⦇ S ⦈ ˘     ∧
--    ∀ {X} → R ○ fmapR F X ○ S ˘ ≑ X → ⦇ R ⦈ ○ ⦇ S ⦈ ˘ ≑ X

hylo-lfp : {A B C : Set} {F : PolyF} {R : B ← ⟦ F ⟧ A B} {S : C ← ⟦ F ⟧ A C}
          → LeastFixedPoint (_≑_) (_⊑_) (λ X → R ○ fmapR F X ○ S ˘) (⦇ R ⦈ ○ ⦇ S ⦈ ˘)
hylo-lfp = lpfp⇒lfp _≑_ _⊑_ ⊑-isPartialOrder _ (λ x⊑y → ○-monotonic-r (○-monotonic-l (bimapR-monotonic _ ⊑-refl x⊑y))) _ hylo-lpfp


-- Consider f X = R ○ fmapR F X ○ S.
-- If (ε F ○ S) is inductive, any postfixed-point of
-- f is at most any prefixed-point of f.

hylo-post⊑pre : {A B C : Set} {F : PolyF} {R : B ← ⟦ F ⟧ A B} {S : ⟦ F ⟧ A C ← C}
            → well-found (ε F ○ S)
            → {X : B ← C} → X ⊑ R ○ fmapR F X ○ S
            → {Y : B ← C} → Y ⊒ R ○ fmapR F Y ○ S
            → X ⊑ Y          
hylo-post⊑pre {F = F} {R} {S} wf {X} X-postfix {Y} Y-prefix =
  (⇐-begin
     X ⊑ Y     
   ⇐⟨ ⊑-trans (refl-elim-r (total-pred wf)) ⟩
     X ○ (Acc (ε F ○ S)) ¿ ⊑ Y     
   ⇐⟨ ⋱-universal-⇒ (Acc (ε F ○ S)) _ _ ⟩
     Acc (ε F ○ S) ⊆ X ⋱ Y
   ⇐⟨ acc-fold (ε F ○ S) ⟩
     (ε F ○ S) ⍀ (X ⋱ Y) ⊆ X ⋱ Y
   ⇐⟨ ⊆-trans (ε-⍀-⊆ _ _) ⟩
     S ⍀ (fmapP F (X ⋱ Y)) ⊆ X ⋱ Y
   ⇐⟨ ⋱-universal-⇐ _ _ _ ⟩
     X ○ (S ⍀ (fmapP F (X ⋱ Y))) ¿ ⊑ Y
   ⇐⟨ ⊑-trans (⇦-mono-l (X ‥) (R ● fmapR F X ● S ‥) X-postfix) ⟩
     R ○ fmapR F X ○ S ○ (S ⍀ fmapP F (X ⋱ Y)) ¿ ⊑ Y
   ⇐⟨ ⊑-trans (⇦-mono-r (R ● fmapR F X ‥) (⍀-cancellation _ _)) ⟩
     R ○ fmapR F X ○ fmapP F (X ⋱ Y) ¿ ○ S ⊑ Y
   ⇐⟨ ⊑-trans (⇦-mono (R ● fmapR F X ‥) (fmapP F (X ⋱ Y) ¿ ‥) (fmapR F ((X ⋱ Y) ¿) ‥) (fmap-¿-⊑ F _)) ⟩
     R ○ fmapR F X ○ fmapR F ((X ⋱ Y) ¿) ○ S ⊑ Y
   ⇐⟨ ⊑-trans (⇦-mono (R ‥) (fmapR F X ● fmapR F ((X ⋱ Y) ¿) ‥) (fmapR F (X ○ (X ⋱ Y) ¿) ‥) (fmapR-functor-⊑ F)) ⟩
     R ○ fmapR F (X ○ (X ⋱ Y) ¿) ○ S ⊑ Y
   ⇐⟨ ⊑-trans (⇦-mono (R ‥) (fmapR F (X ○ (X ⋱ Y) ¿) ‥) (fmapR F Y ‥)
        (bimapR-monotonic F ⊑-refl (⋱-cancellation _ _))) ⟩
     R ○ fmapR F Y ○ S ⊑ Y
   ⇐∎) Y-prefix
  
-- Therefore, if (ε F ○ S) is inductive, 
-- f X = R ○ fmapR F X ○ S has a unique fixed point, if any.

hylo-unique : {A B C : Set} {F : PolyF} {R : B ← ⟦ F ⟧ A B} {S : ⟦ F ⟧ A C ← C}
            → well-found (ε F ○ S)
            → {X : B ← C} → X ≑ R ○ fmapR F X ○ S
            → {Y : B ← C} → Y ≑ R ○ fmapR F Y ○ S
            → X ≑ Y
hylo-unique wf (X-post , X-pre) (Y-post , Y-pre) =
  (hylo-post⊑pre wf X-post Y-pre , hylo-post⊑pre wf Y-post X-pre)          
            
-- a functional hylomoprhism

mutual
 hylo-acc : {F : PolyF} → ∀ {j} {A : Set} {B : Set j} {C : Set}
          → (f : ⟦ F ⟧ A B → B) → (g : C → ⟦ F ⟧ A C)
          → (c : C) → Acc (ε F ○ fun g) c → B
 hylo-acc {F} {A = A} {B} {C} f g c (acc .c h) =
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
 fmap-hylo f g c h arg₂ (snd y) p = snd (hylo-acc f g y (h y (g c , refl , path-to-ε p)))
 fmap-hylo f g c h (G₀ ⊕ G₁) (inj₁ y) p = inj₁ (fmap-hylo f g c h G₀ y (inj₁ p))
 fmap-hylo f g c h (G₀ ⊕ G₁) (inj₂ y) p = inj₂ (fmap-hylo f g c h G₁ y (inj₂ p))
 fmap-hylo f g c h (G₀ ⊗ G₁) (y₀ , y₁) p =
   fmap-hylo f g c h G₀ y₀ (out₁ p) ,
   fmap-hylo f g c h G₁ y₁ (out₂ p)

hylo : {F : PolyF} → ∀ {j} {A : Set} {B : Set j} {C : Set}
     → (f : ⟦ F ⟧ A B → B) → (g : C → ⟦ F ⟧ A C)
     → well-found (ε F ○ fun g)
     → C → B
hylo f g wf c = hylo-acc f g c (wf c)

-- proof irrelevance: as long as there is a proof of
-- accessibility, we don't care which one.

mutual
  hylo-acc-irr : {F : PolyF} → ∀ {j} {A : Set} {B : Set j} {C : Set}
               → (f : ⟦ F ⟧ A B → B) → (g : C → ⟦ F ⟧ A C)
               → (c : C)
               → (ac₁ : Acc (ε F ○ fun g) c) → (ac₂ : Acc (ε F ○ fun g) c)
               → hylo-acc f g c ac₁ ≡ hylo-acc f g c ac₂
  hylo-acc-irr {F} f g c (acc ._ h₁) (acc ._ h₂) 
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
   rewrite hylo-acc-irr f g y (h₁ y (g c , refl , path-to-ε p))
                              (h₂ y (g c , refl , path-to-ε p)) = refl
  fmap-hylo-irr f g c h₁ h₂ (G₀ ⊕ G₁) (inj₁ x) p
   rewrite fmap-hylo-irr f g c h₁ h₂ G₀ x (inj₁ p) = refl
  fmap-hylo-irr f g c h₁ h₂ (G₀ ⊕ G₁) (inj₂ y) p
   rewrite fmap-hylo-irr f g c h₁ h₂ G₁ y (inj₂ p) = refl
  fmap-hylo-irr f g c h₁ h₂ (G₀ ⊗ G₁) (y₀ , y₁) p
   rewrite fmap-hylo-irr f g c h₁ h₂ G₀ y₀ (out₁ p)
         | fmap-hylo-irr f g c h₁ h₂ G₁ y₁ (out₂ p) = refl

fmap-hylo-fmap :
           {F : PolyF} {j : Level} {A : Set} {B : Set j} {C : Set}
           → (f : ⟦ F ⟧ A B → B) → (g : C → ⟦ F ⟧ A C) → (wf : well-found (ε F ○ fun g))
           → (c : C)  → (h : ∀ z → (ε F ○ fun g) z c → Acc (ε F ○ fun g) z)
           → (G : PolyF) → (y : ⟦ G ⟧ A C)
           → (p : Path F (g c) G y)
           → fmap-hylo f g c h G y p ≡
               fmap G (λ d → hylo-acc f g d (wf d)) y
fmap-hylo-fmap f g wf c h zer () p
fmap-hylo-fmap f g wf c h one tt p = refl
fmap-hylo-fmap f g wf c h arg₁ (fst x) p = refl
fmap-hylo-fmap f g wf c h arg₂ (snd x) p
   rewrite hylo-acc-irr f g x (h x (g c , refl , path-to-ε p)) (wf x) = refl
fmap-hylo-fmap f g wf c h (G₀ ⊕ G₁) (inj₁ x) p
   rewrite fmap-hylo-fmap f g wf c h G₀ x (inj₁ p) = refl
fmap-hylo-fmap f g wf c h (G₀ ⊕ G₁) (inj₂ y) p
   rewrite fmap-hylo-fmap f g wf c h G₁ y (inj₂ p) = refl
fmap-hylo-fmap f g wf c h (G₀ ⊗ G₁) (y₀ , y₁) p
   rewrite fmap-hylo-fmap f g wf c h G₀ y₀ (out₁ p)
         | fmap-hylo-fmap f g wf c h G₁ y₁ (out₂ p) = refl

hylo-is-hylo : {F : PolyF} → ∀ {j} {A : Set} {B : Set j} {C : Set}
               → (f : ⟦ F ⟧ A B → B) → (g : C → ⟦ F ⟧ A C)
               → (wf : well-found (ε F ○ fun g))
               → (c : C)
               → hylo f g wf c ≡ (f ∘ fmap F (hylo f g wf) ∘ g) c
hylo-is-hylo {F} f g wf c with wf c
... | acc ._ h rewrite fmap-hylo-fmap f g wf c h F (g c) root = refl


hylo-fix : {F : PolyF} → ∀ {A B C : Set}
         → (f : ⟦ F ⟧ A B → B) → (g : C → ⟦ F ⟧ A C)
         → (wf : well-found (ε F ○ fun g))
         → fun (hylo f g wf) ≑
              fun f ○ fmapR F (fun (hylo f g wf)) ○ fun g
hylo-fix {F} f g wf =
  ≑-begin
    fun (hylo f g wf)
  ≑⟨  fun-cong (hylo-is-hylo f g wf) ⟩
    fun (f ∘ fmap F (hylo f g wf) ∘ g)
  ≑⟨ fun○3-≑ ⟩
    fun f ○ fun (fmap F (hylo f g wf)) ○ fun g
  ≑⟨ ○-cong-r (○-cong-l (fmap-fmapR _ _)) ⟩
    fun f ○ fmapR F (fun (hylo f g wf)) ○ fun g
  ≑∎

hylo-refine : {F : PolyF} → ∀ {A B C : Set}
            → (f : ⟦ F ⟧ A B → B) → (g : C → ⟦ F ⟧ A C)
            → (wf : well-found (ε F ○ fun g))
            → ⦇ fun f  ⦈ ○ ⦇ (fun g)˘ ⦈ ˘ ≑ fun (hylo f g wf)
hylo-refine {F} f g wf =
  hylo-unique wf fp (hylo-fix f g wf)
 where fp : ⦇ fun f ⦈ ○ ⦇ (fun g)˘ ⦈ ˘ ≑
                fun f ○ fmapR F (⦇ fun f ⦈ ○ ⦇ (fun g)˘ ⦈ ˘) ○ fun g
       fp =
         ≑-begin
            ⦇ fun f ⦈ ○ ⦇ (fun g)˘ ⦈ ˘
         ≑⟨ ≑-sym (proj₁ hylo-lfp) ⟩
            fun f ○ fmapR F (⦇ fun f ⦈ ○ ⦇ (fun g)˘ ⦈ ˘) ○ ((fun g)˘) ˘
         ≑⟨ ○-cong-r (○-cong-r ˘-idempotent) ⟩
            fun f ○ fmapR F (⦇ fun f ⦈ ○ ⦇ fun g ˘ ⦈ ˘) ○ fun g
         ≑∎
         
