module Data.Generic.Core where


open import Data.Empty
open import Data.Unit using (⊤)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; ∃; _×_; _,_; proj₁; proj₂)
open import Function using (_∘_; id)
open import Level renaming (_⊔_ to _⊔ℓ_)
open import Relation.Binary.PropositionalEquality

open import AlgebraicReasoning.ExtensionalEquality 
            using (_≐_)

open import Relations

-- Polynomial bifunctors

data PolyF : Set where
  zer : PolyF 
  one  : PolyF
  arg₁ : PolyF
  arg₂ : PolyF
  _⊕_ : PolyF → PolyF → PolyF
  _⊗_ : PolyF → PolyF → PolyF

data Zero {i} : Set i where

data One {i} : Set i where
  tt : One

data Fst {i j} (A : Set i) : Set (i ⊔ℓ j) where
  fst : A → Fst {i} {j} A

data Snd {i j} (X : Set j) : Set (i ⊔ℓ j) where
  snd : X → Snd {i} {j} X

⟦_⟧ : PolyF → ∀{i j} → (A : Set i) (X : Set j) → Set (i ⊔ℓ j)
⟦ zer ⟧ A X = Zero
⟦ one ⟧ A X = One
⟦ arg₁ ⟧ {i} {j} A X = Fst {i} {j} A
⟦ arg₂ ⟧ {i} {j} A X = Snd {i} {j} X
⟦ l ⊕ r ⟧ A X = ⟦ l ⟧ A X ⊎ ⟦ r ⟧ A X
⟦ l ⊗ r ⟧ A X = ⟦ l ⟧ A X × ⟦ r ⟧ A X

data μ (F : PolyF) {i} (A : Set i) : Set i where
  In : ⟦ F ⟧ A (μ F A) → μ F A

bimap : (F : PolyF) → ∀ {i j k l} {A₁ : Set i} {A₂ : Set j} {B₁ : Set k} {B₂ : Set l}
        → (A₁ → A₂) → (B₁ → B₂) → ⟦ F ⟧ A₁ B₁ → ⟦ F ⟧ A₂ B₂
bimap zer f g ()
bimap one f g tt = tt
bimap arg₁ f g (fst a) = fst (f a)
bimap arg₂ f g (snd b) = snd (g b)
bimap (F₁ ⊕ F₂) f g (inj₁ x) = inj₁ (bimap F₁ f g x)
bimap (F₁ ⊕ F₂) f g (inj₂ y) = inj₂ (bimap F₂ f g y)
bimap (F₁ ⊗ F₂) f g (x , y) = bimap F₁ f g x , bimap F₂ f g y

bimap-comp : (F : PolyF) → ∀ {i j k l m n} {A₁ : Set i} {A₂ : Set j} {A₃ : Set k} {B₁ : Set l} {B₂ : Set m} {B₃ : Set n}
            → (f : A₂ → A₃) → (g : B₂ → B₃) → (h : A₁ → A₂) → (k : B₁ → B₂)
            → (bimap F (f ∘ h) (g ∘ k) ≐ bimap F f g ∘ bimap F h k)
bimap-comp zer f g h k ()
bimap-comp one f g h k tt = refl
bimap-comp arg₁ f g h k (fst x) = refl
bimap-comp arg₂ f g h k (snd y) = refl
bimap-comp (F₁ ⊕ F₂) f g h k (inj₁ x) = cong inj₁ (bimap-comp F₁ f g h k x)
bimap-comp (F₁ ⊕ F₂) f g h k (inj₂ y) = cong inj₂ (bimap-comp F₂ f g h k y)
bimap-comp (F₁ ⊗ F₂) f g h k (x , y)
  rewrite bimap-comp F₁ f g h k x | bimap-comp F₂ f g h k y = refl


-- relational bimap

bimapR : (F : PolyF) → ∀ {i j k l} {A₁ : Set i} {A₂ : Set j} {B₁ : Set k} {B₂ : Set l}
        → (A₂ ← A₁ ⊣ zero) → (B₂ ← B₁ ⊣ zero) → (⟦ F ⟧ A₂ B₂ ← ⟦ F ⟧ A₁ B₁ ⊣ zero)
bimapR zer R S () _
bimapR one R S tt tt = ⊤  -- available only as Set.
bimapR arg₁ R S (fst a₁) (fst a₂) = R a₁ a₂
bimapR arg₂ R S (snd b₁) (snd b₂) = S b₁ b₂
bimapR (F₁ ⊕ F₂) R S (inj₁ x₁) (inj₁ x₂) = bimapR F₁ R S x₁ x₂
bimapR (F₁ ⊕ F₂) R S (inj₁ x₁) (inj₂ y₂) = ⊥
bimapR (F₁ ⊕ F₂) R S (inj₂ y₁) (inj₁ x₂) = ⊥
bimapR (F₁ ⊕ F₂) R S (inj₂ y₁) (inj₂ y₂) = bimapR F₂ R S y₁ y₂
bimapR (F₁ ⊗ F₂) R S (x₁ , y₁) (x₂ , y₂) = bimapR F₁ R S x₁ x₂ × bimapR F₂ R S y₁ y₂

bimapR-functor-⊑ : (F : PolyF) → ∀ {i j k l} {A₁ : Set i} {A₂ : Set} {A₃ : Set j} {B₁ : Set k} {B₂ : Set} {B₃ : Set l}
                   {R : A₃ ← A₂} {S : B₃ ← B₂} {T : A₂ ← A₁} {U : B₂ ← B₁}
                  → bimapR F R S ○ bimapR F T U ⊑ bimapR F (R ○ T) (S ○ U)
bimapR-functor-⊑ zer () _ _
bimapR-functor-⊑ one tt tt _ = Data.Unit.tt
bimapR-functor-⊑ arg₁ (fst z) (fst x) (fst y , yTx , zRy) = (y , yTx , zRy)
bimapR-functor-⊑ arg₂ (snd z) (snd x) (snd y , yUx , zSy) = (y , yUx , zSy)
bimapR-functor-⊑ (F₁ ⊕ F₂) (inj₁ z₁) (inj₁ x₁) (inj₁ y₁ , yTUx , zRSy) = bimapR-functor-⊑ F₁ z₁ x₁ (y₁ , yTUx , zRSy)
bimapR-functor-⊑ (F₁ ⊕ F₂) (inj₁ z₁) (inj₁ x₁) (inj₂ y₂ , () , ())
bimapR-functor-⊑ (F₁ ⊕ F₂) (inj₁ z₁) (inj₂ x₂) (inj₁ y₁ , () , zRSy)
bimapR-functor-⊑ (F₁ ⊕ F₂) (inj₁ z₁) (inj₂ x₂) (inj₂ y₂ , yTUx , ())
bimapR-functor-⊑ (F₁ ⊕ F₂) (inj₂ z₂) (inj₁ x₁) (inj₁ y₁ , yTUx , ())
bimapR-functor-⊑ (F₁ ⊕ F₂) (inj₂ z₂) (inj₁ x₁) (inj₂ y₂ , () , zRSy)
bimapR-functor-⊑ (F₁ ⊕ F₂) (inj₂ z₂) (inj₂ x₂) (inj₁ y₁ , () , ())
bimapR-functor-⊑ (F₁ ⊕ F₂) (inj₂ z₂) (inj₂ x₂) (inj₂ y₂ , yTUx , zRSy) = bimapR-functor-⊑ F₂ z₂ x₂ (y₂ , yTUx , zRSy)
bimapR-functor-⊑ (F₁ ⊗ F₂) (z₁ , z₂) (x₁ , x₂) ((y₁ , y₂) , yTUx , zRSy) =
   (bimapR-functor-⊑ F₁ z₁ x₁ (y₁ , (proj₁ yTUx) , (proj₁ zRSy)) , bimapR-functor-⊑ F₂ z₂ x₂ (y₂ , (proj₂ yTUx) , (proj₂ zRSy)))

bimapR-functor-⊒ : (F : PolyF) → ∀ {i j k l} {A₁ : Set i} {A₂ : Set} {A₃ : Set j} {B₁ : Set k} {B₂ : Set} {B₃ : Set l}
                   {R : A₃ ← A₂} {S : B₃ ← B₂} {T : A₂ ← A₁} {U : B₂ ← B₁}
                  → bimapR F R S ○ bimapR F T U ⊒ bimapR F (R ○ T) (S ○ U)
bimapR-functor-⊒ zer () _ _
bimapR-functor-⊒ one tt tt _ = (tt , Data.Unit.tt , Data.Unit.tt)
bimapR-functor-⊒ arg₁ (fst z) (fst x) (y , yTx , zRy) = (fst y , yTx , zRy)
bimapR-functor-⊒ arg₂ (snd z) (snd x) (y , yUx , zSy) = (snd y , yUx , zSy)
bimapR-functor-⊒ (F₁ ⊕ F₂) (inj₁ z₁) (inj₁ x₁) zRTSUx =
   let
     (y₁ , yRTx , zSUy) = bimapR-functor-⊒ F₁ z₁ x₁ zRTSUx
   in (inj₁ y₁ , yRTx , zSUy)
bimapR-functor-⊒ (F₁ ⊕ F₂) (inj₁ z₁) (inj₂ x₂) ()
bimapR-functor-⊒ (F₁ ⊕ F₂) (inj₂ z₂) (inj₁ x₁) ()
bimapR-functor-⊒ (F₁ ⊕ F₂) (inj₂ z₂) (inj₂ x₂) zRTSUx =
   let
     (y₂ , yRTx , zSUy) = bimapR-functor-⊒ F₂ z₂ x₂ zRTSUx
   in (inj₂ y₂ , yRTx , zSUy)
bimapR-functor-⊒ (F₁ ⊗ F₂) (z₁ , z₂) (x₁ , x₂) zRTSUx =
   let
     (y₁ , yRTx₁ , zSUy₁) = bimapR-functor-⊒ F₁ z₁ x₁ (proj₁ zRTSUx)
     (y₂ , yRTx₂ , zSUy₂) = bimapR-functor-⊒ F₂ z₂ x₂ (proj₂ zRTSUx)
   in ((y₁ , y₂) , (yRTx₁ , yRTx₂) , (zSUy₁ , zSUy₂))

bimapR-monotonic-⊑ : (F : PolyF) → ∀ {i j k l} {A : Set i} {B : Set j} {C : Set k} {D : Set l}
                     {R S : B ← A} {T U : D ← C}
                    → (R ⊑ S) → (T ⊑ U) → (bimapR F R T ⊑ bimapR F S U)
bimapR-monotonic-⊑ zer R⊑S T⊑U () _ _
bimapR-monotonic-⊑ one R⊑S T⊑U tt tt _ = Data.Unit.tt
bimapR-monotonic-⊑ arg₁ R⊑S T⊑U (fst b) (fst a) bRa = R⊑S b a bRa
bimapR-monotonic-⊑ arg₂ R⊑S T⊑U (snd d) (snd c) dTc = T⊑U d c dTc
bimapR-monotonic-⊑ (F₁ ⊕ F₂) R⊑S T⊑U (inj₁ y₁) (inj₁ x₁) yRTx = bimapR-monotonic-⊑ F₁ R⊑S T⊑U y₁ x₁ yRTx
bimapR-monotonic-⊑ (F₁ ⊕ F₂) R⊑S T⊑U (inj₁ y₁) (inj₂ x₂) ()
bimapR-monotonic-⊑ (F₁ ⊕ F₂) R⊑S T⊑U (inj₂ y₂) (inj₁ x₁) ()
bimapR-monotonic-⊑ (F₁ ⊕ F₂) R⊑S T⊑U (inj₂ y₂) (inj₂ x₂) yRTx = bimapR-monotonic-⊑ F₂ R⊑S T⊑U y₂ x₂ yRTx
bimapR-monotonic-⊑ (F₁ ⊗ F₂) R⊑S T⊑U (y₁ , y₂) (x₁ , x₂) yRTx =
   (bimapR-monotonic-⊑ F₁ R⊑S T⊑U y₁ x₁ (proj₁ yRTx) , bimapR-monotonic-⊑ F₂ R⊑S T⊑U y₂ x₂ (proj₂ yRTx))

bimapR-monotonic-⊒ : (F : PolyF) → ∀ {i j k l} {A : Set i} {B : Set j} {C : Set k} {D : Set l}
                     {R S : B ← A} {T U : D ← C}
                    → (R ⊒ S) → (T ⊒ U) → (bimapR F R T ⊒ bimapR F S U)
bimapR-monotonic-⊒ zer R⊒S T⊒U () _ _
bimapR-monotonic-⊒ one R⊒S T⊒U tt tt _ = Data.Unit.tt
bimapR-monotonic-⊒ arg₁ R⊒S T⊒U (fst b) (fst a) bRa = R⊒S b a bRa
bimapR-monotonic-⊒ arg₂ R⊒S T⊒U (snd d) (snd c) dTc = T⊒U d c dTc
bimapR-monotonic-⊒ (F₁ ⊕ F₂) R⊒S T⊒U (inj₁ y₁) (inj₁ x₁) yRTx = bimapR-monotonic-⊒ F₁ R⊒S T⊒U y₁ x₁ yRTx
bimapR-monotonic-⊒ (F₁ ⊕ F₂) R⊒S T⊒U (inj₁ y₁) (inj₂ x₂) ()
bimapR-monotonic-⊒ (F₁ ⊕ F₂) R⊒S T⊒U (inj₂ y₂) (inj₁ x₁) ()
bimapR-monotonic-⊒ (F₁ ⊕ F₂) R⊒S T⊒U (inj₂ y₂) (inj₂ x₂) yRTx = bimapR-monotonic-⊒ F₂ R⊒S T⊒U y₂ x₂ yRTx
bimapR-monotonic-⊒ (F₁ ⊗ F₂) R⊒S T⊒U (y₁ , y₂) (x₁ , x₂) yRTx =
   (bimapR-monotonic-⊒ F₁ R⊒S T⊒U y₁ x₁ (proj₁ yRTx) , bimapR-monotonic-⊒ F₂ R⊒S T⊒U y₂ x₂ (proj₂ yRTx))


bimapR-˘-preservation-⊑ : (F : PolyF) → ∀ {i j} {A : Set} {B : Set i} {C : Set j}
                        → {R : C ← B}
                        →  (bimapR F idR R) ˘ ⊑ bimapR F {A₁ = A} idR (R ˘)
bimapR-˘-preservation-⊑ zer () _ _
bimapR-˘-preservation-⊑ one tt tt _ = Data.Unit.tt
bimapR-˘-preservation-⊑ arg₁ (fst a) (fst .a) refl = refl
bimapR-˘-preservation-⊑ arg₂ (snd b₁) (snd b₂) b₂Rb₁ = b₂Rb₁
bimapR-˘-preservation-⊑ (F₁ ⊕ F₂) (inj₁ x₁) (inj₁ y₁) pf = bimapR-˘-preservation-⊑ F₁ x₁ y₁ pf
bimapR-˘-preservation-⊑ (F₁ ⊕ F₂) (inj₁ x₁) (inj₂ y₂) ()
bimapR-˘-preservation-⊑ (F₁ ⊕ F₂) (inj₂ x₂) (inj₁ y₁) ()
bimapR-˘-preservation-⊑ (F₁ ⊕ F₂) (inj₂ x₂) (inj₂ y₂) pf = bimapR-˘-preservation-⊑ F₂ x₂ y₂ pf
bimapR-˘-preservation-⊑ (F₁ ⊗ F₂) (x₁ , x₂) (y₁ , y₂) pf =
  (bimapR-˘-preservation-⊑ F₁ x₁ y₁ (proj₁ pf) , bimapR-˘-preservation-⊑ F₂ x₂ y₂ (proj₂ pf))


bimapR-˘-preservation-⊒ : (F : PolyF) → ∀ {i j} {A : Set} {B : Set i} {C : Set j}
                        → {R : C ← B}
                        →  (bimapR F idR R) ˘ ⊒ bimapR F {A₁ = A} idR (R ˘)
bimapR-˘-preservation-⊒ zer () _ _
bimapR-˘-preservation-⊒ one tt tt _ = Data.Unit.tt
bimapR-˘-preservation-⊒ arg₁ (fst a) (fst .a) refl = refl
bimapR-˘-preservation-⊒ arg₂ (snd b₁) (snd b₂) b₂Rb₁ = b₂Rb₁
bimapR-˘-preservation-⊒ (F₁ ⊕ F₂) (inj₁ x₁) (inj₁ y₁) pf = bimapR-˘-preservation-⊒ F₁ x₁ y₁ pf
bimapR-˘-preservation-⊒ (F₁ ⊕ F₂) (inj₁ x₁) (inj₂ y₂) ()
bimapR-˘-preservation-⊒ (F₁ ⊕ F₂) (inj₂ x₂) (inj₁ y₁) ()
bimapR-˘-preservation-⊒ (F₁ ⊕ F₂) (inj₂ x₂) (inj₂ y₂) pf = bimapR-˘-preservation-⊒ F₂ x₂ y₂ pf
bimapR-˘-preservation-⊒ (F₁ ⊗ F₂) (x₁ , x₂) (y₁ , y₂) pf =
  (bimapR-˘-preservation-⊒ F₁ x₁ y₁ (proj₁ pf) , bimapR-˘-preservation-⊒ F₂ x₂ y₂ (proj₂ pf))
