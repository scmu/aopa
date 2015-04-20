module Relations.Shrink where

open import Level renaming (_⊔_ to _⊔ℓ_)
open import Function using (_∘_; id)
open import Data.Product renaming (map to ×-map)

open import Relations
open import Relations.Factor
open import Relations.Product
open import Relations.Converse
open import Relations.CompChain
open import Relations.Galois
open import Data.Generic
open import AlgebraicReasoning.Equivalence
open import AlgebraicReasoning.Implications
open import Relation.Binary using (IsPreorder; Transitive)
open import Relation.Binary.PropositionalEquality


infixr 7 _↾_

_↾_ : ∀ {i j} {A : Set i} {B : Set j}
      → (R : A ← B ⊣ (i ⊔ℓ j)) → (S : A ← A ⊣ (i ⊔ℓ j))
      → (A ← B ⊣ (i ⊔ℓ j))
R ↾ S = R ⊓ (S / R ˘)

↾-universal-⇒₁ : ∀ {i j} {A : Set i} {B : Set j}
                 → {X R : A ← B} {S : A ← A}
                 → X ⊑ R ↾ S 
                 → X ⊑ R
↾-universal-⇒₁ X⊑R↾S = proj₁ (⊓-universal-⇒ X⊑R↾S)

↾-universal-⇒₂ : ∀ {i j} {A : Set i} {B : Set j}
                 → {X R : A ← B} {S : A ← A}
                 → X ⊑ R ↾ S 
                 → X ○ R ˘ ⊑ S 
↾-universal-⇒₂ {X = X} {R} {S} = 
  ⇒-begin 
    X ⊑ R ↾ S 
  ⇒⟨ proj₂ ∘ ⊓-universal-⇒ ⟩ 
    X ⊑ S / R ˘ 
  ⇒⟨ /-universal-⇒ ⟩ 
    X ○ R ˘ ⊑ S 
  ⇒∎

↾-universal-⇒ : ∀ {i j} {A : Set i} {B : Set j}
                 → {X R : A ← B} {S : A ← A}
                 → X ⊑ R ↾ S 
                 → (X ⊑ R) × (X ○ R ˘ ⊑ S)
↾-universal-⇒ X⊑R↾S = (↾-universal-⇒₁ X⊑R↾S , ↾-universal-⇒₂ X⊑R↾S)

↾-universal-⇐ : ∀ {i j} {A : Set i} {B : Set j}
                 → {X R : A ← B} {S : A ← A}
                 → (X ⊑ R) × (X ○ R ˘ ⊑ S)
                 → X ⊑ R ↾ S 
↾-universal-⇐ {X = X} {R} {S} (X⊑R , XR˘⊑S) = 
  (⇐-begin 
     X ⊑ R ↾ S 
   ⇐⟨ id ⟩ 
     X ⊑ R ⊓ (S / (R ˘)) 
   ⇐⟨ ⊓-universal-⇐ ⟩ 
     (X ⊑ R × X ⊑ S / (R ˘)) 
   ⇐⟨ ×-map id /-universal-⇐ ⟩
     (X ⊑ R × X ○ R ˘ ⊑ S) 
   ⇐∎) (X⊑R , XR˘⊑S)

↾-universal : ∀ {i j} {A : Set i} {B : Set j}
              → {X R : A ← B} {S : A ← A}
              → X ⊑ R ↾ S ⇔
                ((X ⊑ R) × (X ○ R ˘ ⊑ S))
↾-universal {S = S} = ↾-universal-⇒ , ↾-universal-⇐

galois-shrink : ∀ {i} {A B : Set i}
         → (f : A → B) (g : B → A)
         → (R : B ← B ⊣ i) (S : A ← A ⊣ i)
         → IsPreorder (_≡_) S
         → galois f g R S
         → fun g ⊑ ((fun f)˘ ○ R) ↾ (S ˘)
galois-shrink f g R S isPre gal = ↾-universal-⇐ (g⊑f˘R , gR˘f⊑S˘)
  where g⊑f˘R : fun g ⊑ (fun f ˘ ○ R)
        g⊑f˘R = galois-easy-⇒ {S = S} isPre gal

        gR˘f⊑S˘ : fun g ○ ((fun f ˘ ○ R)) ˘ ⊑ S ˘ 
        gR˘f⊑S˘ = galois-hard-⇒ gal


foldR-↾-absorption : (F : PolyF) → {A B : Set}
                   → {S : B ← ⟦ F ⟧ A B} {R : B ← B}
                   → IsPreorder (_≡_) R
                   → S ○ bimapR F idR (R ˘) ⊑ (R ˘) ○ S
                   → foldR F (S ↾ R) ⊑ (foldR F S) ↾ R
foldR-↾-absorption F {S = S} {R} isPre SFR˘⊑R˘S =
  (⇐-begin
     foldR F (S ↾ R) ⊑ (foldR F S) ↾ R
   ⇐⟨ ↾-universal-⇐ ⟩
     (((foldR F (S ↾ R)) ⊑ (foldR F S)) × ((foldR F (S ↾ R)) ○ ((foldR F S) ˘) ⊑ R))
   ⇐⟨ _,_ (foldR-monotonic F (S ↾ R) S (↾-universal-⇒₁ {X = S ↾ R} {S} {R} ⊑-refl)) ⟩
     (foldR F (S ↾ R)) ○ ((foldR F S) ˘) ⊑ R
   ⇐⟨ least-prefix-point F (S ↾ R) S R ⟩
     (S ↾ R) ○ bimapR F idR R ○ (S ˘) ⊑ R
   ⇐⟨ ⊑-trans (○-monotonic-r FRS˘⊑S˘R) ⟩
     (S ↾ R) ○ (S ˘) ○ R ⊑ R
   ⇐⟨ ⊑-trans (○-monotonic-l (proj₂ (⊓-universal-⇒ ⊑-refl))) ⟩
     (R / S ˘) ○ (S ˘) ○ R ⊑ R
    ⇐⟨ ⊑-trans (⇦-mono-l ((R / S ˘) ● (S ˘) ‥) (R ‥) (/-universal-⇒ ⊑-refl)) ⟩
     R ○ R ⊑ R
   ⇐∎) (transitive-○ isPre)
  where
    FRS˘⊑S˘R : bimapR F idR R ○ (S ˘) ⊑ (S ˘) ○ R
    FRS˘⊑S˘R = 
      (⇐-begin
         bimapR F idR R ○ (S ˘) ⊑ (S ˘) ○ R
       ⇐⟨ ⊑-trans (○-monotonic-l ˘-idempotent-⊑) ⟩
         ((bimapR F idR R ˘) ˘) ○ (S ˘) ⊑ (S ˘) ○ R
       ⇐⟨ ⊑-trans (○-monotonic-l (˘-monotonic-⇐ (bimapR-˘-preservation-⊑ F))) ⟩
         (bimapR F idR (R ˘) ˘) ○ (S ˘) ⊑ (S ˘) ○ R
       ⇐⟨ ⊒-trans (○-monotonic-r ˘-idempotent-⊑) ⟩
         (bimapR F idR (R ˘) ˘) ○ (S ˘) ⊑ (S ˘) ○ ((R ˘) ˘)
       ⇐⟨ ⊒-trans (˘-○-distr-⊑ (R ˘) S) ⟩
         (bimapR F idR (R ˘) ˘) ○ (S ˘) ⊑ ((R ˘) ○ S) ˘
       ⇐⟨ ⊑-trans (˘-○-distr-⊒ S (bimapR F idR (R ˘))) ⟩
         (S ○ bimapR F idR (R ˘)) ˘ ⊑ ((R ˘) ○ S) ˘
       ⇐⟨ ˘-monotonic-⇐ ⟩
         S ○ bimapR F idR (R ˘) ⊑ (R ˘) ○ S
       ⇐∎) SFR˘⊑R˘S
