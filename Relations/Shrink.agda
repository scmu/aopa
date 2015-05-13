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
open import Relations.Function
open import Data.Generic
open import AlgebraicReasoning.Equivalence
open import AlgebraicReasoning.Implications
open import AlgebraicReasoning.Relations
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
   ⇐⟨ proj₂ hylo-lpfp ⟩
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

greedy-theorem : {A B C : Set} {F : PolyF} {S : C ← ⟦ F ⟧ A C} {T : B ← ⟦ F ⟧ A B} {R : C ← C} {Q : ⟦ F ⟧ A B ← ⟦ F ⟧ A B}
               → IsPreorder (_≡_) R
               → S ○ S ˘ ⊑ idR
               → S ○ bimapR F idR R ⊑ R ○ S
               → S ○ bimapR F idR ((foldR F S) ○ (foldR F T ˘)) ○ (Q ⊓ (T ˘ ○ T)) ˘ ⊑ R ˘ ○ S ○ bimapR F idR ((foldR F S) ○ (foldR F T ˘))
               → (foldR F S) ○ (foldR F (((T ˘) ↾ Q) ˘) ˘) ⊑ ((foldR F S) ○ (foldR F T ˘)) ↾ R
greedy-theorem {F = F}{S}{T}{R}{Q} isPre S-simple mono greedy =
  (⇐-begin
     foldR F S ○ foldR F (((T ˘) ↾ Q) ˘) ˘ ⊑ ((foldR F S) ○ (foldR F T ˘)) ↾ R
   ⇐⟨ proj₂ hylo-lpfp ⟩
     S ○ bimapR F idR ((foldR F S ○ foldR F T ˘) ↾ R) ○ (T ˘ ↾ Q) ⊑ ((foldR F S) ○ (foldR F T ˘)) ↾ R
   ⇐⟨ ↾-universal-⇐ ⟩
    ((S ○ bimapR F idR ((foldR F S ○ foldR F T ˘) ↾ R) ○ (T ˘ ↾ Q) ⊑ foldR F S ○ foldR F T ˘) ×
     ((S ○ bimapR F idR ((foldR F S ○ foldR F T ˘) ↾ R) ○ (T ˘ ↾ Q)) ○ (foldR F S ○ foldR F T ˘) ˘ ⊑ R))
   ⇐∎) (pf₁ , pf₂)
 where
   pf₁ : S ○ bimapR F idR ((foldR F S ○ foldR F T ˘) ↾ R) ○ (T ˘ ↾ Q) ⊑ foldR F S ○ foldR F T ˘
   pf₁ =
     ⊑-begin
       S ○ bimapR F idR ((foldR F S ○ foldR F T ˘) ↾ R) ○ (T ˘ ↾ Q)
     ⊑⟨ ○-monotonic-r (○-monotonic-r (↾-universal-⇒₁ {S = Q} ⊑-refl)) ⟩
       S ○ bimapR F idR ((foldR F S ○ foldR F T ˘) ↾ R) ○ (T ˘)
     ⊑⟨ ○-monotonic-r (○-monotonic-l (bimapR-monotonic-⊑ F ⊑-refl (↾-universal-⇒₁ {S = R} ⊑-refl))) ⟩
       S ○ bimapR F idR ((foldR F S ○ foldR F T ˘)) ○ (T ˘)
     ⊑⟨ proj₁ hylo-lpfp ⟩
       foldR F S ○ foldR F T ˘
     ⊑∎

   pf₂ : (S ○ bimapR F idR ((foldR F S ○ foldR F T ˘) ↾ R) ○ (T ˘ ↾ Q)) ○ (foldR F S ○ foldR F T ˘) ˘ ⊑ R
   pf₂ = 
     ⊑-begin
       (S ○ bimapR F idR ((foldR F S ○ foldR F T ˘) ↾ R) ○ (T ˘ ↾ Q)) ○ (foldR F S ○ foldR F T ˘) ˘
     ⊑⟨ ○-monotonic-r (˘-○-distr-⊑ (foldR F S) (foldR F T ˘)) ⟩
       (S ○ bimapR F idR ((foldR F S ○ foldR F T ˘) ↾ R) ○ (T ˘ ↾ Q)) ○ (foldR F T ○ foldR F S ˘)
     ⊑⟨ ○-monotonic-r (proj₂ (proj₁ hylo-lfp)) ⟩
       (S ○ bimapR F idR ((foldR F S ○ foldR F T ˘) ↾ R) ○ (T ˘ ↾ Q)) ○ (T ○ bimapR F idR (foldR F T ○ foldR F S ˘) ○ (S ˘))
     ⊑⟨ ○-assocr ⟩
       S ○ (bimapR F idR ((foldR F S ○ foldR F T ˘) ↾ R) ○ (T ˘ ↾ Q)) ○ (T ○ bimapR F idR (foldR F T ○ foldR F S ˘) ○ (S ˘))
     ⊑⟨ ○-monotonic-r ○-assocr ⟩
       S ○ bimapR F idR ((foldR F S ○ foldR F T ˘) ↾ R) ○ ((T ˘) ⊓ (Q / T)) ○ T ○ bimapR F idR (foldR F T ○ foldR F S ˘) ○ (S ˘)
     ⊑⟨ ⇦-mono (S ● bimapR F idR ((foldR F S ○ foldR F T ˘) ↾ R) ‥) ((T ˘) ⊓ (Q / T) ● T ‥) (((T ˘ ○ T) ⊓ (Q / T ○ T)) ‥) ○-⊓-distr-r ⟩
       S ○ bimapR F idR ((foldR F S ○ foldR F T ˘) ↾ R) ○ (((T ˘) ○ T) ⊓ ((Q / T) ○ T)) ○ bimapR F idR (foldR F T ○ foldR F S ˘) ○ (S ˘)
     ⊑⟨ ⇦-mono (S ● bimapR F idR ((foldR F S ○ foldR F T ˘) ↾ R) ‥) (((T ˘ ○ T) ⊓ (Q / T ○ T)) ‥) (((T ˘ ○ T) ⊓ Q) ‥) (⊓-monotonic ⊑-refl (/-universal-⇒ ⊑-refl)) ⟩
       S ○ bimapR F idR ((foldR F S ○ foldR F T ˘) ↾ R) ○ (((T ˘) ○ T) ⊓ Q) ○ bimapR F idR (foldR F T ○ foldR F S ˘) ○ (S ˘)
     ⊑⟨ ○-monotonic-r (○-monotonic-r (○-monotonic-r (○-monotonic-l (bimapR-monotonic-⊑ F ⊑-refl (˘-○-distr-⊒ (foldR F S) (foldR F T ˘)))))) ⟩
       S ○ bimapR F idR ((foldR F S ○ foldR F T ˘) ↾ R) ○ (((T ˘) ○ T) ⊓ Q) ○ bimapR F idR ((foldR F S ○ foldR F T ˘) ˘) ○ (S ˘)
     ⊑⟨ ○-monotonic-r (○-monotonic-r greedy-˘) ⟩
       S ○ bimapR F idR ((foldR F S ○ foldR F T ˘) ↾ R) ○ bimapR F idR ((foldR F S ○ foldR F T ˘) ˘) ○ (S ˘) ○ R
     ⊑⟨ ⇦-mono (S ‥) (bimapR F idR (foldR F S ○ foldR F T ˘ ↾ R) ●
                        bimapR F idR ((foldR F S ○ foldR F T ˘) ˘) ‥)
                     (bimapR F (idR ○ idR)
                       ((foldR F S ○ foldR F T ˘ ↾ R) ○ (foldR F S ○ foldR F T ˘) ˘) ‥) (bimapR-functor-⊑ F) ⟩
       S ○ bimapR F (idR ○ idR) (((foldR F S ○ foldR F T ˘) ↾ R) ○ ((foldR F S ○ foldR F T ˘) ˘)) ○ (S ˘) ○ R
     ⊑⟨ ○-monotonic-r (○-monotonic-l (bimapR-monotonic-⊑ F id-idempotent-⊑ (↾-universal-⇒₂ ⊑-refl))) ⟩
       S ○ bimapR F idR R ○ (S ˘) ○ R
     ⊑⟨ ⇦-mono-l (S ● bimapR F idR R ‥) (R ● S ‥) mono ⟩
       R ○ S ○ S ˘ ○ R
     ⊑⟨ ⇦-mono (R ‥) (S ● (S ˘) ‥) (idR ‥) S-simple ⟩
       R ○ idR ○ R
     ⊑⟨ ○-monotonic-r id-intro-l ⟩
       R ○ R
     ⊑⟨ transitive-○ isPre ⟩
       R
     ⊑∎
    where
      greedy-˘ : (T ˘ ○ T) ⊓ Q ○ bimapR F idR ((foldR F S ○ foldR F T ˘) ˘) ○ (S ˘) ⊑ bimapR F idR ((foldR F S ○ foldR F T ˘) ˘) ○ (S ˘) ○ R
      greedy-˘ =
        (⇐-begin
           (T ˘ ○ T) ⊓ Q ○ bimapR F idR ((foldR F S ○ foldR F T ˘) ˘) ○ (S ˘) ⊑ bimapR F idR ((foldR F S ○ foldR F T ˘) ˘) ○ (S ˘) ○ R
         ⇐⟨ ˘-universal-⇐ ⟩
           ((T ˘ ○ T) ⊓ Q ○ bimapR F idR ((foldR F S ○ foldR F T ˘) ˘) ○ (S ˘)) ˘ ⊑ (bimapR F idR ((foldR F S ○ foldR F T ˘) ˘) ○ (S ˘) ○ R) ˘
         ⇐⟨ ⊑-trans ˘-○-distr3-⊑ ⟩
           S ○ (bimapR F idR ((foldR F S ○ foldR F T ˘) ˘) ˘) ○ ((T ˘ ○ T) ⊓ Q) ˘ ⊑ (bimapR F idR ((foldR F S ○ foldR F T ˘) ˘) ○ (S ˘) ○ R) ˘
         ⇐⟨ ⊑-trans (○-monotonic-r (○-monotonic-l (bimapR-˘-preservation-⊑ F))) ⟩
           S ○ bimapR F idR (foldR F S ○ foldR F T ˘) ○ ((T ˘ ○ T) ⊓ Q) ˘ ⊑ (bimapR F idR ((foldR F S ○ foldR F T ˘) ˘) ○ (S ˘) ○ R) ˘
         ⇐⟨ ⊒-trans (˘-○-distr3-⊒ (bimapR F idR ((foldR F S ○ foldR F T ˘) ˘)) (S ˘) R) ⟩
           S ○ bimapR F idR (foldR F S ○ foldR F T ˘) ○ ((T ˘ ○ T) ⊓ Q) ˘ ⊑ R ˘ ○ S ○ (bimapR F idR ((foldR F S ○ foldR F T ˘) ˘) ˘)
         ⇐⟨ ⊒-trans (○-monotonic-r (○-monotonic-r (bimapR-˘-preservation-⊒ F))) ⟩
           S ○ bimapR F idR (foldR F S ○ foldR F T ˘) ○ ((T ˘ ○ T) ⊓ Q) ˘ ⊑ R ˘ ○ S ○ bimapR F idR (foldR F S ○ foldR F T ˘)
         ⇐⟨ ⊑-trans (○-monotonic-r (○-monotonic-r ⊓-commute)) ⟩
           S ○ bimapR F idR (foldR F S ○ foldR F T ˘) ○ (Q ⊓ (T ˘ ○ T)) ˘ ⊑ R ˘ ○ S ○ bimapR F idR (foldR F S ○ foldR F T ˘)
         ⇐∎) greedy
