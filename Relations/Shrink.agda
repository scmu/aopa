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

greedy-theorem : {A B C : Set} {F : PolyF} {S : B ← ⟦ F ⟧ A B} {R : μ F A ← μ F A} {Q : ⟦ F ⟧ A B ← ⟦ F ⟧ A B}
               → IsPreorder (_≡_) R
               → fun In ○ bimapR F idR R ⊑ R ○ fun In
               → fun In ○ bimapR F idR (foldR F S ˘) ○ (Q ⊓ (S ˘ ○ S)) ˘ ⊑ R ˘ ○ fun In ○ bimapR F idR (foldR F S ˘)
               → (foldR F (((S ˘) ↾ Q) ˘) ˘) ⊑ (foldR F S ˘) ↾ R
greedy-theorem {F = F}{S}{R}{Q} isPre mono greedy =
  (⇐-begin
     (foldR F (((S ˘) ↾ Q) ˘) ˘) ⊑ (foldR F S ˘) ↾ R
   ⇐⟨ ⊑-trans id-elim-l ⟩
     idR ○ foldR F ((S ˘ ↾ Q) ˘) ˘ ⊑ foldR F S ˘ ↾ R
   ⇐⟨ ⊑-trans (○-monotonic-l (idR-foldR-⊑ F)) ⟩
     foldR F (fun In) ○ foldR F ((S ˘ ↾ Q) ˘) ˘ ⊑ foldR F S ˘ ↾ R
   ⇐⟨ proj₂ hylo-lpfp ⟩
     fun In ○ bimapR F idR (foldR F S ˘ ↾ R) ○ (S ˘ ↾ Q) ⊑ foldR F S ˘ ↾ R
   ⇐⟨ ↾-universal-⇐ ⟩
    ((fun In ○ bimapR F idR (foldR F S ˘ ↾ R) ○ (S ˘ ↾ Q) ⊑ foldR F S ˘) ×
     ((fun In ○ bimapR F idR (foldR F S ˘ ↾ R) ○ (S ˘ ↾ Q)) ○ (foldR F S) ⊑ R))
   ⇐∎) (pf₁ , pf₂)
 where
   pf₁ : fun In ○ bimapR F idR (foldR F S ˘ ↾ R) ○ (S ˘ ↾ Q) ⊑ foldR F S ˘
   pf₁ =
     ⊑-begin
       fun In ○ bimapR F idR (foldR F S ˘ ↾ R) ○ (S ˘ ↾ Q)
     ⊑⟨ ○-monotonic-r (○-monotonic-r (↾-universal-⇒₁ {S = Q} ⊑-refl)) ⟩
       fun In ○ bimapR F idR (foldR F S ˘ ↾ R) ○ (S ˘)
     ⊑⟨ ○-monotonic-r (○-monotonic-l (bimapR-monotonic-⊑ F ⊑-refl (↾-universal-⇒₁ {S = R} ⊑-refl))) ⟩
       fun In ○ bimapR F idR (foldR F S ˘) ○ (S ˘)
     ⊑⟨ ○-monotonic-r (○-monotonic-l (bimapR-monotonic-⊑ F ⊑-refl id-elim-l)) ⟩
        fun In ○ bimapR F idR (idR ○ foldR F S ˘) ○ (S ˘)
     ⊑⟨ ○-monotonic-r (○-monotonic-l (bimapR-monotonic-⊑ F ⊑-refl (○-monotonic-l (idR-foldR-⊑ F)))) ⟩
       fun In ○ bimapR F idR (foldR F (fun In) ○ (foldR F S ˘)) ○ (S ˘)
     ⊑⟨ proj₁ hylo-lpfp ⟩
       foldR F (fun In) ○ (foldR F S ˘)
     ⊑⟨ ○-monotonic-l (idR-foldR-⊒ F) ⟩
       idR ○ foldR F S ˘
     ⊑⟨ id-intro-l ⟩
       foldR F S ˘
     ⊑∎

   pf₂ : (fun In ○ bimapR F idR (foldR F S ˘ ↾ R) ○ (S ˘ ↾ Q)) ○ (foldR F S) ⊑ R
   pf₂ =
     ⊑-begin
       (fun In ○ bimapR F idR (foldR F S ˘ ↾ R) ○ (S ˘ ↾ Q)) ○ (foldR F S)
     ⊑⟨ ○-monotonic-r id-elim-r ⟩
       (fun In ○ bimapR F idR (foldR F S ˘ ↾ R) ○ (S ˘ ↾ Q)) ○ (foldR F S ○ idR)
     ⊑⟨ ○-monotonic-r (○-monotonic-r idR⊑InIn˘) ⟩
       (fun In ○ bimapR F idR (foldR F S ˘ ↾ R) ○ (S ˘ ↾ Q)) ○ (foldR F S ○ fun In ○ (fun In ˘))
     ⊑⟨ ○-monotonic-r (⇦-mono-l (foldR F S ● fun In ‥) (S ● bimapR F idR (foldR F S) ‥) (foldR-computation-⊑ F S)) ⟩
       (fun In ○ bimapR F idR (foldR F S ˘ ↾ R) ○ (S ˘ ↾ Q)) ○ (S ○ bimapR F idR (foldR F S) ○ (fun In ˘))
     ⊑⟨ ○-assocr ⟩
       fun In ○ (bimapR F idR (foldR F S ˘ ↾ R) ○ (S ˘ ↾ Q)) ○ S ○ bimapR F idR (foldR F S) ○ (fun In ˘)
     ⊑⟨ ○-monotonic-r ○-assocr ⟩
       fun In ○ bimapR F idR (foldR F S ˘ ↾ R) ○ ((S ˘) ⊓ (Q / S)) ○ S ○ bimapR F idR (foldR F S) ○ (fun In ˘)
     ⊑⟨ ⇦-mono (fun In ● bimapR F idR (foldR F S ˘ ↾ R) ‥) ((S ˘) ⊓ (Q / S) ● S ‥) (((S ˘ ○ S) ⊓ (Q / S ○ S)) ‥) ○-⊓-distr-r ⟩
       fun In ○ bimapR F idR (foldR F S ˘ ↾ R) ○ (((S ˘) ○ S) ⊓ ((Q / S) ○ S)) ○ bimapR F idR (foldR F S) ○ (fun In ˘)
     ⊑⟨ ⇦-mono (fun In ● bimapR F idR (foldR F S ˘ ↾ R) ‥) (((S ˘ ○ S) ⊓ (Q / S ○ S)) ‥) (((S ˘ ○ S) ⊓ Q) ‥) (⊓-monotonic ⊑-refl (/-universal-⇒ ⊑-refl)) ⟩
       fun In ○ bimapR F idR (foldR F S ˘ ↾ R) ○ (((S ˘) ○ S) ⊓ Q) ○ bimapR F idR (foldR F S) ○ (fun In ˘)
     ⊑⟨ ⇦-mono-r (fun In ● bimapR F idR (foldR F S ˘ ↾ R) ‥) greedy-˘ ⟩
       fun In ○ bimapR F idR (foldR F S ˘ ↾ R) ○ bimapR F idR (foldR F S) ○ (fun In ˘) ○ R
     ⊑⟨ ⇦-mono (fun In ‥) (bimapR F idR (foldR F S ˘ ↾ R) ● bimapR F idR (foldR F S) ‥) (bimapR F (idR ○ idR) ((foldR F S ˘ ↾ R) ○ foldR F S) ‥) (bimapR-functor-⊑ F) ⟩
       fun In ○ (bimapR F (idR ○ idR) ((foldR F S ˘ ↾ R) ○ foldR F S)) ○ (fun In ˘) ○ R
     ⊑⟨ ⇦-mono (fun In ‥) (bimapR F (idR ○ idR) ((foldR F S ˘ ↾ R) ○ foldR F S) ‥) (bimapR F idR R ‥) (bimapR-monotonic-⊑ F id-idempotent-⊑ (↾-universal-⇒₂ ⊑-refl)) ⟩
       fun In ○ bimapR F idR R ○ (fun In ˘) ○ R
     ⊑⟨ ⇦-mono-l (fun In ● bimapR F idR R ‥) (R ● fun In ‥) mono ⟩
       R ○ fun In ○ fun In ˘ ○ R
     ⊑⟨ ⇦-mono (R ‥) (fun In ● (fun In ˘) ‥) (idR ‥) fun-simple ⟩
       R ○ idR ○ R
     ⊑⟨ ○-monotonic-r id-intro-l ⟩
       R ○ R
     ⊑⟨ transitive-○ isPre ⟩
       R
     ⊑∎
    where
      idR⊑InIn˘ : idR ⊑ fun In ○ fun In ˘
      idR⊑InIn˘ .(In x) (In x) refl = (x , refl , refl)
      
      greedy-˘ : (S ˘ ○ S) ⊓ Q ○ bimapR F idR (foldR F S) ○ (fun In ˘) ⊑ bimapR F idR (foldR F S) ○ (fun In ˘) ○ R
      greedy-˘ =
        (⇐-begin
           (S ˘ ○ S) ⊓ Q ○ bimapR F idR (foldR F S) ○ (fun In ˘) ⊑ bimapR F idR (foldR F S) ○ (fun In ˘) ○ R
         ⇐⟨ ˘-universal-⇐ ⟩
           ((S ˘ ○ S) ⊓ Q ○ bimapR F idR (foldR F S) ○ (fun In ˘)) ˘ ⊑ (bimapR F idR (foldR F S) ○ (fun In ˘) ○ R) ˘
         ⇐⟨ ⊑-trans ˘-○-distr3-⊑ ⟩
           fun In ○ (bimapR F idR (foldR F S) ˘) ○ ((S ˘ ○ S) ⊓ Q) ˘ ⊑ (bimapR F idR (foldR F S) ○ (fun In ˘) ○ R) ˘
         ⇐⟨ ⊒-trans (˘-○-distr3-⊒ (bimapR F idR (foldR F S)) (fun In ˘) R) ⟩
           fun In ○ (bimapR F idR (foldR F S) ˘) ○ ((S ˘ ○ S) ⊓ Q) ˘ ⊑ R ˘ ○ fun In ○ (bimapR F idR (foldR F S) ˘)
         ⇐⟨ ⊑-trans (○-monotonic-r (○-monotonic-l (bimapR-˘-preservation-⊑ F))) ⟩
           fun In ○ bimapR F idR (foldR F S ˘) ○ ((S ˘ ○ S) ⊓ Q) ˘ ⊑ R ˘ ○ fun In ○ bimapR F idR (foldR F S) ˘
         ⇐⟨ ⊒-trans (○-monotonic-r (○-monotonic-r (bimapR-˘-preservation-⊒ F))) ⟩
           fun In ○ bimapR F idR (foldR F S ˘) ○ ((S ˘ ○ S) ⊓ Q) ˘ ⊑ R ˘ ○ fun In ○ bimapR F idR (foldR F S ˘)
         ⇐⟨ ⊑-trans (○-monotonic-r (○-monotonic-r ⊓-commute)) ⟩
           fun In ○ bimapR F idR (foldR F S ˘) ○ (Q ⊓ (S ˘ ○ S)) ˘ ⊑ R ˘ ○ fun In ○ bimapR F idR (foldR F S ˘)
         ⇐∎) greedy
