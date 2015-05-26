module Data.Generic.Greedy where

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
open import Relations.Shrink
open import Data.Generic

open import AlgebraicReasoning.Equivalence
open import AlgebraicReasoning.Implications
open import AlgebraicReasoning.Relations
open import Relation.Binary using (IsPreorder; Transitive)
open import Relation.Binary.PropositionalEquality


-- A greedy algorithm that makes the greedy choice in the
-- catamorphism phase.

greedy-cata : (F : PolyF) → {A B : Set}
                   → {S : B ← ⟦ F ⟧ A B} {R : B ← B}
                   → IsPreorder (_≡_) R
                   → S ○ fmapR F (R ˘) ⊑ (R ˘) ○ S
                   →  ⦇ S ↾ R ⦈ ⊑ ⦇ S ⦈ ↾ R
greedy-cata F {S = S} {R} isPre SFR˘⊑R˘S =
  (⇐-begin
     ⦇ S ↾ R ⦈ ⊑ ⦇ S ⦈ ↾ R
   ⇐⟨ ↾-universal-⇐ ⟩
     ((⦇ S ↾ R ⦈ ⊑ ⦇ S ⦈) × (⦇ S ↾ R ⦈ ○ ⦇ S ⦈ ˘ ⊑ R))
   ⇐⟨ _,_ (foldR-monotonic F (S ↾ R) S (↾-universal-⇒₁ {X = S ↾ R} {S} {R} ⊑-refl)) ⟩
     ⦇ S ↾ R ⦈ ○ ⦇ S ⦈ ˘ ⊑ R
   ⇐⟨ proj₂ hylo-lpfp ⟩
     (S ↾ R) ○ fmapR F R ○ (S ˘) ⊑ R
   ⇐⟨ ⊑-trans (○-monotonic-r FRS˘⊑S˘R) ⟩
     (S ↾ R) ○ (S ˘) ○ R ⊑ R
   ⇐⟨ ⊑-trans (○-monotonic-l (proj₂ (⊓-universal-⇒ ⊑-refl))) ⟩
     (R / S ˘) ○ (S ˘) ○ R ⊑ R
    ⇐⟨ ⊑-trans (⇦-mono-l ((R / S ˘) ● (S ˘) ‥) (R ‥) (/-universal-⇒ ⊑-refl)) ⟩
     R ○ R ⊑ R
   ⇐∎) (transitive-○ isPre)
  where
    FRS˘⊑S˘R : fmapR F R ○ (S ˘) ⊑ (S ˘) ○ R
    FRS˘⊑S˘R = 
      (⇐-begin
         fmapR F R ○ (S ˘) ⊑ (S ˘) ○ R
       ⇐⟨ ⊑-trans (○-monotonic-l ˘-idempotent-⊑) ⟩
         ((fmapR F R ˘) ˘) ○ (S ˘) ⊑ (S ˘) ○ R
       ⇐⟨ ⊑-trans (○-monotonic-l (˘-monotonic-⇐ (fmapR-˘-preservation-⊑ F))) ⟩
         (fmapR F (R ˘) ˘) ○ (S ˘) ⊑ (S ˘) ○ R
       ⇐⟨ ⊒-trans (○-monotonic-r ˘-idempotent-⊑) ⟩
         (fmapR F (R ˘) ˘) ○ (S ˘) ⊑ (S ˘) ○ ((R ˘) ˘)
       ⇐⟨ ⊒-trans (˘-○-distr-⊑ (R ˘) S) ⟩
         (fmapR F (R ˘) ˘) ○ (S ˘) ⊑ ((R ˘) ○ S) ˘
       ⇐⟨ ⊑-trans (˘-○-distr-⊒ S (fmapR F (R ˘))) ⟩
         (S ○ fmapR F (R ˘)) ˘ ⊑ ((R ˘) ○ S) ˘
       ⇐⟨ ˘-monotonic-⇐ ⟩
         S ○ fmapR F (R ˘) ⊑ (R ˘) ○ S
       ⇐∎) SFR˘⊑R˘S

-- A greedy algorithm that makes the greedy choice in the
-- anamorphism phase, with context.

greedy-ana-cxt : {A B C : Set} {F : PolyF} {S : C ← ⟦ F ⟧ A C} {T : B ← ⟦ F ⟧ A B} {R : C ← C} {Q : ⟦ F ⟧ A B ← ⟦ F ⟧ A B}
               → IsPreorder (_≡_) R
               → S ○ S ˘ ⊑ idR
               → S ○ fmapR F R ⊑ R ○ S
               → S ○ fmapR F (⦇ S ⦈ ○ ⦇ T ⦈ ˘) ○ (Q ⊓ (T ˘ ○ T)) ˘ ⊑ R ˘ ○ S ○ fmapR F (⦇ S ⦈ ○ ⦇ T ⦈ ˘)
               → ⦇ S ⦈ ○ ⦇((T ˘) ↾ Q) ˘ ⦈ ˘ ⊑ (⦇ S ⦈ ○ ⦇ T ⦈ ˘) ↾ R
greedy-ana-cxt {F = F}{S}{T}{R}{Q} isPre S-simple mono greedy =
  (⇐-begin
     ⦇ S ⦈ ○ ⦇((T ˘) ↾ Q) ˘ ⦈ ˘ ⊑ (⦇ S ⦈ ○ ⦇ T ⦈ ˘) ↾ R
   ⇐⟨ proj₂ hylo-lpfp ⟩
     S ○ fmapR F ((⦇ S ⦈ ○ ⦇ T ⦈ ˘) ↾ R) ○ (T ˘ ↾ Q) ⊑ (⦇ S ⦈ ○ ⦇ T ⦈ ˘) ↾ R
   ⇐⟨ ↾-universal-⇐ ⟩
    ((S ○ fmapR F ((⦇ S ⦈ ○ ⦇ T ⦈ ˘) ↾ R) ○ (T ˘ ↾ Q) ⊑ ⦇ S ⦈ ○ ⦇ T ⦈ ˘) ×
     ((S ○ fmapR F ((⦇ S ⦈ ○ ⦇ T ⦈ ˘) ↾ R) ○ (T ˘ ↾ Q)) ○ (⦇ S ⦈ ○ ⦇ T ⦈ ˘) ˘ ⊑ R))
   ⇐∎) (pf₁ , pf₂)
 where
   pf₁ : S ○ fmapR F ((⦇ S ⦈ ○ ⦇ T ⦈ ˘) ↾ R) ○ (T ˘ ↾ Q) ⊑ ⦇ S ⦈ ○ ⦇ T ⦈ ˘
   pf₁ =
     ⊑-begin
       S ○ fmapR F ((⦇ S ⦈ ○ ⦇ T ⦈ ˘) ↾ R) ○ (T ˘ ↾ Q)
     ⊑⟨ ○-monotonic-r (○-monotonic-r (↾-universal-⇒₁ {R = Q} ⊑-refl)) ⟩
       S ○ fmapR F ((⦇ S ⦈ ○ ⦇ T ⦈ ˘) ↾ R) ○ T ˘
     ⊑⟨ ○-monotonic-r
          (○-monotonic-l
           (bimapR-monotonic-⊑ F ⊑-refl (↾-universal-⇒₁ {R = R} ⊑-refl))) ⟩
       S ○ fmapR F (⦇ S ⦈ ○ ⦇ T ⦈ ˘) ○ T ˘
     ⊑⟨ proj₁ hylo-lpfp ⟩
       ⦇ S ⦈ ○ ⦇ T ⦈ ˘
     ⊑∎

   pf₂ : (S ○ fmapR F ((⦇ S ⦈ ○ ⦇ T ⦈ ˘) ↾ R) ○ (T ˘ ↾ Q)) ○ (⦇ S ⦈ ○ ⦇ T ⦈ ˘) ˘ ⊑ R
   pf₂ = 
     ⊑-begin
       (S ○ fmapR F ((⦇ S ⦈ ○ ⦇ T ⦈ ˘) ↾ R) ○ (T ˘ ↾ Q)) ○ (⦇ S ⦈ ○ ⦇ T ⦈ ˘) ˘
     ⊑⟨ ⊑-trans ○-assocr (○-monotonic-r ○-assocr) ⟩ 
       S ○ fmapR F ((⦇ S ⦈ ○ ⦇ T ⦈ ˘) ↾ R) ○ (T ˘ ↾ Q) ○ (⦇ S ⦈ ○ ⦇ T ⦈ ˘) ˘
     ⊑⟨ ⇦-mono-r (S ● fmapR F (⦇ S ⦈ ○ ⦇ T ⦈ ˘ ↾ R) ● (T ˘ ↾ Q) ‥) (˘-○-distr-⊑ ⦇ S ⦈ (⦇ T ⦈ ˘)) ⟩
       S ○ fmapR F ((⦇ S ⦈ ○ ⦇ T ⦈ ˘) ↾ R) ○ (T ˘ ↾ Q) ○ ⦇ T ⦈ ○ ⦇ S ⦈ ˘
     ⊑⟨ ⇦-mono-r (S ● fmapR F (⦇ S ⦈ ○ ⦇ T ⦈ ˘ ↾ R) ● (T ˘ ↾ Q) ‥) (proj₂ (proj₁ hylo-lfp)) ⟩
       S ○ fmapR F ((⦇ S ⦈ ○ ⦇ T ⦈ ˘) ↾ R) ○ (T ˘ ↾ Q) ○ T ○ fmapR F (⦇ T ⦈ ○ ⦇ S ⦈ ˘) ○ (S ˘)
     ⊑⟨ ⊑-refl ⟩ 
       S ○ fmapR F ((⦇ S ⦈ ○ ⦇ T ⦈ ˘) ↾ R) ○ ((T ˘) ⊓ (Q / T)) ○ T ○ fmapR F (⦇ T ⦈ ○ ⦇ S ⦈ ˘) ○ (S ˘)
     ⊑⟨ ⇦-mono (S ● fmapR F ((⦇ S ⦈ ○ ⦇ T ⦈ ˘) ↾ R) ‥) ((T ˘) ⊓ (Q / T) ● T ‥) (((T ˘ ○ T) ⊓ (Q / T ○ T)) ‥) ○-⊓-distr-r ⟩
       S ○ fmapR F ((⦇ S ⦈ ○ ⦇ T ⦈ ˘) ↾ R) ○ ((T ˘ ○ T) ⊓ ((Q / T) ○ T)) ○ fmapR F (⦇ T ⦈ ○ ⦇ S ⦈ ˘) ○ (S ˘)
     ⊑⟨ ⇦-mono (S ● fmapR F ((⦇ S ⦈ ○ ⦇ T ⦈ ˘) ↾ R) ‥) (((T ˘ ○ T) ⊓ (Q / T ○ T)) ‥) (((T ˘ ○ T) ⊓ Q) ‥) (⊓-monotonic ⊑-refl (/-universal-⇒ ⊑-refl)) ⟩
       S ○ fmapR F ((⦇ S ⦈ ○ ⦇ T ⦈ ˘) ↾ R) ○ ((T ˘ ○ T) ⊓ Q) ○ fmapR F (⦇ T ⦈ ○ ⦇ S ⦈ ˘) ○ (S ˘)
     ⊑⟨ ○-monotonic-r (○-monotonic-r (○-monotonic-r (○-monotonic-l (fmapR-monotonic F (˘-○-distr-⊒ ⦇ S ⦈ (⦇ T ⦈ ˘)))))) ⟩
       S ○ fmapR F ((⦇ S ⦈ ○ ⦇ T ⦈ ˘) ↾ R) ○ ((T ˘ ○ T) ⊓ Q) ○ fmapR F ((⦇ S ⦈ ○ ⦇ T ⦈ ˘) ˘) ○ (S ˘)
     ⊑⟨ ○-monotonic-r (○-monotonic-r greedy-˘) ⟩
       S ○ fmapR F ((⦇ S ⦈ ○ ⦇ T ⦈ ˘) ↾ R) ○ fmapR F ((⦇ S ⦈ ○ ⦇ T ⦈ ˘) ˘) ○ (S ˘) ○ R
     ⊑⟨ ⇦-mono (S ‥)
          (fmapR F (⦇ S ⦈ ○ ⦇ T ⦈ ˘ ↾ R) ● fmapR F ((⦇ S ⦈ ○ ⦇ T ⦈ ˘) ˘) ‥)
          (fmapR F ((⦇ S ⦈ ○ ⦇ T ⦈ ˘ ↾ R) ○ (⦇ S ⦈ ○ ⦇ T ⦈ ˘) ˘) ‥)
          (fmapR-functor-⊑ F) ⟩
       S ○ fmapR F (((⦇ S ⦈ ○ ⦇ T ⦈ ˘) ↾ R) ○ ((⦇ S ⦈ ○ ⦇ T ⦈ ˘) ˘)) ○ (S ˘) ○ R
     ⊑⟨ ○-monotonic-r
          (○-monotonic-l (fmapR-monotonic F (↾-universal-⇒₂ ⊑-refl))) ⟩
       S ○ fmapR F R ○ (S ˘) ○ R
     ⊑⟨ ⇦-mono-l (S ● fmapR F R ‥) (R ● S ‥) mono ⟩
       R ○ S ○ S ˘ ○ R
     ⊑⟨ ⇦-mono (R ‥) (S ● (S ˘) ‥) (idR ‥) S-simple ⟩
       R ○ idR ○ R
     ⊑⟨ ○-monotonic-r id-intro-l ⟩
       R ○ R
     ⊑⟨ transitive-○ isPre ⟩
       R
     ⊑∎
    where
      greedy-˘ : (T ˘ ○ T) ⊓ Q ○ fmapR F ((⦇ S ⦈ ○ ⦇ T ⦈ ˘) ˘) ○ (S ˘) ⊑ fmapR F ((⦇ S ⦈ ○ ⦇ T ⦈ ˘) ˘) ○ (S ˘) ○ R
      greedy-˘ =
        (⇐-begin
           (T ˘ ○ T) ⊓ Q ○ fmapR F ((⦇ S ⦈ ○ ⦇ T ⦈ ˘) ˘) ○ (S ˘) ⊑ fmapR F ((⦇ S ⦈ ○ ⦇ T ⦈ ˘) ˘) ○ (S ˘) ○ R
         ⇐⟨ ˘-universal-⇐ ⟩
           ((T ˘ ○ T) ⊓ Q ○ fmapR F ((⦇ S ⦈ ○ ⦇ T ⦈ ˘) ˘) ○ (S ˘)) ˘ ⊑ (fmapR F ((⦇ S ⦈ ○ ⦇ T ⦈ ˘) ˘) ○ (S ˘) ○ R) ˘
         ⇐⟨ ⊑-trans ˘-○-distr3-⊑ ⟩
           S ○ (fmapR F ((⦇ S ⦈ ○ ⦇ T ⦈ ˘) ˘) ˘) ○ ((T ˘ ○ T) ⊓ Q) ˘ ⊑ (fmapR F ((⦇ S ⦈ ○ ⦇ T ⦈ ˘) ˘) ○ (S ˘) ○ R) ˘
         ⇐⟨ ⊑-trans (○-monotonic-r (○-monotonic-l (fmapR-˘-preservation-⊑ F))) ⟩
           S ○ fmapR F (⦇ S ⦈ ○ ⦇ T ⦈ ˘) ○ ((T ˘ ○ T) ⊓ Q) ˘ ⊑ (fmapR F ((⦇ S ⦈ ○ ⦇ T ⦈ ˘) ˘) ○ (S ˘) ○ R) ˘
         ⇐⟨ ⊒-trans (˘-○-distr3-⊒ (fmapR F ((⦇ S ⦈ ○ ⦇ T ⦈ ˘) ˘)) (S ˘) R) ⟩
           S ○ fmapR F (⦇ S ⦈ ○ ⦇ T ⦈ ˘) ○ ((T ˘ ○ T) ⊓ Q) ˘ ⊑ R ˘ ○ S ○ (fmapR F ((⦇ S ⦈ ○ ⦇ T ⦈ ˘) ˘) ˘)
         ⇐⟨ ⊒-trans (○-monotonic-r (○-monotonic-r (fmapR-˘-preservation-⊒ F))) ⟩
           S ○ fmapR F (⦇ S ⦈ ○ ⦇ T ⦈ ˘) ○ ((T ˘ ○ T) ⊓ Q) ˘ ⊑ R ˘ ○ S ○ fmapR F (⦇ S ⦈ ○ ⦇ T ⦈ ˘)
         ⇐⟨ ⊑-trans (○-monotonic-r (○-monotonic-r ⊓-commute)) ⟩
           S ○ fmapR F (⦇ S ⦈ ○ ⦇ T ⦈ ˘) ○ (Q ⊓ (T ˘ ○ T)) ˘ ⊑ R ˘ ○ S ○ fmapR F (⦇ S ⦈ ○ ⦇ T ⦈ ˘)
         ⇐∎) greedy
