module Data.List.GreedyThm where

open import Function
open import Data.List
open import Data.Product renaming (map to map-×)
open import Relation.Binary.PropositionalEquality

open import AlgebraicReasoning.Implications
open import AlgebraicReasoning.Relations
open import Data.List.Fold
open import Data.List.HyloThm
open import Data.List.Utilities
open import Relations
open import Relations.CompChain
open import Relations.Converse
open import Relations.Coreflexive
open import Relations.Factor
open import Relations.Minimum
open import Relations.Product
open import Sets

corefl-greedy-thm : {A B : Set}
  {S : B ← (A × B)} {s : ℙ B} {R : B ← B} {C : (A × B) ← (A × B)} →
  R ○ R ⊑ R  →  C ⊑ idR  →  S ○ (idR ⨉ R ˘) ○ C ⊑ R ˘ ○ S  →
  foldR ((min R ₁∘ Λ S) ○ C) (Λ (min R) s) ⊑ min R ₁∘ Λ (foldR S s)
corefl-greedy-thm {A} {B} {S} {s} {R} {C} R○R⊑R C⊑idR S○FR˘○C⊑R˘○S =
  (⇐-begin
      foldR ((min R ₁∘ Λ S) ○ C) (Λ (min R) s) ⊑ min R ₁∘ Λ (foldR S s)
   ⇐⟨ min-universal-⇐ ⟩
      (foldR ((min R ₁∘ Λ S) ○ C) (Λ (min R) s) ⊑ foldR S s  ×
       foldR ((min R ₁∘ Λ S) ○ C) (Λ (min R) s) ○ (foldR S s)˘ ⊑ R)
   ⇐⟨ map-× (⊑-trans $ foldR-monotonic (○-monotonic-l $ proj₁ $ min-universal-⇒ ⊑-refl) ⊆-refl) id ⟩
      (foldR (S ○ C) (Λ (min R) s) ⊑ foldR S s  ×
       foldR ((min R ₁∘ Λ S) ○ C) (Λ (min R) s) ○ (foldR S s)˘ ⊑ R)
   ⇐⟨ map-× (⊑-trans $ foldR-monotonic (○-monotonic-r $ C⊑idR) ⊆-refl) id ⟩
      (foldR (S ○ idR) (Λ (min R) s) ⊑ foldR S s  ×
       foldR ((min R ₁∘ Λ S) ○ C) (Λ (min R) s) ○ (foldR S s)˘ ⊑ R)
   ⇐⟨ (λ next-line →
          foldR-monotonic id-intro-r (λ b b-minR-s → proj₁ b-minR-s) , next-line) ⟩
      foldR ((min R ₁∘ Λ S) ○ C) (Λ (min R) s) ○ (foldR S s)˘ ⊑ R
   ⇐⟨ (λ next-line →
          hylo-induction-⊒ ((min R ₁∘ Λ S) ○ C) (Λ (min R) s) S s R next-line
           (λ b₂ b₁ b₁∈s b₂-minR-s → proj₂ b₂-minR-s b₁ b₁∈s)) ⟩
      ((min R ₁∘ Λ S) ○ C) ○ (idR ⨉ R) ○ S ˘ ⊑ R
   ⇐⟨ ⊑-trans ○-assocr ⟩
      (min R ₁∘ Λ S) ○ C ○ (idR ⨉ R) ○ S ˘ ⊑ R
   ⇐⟨ ⊑-trans $
       ⇦-mono (min R ₁∘ Λ S ● C ‥) ((idR ⨉ R) ‥) (((idR ˘ ⨉ R ˘) ˘) ‥) 
       (˘-⨉-distr-⊒ {R = idR ˘} {S = R ˘}) ⟩
      (min R ₁∘ Λ S) ○ C ○ (idR ˘ ⨉ R ˘)˘ ○ S ˘ ⊑ R
   ⇐⟨ ⊑-trans $
       ⇦-mono (min R ₁∘ Λ S ● C ‥) (((idR ˘ ⨉ R ˘) ˘) ‥)
       (((idR ⨉ R ˘) ˘) ‥) (˘-monotonic-⇐ $ ⨉-monotonic {S = idR}{T = R ˘} id˘⊑id ⊑-refl) ⟩
      (min R ₁∘ Λ S) ○ C ○ (idR ⨉ R ˘)˘ ○ S ˘ ⊑ R
   ⇐⟨ ⊑-trans $ ⇦-mono ((min R ₁∘ Λ S) ‥) (C ‥) ((C ˘) ‥) (C⊑C˘ C⊑idR) ⟩
      (min R ₁∘ Λ S) ○ C ˘ ○ (idR ⨉ R ˘)˘ ○ S ˘ ⊑ R
   ⇐⟨ ⊑-trans $ ○-monotonic-r $ ˘-○-distr3-⊒ S (idR ⨉ R ˘) C ⟩
      (min R ₁∘ Λ S) ○ (S ○ (idR ⨉ R ˘) ○ C) ˘ ⊑ R
   ⇐⟨ ⊑-trans $ ○-monotonic-r $ ˘-monotonic-⇐ S○FR˘○C⊑R˘○S ⟩
      (min R ₁∘ Λ S) ○ (R ˘ ○ S)˘ ⊑ R
   ⇐⟨ ⊑-trans $ ○-monotonic-r $ ˘-○-distr-⊑ (R ˘) S ⟩
      (min R ₁∘ Λ S) ○ S ˘ ○ R ⊑ R
   ⇐⟨ ⊑-trans $ ○-monotonic-l $ /-universal-⇒ $ proj₂ $ min-universal-⇒ ⊑-refl ⟩
      (R / (S ˘)) ○ S ˘ ○ R ⊑ R
   ⇐⟨ ⊑-trans ○-assocl ⟩
      ((R / (S ˘)) ○ S ˘) ○ R ⊑ R
   ⇐⟨ ⊑-trans $ ○-monotonic-l $ /-universal-⇐ ⊑-refl ⟩
      R ○ R ⊑ R
   ⇐∎) R○R⊑R

greedy-thm : {A B : Set}
  {S : B ← (A × B)} {s : ℙ B} {R : B ← B} →
  R ○ R ⊑ R  →  S ○ (idR ⨉ R ˘) ⊑ R ˘ ○ S  →
  foldR (min R ₁∘ Λ S) (Λ (min R) s) ⊑ min R ₁∘ Λ (foldR S s)
greedy-thm {A} {B} {S} {s} {R} R○R⊑R S○FR˘⊑R˘○S =
 (⇐-begin
    foldR (min R ₁∘ Λ S) (Λ (min R) s) ⊑ min R ₁∘ Λ (foldR S s)
  ⇐⟨ ⊑-trans $ foldR-monotonic id-elim-r ⊆-refl ⟩
    foldR ((min R ₁∘ Λ S) ○ idR) (Λ (min R) s) ⊑ min R ₁∘ Λ (foldR S s)
  ⇐⟨ corefl-greedy-thm R○R⊑R ⊑-refl ⟩
    S ○ (idR ⨉ R ˘) ○ idR ⊑ R ˘ ○ S
  ⇐⟨ ⊑-trans $ ○-monotonic-r id-intro-r ⟩
    S ○ (idR ⨉ R ˘) ⊑ R ˘ ○ S
  ⇐∎) S○FR˘⊑R˘○S

a-simple-exercise-using-the-modular-law : {A B : Set}
  {C : A ← A} {D : B ← B} {R S : B ← A} →  C ⊑ idR → D ⊑ idR →
  S ○ C ⊑ D ○ S → R ⊑ S → R ○ C ⊑ D ○ R
a-simple-exercise-using-the-modular-law {_}{_} {C} {D} {R} {S} C⊑idR D⊑idR S○C⊑D○S R⊑S =
  ⊑-begin
    R ○ C
  ⊑⟨ ⊓-universal-⇐ (○-monotonic-l R⊑S , ⊑-refl) ⟩
    (S ○ C) ⊓ (R ○ C)
  ⊑⟨ ⊓-monotonic S○C⊑D○S ⊑-refl ⟩
    (D ○ S) ⊓ (R ○ C)
  ⊑⟨ ⊓-monotonic ⊑-refl (○-monotonic-r C⊑idR) ⟩
    (D ○ S) ⊓ (R ○ idR)
  ⊑⟨ ⊓-monotonic ⊑-refl id-intro-r ⟩
    (D ○ S) ⊓ R
  ⊑⟨ modular-law ⟩
    D ○ (S ⊓ (D ˘ ○ R))
  ⊑⟨ ○-monotonic-r (proj₂ $ ⊓-universal-⇒ ⊑-refl) ⟩
    D ○ D ˘ ○ R
  ⊑⟨ ○-monotonic-r $ ○-monotonic-l $ ⊑-trans (˘-monotonic-⇐ D⊑idR) id˘⊑id ⟩
    D ○ idR ○ R
  ⊑⟨ ○-monotonic-r id-intro-l ⟩
    D ○ R
  ⊑∎

corefl-extraction : {A B : Set}
  {C : (A × List A) ← (A × List A)} {D : (A × B) ← (A × B)}
  {R S : B ← (A × B)} {t u : ℙ B} → C ⊑ idR → D ⊑ idR →
  (idR ⨉ foldR S u) ○ C ⊑ D ○ (idR ⨉ foldR S u) → R ⊑ S → t ⊆ u →
  foldR R t ○ foldR (cons ○ C) nil ⊑ foldR (R ○ D) t
corefl-extraction {_} {_} {C} {D} {R} {S} {t} {u} C⊑idR D⊑idR FcataS○C⊑D○FcataS R⊑S t⊆u =
  foldR-fusion-⊑ (foldR R t) fuse-step fuse-base
  where
    fuse-base : ℰ (foldR R t) nil ⊆ t
    fuse-base b (.[] , refl , b∈t) = b∈t
    fuse-step : foldR R t ○ cons ○ C ⊑ (R ○ D) ○ (idR ⨉ foldR R t)
    fuse-step =
      ⊑-begin
        foldR R t ○ cons ○ C
      ⊑⟨ ⇦-mono-l (foldR R t ● cons ‥) (R ● (idR ⨉ foldR R t) ‥)
          (foldR-computation-cons-⊑ R) ⟩
        R ○ (idR ⨉ foldR R t) ○ C
      ⊑⟨ ○-monotonic-r $ a-simple-exercise-using-the-modular-law
           C⊑idR D⊑idR FcataS○C⊑D○FcataS 
           (⨉-monotonic {R = idR} ⊑-refl (foldR-monotonic R⊑S t⊆u)) ⟩
        R ○ D ○ (idR ⨉ foldR R t)
      ⊑⟨ ○-assocl ⟩
        (R ○ D) ○ (idR ⨉ foldR R t)
      ⊑∎

partial-greedy-thm : {A B : Set}
  {S : B ← (A × B)} {s : ℙ B} {R : B ← B}
  {C : (A × List A) ← (A × List A)} {D : (A × B) ← (A × B)} →
  R ○ R ⊑ R  →  C ⊑ idR  →  D ⊑ idR  →
  S ○ (idR ⨉ R ˘) ○ D ⊑ R ˘ ○ S  →
  (idR ⨉ foldR S s) ○ C ⊑ D ○ (idR ⨉ foldR S s)  →
    foldR (min R ₁∘ Λ S) (Λ (min R) s) ○ check C
  ⊑ (min R ₁∘ Λ (foldR S s)) ○ check C
partial-greedy-thm {_} {_} {S} {s} {R} {C} {D}
  R○R⊑R C⊑idR D⊑idR S○FR˘○D⊑R˘○S FcataS○C⊑D○FcataS =
  ⊒-begin
    (min R ₁∘ Λ (foldR S s)) ○ check C
  ⊒⟨ ○-monotonic-l $ corefl-greedy-thm R○R⊑R D⊑idR S○FR˘○D⊑R˘○S ⟩
    foldR ((min R ₁∘ Λ S) ○ D) (Λ (min R) s) ○ check C
  ⊒⟨ ○-monotonic-l $ corefl-extraction C⊑idR D⊑idR FcataS○C⊑D○FcataS
      (proj₁ $ min-universal-⇒ ⊑-refl) (λ b b-minR-s → proj₁ b-minR-s) ⟩
    (foldR (min R ₁∘ Λ S) (Λ (min R) s) ○ check C) ○ check C
  ⊒⟨ ○-assocl ⟩
    foldR (min R ₁∘ Λ S) (Λ (min R) s) ○ check C ○ check C
  ⊒⟨ ○-monotonic-r $ corefl-idempotent-⊒ $ corefl-foldR C⊑idR ⊆-refl ⟩
    foldR (min R ₁∘ Λ S) (Λ (min R) s) ○ check C
  ⊒∎
