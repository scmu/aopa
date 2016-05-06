module Data.List.HyloThm where

open import Relation.Binary.PropositionalEquality 

open import Function
open import Data.List
open import Data.Product

open import AlgebraicReasoning.Implications
open import AlgebraicReasoning.Relations
open import Data.List.Fold
open import Relations
open import Relations.CompChain
open import Relations.Converse
open import Relations.Factor
open import Relations.Function
open import Relations.Product
open import Sets

{- For now it seems that we do not need it immediately

foldR-lowerbound : {A B : Set} → (R : B ← (A × B)) → (s : ℙ B) → (X : B ← List A) →
  R ○ (idR ⨉ X) ○ cons ˘ ⊑ X → (∀ b → s b → X [] b) → foldR R s ⊑ X
foldR-lowerbound R s X R○FX○α˘⊑X b∈s⇒[]Xb as b foldR-as-b = 
 foldR-universal-⊒ X R s
  (((⇒-begin
      R ○ (idR ⨉ X) ○ cons ˘ ⊑ X
   ⇒⟨ ⊑-trans ○-assocr ⟩
      (R ○ (idR ⨉ X)) ○ cons ˘ ⊑ X
   ⇒⟨ ˘-monotonic-⇐ ⟩
      ((R ○ (idR ⨉ X)) ○ cons ˘)˘ ⊑ X ˘
   ⇒⟨ ⊑-trans (˘-○-distr-⊒ (R ○ (idR ⨉ X)) (cons ˘)) ⟩
      cons ○ (R ○ (idR ⨉ X))˘ ⊑ X ˘
   ⇒⟨ fR⊑S⇒R⊑f˘S  ⟩
      (R ○ (idR ⨉ X))˘ ⊑ cons ˘ ○ X ˘
   ⇒⟨ ˘-monotonic-⇐ ⟩
      R ○ (idR ⨉ X) ⊑ (cons ˘ ○ X ˘)˘
   ⇒⟨ ⊒-trans (˘-○-distr-⊑ (cons ˘) (X ˘)) ⟩
      R ○ (idR ⨉ X) ⊑ X ○ cons
   ⇒∎) R○FX○α˘⊑X) , (λ b b∈s → ([] , ≡-refl , b∈s⇒[]Xb b b∈s))) 
    as b foldR-as-b
-}

hylo-induction-⊒ : {A B C : Set} →
  (R : B ← (A × B)) (r : ℙ B) →
  (S : C ← (A × C)) (s : ℙ C) → (X : B ← C) →
  (R ○ (idR ⨉ X) ○ S ˘ ⊑ X) → (∀ b c → s c → r b → X b c) →
  X ⊒ (foldR R r) ○ (foldR S s)˘
hylo-induction-⊒ R r S s X R○FX○S˘⊑X c∈s∧b∈r⇒Xcb b c
  ([] , fold-S-[]-c , fold-R-[]-b) =
  c∈s∧b∈r⇒Xcb b c fold-S-[]-c fold-R-[]-b
hylo-induction-⊒ R r S s X R○FX○S˘⊑X c∈s∧b∈r⇒Xbc b c
  (x ∷ xs , fold-S-x∷xs-c , fold-R-x∷xs-b) =
  (⇐-begin
      foldR R r ○ foldR S s ˘ ⊑ X
   ⇐⟨ /-universal-⇒ ⟩
      foldR R r ⊑ X / (foldR S s ˘)
   ⇐⟨ (λ next-line →
       foldR-induction-⊒ (X / (foldR S s ˘)) R r 
         (next-line , λ b b∈r → [] , refl , 
                      λ c c∈s → c∈s∧b∈r⇒Xbc b c c∈s b∈r))  ⟩
      R ○ (idR ⨉ (X / (foldR S s ˘))) ⊑ (X / (foldR S s ˘)) ○ cons
   ⇐⟨ Rf˘⊑S⇒R⊑Sf ⟩
      (R ○ (idR ⨉ (X / (foldR S s ˘)))) ○ cons ˘ ⊑ X / (foldR S s ˘)
   ⇐⟨ ⊑-trans ○-assocr ⟩
      R ○ (idR ⨉ (X / (foldR S s ˘))) ○ cons ˘ ⊑ X / (foldR S s ˘)
   ⇐⟨ /-universal-⇐ ⟩
      (R ○ (idR ⨉ (X / (foldR S s ˘))) ○ cons ˘) ○ foldR S s ˘ ⊑ X
   ⇐⟨ ⊑-trans ○-assocr  ⟩
      R ○ ((idR ⨉ (X / (foldR S s ˘))) ○ cons ˘) ○ foldR S s ˘ ⊑ X
   ⇐⟨ ⊑-trans (○-monotonic-r ○-assocr) ⟩
      R ○ (idR ⨉ (X / (foldR S s ˘))) ○ cons ˘ ○ foldR S s ˘ ⊑ X
   ⇐⟨ ⊑-trans
       (⇦-mono-r (R ● (idR ⨉ X / (foldR S s ˘)) ‥)
        (˘-○-distr-⊒ (foldR S s) cons)) ⟩
      R ○ (idR ⨉ (X / (foldR S s ˘))) ○ (foldR S s ○ cons)˘ ⊑ X
   ⇐⟨ ⊑-trans
       (⇦-mono-r (R ● (idR ⨉ X / (foldR S s ˘)) ‥)
        (˘-monotonic-⇐ (foldR-computation-cons-⊑ S))) ⟩
      R ○ (idR ⨉ (X / (foldR S s ˘))) ○ (S ○ (idR ⨉ foldR S s))˘ ⊑ X
   ⇐⟨ ⊑-trans
       (⇦-mono-r (R ● (idR ⨉ X / (foldR S s ˘)) ‥)
        (˘-○-distr-⊑ S (idR ⨉ foldR S s))) ⟩
      R ○ (idR ⨉ (X / (foldR S s ˘))) ○ (idR ⨉ foldR S s)˘ ○ S ˘ ⊑ X
   ⇐⟨ ⊑-trans
       (⇦-mono (R ● (idR ⨉ X / (foldR S s ˘)) ‥) (((idR ⨉ foldR S s) ˘) ‥)
        ((idR ˘ ⨉ foldR S s ˘) ‥) (˘-⨉-distr-⊑ {R = idR} {S = foldR S s})) ⟩
      R ○ (idR ⨉ (X / (foldR S s ˘))) ○ (idR ˘ ⨉ foldR S s ˘) ○ S ˘ ⊑ X
   ⇐⟨ ⊑-trans
       (⇦-mono (R ● (idR ⨉ X / (foldR S s ˘)) ‥) ((idR ˘ ⨉ foldR S s ˘) ‥)
        ((idR ⨉ foldR S s ˘) ‥) (⨉-monotonic {S = idR}{U = foldR S s ˘} (˘-monotonic-⇐ id⊑id˘) ⊑-refl)) ⟩
      R ○ (idR ⨉ (X / (foldR S s ˘))) ○ (idR ⨉ foldR S s ˘) ○ S ˘ ⊑ X
   ⇐⟨ ⊑-trans
       (⇦-mono (R ‥) ((idR ⨉ X / (foldR S s ˘)) ● (idR ⨉ foldR S s ˘) ‥)
        ((idR ○ idR ⨉ X / (foldR S s ˘) ○ foldR S s ˘) ‥)
        (⨉-functor-⊑ {R = idR} {S = (X / (foldR S s ˘))} {T = idR} {U = foldR S s ˘}) ) ⟩
      R ○ ((idR ○ idR) ⨉ ((X / (foldR S s ˘)) ○ foldR S s ˘)) ○ S ˘ ⊑ X
   ⇐⟨ ⊑-trans $ ○-monotonic-r $ ○-monotonic-l $ 
        ⨉-monotonic {R = idR ○ idR}{T = ((X / (foldR S s ˘)) ○ foldR S s ˘)} id-intro-l ⊑-refl ⟩
      R ○ (idR ⨉ ((X / (foldR S s)˘) ○ (foldR S s)˘)) ○ S ˘ ⊑ X
   ⇐⟨ ⊑-trans $ ○-monotonic-r $ ○-monotonic-l $
          ⨉-monotonic {R = idR} ⊑-refl (/-universal-⇒ {R = (X / (foldR S s)˘)} {S = (foldR S s)˘ } ⊑-refl) ⟩
      R ○ (idR ⨉ X) ○ S ˘ ⊑ X
   ⇐∎) R○FX○S˘⊑X b c (x ∷ xs , fold-S-x∷xs-c , fold-R-x∷xs-b)

hylo-computation-⊒ : {A B C : Set} →
  (R : B ← (A × B)) (r : ℙ B) → (S : C ← (A × C)) (s : ℙ C) →
  (X : B ← C) → (foldR R r) ○ (foldR S s)˘ ⊑ X →
  (∀ c b → s c → r b → X b c) ×
  (R ○ (idR ⨉ ((foldR R r) ○ (foldR S s)˘)) ○ S ˘ ⊑ X)
hylo-computation-⊒ R r S s X hylo⊑X =
  (λ c b c∈s b∈r → hylo⊑X b c ([] , c∈s , b∈r)) ,
  (⊑-begin
     R ○ (idR ⨉ (foldR R r ○ foldR S s ˘)) ○ S ˘
   ⊑⟨ ○-monotonic-r $ ○-monotonic-l $ ⨉-monotonic {T = (foldR R r ○ foldR S s ˘)}  id-idempotent-⊒ ⊑-refl ⟩
     R ○ ((idR ○ idR) ⨉ (foldR R r ○ foldR S s ˘)) ○ S ˘
   ⊑⟨ ⇦-mono (R ‥) (((idR ○ idR) ⨉ (foldR R r ○ foldR S s ˘)) ‥)
       ((idR ⨉ foldR R r) ● (idR ⨉ foldR S s ˘) ‥)
       (⨉-functor-⊒ {R = idR} {S = foldR R r} {T = idR} {U = foldR S s ˘})  ⟩
     R ○ (idR ⨉ foldR R r) ○ (idR ⨉ foldR S s ˘) ○ S ˘
   ⊑⟨ ⇦-mono (R ● (idR ⨉ foldR R r) ‥) ((idR ⨉ foldR S s ˘) ‥)
       ((idR ˘ ⨉ foldR S s ˘) ‥) (⨉-monotonic {T =  foldR S s ˘} id⊑id˘ ⊑-refl) ⟩
     R ○ (idR ⨉ foldR R r) ○ (idR ˘ ⨉ foldR S s ˘) ○ S ˘
   ⊑⟨ ⇦-mono (R ● (idR ⨉ foldR R r) ‥) ((idR ˘ ⨉ foldR S s ˘) ‥)
       (((idR ⨉ foldR S s) ˘) ‥) (˘-⨉-distr-⊒ {R = idR} {S = foldR S s}) ⟩
     R ○ (idR ⨉ foldR R r) ○ (idR ⨉ foldR S s)˘ ○ S ˘
   ⊑⟨ ⇦-mono-r (R ● (idR ⨉ foldR R r) ‥)
       (˘-○-distr-⊒ S (idR ⨉ foldR S s)) ⟩
     R ○ (idR ⨉ foldR R r) ○ (S ○ (idR ⨉ foldR S s))˘
   ⊑⟨ ⇦-mono-r (R ● (idR ⨉ foldR R r) ‥)
       (˘-monotonic-⇐ (foldR-computation-cons-⊒ S)) ⟩
     R ○ (idR ⨉ foldR R r) ○ (foldR S s ○ cons)˘
   ⊑⟨ ⇦-mono-r (R ● (idR ⨉ foldR R r) ‥) (˘-○-distr-⊑ (foldR S s) cons) ⟩
     R ○ (idR ⨉ foldR R r) ○ cons ˘ ○ foldR S s ˘
   ⊑⟨ ⇦-mono-l (R ● (idR ⨉ foldR R r) ‥) (foldR R r ● cons ‥)
       (foldR-computation-cons-⊒ R) ⟩
     foldR R r ○ cons ○ cons ˘ ○ foldR S s ˘
   ⊑⟨ ⇦-mono (foldR R r ‥) (cons ● (cons ˘) ‥) (idR ‥) fun-simple ⟩
     foldR R r ○ idR ○ foldR S s ˘
   ⊑⟨ ○-monotonic-r id-intro-l ⟩
     foldR R r ○ foldR S s ˘
   ⊑⟨ hylo⊑X ⟩
     X
   ⊑∎)

hylo-computation-⊑ : {A B C : Set} →
  (R : B ← (A × B)) (r : ℙ B) →
  (S : C ← (A × C)) (s : ℙ C) →
  (X : B ← C) →
  (R ○ (idR ⨉ ((foldR R r) ○ (foldR S s)˘)) ○ S ˘ ⊑ X) →
  (∀ b c → s c → r b → X b c) →
  (foldR R r) ○ (foldR S s)˘ ⊑ X
hylo-computation-⊑ R r S s X hylo-eqn⊑X c∈s∧b∈r⇒cXb b c
                    ([] , c-fold-S-[] , b-fold-R-[]) =
  c∈s∧b∈r⇒cXb b c c-fold-S-[] b-fold-R-[]
hylo-computation-⊑ R r S s X hylo-eqn⊑X c∈s∧b∈r⇒cXb b c
                    (x ∷ xs , c-fold-S-x∷xs , b-fold-R-x∷xs) =
  (⊒-begin
     X
   ⊒⟨ hylo-eqn⊑X ⟩
     R ○ (idR ⨉ (foldR R r ○ foldR S s ˘)) ○ S ˘
   ⊒⟨ ○-monotonic-r $ ○-monotonic-l $ ⨉-monotonic {R = idR ○ idR}{T = (foldR R r ○ foldR S s ˘)} id-intro-l ⊑-refl ⟩
     R ○ ((idR ○ idR) ⨉ (foldR R r ○ foldR S s ˘)) ○ S ˘
   ⊒⟨ ⇦-mono (R ‥) ((idR ⨉ foldR R r) ● (idR ⨉ foldR S s ˘) ‥)
       ((idR ○ idR ⨉ foldR R r ○ foldR S s ˘) ‥)
       (⨉-functor-⊑ {R = idR} {S = foldR R r} {T = idR} {U = foldR S s ˘})  ⟩
     R ○ (idR ⨉ foldR R r) ○ (idR ⨉ foldR S s ˘) ○ S ˘
   ⊒⟨ ⇦-mono (R ● (idR ⨉ foldR R r) ‥) ((idR ˘ ⨉ foldR S s ˘) ‥)
       ((idR ⨉ foldR S s ˘) ‥) (⨉-monotonic {T = foldR S s ˘} (˘-monotonic-⇐ id⊑id˘) ⊑-refl) ⟩
     R ○ (idR ⨉ foldR R r) ○ (idR ˘ ⨉ foldR S s ˘) ○ S ˘
   ⊒⟨ ⇦-mono (R ● (idR ⨉ foldR R r) ‥) (((idR ⨉ foldR S s) ˘) ‥)
       ((idR ˘ ⨉ foldR S s ˘) ‥) (˘-⨉-distr-⊑ {R = idR} {S = foldR S s}) ⟩
     R ○ (idR ⨉ foldR R r) ○ (idR ⨉ foldR S s)˘ ○ S ˘
   ⊒⟨ ⇦-mono-r (R ● (idR ⨉ foldR R r) ‥)  (˘-○-distr-⊑ S (idR ⨉ foldR S s)) ⟩
     R ○ (idR ⨉ foldR R r) ○ (S ○ (idR ⨉ foldR S s))˘
   ⊒⟨ ⇦-mono-r (R ● (idR ⨉ foldR R r) ‥)
       (˘-monotonic-⇐ (foldR-computation-cons-⊑ S)) ⟩
     R ○ (idR ⨉ foldR R r) ○ (foldR S s ○ cons)˘
   ⊒⟨ ⇦-mono-r (R ● (idR ⨉ foldR R r) ‥) (˘-○-distr-⊒ (foldR S s) cons) ⟩
     R ○ (idR ⨉ foldR R r) ○ cons ˘ ○ foldR S s ˘
   ⊒⟨ ⇦-mono-l (foldR R r ● cons ‥) (R ● (idR ⨉ foldR R r) ‥)
       (foldR-computation-cons-⊑ R) ⟩
     foldR R r ○ cons ○ cons ˘ ○ foldR S s ˘
   ⊒∎) b c (c ≫[ foldR S s ˘ ]→ x ∷ xs   ⟨ c-fold-S-x∷xs ⟩
              →[ cons ˘ ]→      (x , xs) ⟨ refl ⟩
              →[ cons ]→        x ∷ xs   ⟨ refl ⟩
              →[ foldR R r ]→   b        ⟨ b-fold-R-x∷xs ⟩
              →∎)
  where open import AlgebraicReasoning.PipeReasoning
