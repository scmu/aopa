module Examples.Optimisation.ActivitySelection.Mutex-Subseq where

import Data.Nat
import Data.Nat.Properties as NatProp
open import Function    using (id; _∘_; _$_)
open import Data.List        using (List; _∷_; []; length; foldr)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product     using (Σ; _,_; _×_; proj₁; proj₂; uncurry; ∃)
open import Data.Sum         using (_⊎_; inj₁; inj₂)
open import Data.Empty       using (⊥; ⊥-elim)
open import Relation.Binary  using (module DecTotalOrder)
open import Relation.Binary.PropositionalEquality
                             using (_≡_; inspect; _with-≡_; 
                                    refl; cong; sym; subst; trans)
open import Sets             using (ℙ; ⊆-refl; _⊇_; _⊆_)
open import Relations        using (_←_; _○_; fun;  _˘; _⊔_; _⊑_; _⊒_; _≑_; 
                                    _⨉_; idR; ⊑-refl; ⊑-trans; _⊓_; _₁∘_; ℰ; Λ;
                                    ○-⊔-distr-l-⊒; ○-⊔-distr-r-⊑; ⊔-monotonic; 
                                    ○-⊔-distr-l-⊑; ○-⊔-distr-r-⊒;
                                    ○-monotonic-l; ⊔-universal-⇐; 
                                    ○-monotonic-r; ⊓-universal-⇒; id-intro-r; 
                                    ○-assocl)
open import Relations.Coreflexive 
                             using (_¿; corefl-idempotent-⊒; set-corefl⊑idR; 
                                        check-idempotent)
open import Relations.Factor using (_﹨_)
open import Relations.Minimum using (max; corefl-propagation-⊒; 
                                          corefl-propagation-⊑; 
                                     minΛ-cong-⊒; max-monotonic)
open import Relations.Product using (⨉-monotonic)
open import Data.List.Utilities using (All; check)
open import Data.List.GreedyThm using (a-simple-exercise-using-the-modular-law; 
                                       corefl-extraction; partial-greedy-thm)
open import Data.List.Fold
  using (foldR; nil; cons; foldR-monotonic;
         corefl-foldR; foldR-to-foldr;
         foldR-computation-cons-⊒; foldR-fusion-⊒; 
         foldR-computation-cons-⊑; foldR-fusion-⊑)
import AlgebraicReasoning.Relations
open AlgebraicReasoning.Relations using (⊒-begin_; _⊒⟨_⟩_; _⊒∎)
open AlgebraicReasoning.Relations using (⊑-begin_; _⊑⟨_⟩_; _⊑∎)
open import AlgebraicReasoning.PipeReasoning 
  using (_≫[_]→_⟨_⟩; _→[_]→_⟨_⟩; _→∎)

open import Examples.Optimisation.ActivitySelection.Spec 
{-     using (Act; compatible; subseq; mutex; 
            lessfin; fin-ubound; outr) -}

  -- Abbreviation for the mutex-subseq step relation
S : List Act  ←  (Act × List Act)
S = outr ⊔ (cons ○ compatible ¿)

mutex-subseq : List Act ← List Act
mutex-subseq = foldR S nil

subseq-preserves-fin-ubound :
  (idR ⨉ subseq) ○ fin-ubound ¿ ⊑ fin-ubound ¿ ○ (idR ⨉ subseq)
subseq-preserves-fin-ubound (x' , xs') (x , []) (_ , (eq1 , _) , (eq2 , eq3)) with eq1 | eq2 | eq3
subseq-preserves-fin-ubound (.x , .[]) (x , []) (.(x , []) , (_ , _) , (_ , _)) | refl | refl | refl = 
    x , [] 
  ≫[ idR ⨉ subseq ]→ x , [] ⟨ refl , refl ⟩ 
  →[ fin-ubound ¿ ]→ x , [] ⟨ refl , _ ⟩
  →∎
subseq-preserves-fin-ubound (x' , zs') (x , y ∷ ys) 
  (.(x , y ∷ ys) ,
    (refl , (finish-y≤finish-x , fin-ubound-x,ys)) ,
    (eq1 , ((y' , zs) , (eq2 , subseq-ys-zs) , inj₁ eq3))) with eq1 | eq2 | eq3 
subseq-preserves-fin-ubound (.x , .zs) (x , y ∷ ys) 
  (.(x , y ∷ ys) ,
    (refl , (finish-y≤finish-x , fin-ubound-x,ys)) ,
    (eq1 , ((.y , zs) , (eq2 , subseq-ys-zs) , inj₁ eq3))) | refl | refl | refl
 with subseq-preserves-fin-ubound (x , zs) (x , ys) 
         ((x , ys) , (refl , fin-ubound-x,ys) , refl , subseq-ys-zs)
... | .(x , zs) , _ , (refl , fin-ubound-x,zs) =
    (x , y ∷ ys) 
  ≫[ idR ⨉ subseq ]→ x , zs ⟨ refl , (y , zs) , (refl , subseq-ys-zs) , inj₁ refl ⟩
  →[ fin-ubound ¿ ]→ x , zs ⟨ refl , fin-ubound-x,zs ⟩
  →∎
subseq-preserves-fin-ubound (x' , zs') (x , y ∷ ys) 
  (.(x , y ∷ ys) ,
    (refl , (finish-y≤finish-x , fin-ubound-x,ys)) ,
    (eq1 , ((y' , zs) , (eq2 , subseq-ys-zs) , inj₂ eq3))) with eq1 | eq2 | eq3
subseq-preserves-fin-ubound (.x , .(y ∷ zs)) (x , y ∷ ys) 
  (.(x , y ∷ ys) ,
    (refl , (finish-y≤finish-x , fin-ubound-x,ys)) ,
    (eq1 , ((.y , zs) , (eq2 , subseq-ys-zs) , inj₂ eq3))) | refl | refl | refl 
  with subseq-preserves-fin-ubound (x , zs) (x , ys) 
         ((x , ys) , (refl , fin-ubound-x,ys) , refl , subseq-ys-zs)
... | .(x , zs) , _ , (refl , fin-ubound-x,zs) =
    (x , y ∷ ys) 
  ≫[ idR ⨉ subseq ]→ x , y ∷ zs ⟨ refl , (y , zs) , (refl , subseq-ys-zs) , inj₂ refl ⟩
  →[ fin-ubound ¿ ]→ x , y ∷ zs ⟨ refl , finish-y≤finish-x , fin-ubound-x,zs ⟩
  →∎

module MutexDerivation where
  -- with some imports sorted out this could be a separate module
  mutex-subseq⊑mutex○subseq : mutex-subseq ⊑ mutex ○ subseq
  mutex-subseq⊑mutex○subseq = foldR-fusion-⊒ mutex fuse-step fuse-base
    where fuse-base : ℰ mutex nil ⊇ nil
          fuse-base .[] refl = [] , refl , refl

          product-relator : {A : Set} → mutex ○ outr {A} ⊒ outr ○ (idR ⨉ mutex)
          product-relator xs' (a , xs) ((a' , xs'') , (eq1 , mutex-xs-xs) , eq2) with eq1 | eq2 
          product-relator xs' (a , xs) ((.a , .xs') , (_ , mutex-xs-xs) , _) | refl | refl 
             with corefl-foldR (set-corefl⊑idR compatible) ⊆-refl xs' xs mutex-xs-xs
          product-relator .xs (a , xs) ((.a , .xs') , (_ , mutex-xs-xs) , _) | refl | refl | refl = xs , refl , mutex-xs-xs

          fuse-step : mutex ○ (outr ⊔ cons) ⊒ S ○ (idR ⨉ mutex)
          fuse-step =
            ⊒-begin
              mutex ○ (outr ⊔ cons)
            ⊒⟨ ○-⊔-distr-l-⊒ ⟩
              (mutex ○ outr) ⊔ (mutex ○ cons)
            ⊒⟨ ⊔-monotonic product-relator (foldR-computation-cons-⊒ (cons ○ compatible ¿)) ⟩
              (outr ○ (idR ⨉ mutex)) ⊔ ((cons ○ compatible ¿) ○ (idR ⨉ mutex))
            ⊒⟨ ○-⊔-distr-r-⊑ ⟩
              S ○ (idR ⨉ mutex)
            ⊒∎

  mutex-subseq⊒mutex○subseq : mutex-subseq ⊒ mutex ○ subseq
  mutex-subseq⊒mutex○subseq = foldR-fusion-⊑ mutex fuse-step fuse-base
    where fuse-base : ℰ mutex nil ⊆ nil
          fuse-base xs (.[] , refl , mutex-[]-xs)
            with corefl-foldR (set-corefl⊑idR compatible) ⊆-refl xs [] mutex-[]-xs
          fuse-base .[] (.[] , refl , mutex-[]-[])
            | refl = mutex-[]-[]
          product-relator : {A : Set} → mutex ○ outr {A} ⊑ outr ○ (idR ⨉ mutex)
          product-relator xs' (a , xs) (.xs , refl , mutex-xs-xs')
            with corefl-foldR (set-corefl⊑idR compatible) ⊆-refl xs' xs mutex-xs-xs'
          product-relator .xs (a , xs) (.xs , refl , mutex-xs-xs)
            | refl = (a , xs) , (refl , mutex-xs-xs) , refl
          fuse-step : mutex ○ (outr ⊔ cons) ⊑ S ○ (idR ⨉ mutex)
          fuse-step =
            ⊑-begin
              mutex ○ (outr ⊔ cons)
            ⊑⟨ ○-⊔-distr-l-⊑ ⟩
              (mutex ○ outr) ⊔ (mutex ○ cons)
            ⊑⟨ ⊔-monotonic product-relator (foldR-computation-cons-⊑ (cons ○ compatible ¿)) ⟩
              (outr ○ (idR ⨉ mutex)) ⊔ ((cons ○ compatible ¿) ○ (idR ⨉ mutex))
            ⊑⟨ ○-⊔-distr-r-⊒ ⟩
              S ○ (idR ⨉ mutex)
            ⊑∎

  mutex○subseq-is-fold : mutex ○ subseq ≑ mutex-subseq
  mutex○subseq-is-fold = (mutex-subseq⊒mutex○subseq , mutex-subseq⊑mutex○subseq)

open MutexDerivation using (mutex○subseq-is-fold)

fin-ordered-mutex-subseq : List Act ← List Act
fin-ordered-mutex-subseq = foldR (S ○ fin-ubound ¿) nil

mutex-subseq⊑subseq : mutex-subseq ⊑ subseq
mutex-subseq⊑subseq =
  ⊑-begin
    mutex-subseq
  ⊑⟨ ⊑-refl ⟩
    foldR S nil
  ⊑⟨ foldR-monotonic (⊔-monotonic ⊑-refl (○-monotonic-r (set-corefl⊑idR compatible))) ⊆-refl ⟩
    foldR (outr ⊔ (cons ○ idR)) nil
  ⊑⟨ foldR-monotonic (⊔-monotonic ⊑-refl id-intro-r) ⊆-refl ⟩
    foldR (outr ⊔ cons) nil
  ⊑⟨ ⊑-refl ⟩
    subseq
  ⊑∎

mutex-subseq○fin-ordered⊑fin-ordered-mutex-subseq○fin-ordered :
  mutex-subseq ○ fin-ordered ⊑ fin-ordered-mutex-subseq ○ fin-ordered
mutex-subseq○fin-ordered⊑fin-ordered-mutex-subseq○fin-ordered =
  ⊑-begin
    mutex-subseq ○ fin-ordered
  ⊑⟨ ○-monotonic-r $ check-idempotent fin-ubound ⟩
    mutex-subseq ○ fin-ordered ○ fin-ordered
  ⊑⟨ ○-assocl ⟩
    (mutex-subseq ○ fin-ordered) ○ fin-ordered
  ⊑⟨ ○-monotonic-l $ foldR-fusion-⊑ mutex-subseq fuse-step fuse-base ⟩
    fin-ordered-mutex-subseq ○ fin-ordered
  ⊑∎
  where fuse-base : ℰ mutex-subseq nil ⊆ nil
        fuse-base xs (.[] , refl , mutex-subseq-[]-xs) = mutex-subseq-[]-xs

        open import Relations.CompChain using (⇦-mono-l; _●_; _‥)

        fuse-step : mutex-subseq ○ cons ○ fin-ubound ¿
                  ⊑ (S ○ fin-ubound ¿) ○ (idR ⨉ mutex-subseq)
        fuse-step = 
          ⊑-begin
            mutex-subseq ○ cons ○ fin-ubound ¿
          ⊑⟨ ⇦-mono-l (mutex-subseq ● cons ‥)
              (S ● (idR ⨉ mutex-subseq) ‥)
              (foldR-computation-cons-⊑ S) ⟩
            S ○ (idR ⨉ mutex-subseq) ○ fin-ubound ¿
          ⊑⟨ ○-monotonic-r $
              a-simple-exercise-using-the-modular-law
                (set-corefl⊑idR fin-ubound) (set-corefl⊑idR fin-ubound)
                subseq-preserves-fin-ubound 
                (⨉-monotonic {R = idR} {T = mutex-subseq} ⊑-refl mutex-subseq⊑subseq) ⟩
            S ○ fin-ubound ¿ ○ (idR ⨉ mutex-subseq)
          ⊑⟨ ○-assocl ⟩
            (S ○ fin-ubound ¿) ○ (idR ⨉ mutex-subseq)
          ⊑∎

fin-ordered-mutex-subseq⊑mutex-subseq : fin-ordered-mutex-subseq ⊑ mutex-subseq
fin-ordered-mutex-subseq⊑mutex-subseq =
  ⊑-begin
    fin-ordered-mutex-subseq
  ⊑⟨ ⊑-refl ⟩
    foldR (S ○ fin-ubound ¿) nil
  ⊑⟨ foldR-monotonic (○-monotonic-r $ set-corefl⊑idR fin-ubound) ⊆-refl ⟩
    foldR (S ○ idR) nil
  ⊑⟨ foldR-monotonic id-intro-r ⊆-refl ⟩
    foldR S nil
  ⊑⟨ ⊑-refl ⟩
    mutex-subseq
  ⊑∎

fin-ordered-promotion :
   mutex-subseq ○ fin-ordered ≑ fin-ordered-mutex-subseq ○ fin-ordered
fin-ordered-promotion = 
  (mutex-subseq○fin-ordered⊑fin-ordered-mutex-subseq○fin-ordered , 
   ○-monotonic-l fin-ordered-mutex-subseq⊑mutex-subseq)
