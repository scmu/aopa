module Examples.Optimisation.ActivitySelection where

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

import Examples.Optimisation.ActivitySelection.Spec as ActSel-Spec
   {-  using (compatible; subseq; mutex; mutex-subseq; S; 
            lessfin; fin-ubound) -}

open ActSel-Spec using (lessfin; fin-ubound)

-- open SimpleOrderings using (_≤ℓ_; _≡ℓ_; ≤-trans; x<y⇒x≤y)

-- Mutex-Subseq
-- CompatibleOrdering

open CompatibleOrdering using (_⊴_)
open ActSel-Spec using (fin-ordered)

compatible-cons : Act → List Act → List Act
compatible-cons a [] = a ∷ []
compatible-cons a (x ∷ xs) with finish x ≤? start a
...                        | yes _ = a ∷ x ∷ xs
...                        | no  _ = x ∷ xs

compatible-cons⊑outr⊔cons : fun (uncurry compatible-cons) ⊑ outr ⊔ cons
compatible-cons⊑outr⊔cons .(a ∷ [])     (a , []    ) refl = inj₂ refl
compatible-cons⊑outr⊔cons ys            (a , x ∷ xs) eq  with finish x ≤? start a
compatible-cons⊑outr⊔cons .(a ∷ x ∷ xs) (a , x ∷ xs) refl | yes _  =  inj₂ refl
compatible-cons⊑outr⊔cons .(x ∷ xs)     (a , x ∷ xs) refl | no  _  =  inj₁ refl

fin-ubound-result : ∀ xs → ∀ {y ys} →
  foldR (fun (uncurry compatible-cons) ○ fin-ubound ¿) nil (y ∷ ys) xs → fin-ubound (y , ys)
fin-ubound-result [] {y} {ys} ()
fin-ubound-result (x ∷ xs) {.x} {.[]}
  ((.x , []) , (refl , fold-xs-y∷ys) , (.(x , []) , (refl , fin-ubound-x,[]) , refl)) = _
fin-ubound-result (x ∷ xs) {y} {ys}
  ((.x , z ∷ zs) , (refl , fold-xs-y∷ys) , (.(x , z ∷ zs) , (refl , fin-ubound-x,z∷zs) , eq))
  with finish z ≤? start x
fin-ubound-result (x ∷ xs) {.x} {.(z ∷ zs)}
  ((.x , z ∷ zs) , (refl , fold-xs-x∷z∷zs) , (.(x , z ∷ zs) , (refl , fin-ubound-x,z∷zs) , refl))
  | yes _ = fin-ubound-x,z∷zs
fin-ubound-result (x ∷ xs) {.z} {.zs}
  ((.x , z ∷ zs) , (refl , fold-xs-z∷zs) , (.(x , z ∷ zs) , (refl , fin-ubound-x,z∷zs) , refl))
  | no _ = fin-ubound-result xs fold-xs-z∷zs

fin-ubound-relax : ∀ {a a'} xs → finish a ≤ finish a' → fin-ubound (a , xs) → fin-ubound (a' , xs)
fin-ubound-relax [] _ _ = _
fin-ubound-relax (x ∷ xs) finish-a≤finish-a' (finish-x≤finish-a , fin-ubound-a,xs) =
  ≤-trans finish-x≤finish-a finish-a≤finish-a' , fin-ubound-relax xs finish-a≤finish-a' fin-ubound-a,xs

-- PJ: first use of the definition of compatible
compatible-activity : ∀ {x y} ys → finish y ≤ start x → fin-ubound (y , ys) → compatible (x , ys)
compatible-activity {x} {y} [] finish-y≤start-x fin-ubound-y,[] = _
compatible-activity {x} {y} (z ∷ zs) finish-y≤start-x (finish-z≤finish-y , fin-ubound-y,zs) =
  inj₁ (≤-trans finish-z≤finish-y finish-y≤start-x) , compatible-activity zs finish-y≤start-x fin-ubound-y,zs


-- These dependencies should ideally not be on ℕ but on Act
open Data.Nat using (zero; suc; _≤′_; ≤′-step; ≤′-refl; s≤s)
open NatProp using (≤′⇒≤)
open SimpleOrderings using (≤-refl)
open CompatibleOrdering using (¬1+x≤x; ⊴-reflexive; ⊴-transitive)

-- q : {x : ℕ} → {y : ℕ} → {!x ≤ y!} → {! !} → {! !}
-- q a b = ⊥-elim (¬1+x≤x (≤-trans start<finish (≤-trans a b )))

        
monotonicity : (S ○ fin-ubound ¿) ○ (idR ⨉ _⊴_) ○ fin-ubound ¿
             ⊑ _⊴_ ○ S ○ fin-ubound ¿
monotonicity ys' (a , xs) 
  ((a' , ys) , (axs , (eq1 , fin-ubound-a,xs) , (eq2 , i1)) ,
    (.(a' , ys) , (refl , fin-ubound-a,ys) , i2)) = {!!}
{-
monotonicity .ys (a , xs) 
  ((.a , ys) , (.(a , xs) , (refl , fin-ubound-a,xs) , (refl , inj₁ len-ys<len-xs)) ,
    (.(a , ys) , (refl , fin-ubound-a,ys) , inj₁ refl)) =
  (a , xs)
  ≫[ fin-ubound ¿ ]→ (a , xs)  ⟨ refl , fin-ubound-a,xs ⟩
  →[ S ]→ xs  ⟨ inj₁ refl ⟩
  →[ _⊴_ ]→ ys  ⟨ inj₁ len-ys<len-xs ⟩
  →∎
monotonicity .ys (a , xs) 
  ((.a , ys) , (.(a , xs) , (refl , fin-ubound-a,xs) , (refl , inj₂ (len-ys≡len-xs , ∀a-a≻ys⇒a≻xs))) ,
    (.(a , ys) , (refl , fin-ubound-a,ys) , inj₁ refl)) =
  (a , xs)
  ≫[ fin-ubound ¿ ]→ (a , xs)  ⟨ refl , fin-ubound-a,xs ⟩
  →[ S ]→ xs  ⟨ inj₁ refl ⟩
  →[ _⊴_ ]→ ys  ⟨ inj₂ (len-ys≡len-xs , ∀a-a≻ys⇒a≻xs) ⟩
  →∎
monotonicity .(a ∷ ys) (a , xs) 
  ((.a , ys) , (.(a , xs) , (refl , fin-ubound-a,xs) , (refl , inj₁ len-ys<len-xs)) ,
    (.(a , ys) , (refl , fin-ubound-a,ys) , inj₂ (.(a , ys) , (refl , compatible-a,ys) , refl)))
  with inspect (length xs)
monotonicity .(a ∷ ys) (a , xs) 
  ((.a , ys) , (.(a , xs) , (refl , fin-ubound-a,xs) , (refl , inj₁ len-ys<len-xs)) ,
    (.(a , ys) , (refl , fin-ubound-a,ys) , inj₂ (.(a , ys) , (refl , compatible-a,ys) , refl)))
  | len-xs with-≡ eq with length xs | eq | NatProp.≤⇒≤′ len-ys<len-xs
monotonicity .(a ∷ ys) (a , xs) 
  ((.a , ys) , (.(a , xs) , (refl , fin-ubound-a,xs) , (refl , inj₁ len-ys<len-xs)) ,
    (.(a , ys) , (refl , fin-ubound-a,ys) , inj₂ (.(a , ys) , (refl , compatible-a,ys) , refl)))
  | .(length xs) with-≡ refl | zero | len-xs≡0 | ()
monotonicity .(a ∷ ys) (a , xs) 
  ((.a , ys) , (.(a , xs) , (refl , fin-ubound-a,xs) , (refl , inj₁ len-ys<len-xs)) ,
    (.(a , ys) , (refl , fin-ubound-a,ys) , inj₂ (.(a , ys) , (refl , compatible-a,ys) , refl)))
  | .(length xs) with-≡ refl | suc .(length ys) | len-xs≡1+len-ys | ≤′-refl =
  (a , xs)
  ≫[ fin-ubound ¿ ]→ (a , xs)  ⟨ refl , fin-ubound-a,xs ⟩
  →[ S ]→ xs  ⟨ inj₁ refl ⟩
  →[ _⊴_ ]→ a ∷ ys  ⟨ inj₂ (sym len-xs≡1+len-ys , see-below) ⟩
  →∎
  where see-below : (post-compatible ﹨ post-compatible) (a ∷ ys) xs
        see-below a' ((finish-a≤finish-a' , fin-ubound-a',ys) ,
                      (inj₁ finish-a≤start-a' , compatible-a',ys)) =
          fin-ubound-relax xs finish-a≤finish-a' fin-ubound-a,xs ,
          compatible-activity xs finish-a≤start-a' fin-ubound-a,xs
        see-below a' ((finish-a≤finish-a' , fin-ubound-a',ys) ,
                      (inj₂ finish-a'≤start-a , compatible-a',ys)) =
          ⊥-elim (¬1+x≤x (≤-trans start<finish (≤-trans finish-a≤finish-a' finish-a'≤start-a)))
monotonicity .(a ∷ ys) (a , xs) 
  ((.a , ys) , (.(a , xs) , (refl , fin-ubound-a,xs) , (refl , inj₁ len-ys<len-xs)) ,
    (.(a , ys) , (refl , fin-ubound-a,ys) , inj₂ (.(a , ys) , (refl , compatible-a,ys) , refl)))
  | .(length xs) with-≡ refl | suc n | len-xs≡1+n | ≤′-step len-ys<′n =
  (a , xs)
  ≫[ fin-ubound ¿ ]→ (a , xs)  ⟨ refl , fin-ubound-a,xs ⟩
  →[ S ]→ xs  ⟨ inj₁ refl ⟩
  →[ _⊴_ ]→ a ∷ ys  ⟨ inj₁ (subst (λ z → suc (suc (length ys)) ≤ z)
                                  (sym len-xs≡1+n) (s≤s (≤′⇒≤ len-ys<′n))) ⟩
  →∎
monotonicity .(a ∷ ys) (a , xs) 
  ((.a , ys) , (.(a , xs) , (refl , fin-ubound-a,xs) , (refl , inj₂ (len-ys≡len-xs , ∀a-a≻ys⇒a≻xs))) ,
    (.(a , ys) , (refl , fin-ubound-a,ys) , inj₂ (.(a , ys) , (refl , compatible-a,ys) , refl))) =
  (a , xs)
  ≫[ fin-ubound ¿ ]→ (a , xs)  ⟨ refl , fin-ubound-a,xs ⟩
  →[ S ]→ a ∷ xs  ⟨ inj₂ (
    (a , xs)
    ≫[ compatible ¿ ]→ (a , xs)  ⟨ refl , proj₂ (∀a-a≻ys⇒a≻xs a (fin-ubound-a,ys , compatible-a,ys)) ⟩
    →[ cons ]→ a ∷ xs  ⟨ refl ⟩
    →∎) ⟩
  →[ _⊴_ ]→ a ∷ ys  ⟨ inj₂ (cong suc len-ys≡len-xs , see-below) ⟩
  →∎
  where see-below : (post-compatible ﹨ post-compatible) (a ∷ ys) (a ∷ xs)
        see-below a' ((finish-a≤finish-a' , fin-ubound-a',ys) ,
                      (finish-a≤start-a'∨finish-a'≤start-a , compatible-a',ys)) =
          let post-compatible-a',xs = ∀a-a≻ys⇒a≻xs a' (fin-ubound-a',ys , compatible-a',ys)
          in  (finish-a≤finish-a' , proj₁ post-compatible-a',xs) ,
              (finish-a≤start-a'∨finish-a'≤start-a , proj₂ post-compatible-a',xs)
-}
{- 

It turns out that we cannot prove the following property. The missing hole
has type compatible (a , xs), which can be established during the foldR
but not by compatible-cons only.

step-refine : fun (uncurry compatible-cons) ○ fin-ubound ¿ ⊑ 
                max _⊴_ ₁∘ Λ(S ○ fin-ubound ¿)
step-refine (a , []) .(a ∷ []) (._ , (refl , _) , refl) = 
   (((a , []) , (refl , tt) , inj₂ ((a , []) , (refl , tt) , refl)) , aux)
  where aux : (xs : List Act) →
          (S ○ fin-ubound ¿) (a , []) xs  →
             (a ∷ []) ⊴ xs
        aux .[] (.(a , []) , (refl , _) , inj₁ refl) = inj₁ ≤-refl   
        aux .(a ∷ []) (.(a , []) , (refl , _) , inj₂ (._ , (refl , _), refl)) = 
           inj₂ (refl , λ b p → p) 

step-refine (a , x ∷ xs) ._ (._ , (refl , (fx≤fa , fbnd-a,xs)) , refl)  with finish x ≤? start a
... | yes fx≤sa = 
  (((a , x ∷ xs) , (refl , fx≤fa , fbnd-a,xs) , 
    inj₂ ((a , x ∷ xs) , (refl , inj₁ fx≤sa , {! !}) , refl)) , aux)
  where aux : (ys : List Act) →
          (S ○ fin-ubound ¿) (a , x ∷ xs) ys →
             ⊴ (a ∷ x ∷ xs) ys
        aux .(x ∷ xs) (._ , (refl , fx≤fa , fbnd-a,xs) , inj₁ refl) = inj₁ ≤-refl  
        aux .(a ∷ x ∷ xs) (._ , (refl , fx≤fa , fbnd-a,xs) , 
                inj₂ (._ , (refl , pf , comp-a,xs) , refl)) = 
         inj₂ (refl , λ b p → p) 
... | no ¬fx≤sa = 
  (((a , x ∷ xs) , (refl , fx≤fa , fbnd-a,xs) , inj₁ refl) , aux) 
  where aux : (ys : List Act) →
          (S ○ fin-ubound ¿) (a , x ∷ xs) ys →
             (x ∷ xs) ⊴ ys
        aux .(x ∷ xs) (._ , (refl , fx≤fa , fbnd-a,xs) , inj₁ refl) =
           inj₂ (refl , λ b p → p) 
        aux .(a ∷ x ∷ xs) (._ , (refl , fx≤fa , fbnd-a,xs) , 
           inj₂ (._ , (refl , (inj₁ fx≤sa , comp-a,xs)) , refl)) =
           ⊥-elim (¬fx≤sa fx≤sa) 
        aux .(a ∷ x ∷ xs) (._ , (refl , fx≤fa , fbnd-a,xs) , 
           inj₂ (._ , (refl , (inj₂ fa≤sx , comp-a,xs)) , refl)) = 
           ⊥-elim (¬1+x≤x (≤-trans start<finish (≤-trans fx≤fa fa≤sx))) 
-}

algebra-refinement : foldR (fun (uncurry compatible-cons) ○ fin-ubound ¿) nil
                   ⊑ foldR (max _⊴_ ₁∘ Λ(S ○ fin-ubound ¿)) nil
algebra-refinement .[] [] refl = refl
algebra-refinement .(x ∷ []) (x ∷ xs) 
  ((.x , []) , (refl , fold-xs-[]) , (.(x , []) , (refl , fin-ubound-x-[]) , refl)) =
  (x , []) , (refl , algebra-refinement [] xs fold-xs-[]) ,
    ((x , [])
    ≫[ fin-ubound ¿ ]→ (x , [])  ⟨ refl , _ ⟩
    →[ S ]→ x ∷ []  ⟨ inj₂ (
      (x , [])
      ≫[ compatible ¿ ]→ (x , [])  ⟨ refl , _ ⟩
      →[ cons ]→ x ∷ []  ⟨ refl ⟩
      →∎) ⟩
    →∎) , upperbound-wrt-⊴
  where upperbound-wrt-⊴ : ∀ zs → (S ○ fin-ubound ¿) zs (x , [])
                                      → zs ⊴ (x ∷ [])
        upperbound-wrt-⊴ .[] (.(x , []) , (refl , _) , inj₁ refl) = inj₁ ≤-refl
        upperbound-wrt-⊴ .(x ∷ [])
          (.(x , []) , (refl , _) , inj₂ (.(x , []) , (refl , _) , refl)) = ⊴-reflexive (x ∷ [])
algebra-refinement zs (x ∷ xs)
  ((.x , y ∷ ys) , (refl , fold-xs-y∷ys) , (.(x , y ∷ ys) , (refl , fin-ubound-x-y∷ys) , eq))
  with finish y ≤? start x
algebra-refinement .(x ∷ y ∷ ys) (x ∷ xs)
  ((.x , y ∷ ys) , (refl , fold-xs-y∷ys) , (.(x , y ∷ ys) , (refl , fin-ubound-x-y∷ys) , refl))
  | yes finish-y≤start-x =
  (x , y ∷ ys) , (refl , algebra-refinement (y ∷ ys) xs fold-xs-y∷ys) ,
    ((x , y ∷ ys)
    ≫[ fin-ubound ¿ ]→ (x , y ∷ ys)  ⟨ refl , fin-ubound-x-y∷ys ⟩
    →[ S ]→ x ∷ y ∷ ys  ⟨ inj₂ (
      (x , y ∷ ys)
      ≫[ compatible ¿ ]→ (x , y ∷ ys)  ⟨ refl , inj₁ finish-y≤start-x ,
                                           compatible-activity ys finish-y≤start-x
                                            (fin-ubound-result xs fold-xs-y∷ys) ⟩
      →[ cons ]→ x ∷ y ∷ ys  ⟨ refl ⟩
      →∎) ⟩
    →∎) , upperbound-wrt-⊴
  where upperbound-wrt-⊴ : ∀ zs → (S ○ fin-ubound ¿) zs (x , y ∷ ys)
                                      → zs ⊴ (x ∷ y ∷ ys)
        upperbound-wrt-⊴ .(y ∷ ys)
          (.(x , y ∷ ys) , (refl , fin-ubound-x,y∷ys) , inj₁ refl) = inj₁ ≤-refl
        upperbound-wrt-⊴ .(x ∷ y ∷ ys)
          (.(x , y ∷ ys) , (refl , fin-ubound-x,y∷ys) ,
            inj₂ (.(x , y ∷ ys) , (refl , compatible-x,y∷ys) , refl)) = ⊴-reflexive (x ∷ y ∷ ys)
algebra-refinement .(y ∷ ys) (x ∷ xs)
  ((.x , y ∷ ys) , (refl , fold-xs-y∷ys) , (.(x , y ∷ ys) , (refl , fin-ubound-x-y∷ys) , refl))
  | no finish-y≰start-x =
  (x , y ∷ ys) , (refl , algebra-refinement (y ∷ ys) xs fold-xs-y∷ys) ,
    ((x , y ∷ ys)
    ≫[ fin-ubound ¿ ]→ (x , y ∷ ys)  ⟨ refl , fin-ubound-x-y∷ys ⟩
    →[ S ]→ y ∷ ys  ⟨ inj₁ refl ⟩
    →∎) , upperbound-wrt-⊴
  where upperbound-wrt-⊴ : ∀ zs → (S ○ fin-ubound ¿) zs (x , y ∷ ys)
                                      → zs ⊴ (y ∷ ys)
        upperbound-wrt-⊴ .(y ∷ ys)
          (.(x , y ∷ ys) , (refl , fin-ubound-x,y∷ys) , inj₁ refl) = ⊴-reflexive (y ∷ ys)
        upperbound-wrt-⊴ .(x ∷ y ∷ ys)
          (.(x , y ∷ ys) , (refl , finish-y≤finish-x , fin-ubound-x,ys) ,
            inj₂ (.(x , y ∷ ys) , (refl , inj₁ finish-y≤start-x , compatible-x,ys) , refl)) =
          ⊥-elim (finish-y≰start-x finish-y≤start-x)
        upperbound-wrt-⊴ .(x ∷ y ∷ ys)
          (.(x , y ∷ ys) , (refl , finish-y≤finish-x , fin-ubound-x,ys) ,
            inj₂ (.(x , y ∷ ys) , (refl , inj₂ finish-x≤start-y , compatible-x,ys) , refl)) =
          ⊥-elim (¬1+x≤x (≤-trans start<finish (≤-trans finish-y≤finish-x finish-x≤start-y)))

open MutexDerivation using (mutex○subseq-is-fold)

activity-selection-derivation :
  ∃ (λ f → fun f ○ fin-ordered ⊑ act-sel-spec)
activity-selection-derivation = _ ,
 (⊒-begin
    (max _≤ℓ_ ₁∘ Λ(mutex ○ subseq))                            ○ fin-ordered
  ⊒⟨ ○-monotonic-l (minΛ-cong-⊒ mutex○subseq-is-fold)  ⟩
    (max _≤ℓ_ ₁∘ Λ (foldR S nil))                              ○ fin-ordered
  ⊒⟨ ○-monotonic-l $ max-monotonic ⊴-refines-≤ℓ ⟩
    (max _⊴_ ₁∘ Λ (foldR S nil))                               ○ fin-ordered
  ⊒⟨ fin-ubound-promotion ⟩
    (max _⊴_ ₁∘ Λ (foldR (S ○ fin-ubound ¿) nil))              ○ fin-ordered
  ⊒⟨ partial-greedy-thm ⊴˘-trans
      fin-ubound¿⊑idR fin-ubound¿⊑idR monotonicity
      fin-ubound-homo ⟩
    foldR (max _⊴_ ₁∘ Λ(S ○ fin-ubound ¿)) (Λ (max _⊴_) nil)  ○ fin-ordered
  ⊒⟨ ○-monotonic-l $ foldR-monotonic ⊑-refl max-⊴-nil⊇nil ⟩
    foldR (max _⊴_ ₁∘ Λ(S ○ fin-ubound ¿)) nil                 ○ fin-ordered
  ⊒⟨ ○-monotonic-l algebra-refinement ⟩
    foldR (fun (uncurry compatible-cons) ○ fin-ubound ¿) nil ○ fin-ordered
  ⊒⟨ fin-ubound-demotion ⟩
    foldR (fun (uncurry compatible-cons)) nil                ○ fin-ordered
  ⊒⟨ ○-monotonic-l $ foldR-to-foldr compatible-cons [] ⟩
    fun (foldr compatible-cons [])                           ○ fin-ordered
  ⊒∎)
  where 
    open CompatibleOrdering using (⊴-refines-≤ℓ)
    fin-ubound¿⊑idR : fin-ubound ¿ ⊑ idR
    fin-ubound¿⊑idR = set-corefl⊑idR fin-ubound

    fin-ubound-promotion :
     (max _⊴_ ₁∘ Λ (foldR S nil)) ○ fin-ordered ⊒
     (max _⊴_ ₁∘ Λ (foldR (S ○ fin-ubound ¿) nil)) ○ fin-ordered
    fin-ubound-promotion =
     ⊒-begin
        (max _⊴_ ₁∘ Λ (foldR S nil)) ○ fin-ordered
     ⊒⟨ corefl-propagation-⊒ $ corefl-foldR fin-ubound¿⊑idR ⊆-refl ⟩
        (max _⊴_ ₁∘ Λ(mutex-subseq ○ fin-ordered)) ○ fin-ordered
     ⊒⟨ ○-monotonic-l (minΛ-cong-⊒ fin-ordered-promotion)  ⟩
        (max _⊴_ ₁∘ Λ(fin-ordered-mutex-subseq ○ fin-ordered)) ○ fin-ordered
     ⊒⟨ corefl-propagation-⊑ $ corefl-foldR fin-ubound¿⊑idR ⊆-refl ⟩
        (max _⊴_ ₁∘ Λ (foldR (S ○ fin-ubound ¿) nil)) ○ fin-ordered
     ⊒∎

    upperbound-wrt-⊴ : ∀ xs → nil xs → xs ⊴ []
    upperbound-wrt-⊴ .[] refl = ⊴-reflexive [] 

    max-⊴-nil⊇nil : Λ (max _⊴_) nil ⊇ nil
    max-⊴-nil⊇nil .[] refl = refl , upperbound-wrt-⊴  

    fin-ubound-demotion :
      foldR (fun (uncurry compatible-cons) ○ fin-ubound ¿) nil ○ fin-ordered ⊒
      foldR (fun (uncurry compatible-cons)) nil ○ fin-ordered
    fin-ubound-demotion =
     ⊒-begin
        foldR (fun (uncurry compatible-cons) ○ fin-ubound ¿) nil ○ fin-ordered
     ⊒⟨ ○-monotonic-l $
         corefl-extraction fin-ubound¿⊑idR fin-ubound¿⊑idR
           subseq-preserves-fin-ubound compatible-cons⊑outr⊔cons ⊆-refl ⟩
        (foldR (fun (uncurry compatible-cons)) nil ○ fin-ordered) ○ fin-ordered
     ⊒⟨ ○-assocl ⟩
        foldR (fun (uncurry compatible-cons)) nil ○ fin-ordered ○ fin-ordered
     ⊒⟨ ○-monotonic-r $ corefl-idempotent-⊒ $ corefl-foldR fin-ubound¿⊑idR ⊆-refl ⟩
        foldR (fun (uncurry compatible-cons)) nil ○ fin-ordered
     ⊒∎

    open import Relations.Converse using (˘-○-distr-⊒; ˘-monotonic-⇐)
    ⊴˘-trans : (_⊴_ ˘) ○ (_⊴_ ˘) ⊑ (_⊴_ ˘)
    ⊴˘-trans = ⊑-trans (˘-○-distr-⊒ _⊴_ _⊴_) (˘-monotonic-⇐ ⊴-transitive)

    fin-ubound-homo : 
      (idR ⨉ foldR (S ○ fin-ubound ¿) nil) ○ fin-ubound ¿ ⊑
      fin-ubound ¿ ○ (idR ⨉ foldR (S ○ fin-ubound ¿) nil)
    fin-ubound-homo = 
      a-simple-exercise-using-the-modular-law
        fin-ubound¿⊑idR fin-ubound¿⊑idR subseq-preserves-fin-ubound
        (⨉-monotonic {R = idR} {T =  foldR (S ○ fin-ubound ¿) nil} ⊑-refl
          (⊑-trans fin-ordered-mutex-subseq⊑mutex-subseq mutex-subseq⊑subseq))

activity-selection : List Act → List Act
activity-selection = proj₁ activity-selection-derivation
