module Examples.Sorting.iSort where

open import Relation.Nullary
  using (¬_; Dec; yes; no)
import Relation.Binary
open Relation.Binary
  using (Setoid;        module Setoid;
         DecSetoid;     module DecSetoid;
         DecTotalOrder; module DecTotalOrder;
         Decidable; Transitive)
import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality using () renaming (cong₂ to ≡-cong₂)
open import Data.Function using (id)

open import Data.Empty   using (⊥)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; ∃; _×_; _,_; uncurry; proj₁; proj₂)
open import Data.List    using (List; []; _∷_; foldr)
open import Data.Unit    using (⊤; tt)

open import Sets 
  using (_∪_; _⊇_; ℙ; ⊆-refl; ⊇-refl;
         _≡_; ≡-refl; ≡-sym; ≡-trans; ≡-subst; ≡-cong)

open import Relations
  using (_←_; _˘; fun; _○_; _·_; idR; 
         _⨉₁_; _,₁_; Λ; Λ₁; _○₁_;
         ∈; _⊑_; _⊒_; _⨉_; id-intro-r; ⊒-refl;
         ○-monotonic-r)
open import Relations.Coreflexive
open import Data.List.Fold 
  using (nil; cons; foldr₁; foldR; foldR-fusion-⊒;
         idR⊒foldR; foldR-to-foldr; corefl-foldR)

open import AlgebraicReasoning.Sets
     using (⊇-begin_; _⊇⟨_⟩_; _⊇∎)
open import AlgebraicReasoning.Relations
     using (⊑-begin_; _⊑⟨_⟩_; _⊑∎; 
            ⊒-begin_; _⊒⟨_⟩_; _⊒∎)

open import Examples.Sorting.Spec
     using (Val; _≤_; _≤?_; ≤-trans; ≰-elim; <-relax;
            Bag; Bag-decSetoid; 
            bCons; bNil; bagify; permute; lbound; ordered?; ordered?⊑idR; sort;
            _|≈|_; |≈|-refl; |≈|-sym; |≈|-cong; ≡-|≈|-cong; |≈|-≡-cong;
            prop-bCons-commute; nilUniq)


module Combine where

  -- Old text: "combine ought to be defined by
  --   combine = cons ⊔ (cons ○ (idR ⨉ combine) ○ swapl ○ (idR ⨉ (cons ˘)))"

  combine : List Val ← (Val × List Val)
  combine y (a , [])    = cons y (a , [])
  combine y (a , b ∷ x) = cons y (a , b ∷ x) ⊎
    ∃ (λ b,z → (b ≡ proj₁ b,z × combine (proj₂ b,z) (a , x)) × cons y b,z)

--  where P : (Val × List Val) -> Set
--        P (b' , z) = (b ≡ b' × combine z (a , x)) × b' ∷ z ≡ y
--     ∃ (λ (b' , z) → (b ≡ b' × combine z (a , x)) × b' ∷ z ≡ y)

  -- A key lemma that combine and bCons commutes.

  import Relation.Binary.EqReasoning as EqR
  open EqR (DecSetoid.setoid Bag-decSetoid)

  -- import Relation.Binary.EqReasoning as EqR
  -- open EqR (≡-setoid (Bag Val))

  bagify-homo :
    (a : Val) → (x y : List Val) → {w : Bag} →
     (bagify x |≈| w) → combine y (a , x) →
       bagify y |≈| bCons a w 
  bagify-homo a [] y {w} bNil≈w [a]≡y =
     begin 
          bagify y
     ≈⟨ ≡-|≈|-cong bagify (≡-sym [a]≡y) ⟩
          bagify (a ∷ [])
     ≈⟨ |≈|-refl ⟩
          bCons a bNil
     ≈⟨ |≈|-cong (bCons a) bNil≈w ⟩
          bCons a w 
     ∎
  bagify-homo a (b ∷ x) y {w} bagifybx≈w (inj₁ abx≡y) = 
     begin
          bagify y
     ≈⟨ ≡-|≈|-cong bagify (≡-sym abx≡y) ⟩
          bagify (a ∷ b ∷ x)
     ≈⟨ |≈|-refl ⟩
          bCons a (bagify (b ∷ x))
     ≈⟨ |≈|-cong (bCons a) bagifybx≈w ⟩
          bCons a w 
     ∎ 
  bagify-homo a (b ∷ x) y {w} bagifybx≈w 
      (inj₂ ((b' , z) , (b≡b' , z[combine]ax) , b'z≡y)) = 
     begin
          bagify y
     ≈⟨ ≡-|≈|-cong bagify (≡-sym b'z≡y) ⟩
          bagify (b' ∷ z)
     ≈⟨ ≡-|≈|-cong (\b → bagify (b ∷ z)) (≡-sym b≡b') ⟩
          bagify (b ∷ z)
     ≈⟨ |≈|-refl ⟩
          bCons b (bagify z)
     ≈⟨ |≈|-cong (bCons b) (bagify-homo a x z |≈|-refl z[combine]ax) ⟩
          bCons b (bCons a (bagify x))
     ≈⟨ prop-bCons-commute b a (bagify x) ⟩
          bCons a (bCons b (bagify x))
     ≈⟨ |≈|-cong (bCons a) bagifybx≈w  ⟩
          bCons a w
     ∎ 

{-
module Combine_testPJ2 where 
  mutual
    combine : List Val ← (Val × List Val)
    combine  (a , xs    ) = cons (a , xs) ∪ combine' (a , xs)

    combine' : List Val ← (Val × List Val)
    combine' (a , []    ) = \ys → ⊥
    combine' (a , b ∷ bs) = (\ cs → cons (b , cs)) · combine (a , bs)

  import Relation.Binary.EqReasoning as EqR
  open EqR (DecSetoid.setoid Bag-decSetoid)

  -- A simpler (but equally strong) version of bagify-homo
  bagify-homo' : (a : Val) → (xs ys : List Val) →
     combine (a , xs) ys →  bagify (a ∷ xs) |≈| bagify ys
  bagify-homo' a xs ys axs[c]ys with axs[c]ys 
  ... | inj₁ axs≡ys = ≡-|≈|-cong bagify axs≡ys
  ... | inj₂ p with xs | p
  ... |   []     | () 
  ... |   b ∷ bs | (cs , abs[c]cs , b∷cs≡ys) = 
    begin 
      bagify (a ∷ b ∷ bs)
    ≈⟨ |≈|-refl ⟩ 
      bCons a (bagify (b ∷ bs))
    ≈⟨ |≈|-refl ⟩ 
      bCons a (bCons b (bagify bs))
    ≈⟨ prop-bCons-commute a b (bagify bs) ⟩ 
      bCons b (bCons a (bagify bs))
    ≈⟨ |≈|-refl ⟩ 
      bCons b (bagify (a ∷ bs))
    ≈⟨ |≈|-cong (bCons b) (bagify-homo' a bs cs abs[c]cs) ⟩ -- IH
      bCons b (bagify cs)
    ≈⟨ |≈|-refl ⟩ 
      bagify (b ∷ cs)
    ≈⟨ ≡-|≈|-cong bagify b∷cs≡ys ⟩ 
      bagify ys
    ∎

  -- The original bagify-homo follows from the simpler bagify-homo'
  bagify-homo : (a : Val) → (xs ys : List Val) → {w : Bag} →
     (bagify xs |≈| w) → combine (a , xs) ys → bagify ys |≈| bCons a w
  bagify-homo a xs ys {w} xs∼w axs[c]ys = 
    begin
      bagify ys
    ≈⟨ |≈|-sym (bagify-homo' a xs ys axs[c]ys) ⟩ 
      bagify (a ∷ xs)
    ≈⟨ |≈|-refl ⟩ 
      bCons a (bagify xs)
    ≈⟨ |≈|-cong (bCons a) xs∼w  ⟩ 
      bCons a w
    ∎

module Combine_Relationship where

  open Combine         renaming (combine to c)
  open Combine_testPJ2 renaming (combine to cPJ)
  -- The two combine definitions are equivalent → can change paper freely

  convert : cPJ ⊑ c
  convert (a , []    ) ys (inj₁ p) = p 
  convert (a , b ∷ bs) ys (inj₁ p) = inj₁ p 
  convert (a , []    ) ys (inj₂ ())
  convert (a , b ∷ bs) ys (inj₂ (cs , abs[c]cs , b∷cs≡ys))
    = inj₂ ((b , cs) , (≡-refl , convert (a , bs) cs abs[c]cs) , b∷cs≡ys) 

  open Relation.Binary.PropositionalEquality using (setoid)
  import Relation.Binary.EqReasoning as EqR
  open EqR (setoid (List Val))

  convert' : c ⊑ cPJ
  convert' (a , []    ) ys [a]≡ys   = inj₁ [a]≡ys 
  convert' (a , b ∷ bs) ys (inj₁ p) = inj₁ p
  convert' (a , b ∷ bs) ys (inj₂ q) with q
  ... | ((c , cs) , (b≡c , abs[c]cs) , c∷cs≡ys) 
    = inj₂ (cs , convert' (a , bs) cs abs[c]cs , 
                     (begin 
                        b ∷ cs
                      ≈⟨ ≡-cong (\a → a ∷ cs) b≡c ⟩ 
                        c ∷ cs
                      ≈⟨ c∷cs≡ys ⟩ 
                        ys
                      ∎)
                   )
           
-}
{-
module Combine_testPJ where 
  combine : List Val ← (Val × List Val)
  combine (a , [])     []         =  ⊥
  combine (a , [])     (a' ∷ as') =  a ≡ a'  ×  [] ≡ as'
  combine (a , b ∷ bs) []         =  ⊥
  combine (a , b ∷ bs) (a' ∷ as') =  ( (a ≡ a')  ×  ((b ∷ bs) ≡ as') ) 
                                  ⊎  ( (b ≡ a')  ×  (combine (a , bs) as'))

  import Relation.Binary.EqReasoning as EqR
  open EqR (DecSetoid.setoid Bag-decSetoid)


  -- incomplete try to define bagify-homo with a differend combine
  bagify-homo :
    (a : Val) → (bs as : List Val) → {w : Bag} →
     (bagify bs |≈| w) → combine (a , bs) as →
       bagify as |≈| bCons a w
  bagify-homo a []       []         _ ()
  bagify-homo a []       (a' ∷ as') {w} []∼w (a≡a' , []≡as') with as' | []≡as'
  ... | []    | ≡-refl = 
    begin 
         bagify (a' ∷ [])
     ≈⟨ |≈|-refl ⟩
         bCons a' (bagify [])
     ≈⟨ |≈|-cong (bCons a') []∼w ⟩
         bCons a' w
     ≈⟨ ≡-|≈|-cong (\a → bCons a w) (≡-sym a≡a') ⟩
         bCons a w
     ∎ 

  ... | _ ∷ _ | () 
  bagify-homo a (b ∷ bs) []             _ ()
  bagify-homo a (b ∷ bs) (a' ∷ as') {w} bbs∼w p with p
  ... | inj₁ (a≡a' , b∷bs≡as') = -- 
     begin 
         bagify (a' ∷ as') 
     ≈⟨ |≈|-refl  ⟩ 
         bCons a' (bagify as')
     ≈⟨ ≡-|≈|-cong (\cs → bCons a' (bagify cs)) (≡-sym b∷bs≡as') ⟩
         bCons a' (bagify (b ∷ bs))
     ≈⟨ |≈|-cong (bCons a') bbs∼w ⟩
         bCons a' w
     ≈⟨ ≡-|≈|-cong (\a → bCons a w) (≡-sym a≡a') ⟩
         bCons a w
     ∎ 
  ... | inj₂ (b≡a' , a,bs[comb]as') = 
     {! !}
-}
  {-  
  bagify-homo a (b ∷ x) bs {w} bagifybx≈w 
      (inj₂ (exists (b' , z) ((b≡b' , z[combine]ax) , b'z≡bs))) = 
     begin
          bagify bs
     ≈⟨ ≡-|≈|-cong bagify (≡-sym b'z≡bs) ⟩
          bagify (b' ∷ z)
     ≈⟨ ≡-|≈|-cong (\b → bagify (b ∷ z)) (≡-sym b≡b') ⟩
          bagify (b ∷ z)
     ≈⟨ |≈|-refl ⟩
          bCons b (bagify z)
     ≈⟨ |≈|-cong (bCons b) (bagify-homo a x z |≈|-refl z[combine]ax) ⟩
          bCons b (bCons a (bagify x))
     ≈⟨ prop-bCons-commute b a (bagify x) ⟩
          bCons a (bCons b (bagify x))
     ≈⟨ |≈|-cong (bCons a) bagifybx≈w  ⟩
          bCons a w
     ∎ 
-}

open Combine using (combine; bagify-homo)

fuse-step : permute ○ cons ⊒ combine ○ (idR ⨉ permute)
fuse-step y (a , []) 
      ((a' , z) ,  
         (a≡a' , (bnil , bNil≡bnil , bagify·z≡bnil)) ,
          y[combine]a'z)
 with nilUniq {z} (≡-subst (\bn → bagify z ≡ bn) (≡-sym bNil≡bnil) bagify·z≡bnil)
... | z≡[] with ≡-subst (\a → combine y (a , z)) (≡-sym a≡a') y[combine]a'z
... | y[combine]az with ≡-subst (\z → combine y (a , z)) z≡[] y[combine]az
... | [a]≡y
   = (a ∷ [] ,  
      ≡-refl , (bCons a bNil , 
                      ≡-refl , |≈|-≡-cong (\w → w) (≡-|≈|-cong bagify (≡-sym [a]≡y)))) 
fuse-step y (a , b ∷ x) 
    ((a' , z) , 
      (a≡a' , (w , bagify·bx≡w , bagify·z≡w)) , y[combine]a'z)
   with ≡-subst (\a → combine y (a , z)) (≡-sym a≡a') y[combine]a'z
... | y[combine]az
    = (a ∷ b ∷ x , 
       ≡-refl ,  
       (bCons a w ,  
             (≡-cong (\w → bCons a w) bagify·bx≡w , 
              |≈|-≡-cong (\x → x) (bagify-homo a z y (≡-|≈|-cong (\x → x) bagify·z≡w) y[combine]az))))

fuse-base : Λ₁ (permute ○₁ ∈) nil ⊇ nil
fuse-base x []≡x = 
   ([] , ≡-refl , (_ , ≡-refl , ≡-cong bagify (≡-sym []≡x)))

-- permutation as fold!

data Σ₁ (a : Set1) (b : a → Set) : Set1 where
   _₁,_ : (x : a) → b x → Σ₁ a b

witness₁ : ∀ {a b} → Σ₁ a b → a
witness₁ (x ₁, y) = x

proof₁ : ∀ {a b} → (p : Σ₁ a b) → b (witness₁ p)
proof₁ (x ₁, y) = y

perm-der : Σ₁ (List Val ← List Val) (\perm → permute ⊒ perm)
perm-der = 
   (_ ₁,
       (⊒-begin
            permute
        ⊒⟨ id-intro-r ⟩
            permute ○ idR
        ⊒⟨ ○-monotonic-r idR⊒foldR ⟩
            permute ○ foldR cons nil
        ⊒⟨ foldR-fusion-⊒ permute fuse-step fuse-base ⟩
            foldR combine nil
        ⊒∎))

perm : List Val ← List Val
perm = witness₁ perm-der

permute-is-fold : permute ⊒ perm
permute-is-fold = proof₁ perm-der


module Second-try where

  open import AlgebraicReasoning.PipeReasoning
  open import AlgebraicReasoning.Equality

  -- the function insert and its properties

  insert : Val → List Val → List Val
  insert a [] = a ∷ []
  insert a (b ∷ x) with a ≤? b
  ...              | yes a≤b = a ∷ b ∷ x
  ...              | no  a≰b = b ∷ insert a x

  insert⊑combine : fun (uncurry insert) ⊑ combine
  insert⊑combine y (a , []) insert-a-[]≡y = insert-a-[]≡y
  insert⊑combine y (a , b ∷ x) insert-a-b∷x≡y
      with a ≤? b | insert⊑combine (insert a x) (a , x) ≡-refl
  ... | yes a≤b | _ = inj₁ insert-a-b∷x≡y
  ... | no  a≰b | combine-a,x-insert-a-x =
    inj₂ ((b , insert a x) , 
           (≡-refl , combine-a,x-insert-a-x) , insert-a-b∷x≡y)

  relax-lbound : {a b : Val} → a ≤ b → 
    ∀ x → lbound (b , x) → lbound (a , x)
  relax-lbound a≤b []      lbound-b,[]        = tt
  relax-lbound a≤b (c ∷ x) (b≤c , lbound-b,x) = (≤-trans a≤b b≤c) ,
       (relax-lbound a≤b x lbound-b,x)

  insert-respects-lbound :
    ∀ a b x → lbound (b , x) → b ≤ a → lbound (b , insert a x)
  insert-respects-lbound a b [] lbound-b,[] b≤a = b≤a , lbound-b,[]
  insert-respects-lbound a b (c ∷ x) (b≤c , lbound-b-x) b≤a
      with a ≤? c
  ... | yes a≤c = b≤a , b≤c , lbound-b-x
  ... | no  a≰c = b≤c , insert-respects-lbound a b x lbound-b-x b≤a

  insert-respects-order :
    ∀ a x → ordered? x x → ordered? (insert a x) (insert a x)
  insert-respects-order a [] ordered-[]-[] =
    (a ,₁ nil)
    ≫₁[ idR ⨉₁ ∈ ]→ (a , [])      ⟨ ≡-refl , ≡-refl ⟩
    →[ cons ○ lbound ¿ ]→ a ∷ []  ⟨
       a , []
       ≫[ lbound ¿ ]→ a , []      ⟨ ≡-refl , _ ⟩
       →[ cons ]→ a ∷ []          ⟨ ≡-refl ⟩
       →∎ ⟩
    →∎
  insert-respects-order a (b ∷ x) ordered-b∷x-b∷x with ordered-b∷x-b∷x
  ... | ((.b , .x) , (≡-refl , ordered-x-x) , .(b , x) , (≡-refl , b≤x) , ≡-refl)
      with a ≤? b
  ... | yes a≤b =
    (a ,₁ Λ ordered? (b ∷ x))
    ≫₁[ idR ⨉₁ ∈ ]→ (a , b ∷ x)      ⟨ ≡-refl , ordered-b∷x-b∷x ⟩
    →[ cons ○ lbound ¿ ]→ a ∷ b ∷ x  ⟨
       (a , b ∷ x)
       ≫[ lbound ¿ ]→ (a , b ∷ x)    ⟨ ≡-refl , a≤b , relax-lbound a≤b x b≤x ⟩
       →[ cons ]→ a ∷ b ∷ x          ⟨ ≡-refl ⟩
       →∎ ⟩
    →∎
  ... | no  a≰b =
    (b ,₁ Λ ordered? (insert a x))
    ≫₁[ idR ⨉₁ ∈ ]→ (b , insert a x)      ⟨ ≡-refl ,
                                            insert-respects-order a x ordered-x-x ⟩
    →[ cons ○ lbound ¿ ]→ b ∷ insert a x  ⟨
       (b , insert a x)
       ≫[ lbound ¿ ]→ (b , insert a x)    ⟨ ≡-refl , 
                                            insert-respects-lbound a b x
                                              b≤x (<-relax (≰-elim a≰b)) ⟩
       →[ cons ]→ b ∷ insert a x          ⟨ ≡-refl ⟩
       →∎ ⟩
    →∎

  -- derivation of insertion sort!

  isort-der : ∃ (\f → ordered? ○ permute ⊒ fun f )
  isort-der = (_ , 
         (⊒-begin
              ordered? ○ permute
          ⊒⟨ ○-monotonic-r permute-is-fold ⟩
              ordered? ○ perm
          ⊒⟨ ⊒-refl ⟩
              ordered? ○ foldR combine nil
          ⊒⟨ foldR-fusion-⊒ ordered? ins-step ins-base ⟩
              foldR (fun (uncurry insert)) nil
          ⊒⟨ foldR-to-foldr insert [] ⟩
              fun (foldr insert [])
          ⊒∎))
    where
      ins-base : Λ₁ (ordered? ○₁ ∈) nil ⊇ nil
      ins-base .[] ≡-refl = ([] , ≡-refl , ≡-refl)

      ins-step : (ordered? ○ combine)
                ⊒ ((fun (uncurry insert)) ○ (idR ⨉ ordered?))
      ins-step .(a ∷ []) (a , [])
        ((.a , .[]) , (≡-refl , ≡-refl) , ≡-refl) = a ∷ [] , ≡-refl ,
        ((a ,₁ nil)
         ≫₁[ idR ⨉₁ ∈ ]→ (a , [])      ⟨ ≡-refl , ≡-refl ⟩
         →[ cons ○ lbound ¿ ]→ a ∷ []  ⟨
            (a , [])
            ≫[ lbound ¿ ]→ (a , [])    ⟨ ≡-refl , _ ⟩
            →[ cons ]→ a ∷ []          ⟨ ≡-refl ⟩
            →∎ ⟩
         →∎)
      ins-step _ (a , b ∷ x) ((.a , _) , (≡-refl , ordered-b∷x-b∷x) , _)
          with ordered-b∷x-b∷x
      ins-step _ (a , b ∷ x)
          ((.a , _) , (≡-refl , ordered-b∷x-b∷x) , _)
          | ((.b , x') , (≡-refl , ordered-x'-x) , _)
          with corefl-foldR (set-corefl⊑idR lbound) ⊆-refl x' x ordered-x'-x
      ins-step _ (a , b ∷ x)
          ((.a , .(b ∷ x)) , (≡-refl , ordered-b∷x-b∷x) , _)
          | ((.b , .x) , (≡-refl , ordered-x-x) ,
                         (.(b , x) , (≡-refl , b≤x) , ≡-refl))
          | ≡-refl with a ≤? b
      ins-step .(a ∷ b ∷ x) (a , b ∷ x)
          ((.a , .(b ∷ x)) , (≡-refl , ordered-b∷x-b∷x) , ≡-refl)
          | ((.b , .x) , (≡-refl , ordered-x-x) ,
                         (.(b , x) , (≡-refl , b≤x) , ≡-refl))
          | ≡-refl | yes a≤b =
        (a , b ∷ x)
        ≫[ combine ]→ a ∷ b ∷ x ⟨ inj₁ ≡-refl ⟩
        →[ ordered? ]→ a ∷ b ∷ x ⟨ 
           (a ,₁ Λ ordered? (b ∷ x))
           ≫₁[ idR ⨉₁ ∈ ]→ (a , b ∷ x) ⟨ ≡-refl , ordered-b∷x-b∷x ⟩
           →[ cons ○ lbound ¿ ]→ a ∷ b ∷ x ⟨
              (a , b ∷ x)
              ≫[ lbound ¿ ]→ (a , b ∷ x) ⟨ ≡-refl , a≤b ,
                                           relax-lbound a≤b x b≤x ⟩
              →[ cons ]→ a ∷ b ∷ x ⟨ ≡-refl ⟩
              →∎ ⟩
           →∎ ⟩
        →∎
      ins-step .(b ∷ insert a x) (a , b ∷ x)
          ((.a , .(b ∷ x)) , (≡-refl , ordered-b∷x-b∷x) , ≡-refl)
          | ((.b , .x) , (≡-refl , ordered-x-x) ,
                         (.(b , x) , (≡-refl , b≤x) , ≡-refl))
          | ≡-refl | no a≰b = (a , b ∷ x)
        ≫[ combine ]→ b ∷ insert a x ⟨ inj₂ ((b , insert a x) , (≡-refl ,
                                       insert⊑combine (insert a x) (a , x) ≡-refl) ,
                                       ≡-refl) ⟩
        →[ ordered? ]→ b ∷ insert a x ⟨
           (b ,₁ Λ ordered? (insert a x))
           ≫₁[ idR ⨉₁ ∈ ]→ (b , insert a x) ⟨ ≡-refl ,
                                              insert-respects-order a x ordered-x-x ⟩
           →[ cons ○ lbound ¿ ]→ b ∷ insert a x ⟨
              (b , insert a x)
              ≫[ lbound ¿ ]→ (b , insert a x) ⟨ ≡-refl ,
                                                insert-respects-lbound a b x
                                                b≤x (<-relax (≰-elim a≰b)) ⟩
              →[ cons ]→ b ∷ insert a x ⟨ ≡-refl ⟩
              →∎ ⟩
           →∎ ⟩
        →∎

  isort : List Val → List Val
  isort = proj₁ isort-der

  module CombineRecEq where 
    -- PJ: sketch of how to handle the recursion equation for combine

    _≡r_ : {A B : Set} → (B ← A) → (B ← A) → Set
    _≡r_ {A} {B} r s = r ⊑ s  ×  s ⊑ r

--    combineRecEq : combine ≡r (cons ⊔ (cons ○ (idR ⨉ combine) ○ swapl ○ (idR ⨉ (cons ˘))))
--    combineRecEq = ({! !} , {! !})
