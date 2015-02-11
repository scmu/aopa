module Examples.Optimisation.ActivitySelection.CompatibleOrdering where

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

open import Examples.Optimisation.ActivitySelection.Spec as ActSel-Spec
open ActSel-Spec.SimpleOrderings using (_≤ℓ_; _<ℓ_; _≡ℓ_; ≤-trans; x<y⇒x≤y; <ℓ⊑≤ℓ; ≡ℓ⊑≤ℓ)

post-compatible : Act ← List Act
post-compatible a xs = fin-ubound (a , xs) × compatible (a , xs)

_⊴_ : List Act ← List Act
_⊴_ = _<ℓ_ ⊔ (_≡ℓ_ ⊓ (post-compatible ﹨ post-compatible))

⊴-reflexive : ∀ xs → xs ⊴ xs
⊴-reflexive _ = inj₂ (refl , λ _ → id)

open Data.Nat    using (s≤s; zero; suc; _≤_; _<_)

⊴-transitive : _⊴_ ○ _⊴_ ⊑ _⊴_
⊴-transitive ys xs (zs , inj₁ len-zs<len-xs , inj₁ len-ys<len-zs) =
    inj₁ (≤-trans len-ys<len-zs (x<y⇒x≤y len-zs<len-xs))
⊴-transitive ys xs (zs , inj₁ len-zs<len-xs , inj₂ (len-ys≡len-zs , ∀a-a≻ys⇒a≻zs)) =
    inj₁ (subst (λ z → suc z ≤ length xs) (sym len-ys≡len-zs) len-zs<len-xs)
⊴-transitive ys xs (zs , inj₂ (len-zs≡len-xs , ∀a-a≻zs⇒a≻xs) , inj₁ len-ys<len-zs) =
    inj₁ (subst (λ z → length ys < z) len-zs≡len-xs len-ys<len-zs)
⊴-transitive ys xs (zs , inj₂ (len-zs≡len-xs , ∀a-a≻zs⇒a≻xs) , inj₂ (len-ys≡len-zs , ∀a-a≻ys⇒a≻zs)) =
    inj₂ (trans len-ys≡len-zs len-zs≡len-xs , λ a a≻ys → ∀a-a≻zs⇒a≻xs a (∀a-a≻ys⇒a≻zs a a≻ys))

⊴-refines-≤ℓ : _⊴_ ⊑ _≤ℓ_
⊴-refines-≤ℓ =
    ⊑-begin
      _⊴_
    ⊑⟨ ⊑-refl ⟩
      _<ℓ_ ⊔ (_≡ℓ_ ⊓ (post-compatible ﹨ post-compatible))
    ⊑⟨ ⊔-monotonic <ℓ⊑≤ℓ (proj₁ $ ⊓-universal-⇒ ⊑-refl) ⟩
      _≤ℓ_ ⊔ _≡ℓ_
    ⊑⟨ ⊔-monotonic ⊑-refl ≡ℓ⊑≤ℓ ⟩
      _≤ℓ_ ⊔ _≤ℓ_
    ⊑⟨ ⊔-universal-⇐ (⊑-refl , ⊑-refl) ⟩
      _≤ℓ_
    ⊑∎

¬1+x≤x : ∀ {x} → ¬ suc x ≤ x
¬1+x≤x {zero} ()
¬1+x≤x {suc x} (s≤s 1+x≤x) = ¬1+x≤x 1+x≤x
