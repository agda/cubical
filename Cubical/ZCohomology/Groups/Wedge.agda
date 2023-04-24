{-# OPTIONS --safe --lossy-unification #-}
module Cubical.ZCohomology.Groups.Wedge where

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws renaming (assoc to assoc∙)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Data.Nat
open import Cubical.Data.Int hiding (_+_)
open import Cubical.Data.Sigma

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.DirProd
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties

open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.Truncation as T
open import Cubical.HITs.Susp
open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.HITs.Wedge
open import Cubical.HITs.Pushout as Pushout

open import Cubical.Homotopy.Connected

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.Groups.Unit
open import Cubical.ZCohomology.Groups.Sn

open IsGroupHom
open Iso



{-
This module proves that Hⁿ(A ⋁ B) ≅ Hⁿ(A) × Hⁿ(B) for n ≥ 1 directly (rather than by means of Mayer-Vietoris).
It also proves that Ĥⁿ(A ⋁ B) ≅ Ĥ⁰(A) × Ĥ⁰(B) (reduced groups)

Proof sketch for n ≥ 1:

Any ∣ f ∣₂ ∈ Hⁿ(A ⋁ B) is uniquely characterised by a pair of functions
  f₁ : A → Kₙ
  f₂ : B → Kₙ
together with a path
  p : f₁ (pt A) ≡ f₂ (pt B)

The map F : Hⁿ(A ⋁ B) → Hⁿ(A) × Hⁿ(B) simply forgets about p, i.e.:
  F(∣ f ∣₂) := (∣ f₁ ∣₂ , ∣ f₂ ∣₂)

The construction of its inverse is defined by
  F⁻(∣ f₁ ∣₂ , ∣ f₂ ∣₂) := ∣ f₁∨f₂ ∣₂
  where
  f₁∨f₂ : A ⋁ B → Kₙ is defined inductively by
  f₁∨f₂ (inl x) := f₁ x + f₂ (pt B)
  f₁∨f₂ (inr x) := f₁ (pt B) + f₂ x
  cong f₁∨f₂ (push tt) := refl
  (this is the map wedgeFun⁻ below)

The fact that F and F⁻ cancel out is a proposition and we may thus assume for any
  ∣ f ∣₂ ∈ Hⁿ(A ⋁ B) and its corresponding f₁ that
  f₁ (pt A) = f₂ (pt B) = 0                (*)
  and
  f (inl (pt A)) = 0                       (**)

The fact that F(F⁻(∣ f₁ ∣₂ , ∣ f₂ ∣₂)) = ∣ f₁ ∣₂ , ∣ f₂ ∣₂) follows immediately from (*)

The other way is slightly trickier. We need to construct paths
  Pₗ(x) : f (inl (x)) + f (inr (pt B)) ---> f (inl (x))
  Pᵣ(x)  : f (inl (pt A)) + f (inr (x)) ---> f (inr (x))

Together with a filler of the following square

           cong f (push tt)
          ----------------->
         ^                  ^
         |                  |
         |                  |
Pₗ(pr A) |                  | Pᵣ(pt B)
         |                  |
         |                  |
         |                  |
          ----------------->
                  refl

The square is filled by first constructing Pₗ by
  f (inl (x)) + f (inr (pt B))    ---[cong f (push tt)⁻¹]--->
  f (inl (x)) + f (inl (pt A))    ---[(**)]--->
  f (inl (x)) + 0                 ---[right-unit]--->
  f (inl (x))

and then Pᵣ by
  f (inl (pt A)) + f (inr (x))    ---[(**)⁻¹]--->
  0 + f (inr (x))                 ---[left-unit]--->
  f (inr (x))

and finally by using the fact that the group laws for Kₙ are refl at its base point.
-}

module _ {ℓ ℓ'} (A : Pointed ℓ) (B : Pointed ℓ') where

  private
    wedgeFun⁻ : ∀ n → (f : typ A → coHomK (suc n)) (g : typ B → coHomK (suc n))
            → ((A ⋁ B) → coHomK (suc n))
    wedgeFun⁻ n f g (inl x) = f x +ₖ g (pt B)
    wedgeFun⁻ n f g (inr x) = f (pt A) +ₖ g x
    wedgeFun⁻ n f g (push a i) = f (pt A) +ₖ g (pt B)

  Hⁿ-⋁ : (n : ℕ) → GroupIso (coHomGr (suc n) (A ⋁ B)) (×coHomGr (suc n) (typ A) (typ B))
  fun (fst (Hⁿ-⋁ zero)) =
    ST.elim (λ _ → isSet× isSetSetTrunc isSetSetTrunc)
           λ f → ∣ (λ x → f (inl x)) ∣₂ , ∣ (λ x → f (inr x)) ∣₂
  inv (fst (Hⁿ-⋁ zero)) =
    uncurry (ST.elim2 (λ _ _ → isSetSetTrunc)
             λ f g → ∣ wedgeFun⁻ 0 f g ∣₂)
  rightInv (fst (Hⁿ-⋁ zero)) =
    uncurry
    (coHomPointedElim _ (pt A) (λ _ → isPropΠ λ _ → isSet× isSetSetTrunc isSetSetTrunc _ _)
      λ f fId → coHomPointedElim _ (pt B) (λ _ → isSet× isSetSetTrunc isSetSetTrunc _ _)
        λ g gId → ΣPathP ((cong ∣_∣₂ (funExt (λ x → cong (f x +ₖ_) gId ∙ rUnitₖ 1 (f x))))
                          , cong ∣_∣₂ (funExt (λ x → cong (_+ₖ g x) fId ∙ lUnitₖ 1 (g x)))))
  leftInv (fst (Hⁿ-⋁ zero)) =
    ST.elim (λ _ → isOfHLevelPath 2 isSetSetTrunc _ _)
      (λ f → PT.rec (isSetSetTrunc _ _)
                   (λ fId → cong ∣_∣₂ (sym fId))
                   (helper f _ refl))
    where
    helper : (f : A ⋁ B → coHomK 1) (x : coHomK 1)
          → f (inl (pt A)) ≡ x
          → ∥ f ≡ wedgeFun⁻ 0 (λ x → f (inl x)) (λ x → f (inr x)) ∥₁
    helper f =
      T.elim (λ _ → isProp→isOfHLevelSuc 2 (isPropΠ λ _ → isPropPropTrunc))
        (sphereElim 0 (λ _ → isPropΠ λ _ → isPropPropTrunc)
         λ inlId → ∣ funExt (λ { (inl x) → sym (rUnitₖ 1 (f (inl x)))
                                         ∙∙ cong ((f (inl x)) +ₖ_) (sym inlId)
                                         ∙∙ cong ((f (inl x)) +ₖ_) (cong f (push tt))
                                 ; (inr x) → sym (lUnitₖ 1 (f (inr x)))
                                            ∙ cong (_+ₖ (f (inr x))) (sym inlId)
                                 ; (push tt i) j → helper2 (f (inl (pt A))) (sym (inlId))
                                                            (f (inr (pt B))) (cong f (push tt)) j i} ) ∣₁)
      where
      helper2 : (x : coHomK 1) (r : ∣ base ∣ ≡ x) (y : coHomK 1) (p : x ≡ y)
              → PathP (λ j → ((sym (rUnitₖ 1 x) ∙∙ cong (x +ₖ_) r ∙∙ cong (x +ₖ_) p)) j
                             ≡ (sym (lUnitₖ 1 y) ∙ cong (_+ₖ y) r) j)
                       p refl
      helper2 x = J (λ x r → (y : coHomK 1) (p : x ≡ y)
                           → PathP (λ j → ((sym (rUnitₖ 1 x) ∙∙ cong (x +ₖ_) r ∙∙ cong (x +ₖ_) p)) j
                                           ≡ (sym (lUnitₖ 1 y) ∙ cong (_+ₖ y) r) j)
                                    p refl)
                     λ y → J (λ y p → PathP (λ j → ((sym (rUnitₖ 1 ∣ base ∣) ∙∙ refl ∙∙ cong (∣ base ∣ +ₖ_) p)) j
                                                    ≡ (sym (lUnitₖ 1 y) ∙ refl) j)
                                             p refl)
                               λ i _ → (refl ∙ (λ _ → 0ₖ 1)) i
  snd (Hⁿ-⋁ zero) =
    makeIsGroupHom
      (ST.elim2 (λ _ _ → isOfHLevelPath 2 (isSet× isSetSetTrunc isSetSetTrunc) _ _)
        λ _ _ → refl)
  fun (fst (Hⁿ-⋁ (suc n))) =
    ST.elim (λ _ → isSet× isSetSetTrunc isSetSetTrunc)
           λ f → ∣ (λ x → f (inl x)) ∣₂ , ∣ (λ x → f (inr x)) ∣₂
  inv (fst (Hⁿ-⋁ (suc n))) =
    uncurry (ST.elim2 (λ _ _ → isSetSetTrunc)
                     λ f g → ∣ wedgeFun⁻ (suc n) f g ∣₂)
  rightInv (fst (Hⁿ-⋁ (suc n))) =
   uncurry
    (coHomPointedElim _ (pt A) (λ _ → isPropΠ λ _ → isSet× isSetSetTrunc isSetSetTrunc _ _)
      λ f fId → coHomPointedElim _ (pt B) (λ _ → isSet× isSetSetTrunc isSetSetTrunc _ _)
        λ g gId → ΣPathP ((cong ∣_∣₂ (funExt (λ x → cong (f x +ₖ_) gId ∙ rUnitₖ (2 + n) (f x))))
                          , cong ∣_∣₂ (funExt (λ x → cong (_+ₖ g x) fId ∙ lUnitₖ (2 + n) (g x)))))
  leftInv (fst (Hⁿ-⋁ (suc n))) =
    ST.elim (λ _ → isOfHLevelPath 2 isSetSetTrunc _ _)
      (λ f → PT.rec (isSetSetTrunc _ _)
                   (λ fId → cong ∣_∣₂ (sym fId))
                   (helper f _ refl))
    where
    helper : (f : A ⋁ B → coHomK (2 + n)) (x : coHomK (2 + n))
          → f (inl (pt A)) ≡ x
          → ∥ f ≡ wedgeFun⁻ (suc n) (λ x → f (inl x)) (λ x → f (inr x)) ∥₁
    helper f =
      T.elim (λ _ → isProp→isOfHLevelSuc (3 + n) (isPropΠ λ _ → isPropPropTrunc))
        (sphereToPropElim (suc n) (λ _ → isPropΠ λ _ → isPropPropTrunc)
          λ inlId → (∣ funExt (λ { (inl x) → sym (rUnitₖ (2 + n) (f (inl x)))
                                           ∙∙ cong ((f (inl x)) +ₖ_) (sym inlId)
                                           ∙∙ cong ((f (inl x)) +ₖ_) (cong f (push tt))
                                 ; (inr x) → sym (lUnitₖ (2 + n) (f (inr x)))
                                            ∙ cong (_+ₖ (f (inr x))) (sym inlId)
                                 ; (push tt i) j → helper2 (f (inl (pt A))) (sym (inlId))
                                                            (f (inr (pt B))) (cong f (push tt)) j i}) ∣₁))
      where
      helper2 : (x : coHomK (2 + n)) (r : ∣ north ∣ ≡ x) (y : coHomK (2 + n)) (p : x ≡ y)
             → PathP (λ j → ((sym (rUnitₖ (2 + n) x) ∙∙ cong (x +ₖ_) r ∙∙ cong (x +ₖ_) p)) j
                            ≡ (sym (lUnitₖ (2 + n) y) ∙ cong (_+ₖ y) r) j)
                      p refl
      helper2 x = J (λ x r → (y : coHomK (2 + n)) (p : x ≡ y)
                           → PathP (λ j → ((sym (rUnitₖ (2 + n) x) ∙∙ cong (x +ₖ_) r ∙∙ cong (x +ₖ_) p)) j
                                           ≡ (sym (lUnitₖ (2 + n) y) ∙ cong (_+ₖ y) r) j)
                                    p refl)
                     λ y → J (λ y p → PathP (λ j → ((sym (rUnitₖ (2 + n) ∣ north ∣) ∙∙ refl ∙∙ cong (∣ north ∣ +ₖ_) p)) j
                                                    ≡ (sym (lUnitₖ (2 + n) y) ∙ refl) j)
                                             p refl)
                              λ i j → ((λ _ → ∣ north ∣) ∙ refl) i
  snd (Hⁿ-⋁ (suc n)) =
    makeIsGroupHom
      (ST.elim2 (λ _ _ → isOfHLevelPath 2 (isSet× isSetSetTrunc isSetSetTrunc) _ _)
        λ _ _ → refl)

  H⁰Red-⋁ : GroupIso (coHomRedGrDir 0 (A ⋁ B , inl (pt A)))
                      (DirProd (coHomRedGrDir 0 A) (coHomRedGrDir 0 B))
  fun (fst H⁰Red-⋁) =
    ST.rec (isSet× isSetSetTrunc isSetSetTrunc)
         λ {(f , p) → ∣ (f ∘ inl) , p ∣₂
                     , ∣ (f ∘ inr) , cong f (sym (push tt)) ∙ p ∣₂}
  inv (fst H⁰Red-⋁) =
    uncurry (ST.rec2 isSetSetTrunc
              λ {(f , p) (g , q) → ∣ (λ {(inl a) → f a
                                       ; (inr b) → g b
                                       ; (push tt i) → (p ∙ sym q) i})
                                       , p ∣₂})
  rightInv (fst H⁰Red-⋁) =
    uncurry
      (ST.elim2 (λ _ _ → isOfHLevelPath 2 (isSet× isSetSetTrunc isSetSetTrunc) _ _)
        λ {(_ , _) (_ , _) → ΣPathP (cong ∣_∣₂ (Σ≡Prop (λ _ → isSetℤ _ _) refl)
                                    , cong ∣_∣₂ (Σ≡Prop (λ _ → isSetℤ _ _) refl))})
  leftInv (fst H⁰Red-⋁) =
    ST.elim (λ _ → isOfHLevelPath 2 isSetSetTrunc _ _)
      λ {(f , p) → cong ∣_∣₂ (Σ≡Prop (λ _ → isSetℤ _ _)
                                 (funExt λ {(inl a) → refl
                                          ; (inr b) → refl
                                          ; (push tt i) j → (cong (p ∙_) (symDistr (cong f (sym (push tt))) p)
                                                           ∙∙ assoc∙ p (sym p) (cong f (push tt))
                                                           ∙∙ cong (_∙ (cong f (push tt))) (rCancel p)
                                                            ∙ sym (lUnit (cong f (push tt)))) j i}))}
                                          -- Alt. use isOfHLevel→isOfHLevelDep
  snd H⁰Red-⋁ =
    makeIsGroupHom
      (ST.elim2 (λ _ _ → isOfHLevelPath 2 (isSet× isSetSetTrunc isSetSetTrunc) _ _)
              λ {(f , p) (g , q) → ΣPathP (cong ∣_∣₂ (Σ≡Prop (λ _ → isSetℤ _ _) refl)
                                          , cong ∣_∣₂ (Σ≡Prop (λ _ → isSetℤ _ _) refl))})

  wedgeConnected : ((x : typ A) → ∥ pt A ≡ x ∥₁) → ((x : typ B) → ∥ pt B ≡ x ∥₁) → (x : A ⋁ B) → ∥ inl (pt A) ≡ x ∥₁
  wedgeConnected conA conB =
    Pushout.elimProp _
      (λ _ → isPropPropTrunc)
      (λ a → PT.rec isPropPropTrunc (λ p → ∣ cong inl p ∣₁) (conA a))
      (λ b → PT.rec isPropPropTrunc (λ p → ∣ push tt ∙ cong inr p ∣₁) (conB b))
