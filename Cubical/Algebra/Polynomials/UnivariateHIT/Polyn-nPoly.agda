{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Algebra.Polynomials.UnivariateHIT.Polyn-nPoly where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat renaming (_+_ to _+n_; _·_ to _·n_)
open import Cubical.Data.Vec
open import Cubical.Data.Sigma

open import Cubical.Algebra.DirectSum.DirectSumHIT.Base
open import Cubical.Algebra.Ring
open import Cubical.Algebra.GradedRing.DirectSumFun
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Polynomials.UnivariatePolyHIT
open import Cubical.Algebra.CommRing.Instances.Polynomials.MultivariatePoly

open import Cubical.Algebra.Polynomials.Multivariate.EquivCarac.Poly0-A
open import Cubical.Algebra.Polynomials.Multivariate.EquivCarac.An[Am[X]]-Anm[X]
open import Cubical.Algebra.Polynomials.Multivariate.EquivCarac.AB-An[X]Bn[X]

open CommRingEquivs renaming (compCommRingEquiv to _∘-ecr_ ; invCommRingEquiv to inv-ecr)

private variable
  ℓ : Level


-----------------------------------------------------------------------------
-- Definition

module equiv1 (A'@(A , Astr) : CommRing ℓ)
  where

  private
    PA = PolyCommRing A' 1
    PAstr = snd PA
    PA' = nUnivariatePolyHIT A' 1
    PA'str = snd PA'

  open CommRingStr

  directSense : fst (PolyCommRing A' 1) → fst (nUnivariatePolyHIT A' 1)
  directSense = DS-Rec-Set.f _ _ _ _
                (is-set PA'str)
                (0r PA'str)
                (λ { (n ∷ []) a → base n a})
                (_+_ PA'str)
                (+Assoc PA'str)
                (+IdR PA'str)
                (+Comm PA'str)
                (λ { (n ∷ []) → base-neutral _ })
                λ { (n ∷ []) a b  → base-add _ _ _}

  convSense : fst (nUnivariatePolyHIT A' 1) → fst (PolyCommRing A' 1)
  convSense = DS-Rec-Set.f _ _ _ _
               (is-set PAstr)
               (0r PAstr)
               (λ n a → base (n ∷ []) a)
               (_+_ PAstr)
               (+Assoc PAstr)
               (+IdR PAstr)
               (+Comm PAstr)
               (λ n → base-neutral _)
               λ _ _ _ → base-add _ _ _

  retr : (x : fst (PolyCommRing A' 1)) → convSense (directSense x) ≡ x
  retr = DS-Ind-Prop.f _ _ _ _ (λ _ → is-set PAstr _ _)
         refl
         (λ { (n ∷ []) a → refl})
         (λ {U V} ind-U ind-V → cong₂ (_+_ PAstr) ind-U ind-V)

  sect : (x : fst (nUnivariatePolyHIT A' 1)) → (directSense (convSense x) ≡ x)
  sect = DS-Ind-Prop.f _ _ _ _ (λ _ → is-set PA'str _ _)
         refl
         (λ n a → refl)
         (λ {U V} ind-U ind-V → cong₂ (_+_ PA'str) ind-U ind-V)

  converseSense-pres· : (x y : fst (PolyCommRing A' 1)) →
                        directSense (_·_ PAstr x y) ≡ _·_ PA'str (directSense x) (directSense y)
  converseSense-pres· = DS-Ind-Prop.f _ _ _ _
                        (λ _ → isPropΠ λ _ → is-set PA'str _ _)
                        (λ _ → refl)
                        (λ { (n ∷ []) a → DS-Ind-Prop.f _ _ _ _ (λ _ → is-set PA'str _ _)
                                           refl
                                           (λ { (m ∷ []) b → refl})
                                           λ {U V} ind-U ind-V → cong₂ (_+_ PA'str) ind-U ind-V})
                        λ {U V} ind-U ind-V y → cong₂ (_+_ PA'str) (ind-U y) (ind-V y)

  open Iso

  equivR : CommRingEquiv PA PA'
  fst equivR = isoToEquiv is
    where
    is : Iso (PA .fst) (PA' .fst)
    fun is = directSense
    inv is = convSense
    rightInv is = sect
    leftInv is = retr
  snd equivR = makeIsRingHom refl (λ _ _ → refl) converseSense-pres·


open equiv1

Equiv-Polyn-nPolyHIT : (A' : CommRing ℓ) → (n : ℕ) → CommRingEquiv (PolyCommRing A' n) (nUnivariatePolyHIT A' n)
Equiv-Polyn-nPolyHIT A' zero = CRE-Poly0-A A'
Equiv-Polyn-nPolyHIT A' (suc n) =       inv-ecr _ _ (CRE-PolyN∘M-PolyN+M A' 1 n)
                               ∘-ecr (lift-equiv-poly _ _ 1 (Equiv-Polyn-nPolyHIT A' n)
                               ∘-ecr equivR (nUnivariatePolyHIT A' n))
