{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Algebra.Polynomials.Multivariate.EquivCarac.An[Am[X]]-Anm[X] where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat using (ℕ) renaming (_+_ to _+n_)
open import Cubical.Data.Vec
open import Cubical.Data.Vec.OperationsNat
open import Cubical.Data.Sigma

open import Cubical.Algebra.DirectSum.DirectSumHIT.Base
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing

open import Cubical.Algebra.CommRing.Instances.Polynomials.MultivariatePoly

private variable
  ℓ ℓ' : Level

module Comp-Poly-nm
  (Acr@(A , Astr) : CommRing ℓ)
  (n m : ℕ)
  where

  private
    PAm   = PolyCommRing Acr m
    PAn+m = PolyCommRing Acr (n +n m)
    PAmn  = PolyCommRing (PolyCommRing Acr m) n

  open CommRingStr

-----------------------------------------------------------------------------
-- direct sens

  PAmn→PAn+m-base : (v : Vec ℕ n) → Poly Acr m → Poly Acr (n +n m)
  PAmn→PAn+m-base v = DS-Rec-Set.f _ _ _ _ trunc
                       (0r (snd PAn+m))
                       (λ v' a → base (v ++ v') a)
                       (_+_ (snd PAn+m))
                       (+Assoc (snd PAn+m))
                       (+IdR (snd PAn+m))
                       (+Comm (snd PAn+m))
                       (λ v' → base-neutral (v ++ v'))
                       (λ v' a b → base-add (v ++ v') a b)

  PAmn→PAn+m : Poly (PolyCommRing Acr m) n → Poly Acr (n +n m)
  PAmn→PAn+m = DS-Rec-Set.f _ _ _ _ trunc
                (0r (snd PAn+m))
                PAmn→PAn+m-base
                (_+_ (snd PAn+m))
                (+Assoc (snd PAn+m))
                (+IdR (snd PAn+m))
                (+Comm (snd PAn+m))
                (λ _ → refl)
                λ _ _ _ → refl

-----------------------------------------------------------------------------
-- Converse sens

  PAn+m→PAmn : Poly Acr (n +n m) → Poly (PolyCommRing Acr m) n
  PAn+m→PAmn = DS-Rec-Set.f _ _ _ _ trunc
                (0r (snd PAmn))
                (λ v a → base (fst (sep-vec n m v)) (base (snd (sep-vec n m v)) a))
                (_+_ (snd PAmn))
                (+Assoc (snd PAmn))
                (+IdR (snd PAmn))
                (+Comm (snd PAmn))
                (λ v → (cong (base (fst (sep-vec n m v))) (base-neutral _)) ∙ (base-neutral _))
                 λ v a b → base-add _ _ _ ∙ cong (base (fst (sep-vec n m v))) (base-add _ _ _)

-----------------------------------------------------------------------------
-- Section

  e-sect : (P : Poly Acr (n +n m)) → PAmn→PAn+m (PAn+m→PAmn P) ≡ P
  e-sect = DS-Ind-Prop.f _ _ _ _ (λ _ → trunc _ _)
           refl
           (λ v a → cong (λ X → base X a) (sep-vec-id n m v))
           (λ {U V} ind-U ind-V → cong₂ (_+_ (snd PAn+m)) ind-U ind-V)


-----------------------------------------------------------------------------
-- Retraction

  e-retr : (P : Poly (PolyCommRing Acr m) n) → PAn+m→PAmn (PAmn→PAn+m P) ≡ P
  e-retr = DS-Ind-Prop.f _ _ _ _ (λ _ → trunc  _ _)
           refl
           (λ v → DS-Ind-Prop.f _ _ _ _ (λ _ → trunc _ _)
                   (sym (base-neutral _))
                   (λ v' a → cong₂ base (sep-vec-fst n m v v')
                                          (cong (λ X → base X a) (sep-vec-snd n m v v')))
                   λ {U V} ind-U ind-V → (cong₂ (_+_ (snd PAmn)) ind-U ind-V) ∙ (base-add _ _ _))
           (λ {U V} ind-U ind-V → cong₂ (_+_ (snd PAmn)) ind-U ind-V)

-----------------------------------------------------------------------------
-- Morphism of ring

  PAmn→PAn+m-pres1 : PAmn→PAn+m (1r (snd PAmn)) ≡ 1r (snd PAn+m)
  PAmn→PAn+m-pres1 = cong (λ X → base X (1r Astr)) (rep-concat n m 0 )

  PAmn→PAn+m-pres+ : (P Q : Poly (PolyCommRing Acr m) n) →
                      PAmn→PAn+m (snd PAmn ._+_ P Q) ≡ snd PAn+m ._+_ (PAmn→PAn+m P) (PAmn→PAn+m Q)
  PAmn→PAn+m-pres+ = λ _ _ → refl

  PAmn→PAn+m-pres· : (P Q : Poly (PolyCommRing Acr m) n) →
                      PAmn→PAn+m ( snd PAmn ._·_ P Q) ≡ snd PAn+m ._·_ (PAmn→PAn+m P) (PAmn→PAn+m Q)
  PAmn→PAn+m-pres· =
    DS-Ind-Prop.f _ _ _ _ (λ _ → isPropΠ (λ _ → trunc _ _))
    (λ Q → refl)
    (λ v → DS-Ind-Prop.f _ _ _ _ (λ _ → isPropΠ (λ _ → trunc _ _))
            (λ Q → cong (λ X → PAmn→PAn+m (snd PAmn ._·_ X Q)) (base-neutral v))
            (λ v' a → DS-Ind-Prop.f _ _ _ _ (λ _ → trunc _ _)
                       refl
                       (λ w → DS-Ind-Prop.f _ _ _ _ (λ _ → trunc _ _)
                               refl
                               (λ w' b → cong (λ X → base X (Astr ._·_ a b)) (+n-vec-concat _ _ _ _ _ _))
                               λ {U V} ind-U ind-V → cong (λ X → PAmn→PAn+m (snd PAmn ._·_ (base v (base v' a)) X))
                                                           (sym (base-add _ _ _))
                                                      ∙ cong₂ (snd PAn+m ._+_) ind-U ind-V
                                                      ∙ sym (cong (λ X → snd PAn+m ._·_ (PAmn→PAn+m (base v (base v' a)))
                                                                  (PAmn→PAn+m X)) (base-add _ _ _)))
                       λ {U V} ind-U ind-V → cong₂ (snd PAn+m ._+_) ind-U ind-V)
            λ {U V} ind-U ind-V Q → cong (λ X → PAmn→PAn+m (snd PAmn ._·_ X Q)) (sym (base-add _ _ _))
                                     ∙ cong₂ (snd PAn+m ._+_) (ind-U Q) (ind-V Q)
                                     ∙ sym (cong (λ X → snd PAn+m ._·_ (PAmn→PAn+m X) (PAmn→PAn+m Q)) (base-add _ _ _)))
    λ {U V} ind-U ind-V Q → cong₂ (_+_ (snd PAn+m)) (ind-U Q) (ind-V Q)


-----------------------------------------------------------------------------
-- Ring Equivalence

module _ (A' : CommRing ℓ) (n m : ℕ) where

  open Comp-Poly-nm A' n m

  CRE-PolyN∘M-PolyN+M : CommRingEquiv (PolyCommRing (PolyCommRing A' m) n) (PolyCommRing A' (n +n m))
  fst CRE-PolyN∘M-PolyN+M = isoToEquiv is
    where
    is : Iso _ _
    Iso.fun is = PAmn→PAn+m
    Iso.inv is = PAn+m→PAmn
    Iso.rightInv is = e-sect
    Iso.leftInv is = e-retr

  snd CRE-PolyN∘M-PolyN+M = makeIsRingHom PAmn→PAn+m-pres1 PAmn→PAn+m-pres+ PAmn→PAn+m-pres·
