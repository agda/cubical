{-# OPTIONS --lossy-unification --safe #-}
module Cubical.Homotopy.Serre.FPAbGroup where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.QuotientGroup
open import Cubical.Algebra.Group.Subgroup
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.DirectProduct
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup
open import Cubical.Algebra.AbGroup.Instances.Int
open import Cubical.Algebra.AbGroup.Instances.IntMod renaming (ℤAbGroup/_ to ℤMod)
open import Cubical.Algebra.AbGroup.FinitePresentation
open import Cubical.Algebra.AbGroup.Instances.IntMod

open import Cubical.Data.List
open import Cubical.Data.Fin
open import Cubical.Data.Fin as FinAlt using (isContrFin1)
open import Cubical.Data.Int
open import Cubical.Data.Nat
open import Cubical.Data.Sigma.Properties

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Homotopy.Serre.LastMinuteLemmas.Smith

open FinitePresentation

private
  variable
    ℓ ℓ' : Level

AbGroup₀ = AbGroup ℓ-zero

ℤMod-finite : (n : ℕ) → fst (ℤMod (suc n)) ≃ (Fin (suc n))
ℤMod-finite n = idEquiv _

-- finitely presented abelian groups
isFP : AbGroup ℓ → Type ℓ
isFP A = ∥ FinitePresentation A ∥₁

isFP-prop : {A : AbGroup ℓ} → isProp (isFP A)
isFP-prop = squash₁

indFP : (P : AbGroup₀ → Type ℓ) → (∀ A → isProp (P A))
   → (∀ n → P (ℤMod n))
   → (∀ H K → P H → P K → P (AbDirProd H K))
   → (∀ A → isFP A → (P A))
indFP P pr bas prod A = PT.rec (pr A)
  λ FP → subst P (AbGroupPath _ _ .fst
          (GroupIso→GroupEquiv
            (invGroupIso (isFP→isFPGroupNormalForm FP .snd .snd))))
              (main _ _)
 where
 lem : AbGroupEquiv (ℤAbGroup/ 1) (trivialAbGroup {ℓ-zero})
 fst lem = isContr→Equiv FinAlt.isContrFin1 (tt* , (λ {tt* → refl}))
 snd lem = makeIsGroupHom λ _ _ → refl

 main : (l : List ℤ) (n : ℕ) → P (FPGroupNormalForm' (pos n) l)
 main [] zero = subst P (AbGroupPath _ _ .fst lem) (bas 1)
 main [] (suc n) = prod _ _ (bas 0) (main [] n)
 main (x ∷ l) n = prod _ _ (bas (abs x)) (main l n)

indFP' : (P : AbGroup ℓ' → Type ℓ) → (∀ A → isProp (P A))
   → (∀ n G → AbGroupIso G (ℤMod n) → P G)
   → (∀ H K → P H → P K → P (AbDirProd H K))
   → (∀ A → isFP A → (P A))
indFP' {ℓ'} {ℓ} P prop bas prod A fpA = PT.rec (prop A) main fpA
  where
    open IsGroupHom
    open Iso

    LiftGroup : AbGroup ℓ-zero → AbGroup ℓ'
    LiftGroup G = AbDirProd G (trivialAbGroup {ℓ'})     -- Owen's trick

    LiftGroupIso : (G : AbGroup ℓ-zero) → AbGroupIso G (LiftGroup G)
    LiftGroupIso G .fst = invIso rUnit*×Iso
    LiftGroupIso G .snd .pres· _ _ = refl
    LiftGroupIso G .snd .pres1 = refl
    LiftGroupIso G .snd .presinv _ = refl

    LiftDirProdIso : (H K : AbGroup ℓ-zero)
      → AbGroupIso (LiftGroup (AbDirProd H K)) (AbDirProd (LiftGroup H) (LiftGroup K))
    LiftDirProdIso H K .fst .fun ((h , k) , _) = (h , tt*) , (k , tt*)
    LiftDirProdIso H K .fst .inv ((h , _) , (k , _)) = (h , k) , tt*
    LiftDirProdIso H K .fst .sec ((h , _) , (k , _)) = refl
    LiftDirProdIso H K .fst .ret ((h , k) , _) = refl
    LiftDirProdIso H K .snd .pres· _ _ = refl
    LiftDirProdIso H K .snd .pres1 = refl
    LiftDirProdIso H K .snd .presinv _ = refl

    P' : AbGroup ℓ-zero → Type _
    P' B = P (LiftGroup B)

    main : FinitePresentation A → P A
    main pr = subst P
        (fst (AbGroupPath _ _)
         (GroupIso→GroupEquiv (invGroupIso (compGroupIso (pr .fpiso) (LiftGroupIso _))))) res -- res A (invGroupIso (pr .fpiso))
      where
        open FinitePresentation

        A0 : AbGroup ℓ-zero
        A0 = ℤ[Fin (nGens pr) ] /Im (rels pr)

        fpA0 : isFP A0
        fpA0 = ∣ x ∣₁
          where
            x : FinitePresentation A0
            x .nGens = pr .nGens
            x .nRels = pr .nRels
            x .rels = pr .rels
            x .fpiso = idGroupIso

        res : P' (ℤ[Fin (nGens pr) ] /Im (rels pr))
        res = indFP P'
          (λ B → prop _)
          (λ n → bas n (LiftGroup (ℤMod n)) (invGroupIso (LiftGroupIso (ℤMod n))))
          (λ H K pH pK →
            subst P
              (fst (AbGroupPath _ _) (GroupIso→GroupEquiv (invGroupIso (LiftDirProdIso H K))))
              (prod (LiftGroup H) (LiftGroup K) pH pK))
          (ℤ[Fin (nGens pr) ] /Im (rels pr)) fpA0
