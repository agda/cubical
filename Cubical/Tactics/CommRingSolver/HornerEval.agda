module Cubical.Tactics.CommRingSolver.HornerEval where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Vec
open import Cubical.Data.Bool as 𝟚

open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary

open import Cubical.Tactics.CommRingSolver.Utility
open import Cubical.Tactics.CommRingSolver.RawRing
open import Cubical.Tactics.CommRingSolver.RawAlgebra
open import Cubical.Tactics.CommRingSolver.HornerForms
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring


private
  variable
    ℓ ℓ' : Level


module HornerEval (R@(⟨R⟩ , _) : CommRing ℓ)
                         (R'@(⟨R'⟩ , _) : CommRing ℓ')
                         (hom@(scalar‵ , _) : CommRingHom R R') where
 open CommRingStr (snd R)

 open RingTheory (CommRing→Ring R)


 open HornerForms R R' hom public
 open IteratedHornerOperations public

 open IsCommRingHom (snd hom)

 open CommRingStr (snd R') using () renaming
   (0r to 0r‵;1r to 1r‵;_+_ to _+‵_; _·_ to _·‵_; -_ to -‵_)



 eval : {n : ℕ} (P : IteratedHornerForms n)
        → Vec ⟨R'⟩ n → ⟨R'⟩
 eval  (const r) [] = scalar‵ r
 eval 0H _ = 0r‵
 eval (P ·X+ Q) (x ∷ xs) =
      let
          P' = (eval P (x ∷ xs))
          Q' = eval Q xs
      in ((P' ·‵ x) +‵ Q')


 record EvalInVecR {ℓ} (A : ℕ → Type ℓ) : Type (ℓ-max ℓ ℓ') where
  no-eta-equality
  field
   evalInVecR : {n : ℕ} → A n → Vec ⟨R'⟩ n → ⟨R'⟩

  _≑_ : ∀ {n} → A n → A n → Type ℓ'
  P ≑ Q = ∀ xs → evalInVecR P xs ≡ evalInVecR Q xs

  isProp≑ : ∀ {n} P Q → isProp (_≑_ {n} P Q)
  isProp≑ P Q  = isPropΠ λ _ → R‵.is-set _ _

  module ≑Rel {n} where
   open BinaryRelation (_≑_ {n})
   open isEquivRel
   isEquivRel≑ : isEquivRel
   isEquivRel≑ .reflexive _ _ = refl
   isEquivRel≑ .symmetric _ _ x _ = sym (x _)
   isEquivRel≑ .transitive _ _ _ x y _ = x _ ∙ y _

   open isEquivRel isEquivRel≑
     public using () renaming (symmetric to sym ; reflexive to refl ; _equivRel∙_ to _∙∶_)


 open EvalInVecR ⦃...⦄ public

 instance
  EvalInVecRIteratedHornerForms : EvalInVecR IteratedHornerForms
  EvalInVecRIteratedHornerForms .EvalInVecR.evalInVecR = eval
