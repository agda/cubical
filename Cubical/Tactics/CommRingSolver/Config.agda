module Cubical.Tactics.CommRingSolver.Config where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Relation.Nullary

open import Cubical.Data.Maybe
open import Cubical.Data.Sigma
open import Cubical.Data.Bool
open import Cubical.Data.Empty
open import Cubical.Data.List

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.Ring
open import Cubical.Tactics.CommRingSolver.GenericCommRing
open import Agda.Builtin.Reflection hiding (Type)


record CommRingSolverConfig : Typeω where
 field
  {ℓ ℓ`} : Level
  R : CommRing ℓ
  commAlg : CommAlgebra {ℓ} R ℓ`
  mbDiscreteScalars : Maybe (Discrete ⟨ R ⟩)
 R` : CommRing ℓ`
 R` = fst commAlg

 scalar` : ⟨ R ⟩ → ⟨ R` ⟩
 scalar` = fst (snd commAlg)

 open CommRingStr (snd R)
   public
 open RingTheory (CommRing→Ring R)
   public
 open CommRingStr (snd R`) using () renaming
   (0r to 0r`;1r to 1r`;_+_ to _+`_; _·_ to _·`_; -_ to -`_ ; _-_ to _-`_)
   public


 open IsCommRingHom (snd (snd commAlg))
   public
 open Exponentiation R`
   public



 CommonDenom : ⟨ R ⟩ → ⟨ R ⟩ → Type ℓ
 CommonDenom a b =
             Σ[ (a' , b' , c ) ∈ ⟨ R ⟩ × ⟨ R ⟩ × ⟨ R ⟩ ]
                (a ≡ a' · c) × (b ≡ b' · c)


 field
  mbNeg?Scalar : Maybe ((x : ⟨ R ⟩) → Maybe (Σ[ -x ∈ ⟨ R ⟩ ] - -x ≡ x))
  mbCommonDenom : Maybe (∀ a b → CommonDenom a b)
  mb·`lCancel : Maybe (∀ c m n → c ·` m ≡ c ·` n → (c ≡ 0r` → ⊥) → m ≡ n)
  mbNotZeroRing : Maybe (1r` ≡ 0r` → ⊥)
  mb≢0r→≢0r` : Maybe (∀ x → (x ≡ 0r → ⊥) → (scalar` x ≡ 0r` → ⊥))

  ringReflectionMatcher : RingReflectionMatcher
  doNotUnfold : List Name
  polyVarGuard : Term → TC Bool

  scalarSolver : Term → Term → TC Bool

 module R` where
    open CommRingStr (snd R`) public
    open RingTheory (CommRing→Ring R`) public
    open CommRingTheory R` public
