{-# OPTIONS --lossy-unification #-}
module Cubical.Algebra.DistLattice.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma

open import Cubical.Structures.Axioms
open import Cubical.Structures.Auto
open import Cubical.Structures.Macro
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.Semilattice
open import Cubical.Algebra.Lattice
open import Cubical.Algebra.DistLattice.Base

open import Cubical.Relation.Binary.Order.Poset

private
  variable
    ℓ ℓ' ℓ'' : Level

module _ where
  open LatticeHoms

  compDistLatticeHom : (L : DistLattice ℓ) (M : DistLattice ℓ') (N : DistLattice ℓ'')
                  → DistLatticeHom L M → DistLatticeHom M N → DistLatticeHom L N
  compDistLatticeHom L M N = compLatticeHom {L = DistLattice→Lattice L} {DistLattice→Lattice M} {DistLattice→Lattice N}

  _∘dl_ : {L : DistLattice ℓ} {M : DistLattice ℓ'} {N : DistLattice ℓ''}
        → DistLatticeHom M N → DistLatticeHom L M → DistLatticeHom L N
  g ∘dl f = compDistLatticeHom _ _ _ f g

  compIdDistLatticeHom : {L M : DistLattice ℓ} (f : DistLatticeHom L M)
                    → compDistLatticeHom _ _ _ (idDistLatticeHom L) f ≡ f
  compIdDistLatticeHom = compIdLatticeHom

  idCompDistLatticeHom : {L M : DistLattice ℓ} (f : DistLatticeHom L M)
                    → compDistLatticeHom _ _ _ f (idDistLatticeHom M) ≡ f
  idCompDistLatticeHom = idCompLatticeHom

  compAssocDistLatticeHom : {L M N U : DistLattice ℓ}
                         (f : DistLatticeHom L M) (g : DistLatticeHom M N) (h : DistLatticeHom N U)
                       → compDistLatticeHom _ _ _ (compDistLatticeHom _ _ _ f g) h
                       ≡ compDistLatticeHom _ _ _ f (compDistLatticeHom _ _ _ g h)
  compAssocDistLatticeHom = compAssocLatticeHom
