module Cubical.Algebra.Lattice.Properties where

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
open import Cubical.Algebra.Lattice.Base

open import Cubical.Relation.Binary.Order.Poset

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level

module LatticeTheory (L' : Lattice ℓ) where
  private L = fst L'
  open LatticeStr (snd L')

  0lLeftAnnihilates∧l : ∀ (x : L) → 0l ∧l x ≡ 0l
  0lLeftAnnihilates∧l x = 0l ∧l x          ≡⟨ cong (0l ∧l_) (sym (∨lLid _)) ⟩
                           0l ∧l (0l ∨l x) ≡⟨ ∧lAbsorb∨l _ _ ⟩
                           0l ∎

  0lRightAnnihilates∧l : ∀ (x : L) → x ∧l 0l ≡ 0l
  0lRightAnnihilates∧l _ = ∧lComm _ _ ∙ 0lLeftAnnihilates∧l _

  1lLeftAnnihilates∨l : ∀ (x : L) → 1l ∨l x ≡ 1l
  1lLeftAnnihilates∨l x = 1l ∨l x          ≡⟨ cong (1l ∨l_) (sym (∧lLid _)) ⟩
                           1l ∨l (1l ∧l x) ≡⟨ ∨lAbsorb∧l _ _ ⟩
                           1l ∎

  1lRightAnnihilates∨l : ∀ (x : L) → x ∨l 1l ≡ 1l
  1lRightAnnihilates∨l _ = ∨lComm _ _ ∙ 1lLeftAnnihilates∨l _

  -- Provide an interface to CommMonoid lemmas about _∧l_.
  module ∧l = CommMonoidTheory (Semilattice→CommMonoid (Lattice→MeetSemilattice L'))

  ∧lLdist∧l : ∀ x y z → x ∧l (y ∧l z) ≡ (x ∧l y) ∧l (x ∧l z)
  ∧lLdist∧l x y z = congL _∧l_ (sym (∧lIdem _)) ∙ ∧l.commAssocSwap x x y z


module Order (L' : Lattice ℓ) where
 private L = fst L'
 open LatticeStr (snd L')
 open JoinSemilattice (Lattice→JoinSemilattice L') renaming (_≤_ to _≤j_ ; IndPoset to JoinPoset)
 open MeetSemilattice (Lattice→MeetSemilattice L') renaming (_≤_ to _≤m_ ; IndPoset to MeetPoset)

 ≤j→≤m : ∀ x y → x ≤j y → x ≤m y
 ≤j→≤m x y x∨ly≡y = x ∧l y         ≡⟨ cong (x ∧l_) (sym x∨ly≡y) ⟩
                    x ∧l (x ∨l y) ≡⟨ ∧lAbsorb∨l _ _ ⟩
                    x ∎

 ≤m→≤j : ∀ x y → x ≤m y → x ≤j y
 ≤m→≤j x y x∧ly≡x = x ∨l y ≡⟨ ∨lComm _ _ ⟩
                    y ∨l x ≡⟨ cong (y ∨l_) (sym x∧ly≡x) ⟩
                    y ∨l (x ∧l y) ≡⟨ cong (y ∨l_) (∧lComm _ _) ⟩
                    y ∨l (y ∧l x) ≡⟨ ∨lAbsorb∧l _ _ ⟩
                    y ∎

 ≤Equiv : ∀ (x y : L) → (x ≤j y) ≃ (x ≤m y)
 ≤Equiv x y = propBiimpl→Equiv (is-set _ _) (is-set _ _) (≤j→≤m x y) (≤m→≤j x y)

 IndPosetPath : JoinPoset ≡ MeetPoset
 IndPosetPath = PosetPath _ _ .fst ((idEquiv _) , isposetequiv ≤Equiv )

 -- transport some inequalities from ≤m to ≤j
 ∧lIsMinJoin : ∀ x y z → z ≤j x → z ≤j y → z ≤j x ∧l y
 ∧lIsMinJoin _ _ _ z≤jx z≤jy = ≤m→≤j _ _ (∧lIsMin _ _ _ (≤j→≤m _ _ z≤jx) (≤j→≤m _ _ z≤jy))

 ∧≤LCancelJoin : ∀ x y → x ∧l y ≤j y
 ∧≤LCancelJoin x y = ≤m→≤j _ _ (∧≤LCancel x y)

 ∧≤RCancelJoin : ∀ x y → x ∧l y ≤j x
 ∧≤RCancelJoin x y = ≤m→≤j _ _ (∧≤RCancel x y)


module _ {L : Lattice ℓ} {M : Lattice ℓ'} (φ ψ : LatticeHom L M) where
 open LatticeStr ⦃...⦄
 open IsLatticeHom
 private
   instance
     _ = L
     _ = M
     _ = snd L
     _ = snd M

 LatticeHom≡f : fst φ ≡ fst ψ → φ ≡ ψ
 LatticeHom≡f = Σ≡Prop λ f → isPropIsLatticeHom _ f _



module LatticeHoms where
  open IsLatticeHom

  compIsLatticeHom : {A : Lattice ℓ} {B : Lattice ℓ'} {C : Lattice ℓ''}
    {g : ⟨ B ⟩ → ⟨ C ⟩} {f : ⟨ A ⟩ → ⟨ B ⟩}
    → IsLatticeHom (B .snd) g (C .snd)
    → IsLatticeHom (A .snd) f (B .snd)
    → IsLatticeHom (A .snd) (g ∘ f) (C .snd)
  compIsLatticeHom {g = g} {f} gh fh .pres0 = cong g (fh .pres0) ∙ gh .pres0
  compIsLatticeHom {g = g} {f} gh fh .pres1 = cong g (fh .pres1) ∙ gh .pres1
  compIsLatticeHom {g = g} {f} gh fh .pres∨l x y = cong g (fh .pres∨l x y) ∙ gh .pres∨l (f x) (f y)
  compIsLatticeHom {g = g} {f} gh fh .pres∧l x y = cong g (fh .pres∧l x y) ∙ gh .pres∧l (f x) (f y)


  compLatticeHom : {L : Lattice ℓ} {M : Lattice ℓ'} {N : Lattice ℓ''}
              → LatticeHom L M → LatticeHom M N → LatticeHom L N
  fst (compLatticeHom f g) x = g .fst (f .fst x)
  snd (compLatticeHom f g) = compIsLatticeHom (g .snd) (f .snd)

  _∘l_ : {L : Lattice ℓ} {M : Lattice ℓ'} {N : Lattice ℓ''} → LatticeHom M N → LatticeHom L M → LatticeHom L N
  _∘l_ = flip compLatticeHom

  compIdLatticeHom : {L : Lattice ℓ} {M : Lattice ℓ'} (φ : LatticeHom L M) → compLatticeHom (idLatticeHom L) φ ≡ φ
  compIdLatticeHom φ = LatticeHom≡f _ _ refl

  idCompLatticeHom : {L : Lattice ℓ} {M : Lattice ℓ'} (φ : LatticeHom L M) → compLatticeHom φ (idLatticeHom M) ≡ φ
  idCompLatticeHom φ = LatticeHom≡f _ _ refl

  compAssocLatticeHom : {L : Lattice ℓ} {M : Lattice ℓ'} {N : Lattice ℓ''} {U : Lattice ℓ'''}
                   → (φ : LatticeHom L M) (ψ : LatticeHom M N) (χ : LatticeHom N U)
                   → compLatticeHom (compLatticeHom φ ψ) χ ≡ compLatticeHom φ (compLatticeHom ψ χ)
  compAssocLatticeHom _ _ _ = LatticeHom≡f _ _ refl
