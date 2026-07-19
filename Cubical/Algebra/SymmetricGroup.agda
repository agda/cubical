module Cubical.Algebra.SymmetricGroup where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.SumFin
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Bool
open import Cubical.Data.Unit

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.GroupPath
open import Cubical.Algebra.Group.Instances.Bool
open import Cubical.Algebra.Group.Instances.Unit

private variable
  ℓ ℓ' : Level
  X Y : Type ℓ

SymGroup : (X : Type ℓ) → isSet X → Group ℓ
SymGroup X isSetX = makeGroup {G = X ≃ X} (idEquiv X) compEquiv invEquiv
  (isOfHLevel≃ 2 isSetX isSetX)
  compEquiv-assoc
  compEquivEquivId
  compEquivIdEquiv
  invEquiv-is-rinv
  invEquiv-is-linv

FinSymGroup : ℕ → Group₀
FinSymGroup n = SymGroup (Fin n) isSetFin

Sym0≃1 : GroupEquiv (FinSymGroup 0) UnitGroup₀
Sym0≃1 = contrGroupEquivUnit $ inhProp→isContr (idEquiv _) $ isOfHLevel≃ 1 isProp⊥ isProp⊥

Sym0≡1 : FinSymGroup 0 ≡ UnitGroup₀
Sym0≡1 = uaGroup Sym0≃1

Sym1≃1 : GroupEquiv (FinSymGroup 1) UnitGroup₀
Sym1≃1 = contrGroupEquivUnit $ isOfHLevel≃ 0 isContrSumFin1 isContrSumFin1

Sym1≡1 : FinSymGroup 1 ≡ UnitGroup₀
Sym1≡1 = uaGroup Sym1≃1

Sym2≃Bool : GroupEquiv (FinSymGroup 2) BoolGroup
Sym2≃Bool = GroupIso→GroupEquiv $ invGroupIso $ ≅Bool $
  Fin 2 ≃ Fin 2 Iso⟨ equivCompIso SumFin2≃Bool SumFin2≃Bool ⟩
  Bool ≃ Bool   Iso⟨ invIso univalenceIso ⟩
  Bool ≡ Bool   Iso⟨ invIso reflectIso ⟩
  Bool          ∎Iso
  where open BoolReflection

Sym2≡Bool : FinSymGroup 2 ≡ BoolGroup
Sym2≡Bool = uaGroup Sym2≃Bool

SymUnit≃Unit : GroupEquiv (SymGroup Unit isSetUnit) UnitGroup₀
SymUnit≃Unit = contrGroupEquivUnit $ isOfHLevel≃ 0 isContrUnit isContrUnit

SymUnit≡Unit : SymGroup Unit isSetUnit ≡ UnitGroup₀
SymUnit≡Unit = uaGroup SymUnit≃Unit

SymBool≃Bool : GroupEquiv (SymGroup Bool isSetBool) BoolGroup
SymBool≃Bool = GroupIso→GroupEquiv $ invGroupIso $ ≅Bool $
  Bool ≃ Bool Iso⟨ invIso univalenceIso ⟩
  Bool ≡ Bool Iso⟨ invIso reflectIso ⟩
  Bool        ∎Iso
  where open BoolReflection

SymBool≡Bool : SymGroup Bool isSetBool ≡ BoolGroup
SymBool≡Bool = uaGroup SymBool≃Bool

module _ (n : ℕ) where

  ⟨Sym⟩≃factorial : ⟨ FinSymGroup n ⟩ ≃ Fin (n !)
  ⟨Sym⟩≃factorial = SumFin≃≃ n

  ⟨Sym⟩≡factorial : ⟨ FinSymGroup n ⟩ ≡ Fin (n !)
  ⟨Sym⟩≡factorial = ua ⟨Sym⟩≃factorial

Sym-cong-≃ : ∀ isSetX isSetY → X ≃ Y → GroupEquiv (SymGroup X isSetX) (SymGroup Y isSetY)
Sym-cong-≃ isSetX isSetY e .fst = equivComp e e
Sym-cong-≃ isSetX isSetY e .snd = makeIsGroupHom λ g h → sym $ equivEq $ funExt λ x → cong (e .fst ∘ h .fst) (retEq e _)
