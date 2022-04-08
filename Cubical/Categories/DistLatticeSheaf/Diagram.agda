{-

The sheaf property of a presheaf on a distributive lattice or a basis thereof
can be expressed as preservation of limits over diagrams defined in this file.

-}
{-# OPTIONS --safe #-}

module Cubical.Categories.DistLatticeSheaf.Diagram where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Data.FinData

open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary.Poset

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.Limits
open import Cubical.Categories.Instances.DistLattice

open import Cubical.Algebra.DistLattice
open import Cubical.Algebra.Lattice
open import Cubical.Algebra.Semilattice
open import Cubical.Algebra.DistLattice.BigOps

private
  variable
    ℓ ℓ' ℓ'' : Level

data DLShfDiagOb (n : ℕ) : Type where
  sing : Fin n → DLShfDiagOb n
  pair : Fin n → Fin n → DLShfDiagOb n

data DLShfDiagHom (n : ℕ) : DLShfDiagOb n → DLShfDiagOb n → Type where
  idAr : {x : DLShfDiagOb n} → DLShfDiagHom n x x
  singPair : {i j : Fin n} → DLShfDiagHom n (sing i) (pair i j)



module DLShfDiagHomPath where
  variable
   n : ℕ
   x y : DLShfDiagOb n
   f g : DLShfDiagHom n x y
   i j k l : Fin n

  module _ (P : ∀ x y → DLShfDiagHom n x y → Type)
           (d1 : ∀ {i} → P (sing i) (sing i) idAr)
           (d2 : ∀ {i j} → P (pair i j) (pair i j) idAr)
           (d3 : ∀ {i j} → P (sing i) (pair i j) singPair) where
    homJ : ∀ x y f → P x y f
    homJ (sing i) .(sing i) idAr = d1
    homJ (pair i j) .(pair i j) idAr = d2
    homJ (sing i) .(pair i _) singPair = d3


  -- DLShfDiagHom n x y is a retract of Code x y
  Code : (x y : DLShfDiagOb n) → Type
  Code (sing i) (sing j) = i ≡ j
  Code (sing i) (pair j k) = i ≡ j
  Code (pair i j) (sing k) = ⊥
  Code (pair i j) (pair k l) = (i ≡ k) × (j ≡ l)

  isPropCode : ∀ (x y : DLShfDiagOb n) → isProp (Code x y)
  isPropCode (sing i) (sing j) = isSetFin _ _
  isPropCode (sing i) (pair j k) = isSetFin _ _
  isPropCode (pair i j) (sing k) = isProp⊥
  isPropCode (pair i j) (pair k l) = isProp× (isSetFin _ _) (isSetFin _ _)

  encode : (x y : DLShfDiagOb n) → DLShfDiagHom n x y → Code x y
  encode (sing i) .(sing i) idAr = refl
  encode (sing i) .(pair i _) singPair = refl
  encode (pair i j) .(pair i j) idAr = refl , refl

  decode : (x y : DLShfDiagOb n) → Code x y → DLShfDiagHom n x y
  decode (sing i) (sing j) p = subst (λ k → DLShfDiagHom _ (sing i) (sing k)) p idAr
  decode (sing i) (pair j _) p = subst (λ k → DLShfDiagHom _ (sing i) (pair k _)) p singPair
  decode (pair _ _) (sing _) ()
  decode (pair i j) (pair k l) (p , q) =
         subst2 (λ m o → DLShfDiagHom _ (pair i j) (pair m o)) p q idAr

  codeRetract : ∀ (x y : DLShfDiagOb n) (f : DLShfDiagHom n x y)
              → decode x y (encode x y f) ≡ f
  codeRetract = homJ (λ x y f → decode x y (encode x y f) ≡ f)
                  (transportRefl idAr) (transportRefl idAr) (transportRefl singPair)

  isPropDLShfDiagHom : ∀ (x y : DLShfDiagOb n) → isProp (DLShfDiagHom n x y)
  isPropDLShfDiagHom x y = isPropRetract (encode x y) (decode x y)
                                         (codeRetract x y) (isPropCode x y)



open Category
DLShfDiag : ℕ → Category ℓ-zero ℓ-zero
ob (DLShfDiag n) = DLShfDiagOb n
Hom[_,_] (DLShfDiag n) = DLShfDiagHom n
id (DLShfDiag n) = idAr
_⋆_ (DLShfDiag n) idAr f = f
_⋆_ (DLShfDiag n) singPair idAr = singPair
⋆IdL (DLShfDiag n) _ = refl
⋆IdR (DLShfDiag n) idAr = refl
⋆IdR (DLShfDiag n) singPair = refl
⋆Assoc (DLShfDiag n) idAr _ _ = refl
⋆Assoc (DLShfDiag n) singPair idAr _ = refl
isSetHom (DLShfDiag n) = let open DLShfDiagHomPath in isProp→isSet (isPropDLShfDiagHom _ _)


module _ (L' : DistLattice ℓ) where
 private
  L = fst L'
  LCat = (DistLatticeCategory L') ^op
  instance
   _ = snd L'

 open DistLatticeStr ⦃...⦄
 open Join L'
 open JoinSemilattice (Lattice→JoinSemilattice (DistLattice→Lattice L'))
 open PosetStr (IndPoset .snd) hiding (_≤_)
 open MeetSemilattice (Lattice→MeetSemilattice (DistLattice→Lattice L'))
      using (∧≤RCancel ; ∧≤LCancel)
 open Order (DistLattice→Lattice L')

 open Category LCat
 open Functor
 open Cone


 FinVec→Diag : {n : ℕ} → FinVec L n → Functor (DLShfDiag n) LCat
 F-ob (FinVec→Diag α) (sing i) = α i
 F-ob (FinVec→Diag α) (pair i j) = α i ∧l α j
 F-hom (FinVec→Diag α) idAr = is-refl _
 F-hom (FinVec→Diag α) singPair = ≤m→≤j _ _ (∧≤RCancel _ _)
 F-id (FinVec→Diag α) = is-prop-valued _ _ _ _
 F-seq (FinVec→Diag α) _ _ = is-prop-valued _ _ _ _

 ⋁Cone : {n : ℕ} (α : FinVec L n) → Cone (FinVec→Diag α) (⋁ α)
 coneOut (⋁Cone α) (sing i) = ind≤⋁ α i
 coneOut (⋁Cone α) (pair i j) = is-trans _ (α i) _ (≤m→≤j _ _ (∧≤RCancel _ _)) (ind≤⋁ α i)
 coneOutCommutes (⋁Cone α) _ = is-prop-valued _ _ _ _

 isLimCone⋁Cone : {n : ℕ} (α : FinVec L n) → isLimCone (FinVec→Diag α) (⋁ α) (⋁Cone α)
 fst (fst (isLimCone⋁Cone α u uCone)) = ⋁IsMax α _ λ i → uCone .coneOut (sing i)
 snd (fst (isLimCone⋁Cone α u uCone)) _ = is-prop-valued _ _ _ _
 snd (isLimCone⋁Cone α _ uCone) _ = Σ≡Prop (λ _ → isPropIsConeMor uCone (⋁Cone α) _)
                                           (is-prop-valued _ _ _ _)
