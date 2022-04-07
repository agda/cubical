{-

The sheaf property of a presheaf on a distributive lattice or a basis thereof
can be expressed as preservation of limits over diagrams defined in this file.

-}
{-# OPTIONS --safe #-}

module Cubical.Categories.DistLatticeSheaf.Diagram where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat
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



-- DLShfDiagHom n (sing i) (sing j) is retract of i≡j
-- DLShfDiagHom n (sing i) (pair j k) is retract of i≡j

encode : {n : ℕ} (x y : DLShfDiagOb n) → Type
encode (sing x) (sing x₁) = x ≡ x₁
encode (sing x) (pair x₁ x₂) = {!!}
encode (pair x x₁) (sing x₂) = {!!}
encode (pair x x₁) (pair x₂ x₃) = {!!}

discreteDLShfDiagHom : {n : ℕ} (x y : DLShfDiagOb n) → Discrete (DLShfDiagHom n x y)
discreteDLShfDiagHom = {!!}
-- discreteDLShfDiagHom _ _ idAr g = {!g!}
-- discreteDLShfDiagHom _ _ singPair g = {!!}
-- discreteDLShfDiagHom (sing zero) (sing zero) idAr idAr = yes refl
-- discreteDLShfDiagHom (sing zero) (sing (suc _)) ()
-- discreteDLShfDiagHom (sing (suc _)) (sing zero) ()
-- discreteDLShfDiagHom (sing (suc i)) (sing (suc .i)) idAr g = {!!}
-- discreteDLShfDiagHom (sing zero) (pair .zero j) singPair singPair = yes refl
-- discreteDLShfDiagHom (sing (suc i)) (pair .(suc i) j) singPair g = {!!}
-- discreteDLShfDiagHom (pair _ _) (sing _) ()
-- discreteDLShfDiagHom (pair zero zero) (pair .zero .zero) idAr idAr = yes refl
-- discreteDLShfDiagHom (pair zero (suc j)) (pair .zero .(suc j)) idAr g = {!!}
-- discreteDLShfDiagHom (pair (suc i) zero) (pair .(suc i) .zero) idAr g = {!!}
-- discreteDLShfDiagHom (pair (suc i) (suc j)) (pair .(suc i) .(suc j)) idAr g = {!!}

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
isSetHom (DLShfDiag n) = Discrete→isSet (discreteDLShfDiagHom _ _)


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
 snd (isLimCone⋁Cone α u uCone) _ = Σ≡Prop (λ _ → isPropIsConeMor uCone (⋁Cone α) _)
                                           (is-prop-valued _ _ _ _)
