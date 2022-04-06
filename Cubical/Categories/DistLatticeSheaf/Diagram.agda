{-

The sheaf property of a presheaf on a distributive lattice or a basis thereof
can be expressed as preservation of limits over diagrams defined in this file.

-}
{-# OPTIONS --safe #-}

module Cubical.Categories.DistLatticeSheaf.Diagram where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat
open import Cubical.Data.FinData
open import Cubical.Relation.Nullary
open import Cubical.Categories.Category


data DLShfDiagOb (n : ℕ) : Type where
  sing : Fin n → DLShfDiagOb n
  pair : Fin n → Fin n → DLShfDiagOb n

data DLShfDiagHom (n : ℕ) : DLShfDiagOb n → DLShfDiagOb n → Type where
  idAr : {x : DLShfDiagOb n} → DLShfDiagHom n x x
  singPair : {i j : Fin n} → DLShfDiagHom n (sing i) (pair i j)

open Iso
private
 singIso : ∀ (n : ℕ) (i : Fin n)
         → Iso (DLShfDiagHom n (sing i) (sing i))
               (DLShfDiagHom (suc n) (sing (suc i)) (sing (suc i)))
 fun (singIso (suc n) i) _ = idAr
 inv (singIso (suc n) i) _ = idAr
 rightInv (singIso (suc n) i) f = {!f!}
 leftInv (singIso (suc n) i) = {!!}

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
