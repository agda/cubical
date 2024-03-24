{-# OPTIONS --safe  #-}

module Cubical.Tactics.GroupSolver.Solver where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Data.Unit
open import Cubical.Data.List
open import Cubical.Data.Maybe

open import Cubical.Reflection.Base
import Agda.Builtin.Reflection as R

open import Cubical.WildCat.Base
open import Cubical.Tactics.WildCatSolver.Solvers

open import Cubical.WildCat.Functor
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties

open import Cubical.Tactics.WildCatSolver.Solvers


module _ {ℓ} where

 module _ (G : Group ℓ) where
  open GroupStr (snd G)
  Group→WildGroupoid : WildGroupoid ℓ-zero ℓ
  WildCat.ob (WildGroupoid.wildCat Group→WildGroupoid) = Unit
  WildCat.Hom[_,_] (WildGroupoid.wildCat Group→WildGroupoid) _ _ = ⟨ G ⟩
  WildCat.id (WildGroupoid.wildCat Group→WildGroupoid) = 1g
  WildCat._⋆_ (WildGroupoid.wildCat Group→WildGroupoid) = _·_
  WildCat.⋆IdL (WildGroupoid.wildCat Group→WildGroupoid) = ·IdL
  WildCat.⋆IdR (WildGroupoid.wildCat Group→WildGroupoid) = ·IdR
  WildCat.⋆Assoc (WildGroupoid.wildCat Group→WildGroupoid) _ _ _ = sym (·Assoc _ _ _)
  wildIsIso.inv' (WildGroupoid.isWildGroupoid Group→WildGroupoid f) = inv f
  wildIsIso.sect (WildGroupoid.isWildGroupoid Group→WildGroupoid f) = ·InvL f
  wildIsIso.retr (WildGroupoid.isWildGroupoid Group→WildGroupoid f) = ·InvR f


 GroupHom' : (G H : Group ℓ) → Type ℓ

 GroupHom' G H = WildFunctor
    (WildGroupoid.wildCat (Group→WildGroupoid G))
    (WildGroupoid.wildCat (Group→WildGroupoid H))

 IsoGroupHom' : ∀ {G H} → Iso (GroupHom' G H) (GroupHom G H)
 Iso.fun IsoGroupHom' wf = _ , makeIsGroupHom (WildFunctor.F-seq wf)
 WildFunctor.F-ob (Iso.inv IsoGroupHom' _) = λ _ → tt
 WildFunctor.F-hom (Iso.inv IsoGroupHom' (f , _)) = f
 WildFunctor.F-id (Iso.inv IsoGroupHom' (_ , gh)) = IsGroupHom.pres1 gh
 WildFunctor.F-seq (Iso.inv IsoGroupHom' (_ , gh)) = IsGroupHom.pres· gh
 Iso.rightInv IsoGroupHom' _ = GroupHom≡ refl
 WildFunctor.F-ob (Iso.leftInv IsoGroupHom' _ i) = λ _ → tt
 WildFunctor.F-hom (Iso.leftInv IsoGroupHom' wf i) = WildFunctor.F-hom wf
 WildFunctor.F-id (Iso.leftInv (IsoGroupHom' {G = G} {H = H}) wf i) =
   IsGroup.is-set (GroupStr.isGroup (snd H))
      (WildFunctor.F-hom wf (GroupStr.1g (snd G)))
      (GroupStr.1g (snd H))
      (hom1g (G .snd) (WildFunctor.F-hom wf) (H .snd)
         (WildFunctor.F-seq wf))
      (WildFunctor.F-id wf) i
 WildFunctor.F-seq (Iso.leftInv IsoGroupHom' wf i) = λ f g → WildFunctor.F-seq wf f g


module Group-Solver ℓ where

 GroupWS : WildCatInstance ℓ-zero ℓ
 WildCatInstance.wildStr GroupWS = Group ℓ
 WildCatInstance.toWildCat GroupWS = WildGroupoid.wildCat ∘ Group→WildGroupoid
 WildCatInstance.mbIsWildGroupoid GroupWS = just (WildGroupoid.isWildGroupoid ∘ Group→WildGroupoid)

 private
  module GRP-WS = WildCatInstance GroupWS

 macro
  solveGroup : R.Term → R.Term → R.TC Unit
  solveGroup = GRP-WS.solveW (R.def (quote GroupWS) ( R.unknown v∷ []))

