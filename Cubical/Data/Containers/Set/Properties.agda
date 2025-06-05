{-# OPTIONS --safe #-}

module Cubical.Data.Containers.Set.Properties where

open import Cubical.Categories.Category
open import Cubical.Categories.Functor 
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.NaturalTransformation hiding (_⟦_⟧)
open import Cubical.Foundations.Prelude hiding (_◁_)
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Containers.Generalised.Base
open import Cubical.Categories.Instances.Sets
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Categories.Equivalence.Base
open import Cubical.Data.Containers.Set.Base

open Iso
open SetCon
open GenContainer
open _⇒ᶜ_
open Functor

-- Type of SetCont is iso to GenContainer SET 
setToGenCont : ∀ {ℓ} → Iso (SetCon {ℓ} {ℓ}) (GenContainer (SET ℓ))
S (fun setToGenCont C) = Shape C
P (fun setToGenCont C) s = (Position C s , isSetPos C)
isSetS (fun setToGenCont C) = isSetShape C
Shape (inv setToGenCont C) = S C
Position (inv setToGenCont C) s = fst (P C s)
isSetShape (inv setToGenCont C) = isSetS C
isSetPos (inv setToGenCont C) {s} = snd (P C s)
rightInv setToGenCont _ = refl
leftInv setToGenCont _ = refl

open Conts
open _≃ᶜ_
open _⇒c_

-- Category of set containers is equivalent to category of generalised containers on SET
equivSetContGenContSet : ∀ {ℓ} → SetCont {ℓ} {ℓ} ≃ᶜ Cont (SET ℓ)
F-ob (func equivSetContGenContSet) = fun setToGenCont
shape (F-hom (func equivSetContGenContSet) g) = u g
pos (F-hom (func equivSetContGenContSet) g) = f g
F-id (func equivSetContGenContSet) = refl
shape (F-seq (func equivSetContGenContSet) g h i) s = u h (u g s)
pos (F-seq (func equivSetContGenContSet) g h i) s p = f g s (f h (u g s) p)
isEquiv (equivSetContGenContSet {ℓ}) = ∣ winv ∣₁
  where
    open WeakInverse
    winv : WeakInverse {ℓ-suc ℓ} {ℓ} {ℓ-suc (ℓ-suc ℓ)} {ℓ-suc (ℓ-suc ℓ)}
      {SetCont {ℓ} {ℓ}} {Cont {ℓ-suc ℓ} {ℓ} (SET ℓ)} (func equivSetContGenContSet)
    F-ob (invFunc winv) = inv setToGenCont
    u (F-hom (invFunc winv) g) = shape g
    f (F-hom (invFunc winv) g) = pos g
    F-id (invFunc winv) = refl
    u (F-seq (invFunc winv) g h i) s = shape h (shape g s)
    f (F-seq (invFunc winv) g h i) s p = pos g s (pos h (shape g s) p)
    u (NatTrans.N-ob (NatIso.trans (η winv)) C) s = s
    f (NatTrans.N-ob (NatIso.trans (η winv)) C) s p = p
    u (NatTrans.N-hom (NatIso.trans (η winv)) g i) s = u g s
    f (NatTrans.N-hom (NatIso.trans (η winv)) g i) s p = f g s p
    u (isIso.inv (NatIso.nIso (η winv) C)) s = s
    f (isIso.inv (NatIso.nIso (η winv) C)) s p = p
    u (isIso.sec (NatIso.nIso (η winv) C) i) s = s
    f (isIso.sec (NatIso.nIso (η winv) C) i) s p = p
    u (isIso.ret (NatIso.nIso (η winv) C) i) s = s
    f (isIso.ret (NatIso.nIso (η winv) C) i) s p = p
    shape (NatTrans.N-ob (NatIso.trans (ε winv)) C) s = s
    pos (NatTrans.N-ob (NatIso.trans (ε winv)) C) s p = p
    shape (NatTrans.N-hom (NatIso.trans (ε winv)) g i) s = shape g s
    pos (NatTrans.N-hom (NatIso.trans (ε winv)) g i) s p = pos g s p
    shape (isIso.inv (NatIso.nIso (ε winv) C)) s = s
    pos (isIso.inv (NatIso.nIso (ε winv) C)) s p = p
    shape (isIso.sec (NatIso.nIso (ε winv) C) i) s = s
    pos (isIso.sec (NatIso.nIso (ε winv) C) i) s p = p
    shape (isIso.ret (NatIso.nIso (ε winv) C) i) s = s
    pos (isIso.ret (NatIso.nIso (ε winv) C) i) s p = p
