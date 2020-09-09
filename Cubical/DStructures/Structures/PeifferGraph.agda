{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.DStructures.Structures.PeifferGraph where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.FunExtEquiv

open import Cubical.Homotopy.Base

open import Cubical.Data.Sigma

open import Cubical.Relation.Binary

open import Cubical.Algebra.Group
open import Cubical.Structures.LeftAction

open import Cubical.DStructures.Base
open import Cubical.DStructures.Meta.Properties
open import Cubical.DStructures.Structures.Constant
open import Cubical.DStructures.Meta.Combine
open import Cubical.DStructures.Structures.Type
open import Cubical.DStructures.Structures.Group
open import Cubical.DStructures.Structures.ReflGraph

open GroupLemmas
open MorphismLemmas

private
  variable
    ℓ ℓ' : Level

module _ (𝒢 : ReflGraph ℓ ℓ') where
  open ReflGraphNotation 𝒢

  ----------------------------------------------------
  -- The peiffer condition for reflexive graphs,
  -- i.e. the missing property to turn a precrossed
  -- module into a crossed module
  ----------------------------------------------------
  isPeifferGraph : Type ℓ'
  isPeifferGraph = (a b : ⟨ G₁ ⟩) → ((is b +₁ (a -₁ it a)) +₁ (-is b +₁ b)) +₁ it a ≡ b +₁ a

  -- G₁ is a set, so isPeifferGraph is a proposition
  isPropIsPeifferGraph : isProp isPeifferGraph
  isPropIsPeifferGraph = isPropΠ2 (λ a b → set₁ (((is b +₁ (a -₁ it a)) +₁ (-is b +₁ b)) +₁ it a) (b +₁ a))

  ---------------------------------------------------
  -- lemmas about the peiffer graphs
  ---------------------------------------------------
  module _ (isPeifferG : isPeifferGraph) where
   abstract
     -- the peiffer condition can be simplified to this
     isPeifferGraph2 : (a b : ⟨ G₁ ⟩) → (a -₁ it a) +₁ (-is b +₁ b) ≡ (-is b +₁ (b +₁ a)) -₁ it a
     isPeifferGraph2 a b = (a -₁ ita) +₁ (-isb +₁ b)
                              ≡⟨ sym (lCancel-lId G₁ isb ((a -₁ ita) +₁ (-isb +₁ b)))
                                 ∙ sym (rCancel-rId G₁ ((-isb +₁ isb) +₁ ((a -₁ ita) +₁ (-isb +₁ b))) ita) ⟩
                           ((-isb +₁ isb) +₁ ((a -₁ ita) +₁ (-isb +₁ b))) +₁ (ita -₁ ita)
                              ≡⟨ assoc₁ ((-isb +₁ isb) +₁ ((a -₁ ita) +₁ (-isb +₁ b))) ita -ita ⟩
                           (((-isb +₁ isb) +₁ ((a -₁ ita) +₁ (-isb +₁ b))) +₁ ita) +₁ -ita
                              ≡⟨ cong (λ z → (z +₁ ita) -₁ ita)
                                      (sym (assoc₁ -isb isb _)) ⟩
                           ((-isb +₁ (isb +₁ ((a -₁ ita) +₁ (-isb +₁ b)))) +₁ ita) +₁ -ita
                              ≡⟨ cong (λ z → ((-isb +₁ z) +₁ ita) +₁ -ita)
                                      (assoc₁ _ _ _) ⟩
                           ((-isb +₁ ((isb +₁ (a -₁ ita)) +₁ (-isb +₁ b))) +₁ ita) +₁ -ita
                              ≡⟨ cong (_+₁ -ita)
                                      (sym (assoc₁ -isb _ ita)) ⟩
                           (-isb +₁ (((isb +₁ (a -₁ ita)) +₁ (-isb +₁ b)) +₁ ita)) -₁ ita
                             ≡⟨ cong (λ z → (-isb +₁ z) -₁ ita)
                                     (isPeifferG a b) ⟩
                           (-isb +₁ (b +₁ a)) -₁ ita ∎
                           where
                             -a = -₁ a
                             -ita = -it a
                             ita = it a
                             isb = is b
                             -isb = -is b
                             -b = -₁ b

     -- inverting both sides of the identity isPeifferGraph2 and simplifying
     -- gives this
     isPeifferGraph3 : (a b : ⟨ G₁ ⟩) → (-₁ b) +₁ (is b +₁ (it a -₁ a)) ≡ it a +₁ ((-₁ a) +₁ ((-₁ b) +₁ is b))
     isPeifferGraph3 a b = -b +₁ (isb +₁ (ita -₁ a))
                              ≡⟨ cong (λ z → -b +₁ (z +₁ (ita -₁ a)))
                                      (sym (invInvo G₁ isb))
                                 ∙ cong (λ z → -b +₁ ((-₁ -isb) +₁ (z -₁ a)))
                                        (sym (invInvo G₁ ita)) ⟩
                           -b +₁ ((-₁ -isb) +₁ ((-₁ -ita) -₁ a))
                              ≡⟨ sym (invDistr₄ G₁ a -ita -isb b) ⟩
                           -₁ (((a +₁ -ita) +₁ -isb) +₁ b)
                              ≡⟨ cong -₁_ (sym (assoc₁ _ -isb b)) ⟩
                           -₁ ((a -₁ ita) +₁ (-isb +₁ b))
                             ≡⟨ cong -₁_ (isPeifferGraph2 a b) ⟩
                           -₁ ((-isb +₁ (b +₁ a)) -₁ ita)
                             ≡⟨ cong (λ z → -₁ (z -₁ ita)) (assoc₁ -isb b a) ⟩
                           -₁ (((-isb +₁ b) +₁ a) -₁ ita)
                             ≡⟨ invDistr₄ G₁ -isb b a -ita ⟩
                           (-₁ -ita) +₁ (-a +₁ (-b +₁ (-₁ -isb)))
                             ≡⟨ cong (_+₁ (-a +₁ (-b +₁ (-₁ -isb))))
                                     (invInvo G₁ ita)
                                ∙ cong (λ z → ita +₁ (-a +₁ (-b +₁ z)))
                                       (invInvo G₁ isb) ⟩
                           ita +₁ (-a +₁ (-b +₁ isb)) ∎
                           where
                             -a = -₁ a
                             -ita = -₁ (it a)
                             ita = it a
                             isb = is b
                             -isb = -₁ isb
                             -b = -₁ b

     -- plugging -a and -b into isPeifferGraph4 gives this
     isPeifferGraph4 : (a b : ⟨ G₁ ⟩) → b +₁ ((-₁ (is b)) +₁ ((-₁ (it a)) +₁ a)) ≡ (-₁ (it a)) +₁ (a +₁ (b -₁ (is b)))
     isPeifferGraph4 a b = b +₁ (-isb +₁ (-ita +₁ a))
                             ≡⟨ cong (_+₁ (-isb +₁ (-ita +₁ a)))
                                     (sym (invInvo G₁ b)) ⟩
                           (-₁ -b) +₁ (-isb +₁ (-ita +₁ a))
                             ≡⟨ cong (λ z → (-₁ -b) +₁ (-isb +₁ (-ita +₁ z)))
                                     (sym (invInvo G₁ a)) ⟩
                           (-₁ -b) +₁ (-isb +₁ (-ita -₁ -a))
                             ≡⟨ cong (λ z → (-₁ -b) +₁ (-isb +₁ (z -₁ -a))) (sym (mapInv ι∘τ a)) ⟩
                           (-₁ -b) +₁ (-isb +₁ ((it -a) -₁ -a))
                             ≡⟨ cong (λ z → (-₁ -b) +₁ (z +₁ ((it -a) -₁ -a))) (sym (mapInv ι∘σ b)) ⟩
                           (-₁ -b) +₁ (is -b +₁ ((it -a) -₁ -a))
                             ≡⟨ isPeifferGraph3 -a -b ⟩
                           it -a +₁ ((-₁ -a) +₁ ((-₁ -b) +₁ is -b))
                             ≡⟨ cong (_+₁ ((-₁ -a) +₁ ((-₁ -b) +₁ is -b)))
                                     (mapInv ι∘τ a) ⟩
                           -ita +₁ ((-₁ -a) +₁ ((-₁ -b) +₁ is -b))
                             ≡⟨ cong (λ z → -ita +₁ (z +₁ ((-₁ -b) +₁ is -b)))
                                     (invInvo G₁ a) ⟩
                           -ita +₁ (a +₁ ((-₁ -b) +₁ is -b))
                             ≡⟨ cong (λ z → -ita +₁ (a +₁ (z +₁ is -b)))
                                     (invInvo G₁ b) ⟩
                           -ita +₁ (a +₁ (b +₁ is -b))
                             ≡⟨ cong (λ z → -ita +₁ (a +₁ (b +₁ z)))
                                     (mapInv ι∘σ b) ⟩
                           -ita +₁ (a +₁ (b -₁ isb)) ∎
                           where
                             -a = -₁ a
                             -ita = -it a
                             isb = is b
                             -isb = -is b
                             -b = -₁ b

-----------------------------------------------
-- URG structure on the type of peiffer graphs
--
--   isPeifferGraph
--        |
--    ReflGraph
-----------------------------------------------

module _ (ℓ ℓ' : Level) where
  private
    ℓℓ' = ℓ-max ℓ ℓ'

  𝒮ᴰ-ReflGraph\Peiffer : URGStrᴰ (𝒮-ReflGraph ℓ ℓℓ')
                                 (λ 𝒢 → isPeifferGraph 𝒢)
                                 ℓ-zero
  𝒮ᴰ-ReflGraph\Peiffer = Subtype→Sub-𝒮ᴰ (λ 𝒢 → isPeifferGraph 𝒢 , isPropIsPeifferGraph 𝒢)
                                        (𝒮-ReflGraph ℓ ℓℓ')

  PeifferGraph : Type (ℓ-suc ℓℓ')
  PeifferGraph = Σ[ 𝒢 ∈ ReflGraph ℓ ℓℓ' ] isPeifferGraph 𝒢

  𝒮-PeifferGraph : URGStr PeifferGraph ℓℓ'
  𝒮-PeifferGraph = ∫⟨ 𝒮-ReflGraph ℓ ℓℓ' ⟩ 𝒮ᴰ-ReflGraph\Peiffer
