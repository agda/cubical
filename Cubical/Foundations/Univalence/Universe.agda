{-# OPTIONS --cubical --safe --postfix-projections #-}

open import Cubical.Core.Everything

open import Cubical.Functions.Embedding
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence

-- A helper module for deriving univalence for a higher inductive-recursive
-- universe.
--
--  U is the type of codes
--  El is the decoding
--  uaf is a higher constructor that requires paths between codes to exist
--    for equivalences of decodings
--  comp is intended to be the computational behavior of El on uaf, although
--    it seems that being a path is sufficient.
--  ret is a higher constructor that fills out the equivalence structure
--    for uaf and the computational behavior of El.
--
-- Given a universe defined as above, it's possible to show that the path
-- space of the code type is equivalent to the path space of the actual
-- decodings, which are themselves determined by equivalences.
--
-- The levels are left independent, but of course it will generally be
-- impossible to define this sort of universe unless ℓ' < ℓ, because El will
-- be too big to go in a constructor of U. The exception would be if U could
-- be defined independently of El, though it might be tricky to get the right
-- higher structure in such a case.
module Cubical.Foundations.Univalence.Universe {ℓ ℓ'}
    (U : Type ℓ)
    (El : U → Type ℓ')
    (uaf : ∀{s t} → El s ≃ El t → s ≡ t)
    (comp : ∀{s t} (e : El s ≃ El t) → cong El (uaf e) ≡ ua e)
    (ret : ∀{s t : U} → (p : s ≡ t) → uaf (lineToEquiv (λ i → El (p i))) ≡ p)
  where

minivalence : ∀{s t} → (s ≡ t) ≃ (El s ≡ El t)
minivalence {s} {t} = isoToEquiv mini
  where
  open Iso
  mini : Iso (s ≡ t) (El s ≡ El t)
  mini .fun = cong El
  mini .inv = uaf ∘ pathToEquiv
  mini .rightInv p = comp (pathToEquiv p) ∙ uaη p
  mini .leftInv = ret

isEmbeddingEl : isEmbedding El
isEmbeddingEl s t = snd minivalence
