{-# OPTIONS --safe --postfix-projections #-}

open import Cubical.Core.Everything

open import Cubical.Functions.Embedding
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport

-- A helper module for deriving univalence for a higher inductive-recursive
-- universe.
--
--  U is the type of codes
--  El is the decoding
--  un is a higher constructor that requires paths between codes to exist
--    for equivalences of decodings
--  comp is intended to be the computational behavior of El on un, although
--    it seems that being a path is sufficient.
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
    (un : ∀ s t → El s ≃ El t → s ≡ t)
    (comp : ∀{s t} (e : El s ≃ El t) → cong El (un s t e) ≡ ua e)
  where
private
  variable
    A : Type ℓ'

module UU-Lemmas where
  reg : transport (λ _ → A) ≡ idfun A
  reg {A} i z = transp (λ _ → A) i z

  nu : ∀ x y → x ≡ y → El x ≃ El y
  nu x y p = pathToEquiv (cong El p)

  cong-un-te
    : ∀ x y (p : El x ≡ El y)
    → cong El (un x y (pathToEquiv p)) ≡ p
  cong-un-te x y p
    = comp (pathToEquiv p) ∙ uaη p

  nu-un : ∀ x y (e : El x ≃ El y) → nu x y (un x y e) ≡ e
  nu-un x y e
    = equivEq {e = nu x y (un x y e)} {f = e} λ i z
        → (cong (λ p → transport p z) (comp e) ∙ uaβ e z) i

  El-un-equiv : ∀ x i → El (un x x (idEquiv _) i) ≃ El x
  El-un-equiv x i = λ where
      .fst → transp (λ j → p j) (i ∨ ~ i)
      .snd → transp (λ j → isEquiv (transp (λ k → p (j ∧ k)) (~ j ∨ i ∨ ~ i)))
                (i ∨ ~ i) (idIsEquiv T)
    where
    T = El (un x x (idEquiv _) i)
    p : T ≡ El x
    p j = (comp (idEquiv _) ∙ uaIdEquiv {A = El x}) j i

  un-refl : ∀ x → un x x (idEquiv (El x)) ≡ refl
  un-refl x i j
    = hcomp (λ k → λ where
          (i = i0) → un x x (idEquiv (El x)) j
          (i = i1) → un x x (idEquiv (El x)) (j ∨ k)
          (j = i0) → un x x (idEquiv (El x)) (~ i ∨ k)
          (j = i1) → x)
        (un (un x x (idEquiv (El x)) (~ i)) x (El-un-equiv x (~ i)) j)

  nu-refl : ∀ x → nu x x refl ≡ idEquiv (El x)
  nu-refl x = equivEq {e = nu x x refl} {f = idEquiv (El x)} reg

  un-nu : ∀ x y (p : x ≡ y) → un x y (nu x y p) ≡ p
  un-nu x y p
    = J (λ z q → un x z (nu x z q) ≡ q) (cong (un x x) (nu-refl x) ∙ un-refl x) p

open UU-Lemmas
open Iso

equivIso : ∀ s t → Iso (s ≡ t) (El s ≃ El t)
equivIso s t .fun = nu s t
equivIso s t .inv = un s t
equivIso s t .rightInv = nu-un s t
equivIso s t .leftInv = un-nu s t

pathIso : ∀ s t → Iso (s ≡ t) (El s ≡ El t)
pathIso s t .fun = cong El
pathIso s t .inv = un s t ∘ pathToEquiv
pathIso s t .rightInv = cong-un-te s t
pathIso s t .leftInv = un-nu s t

minivalence : ∀{s t} → (s ≡ t) ≃ (El s ≃ El t)
minivalence {s} {t} = isoToEquiv (equivIso s t)

path-reflection : ∀{s t} → (s ≡ t) ≃ (El s ≡ El t)
path-reflection {s} {t} = isoToEquiv (pathIso s t)

isEmbeddingEl : isEmbedding El
isEmbeddingEl s t = snd path-reflection
