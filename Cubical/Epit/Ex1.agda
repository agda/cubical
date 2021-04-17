{-# OPTIONS --cubical --allow-unsolved-metas #-}
module Cubical.Epit.Ex1 where

open import Cubical.Epit.Part1 hiding (B)

-- We redefine B to be a family of types in this file
variable
  B : A → Type ℓ

-- Exercise 1: state and prove funExt for dependent functions f g : (x : A) → B x


-- Exercise 2: generalize the type of cong to dependent function f : (x : A) → B x
-- (hint: the result should be a PathP)


-- Exercise 3 (easy) state and prove that inhabited propositions are contractible


-- We could have stated isProp as follows:
isProp' : Type ℓ → Type ℓ
isProp' A = (x y : A) → isContr (x ≡ y)

-- Exercise 4 (easy): prove that isProp' A implies isProp A

-- For the converse we need path composition, see ExerciseSession2


-- Exercise 5: prove isPropΠ
isPropΠ : (h : (x : A) → isProp (B x)) → isProp ((x : A) → B x)
isPropΠ h = {!!}


-- Exercise 6: prove the inverse of funExt (sometimes called happly)
funExt⁻ : {f g : (x : A) → B x} → f ≡ g → ((x : A) → f x ≡ g x)
funExt⁻ p = {!!}


-- Exercise 7: use funExt⁻ to prove isSetΠ
isSetΠ : (h : (x : A) → isSet (B x)) → isSet ((x : A) → B x)
isSetΠ h = {!!}


-- We could have defined the type of singletons as follows
singl' : {A : Type ℓ} (a : A) → Type ℓ
singl' {A = A} a = Σ[ x ∈ A ] x ≡ a

-- Exercise 8 (harder): prove the corresponding version of contractibility of singetons for singl'
-- (hint: use a suitable combinations of connections and _~)
isContrSingl' : (x : A) → isContr (singl' x)
isContrSingl' x = {!!}
