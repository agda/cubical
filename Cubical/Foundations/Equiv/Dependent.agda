{-

Dependent version of isomorphisms and equivalences

Extremely useful if one wants to construct explicit isomorphisms between record types
with fields dependent on each other.

This can be generalize in inumerable ways.
Maybe one day someone will find a common scheme and then computer could automatically generate them.

-}
{-# OPTIONS --safe #-}
module Cubical.Foundations.Equiv.Dependent where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Isomorphism

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    A : Type ℓ
    B : Type ℓ'
    P : A → Type ℓ''
    Q : B → Type ℓ'''


-- Relative version of maps and their composition

mapOver :
  (f : A → B)
  (P : A → Type ℓ'')(Q : B → Type ℓ''')
  → Type _
mapOver {A = A} f P Q = (a : A) → P a → Q (f a)

compMapOver :
  {ℓA ℓB ℓC ℓP ℓQ ℓR : Level}
  {A : Type ℓA}{B : Type ℓB}{C : Type ℓC}
  {P : A → Type ℓP}{Q : B → Type ℓQ}{R : C → Type ℓR}
  {f : A → B}{g : B → C}
  → mapOver f P Q → mapOver g Q R
  → mapOver (g ∘ f) P R
compMapOver f g _ p = g _ (f _ p)


-- Fiberwise equivalence

isEquivOver :
  {f : A → B}
  (F : mapOver f P Q)
  → Type _
isEquivOver {A = A} F = (a : A) → isEquiv (F a)


-- Relative version of section and retract

sectionOver :
  {f : A → B}{g : B → A}
  (sec : section f g)
  (F : mapOver f P Q)(G : mapOver g Q P)
  → Type _
sectionOver {B = B} {Q = Q} sec F G =
  (b : B)(q : Q b) → PathP (λ i → Q (sec b i)) (F _ (G _ q)) q

retractOver :
  {f : A → B}{g : B → A}
  (ret : retract f g)
  (F : mapOver f P Q)(G : mapOver g Q P)
  → Type _
retractOver {A = A} {P = P} ret F G =
  (a : A)(p : P a) → PathP (λ i → P (ret a i)) (G _ (F _ p)) p


-- Relative version of isomorphism

open Iso

record IsoOver {ℓ ℓ'} {A : Type ℓ}{B : Type ℓ'}
  (isom : Iso A B)(P : A → Type ℓ'')(Q : B → Type ℓ''')
  : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓ'' ℓ''')) where
  no-eta-equality
  constructor isoover
  field
    fun : mapOver (isom .fun) P Q
    inv : mapOver (isom .inv) Q P
    rightInv : sectionOver (isom .rightInv) fun inv
    leftInv  : retractOver (isom .leftInv ) fun inv

record isIsoOver {ℓ ℓ'} {A : Type ℓ}{B : Type ℓ'}
  (isom : Iso A B)(P : A → Type ℓ'')(Q : B → Type ℓ''')
  (fun : mapOver (isom .fun) P Q)
  : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓ'' ℓ''')) where
  no-eta-equality
  constructor isisoover
  field
    inv : mapOver (isom .inv) Q P
    rightInv : sectionOver (isom .rightInv) fun inv
    leftInv  : retractOver (isom .leftInv ) fun inv

open IsoOver
open isIsoOver


isIsoOver→IsoOver :
  {isom : Iso A B}
  {fun : mapOver (isom .fun) P Q}
  → isIsoOver isom P Q fun
  → IsoOver isom P Q
isIsoOver→IsoOver {fun = fun} isom .fun = fun
isIsoOver→IsoOver {fun = fun} isom .inv = isom .inv
isIsoOver→IsoOver {fun = fun} isom .rightInv = isom .rightInv
isIsoOver→IsoOver {fun = fun} isom .leftInv  = isom .leftInv

IsoOver→isIsoOver :
  {isom : Iso A B}
  → (isom' : IsoOver isom P Q)
  → isIsoOver isom P Q (isom' .fun)
IsoOver→isIsoOver isom .inv = isom .inv
IsoOver→isIsoOver isom .rightInv = isom .rightInv
IsoOver→isIsoOver isom .leftInv  = isom .leftInv


compIsoOver :
  {ℓA ℓB ℓC ℓP ℓQ ℓR : Level}
  {A : Type ℓA}{B : Type ℓB}{C : Type ℓC}
  {P : A → Type ℓP}{Q : B → Type ℓQ}{R : C → Type ℓR}
  {isom₁ : Iso A B}{isom₂ : Iso B C}
  → IsoOver isom₁ P Q → IsoOver isom₂ Q R
  → IsoOver (compIso isom₁ isom₂) P R
compIsoOver {A = A} {B} {C} {P} {Q} {R} {isom₁} {isom₂} isoover₁ isoover₂ = w
  where
  w : IsoOver _ _ _
  w .fun _ = isoover₂ .fun _ ∘ isoover₁ .fun _
  w .inv _ = isoover₁ .inv _ ∘ isoover₂ .inv _
  w .rightInv b q i =
    comp
    (λ j → R (compPath-filler (cong (isom₂ .fun) (isom₁ .rightInv _)) (isom₂ .rightInv b) j i))
    (λ j → λ
      { (i = i0) → w .fun _ (w .inv _ q)
      ; (i = i1) → isoover₂ .rightInv _ q j })
    (isoover₂ .fun _ (isoover₁ .rightInv _ (isoover₂ .inv _ q) i))
  w .leftInv a p i =
    comp
    (λ j → P (compPath-filler (cong (isom₁ .inv) (isom₂ .leftInv _)) (isom₁ .leftInv a) j i))
    (λ j → λ
      { (i = i0) → w .inv _ (w .fun _ p)
      ; (i = i1) → isoover₁ .leftInv _ p j })
    (isoover₁ .inv _ (isoover₂ .leftInv _ (isoover₁ .fun _ p) i))


-- Special cases

fiberIso→IsoOver :
  {ℓA ℓP ℓQ : Level}
  {A : Type ℓA}
  {P : A → Type ℓP}{Q : A → Type ℓQ}
  → ((a : A) → Iso (P a) (Q a))
  → IsoOver idIso P Q
fiberIso→IsoOver isom .fun a = isom a .fun
fiberIso→IsoOver isom .inv b = isom b .inv
fiberIso→IsoOver isom .rightInv b = isom b .rightInv
fiberIso→IsoOver isom .leftInv  a = isom a .leftInv

-- Only half-adjoint equivalence can be lifted.
-- This is another clue that HAE is more natural than isomorphism.

open isHAEquiv

pullbackIsoOver :
  {ℓA ℓB ℓP : Level}
  {A : Type ℓA}{B : Type ℓB}
  {P : B → Type ℓP}
  (f : A → B)
  (hae : isHAEquiv f)
  → IsoOver (isHAEquiv→Iso hae) (P ∘ f) P
pullbackIsoOver {A = A} {B} {P} f hae = w
  where
  isom = isHAEquiv→Iso hae

  w : IsoOver _ _ _
  w .fun a = idfun _
  w .inv b = subst P (sym (isom .rightInv b))
  w .rightInv b p i = subst-filler P (sym (isom .rightInv b)) p (~ i)
  w .leftInv  a p i =
    comp
    (λ j → P (hae .com a (~ j) i))
    (λ j → λ
      { (i = i0) → w .inv _ (w .fun _ p)
      ; (i = i1) → p })
    (w .rightInv _ p i)


-- Lifting isomorphism of bases to isomorphism of families

-- Since there is no regularity for transport (also no-eta-equality),
-- we have to fix one field manually to make it invariant under transportation.

liftHAEToIsoOver :
  (f : A → B)
  (hae : isHAEquiv f)
  → ((a : A) → Iso (P a) (Q (f a)))
  → IsoOver (isHAEquiv→Iso hae) P Q
liftHAEToIsoOver {P = P} {Q = Q} f hae isom =
  isIsoOver→IsoOver
    (transport (λ i → isIsoOver (compIsoIdL (isHAEquiv→Iso hae) i) P Q (λ a x → isom a .fun x))
    (IsoOver→isIsoOver (compIsoOver (fiberIso→IsoOver isom) (pullbackIsoOver f hae))))

equivOver→IsoOver :
  (e : A ≃ B)
  (f : mapOver (e .fst) P Q)
  → isEquivOver {P = P} {Q = Q} f
  → IsoOver (equivToIso e) P Q
equivOver→IsoOver {P = P} {Q = Q} e f equiv = w
  where
  isom = liftHAEToIsoOver _ (equiv→HAEquiv e .snd) (λ a → equivToIso (_ , equiv a))

  -- no-eta-equality for Iso, so we have to fill in fields manually
  w : IsoOver (equivToIso e) P Q
  w .fun = isom .fun
  w .inv = isom .inv
  w .rightInv = isom .rightInv
  w .leftInv  = isom .leftInv
