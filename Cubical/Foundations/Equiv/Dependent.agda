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
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport

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

isPropIsEquivOver :
  {f : A → B}
  (F : mapOver f P Q)
  → isProp (isEquivOver {Q = Q} F)
isPropIsEquivOver F = isPropΠ (λ a → isPropIsEquiv (F a))

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

invIsoOver : {isom : Iso A B} → IsoOver isom P Q → IsoOver (invIso isom) Q P
invIsoOver {isom = isom} isom' .fun = isom' .inv
invIsoOver {isom = isom} isom' .inv = isom' .fun
invIsoOver {isom = isom} isom' .rightInv = isom' .leftInv
invIsoOver {isom = isom} isom' .leftInv = isom' .rightInv

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

open isHAEquiv renaming (g to inv)

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


-- Turn isomorphism over HAE into relative equivalence,
-- i.e. the inverse of the previous precedure.

isoToEquivOver :
  {A : Type ℓ } {P : A → Type ℓ'' }
  {B : Type ℓ'} {Q : B → Type ℓ'''}
  (f : A → B) (hae : isHAEquiv f)
  (isom' : IsoOver (isHAEquiv→Iso hae) P Q)
  → isEquivOver {Q = Q} (isom' .fun)
isoToEquivOver {A = A} {P} {Q = Q} f hae isom' a = isoToEquiv (fibiso a) .snd
  where
  isom = isHAEquiv→Iso hae
  finv = isom .inv

  fibiso : (a : A) → Iso (P a) (Q (f a))
  fibiso a .fun = isom' .fun a
  fibiso a .inv x = transport (λ i → P (isom .leftInv a i)) (isom' .inv (f a) x)
  fibiso a .leftInv  x = fromPathP (isom' .leftInv _ _)
  fibiso a .rightInv x =
    sym (substCommSlice _ _ (isom' .fun) _ _)
    ∙ cong (λ p → subst Q p (isom' .fun _ (isom' .inv _ x))) (hae .com a)
    ∙ fromPathP (isom' .rightInv _ _)


-- Half-adjoint equivalence over half-adjoint equivalence

record isHAEquivOver {ℓ ℓ'} {A : Type ℓ}{B : Type ℓ'}
  (hae : HAEquiv A B)(P : A → Type ℓ'')(Q : B → Type ℓ''')
  (fun : mapOver (hae .fst) P Q)
  : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓ'' ℓ''')) where
  field
    inv  : mapOver (hae .snd .inv) Q P
    rinv : sectionOver (hae .snd .rinv) fun inv
    linv : retractOver (hae .snd .linv) fun inv
    com  : ∀ {a} b → SquareP (λ i j → Q (hae .snd .com a i j))
      (λ i → fun _ (linv _ b i)) (rinv _ (fun _ b))
      (refl {x = fun _ (inv _ (fun a b))}) (refl {x = fun a b})

open isHAEquivOver

HAEquivOver : (P : A → Type ℓ'')(Q : B → Type ℓ''')(hae : HAEquiv A B) → Type _
HAEquivOver P Q hae = Σ[ f ∈ mapOver (hae .fst) P Q ] isHAEquivOver hae P Q f


-- forget the coherence square to get an dependent isomorphism

isHAEquivOver→isIsoOver :
  {hae : HAEquiv A B} (hae' : HAEquivOver P Q hae)
  → IsoOver (isHAEquiv→Iso (hae .snd)) P Q
isHAEquivOver→isIsoOver hae' .fun = hae' .fst
isHAEquivOver→isIsoOver hae' .inv = hae' .snd .inv
isHAEquivOver→isIsoOver hae' .leftInv  = hae' .snd .linv
isHAEquivOver→isIsoOver hae' .rightInv = hae' .snd .rinv


-- A dependent version of `isoToHAEquiv`

IsoOver→HAEquivOver :
  {isom : Iso A B}
  → (isom' : IsoOver isom P Q)
  → isHAEquivOver (iso→HAEquiv isom) P Q (isom' .fun)
IsoOver→HAEquivOver {A = A} {P = P} {Q = Q} {isom = isom} isom' = w
  where
  f = isom .fun
  g = isom .inv
  ε = isom .rightInv
  η = isom .leftInv

  f' = isom' .fun
  g' = isom' .inv
  ε' = isom' .rightInv
  η' = isom' .leftInv

  sq : _ → I → I → _
  sq b i j =
    hfill (λ j → λ
      { (i = i0) → ε (f (g b)) j
      ; (i = i1) → ε b j })
    (inS (f (η (g b) i))) j

  Hfa≡fHa : (f : A → A) (H : ∀ a → f a ≡ a) → ∀ a → H (f a) ≡ cong f (H a)
  Hfa≡fHa f H =
    J (λ f p → ∀ a → funExt⁻ (sym p) (f a) ≡ cong f (funExt⁻ (sym p) a))
      (λ a → refl) (sym (funExt H))

  Hfa≡fHaRefl : Hfa≡fHa (idfun _) (λ _ → refl) ≡ λ _ → refl
  Hfa≡fHaRefl =
    JRefl {x = idfun _}
      (λ f p → ∀ a → funExt⁻ (sym p) (f a) ≡ cong f (funExt⁻ (sym p) a))
      (λ a → refl)

  Hfa≡fHaOver : (f : A → A) (H : ∀ a → f a ≡ a)
    (f' : mapOver f P P) (H' : ∀ a b → PathP (λ i → P (H a i)) (f' _ b) b)
    → ∀ a b → SquareP (λ i j →
      P (Hfa≡fHa f H a i j)) (H' _ (f' _ b)) (λ i → f' _ (H' _ b i)) refl refl
  Hfa≡fHaOver f H f' H' =
   JDep {B = λ f → mapOver f P P}
    (λ f p f' p' → ∀ a b
      → SquareP (λ i j → P (Hfa≡fHa f (funExt⁻ (sym p)) a i j))
          (λ i → p' (~ i) _ (f' _ b)) (λ i → f' _ (p' (~ i) _ b))
          (refl {x = f' _ (f' _ b)}) (refl {x = f' _ b}))
    (λ a b →
      transport (λ t → SquareP (λ i j → P (Hfa≡fHaRefl (~ t) a i j))
        (refl {x = b}) refl refl refl) refl)
    (sym (funExt H)) (λ i a b → H' a b (~ i))

  cube : _ → I → I → I → _
  cube a i j k =
    hfill (λ k → λ
      { (i = i0) → ε (f (η a j)) k
      ; (j = i0) → ε (f (g (f a))) k
      ; (j = i1) → ε (f a) k})
    (inS (f (Hfa≡fHa (λ x → g (f x)) η a (~ i) j))) k

  w : isHAEquivOver _ _ _ _
  w .inv  = isom' .inv
  w .linv = isom' .leftInv
  w .rinv b x i =
    comp (λ j → Q (sq b i j))
    (λ j → λ
      { (i = i0) → ε' _ (f' _ (g' _ x)) j
      ; (i = i1) → ε' _ x j })
    (f' _ (η' _ (g' _ x) i))
  w. com {a} b i j =
    comp (λ k → Q (cube a i j k))
    (λ k → λ
      { (i = i0) → ε' _ (f' _ (η' _ b j)) k
      ; (j = i0) → ε' _ (f' _ (g' _ (f' _ b))) k
      ; (j = i1) → ε' _ (f' _ b) k})
    (f' _ (Hfa≡fHaOver _ η _ η' a b (~ i) j))


-- transform an isomorphism over some isomorphism to an isomorphism over its half-adjoint-ization

IsoOverIso→IsoOverHAEquiv :
  {isom : Iso A B} (isom' : IsoOver isom P Q)
  → IsoOver (isHAEquiv→Iso (iso→HAEquiv isom .snd)) P Q
IsoOverIso→IsoOverHAEquiv isom' =
  isHAEquivOver→isIsoOver (_ , IsoOver→HAEquivOver isom')
