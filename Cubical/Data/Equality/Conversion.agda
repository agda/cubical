{- Conversion between paths and the inductively defined equality type

- Path and _≡_ are equal (Path≡Eq)

- conversion between dependent paths and PathP (pathOver→PathP and PathP→pathOver)

- cong-PathP→apd-pathOver for HIT β rules (see S¹ loop case)

-}

{-# OPTIONS --safe #-}
module Cubical.Data.Equality.Conversion where

open import Cubical.Foundations.Prelude
  hiding (_≡_ ; step-≡ ; _∎ ; isPropIsContr)
  renaming ( refl      to reflPath
           ; transport to transportPath
           ; J         to JPath
           ; JRefl     to JPathRefl
           ; sym       to symPath
           ; _∙_       to compPath
           ; cong      to congPath
           ; subst     to substPath
           ; substRefl to substPathReflPath
           ; funExt    to funExtPath
           ; isContr   to isContrPath
           ; isProp    to isPropPath
           )
open import Cubical.Foundations.Equiv
  renaming ( fiber     to fiberPath
           ; isEquiv   to isEquivPath
           ; _≃_       to EquivPath
           ; equivFun  to equivFunPath
           ; isPropIsEquiv to isPropIsEquivPath
           )
  hiding   ( equivCtr
           ; equivIsEquiv )
open import Cubical.Foundations.Isomorphism
  using ()
  renaming ( Iso to IsoPath
           ; iso to isoPath
           ; isoToPath to isoPathToPath
           ; isoToEquiv to isoPathToEquivPath
           )

open import Cubical.Data.Equality.Base

private
 variable
  a b ℓ ℓ' : Level
  A : Type a
  B : Type b
  x y z : A

--------------------------------------------------------------------------------
-- Paths

congPathd : {C : A → Type ℓ} (f : (x : A) → C x) {x y : A} (p : Path A x y) → Path (C y) (substPath C p (f x)) (f y)
congPathd f p = fromPathP (congPath f p)

-- Equality between Path and equality
eqToPath : {x y : A} → x ≡ y → Path A x y
eqToPath refl = reflPath

pathToEq : {x y : A} → Path A x y → x ≡ y
pathToEq {x = x} = JPath (λ y _ → x ≡ y) refl

pathToEq-reflPath : {x : A} → pathToEq reflPath ≡ refl {x = x}
pathToEq-reflPath {x = x} = pathToEq (JPathRefl (λ y _ → x ≡ y) refl)

eqToPath-pathToEq : {x y : A} → (p : Path A x y) → Path _ (eqToPath (pathToEq p)) p
eqToPath-pathToEq p =
  JPath (λ _ h → Path _ (eqToPath (pathToEq h)) h)
        (congPath eqToPath (transportRefl refl)) p

pathToEq-eqToPath : {x y : A} → (p : x ≡ y) → Path _ (pathToEq (eqToPath p)) p
pathToEq-eqToPath refl = transportRefl refl

PathIsoEq : {x y : A} → IsoPath (Path A x y) (x ≡ y)
PathIsoEq = isoPath pathToEq eqToPath pathToEq-eqToPath eqToPath-pathToEq

PathPathEq : {x y : A} → Path _ (Path A x y) (x ≡ y)
PathPathEq = isoPathToPath PathIsoEq

Path≡Eq : {x y : A} → (Path A x y) ≡ (x ≡ y)
Path≡Eq = pathToEq PathPathEq

happly : {B : A → Type ℓ} {f g : (x : A) → B x} → f ≡ g → (x : A) → f x ≡ g x
happly refl x = refl

-- We get funExt by going back and forth between Path and Eq
funExt : {B : A → Type ℓ} {f g : (x : A) → B x} → ((x : A) → f x ≡ g x) → f ≡ g
funExt p = pathToEq (λ i x → eqToPath (p x) i)

funExtRefl : {B : A → Type ℓ} {f : (x : A) → B x} → funExt (λ x → refl {x = f x}) ≡ refl
funExtRefl = pathToEq-reflPath

Σ≡Prop : {P : A → Type ℓ} → ((x : A) → isProp (P x)) →  {u v : Σ A P} → u .pr₁ ≡ v .pr₁ → u ≡ v
Σ≡Prop p {v = (x , y)} refl = ap (x ,_) (p x _ y)

-- Some lemmas relating the definitions for Path and ≡
substPath≡transport' : (C : A → Type ℓ) {x y : A} (b : C x) (p : x ≡ y) → substPath C (eqToPath p) b ≡ transport C p b
substPath≡transport' C b refl = pathToEq (transportRefl b)

substPath≡transport : (C : A → Type ℓ) {x y : A} (b : C x) (p : Path _ x y) → substPath C p b ≡ transport C (pathToEq p) b
substPath≡transport C b p = ap (λ x → substPath C x b) (pathToEq (symPath (eqToPath-pathToEq p)))
                          ∙ substPath≡transport' C b (pathToEq p)


congPath≡ap : {x y : A} → (f : A → B) (p : x ≡ y) → congPath f (eqToPath p) ≡ eqToPath (ap f p)
congPath≡ap f refl = refl

ap≡congPath : {x y : A} → (f : A → B) (p : Path A x y) → ap f (pathToEq p) ≡ pathToEq (congPath f p)
ap≡congPath {x = x} f p = JPath (λ _ q → ap f (pathToEq q) ≡ pathToEq (congPath f q)) rem p
  where
  rem : ap f (transp (λ i → x ≡ x) i0 refl) ≡ transp (λ i → f x ≡ f x) i0 refl
  rem = pathToEq (compPath (λ i → ap f (transportRefl refl i)) (symPath (transportRefl refl)))




-- Functions for going between the various definitions. This could
-- also be achieved by making lines in the universe and transporting
-- back and forth along them.

fiberPathToFiber : {f : A → B} {y : B} → fiberPath f y → fiber f y
fiberPathToFiber (x , p) = (x , pathToEq p)

fiberToFiberPath : {f : A → B} {y : B} → fiber f y → fiberPath f y
fiberToFiberPath (x , p) = (x , eqToPath p)

fiberToFiber : {f : A → B} {y : B} (p : fiber f y) → Path _ (fiberPathToFiber (fiberToFiberPath p)) p
fiberToFiber (x , p) i = x , pathToEq-eqToPath p i

fiberPathToFiberPath : {f : A → B} {y : B} (p : fiberPath f y) → Path _ (fiberToFiberPath (fiberPathToFiber p)) p
fiberPathToFiberPath (x , p) i = x , eqToPath-pathToEq p i

isContrPathToIsContr : isContrPath A → isContr A
isContrPathToIsContr (ctr , p) = (ctr , λ y → pathToEq (p y))

isContrToIsContrPath : isContr A → isContrPath A
isContrToIsContrPath (ctr , p) = (ctr , λ y → eqToPath (p y))

isPropPathToIsProp : isPropPath A → isProp A
isPropPathToIsProp H x y = pathToEq (H x y)

isPropToIsPropPath : isProp A → isPropPath A
isPropToIsPropPath H x y = eqToPath (H x y)

-- Specialized helper lemmas for going back and forth between
-- isContrPath and isContr:

private
  helper1 : {A B : Type ℓ} (f : A → B) (g : B → A) (h : ∀ y → Path _ (f (g y)) y)
          → isContrPath A → isContr B
  helper1 f g h (x , p) =
    (f x , λ y → pathToEq (λ i → hcomp (λ j → λ { (i = i0) → f x
                                                ; (i = i1) → h y j })
                                       (f (p (g y) i))))

  helper2 : {A B : Type ℓ} (f : A → B) (g : B → A) (h : ∀ y → Path _ (g (f y)) y)
          → isContr B → isContrPath A
  helper2 {A = A} f g h (x , p) = (g x , λ y → eqToPath (ap g (p (f y)) ∙ pathToEq (h y)))

-- This proof is essentially the one for proving that isContr with
-- Path is a proposition, but as we are working with ≡ we have to
-- insert a lot of conversion functions.
-- TODO: prove this directly following the HoTT proof?
isPropIsContr : (p1 p2 : isContr A) → Path (isContr A) p1 p2
isPropIsContr (a0 , p0) (a1 , p1) j =
  ( eqToPath (p0 a1) j ,
    hcomp (λ i → λ { (j = i0) →  λ x → pathToEq-eqToPath (p0 x) i
                   ; (j = i1) →  λ x → pathToEq-eqToPath (p1 x) i })
          (λ x → pathToEq (λ i → hcomp (λ k → λ { (i = i0) → eqToPath (p0 a1) j
                                                ; (i = i1) → eqToPath (p0 x) (j ∨ k)
                                                ; (j = i0) → eqToPath (p0 x) (i ∧ k)
                                                ; (j = i1) → eqToPath (p1 x) i })
                                       (eqToPath (p0 (eqToPath (p1 x) i)) j))))

-- We now prove that isEquiv is a proposition
isPropIsEquiv : {A B : Type ℓ} {f : A → B} (h1 h2 : isEquiv f) → Path _ h1 h2
equiv-proof (isPropIsEquiv h1 h2 i) y = isPropIsContr (h1 .equiv-proof y) (h2 .equiv-proof y) i

equivToEquivPath : A ≃ B → EquivPath A B
equivToEquivPath (f , p) =
  (f , λ { .equiv-proof y → helper2 fiberPathToFiber fiberToFiberPath fiberPathToFiberPath (p .equiv-proof y) })

-- Go from a Path equivalence to an ≡ equivalence
equivPathToEquiv : EquivPath A B → A ≃ B
equivPathToEquiv (f , p) =
  (f , λ { .equiv-proof y → helper1 fiberPathToFiber fiberToFiberPath fiberToFiber (p .equiv-proof y) })

equivToEquiv : {A B : Type ℓ} (p : A ≃ B) → Path _ (equivPathToEquiv (equivToEquivPath p)) p
equivToEquiv (f , p) i =
  (f , isPropIsEquiv (λ { .equiv-proof y → helper1 fiberPathToFiber fiberToFiberPath fiberToFiber
                                             (helper2 fiberPathToFiber fiberToFiberPath fiberPathToFiberPath (p .equiv-proof y)) }) p i)

equivPathToEquivPath : {A B : Type ℓ} (p : EquivPath A B) → Path _ (equivToEquivPath (equivPathToEquiv p)) p
equivPathToEquivPath (f , p) i =
  ( f , isPropIsEquivPath f (equivToEquivPath (equivPathToEquiv (f , p)) .snd) p i )

equivPath≡Equiv : {A B : Type ℓ} → Path _ (EquivPath A B) (A ≃ B)
equivPath≡Equiv {ℓ} = isoPathToPath (isoPath (equivPathToEquiv {ℓ}) equivToEquivPath equivToEquiv equivPathToEquivPath)

path≡Eq : {A B : Type ℓ} → Path _ (Path _ A B) (A ≡ B)
path≡Eq = isoPathToPath (isoPath pathToEq eqToPath pathToEq-eqToPath eqToPath-pathToEq)


--------------------------------------------------------------------------------
-- Isomorphisms

record Iso {ℓ ℓ'} (A : Type ℓ) (B : Type ℓ') : Type (ℓ-max ℓ ℓ') where
  no-eta-equality
  constructor iso
  pattern
  field
    fun : A → B
    inv : B → A
    rightInv : (b : B) → fun (inv b) ≡ b
    leftInv  : (a : A) → inv (fun a) ≡ a

isoToIsoPath : Iso A B → IsoPath A B
isoToIsoPath (iso f g η ε) = isoPath f g (λ b → eqToPath (η b)) (λ a → eqToPath (ε a))

isoToEquiv : Iso A B → A ≃ B
isoToEquiv f = equivPathToEquiv (isoPathToEquivPath (isoToIsoPath f))


--------------------------------------------------------------------------------
-- dependent paths and PathP

-- similar to https://www.cse.chalmers.se/~nad/listings/equality/Equality.Path.Isomorphisms.html
-- used for eliminators and β rules for HITs

transportPathToEq→transportPath : (P : A → Type ℓ) (p : Path A x y) (u : P x) → transport P (pathToEq p) u ≡ substPath P p u
transportPathToEq→transportPath {x = x} P = JPath (λ y p → (u : P x) → transport P (pathToEq p) u ≡ substPath P p u)
  λ u → ap (λ t → transport P t u) pathToEq-reflPath ∙ sym (pathToEq (substPathReflPath {B = P} u))

module _ (P : A → Type ℓ) {x y : A} {u : P x} {v : P y} where
  pathOver→PathP : (p : Path _ x y) → transport P (pathToEq p) u ≡ v → PathP (λ i → P (p i)) u v
  pathOver→PathP p q =
    JPath (λ y p → (v : P y) → transport P (pathToEq p) u ≡ v → PathP (λ i → P (p i)) u v)
      (λ v q → eqToPath (ap (λ r → transport P r u) (sym pathToEq-reflPath) ∙ q)) p v q

  PathP→pathOver : (p : Path _ x y) → PathP (λ i → P (p i)) u v → transport P (pathToEq p) u ≡ v
  PathP→pathOver p q = JPath (λ y p → (v : P y) (q : PathP (λ i → P (p i)) u v) → transport P (pathToEq p) u ≡ v)
    (λ v q → ap (λ t → transport P t u) pathToEq-reflPath ∙ pathToEq q) p _ q

module _ (P : A → Type ℓ) {x : A} {u v : P x} where
  pathOver→PathP-reflPath : (q : transport P (pathToEq reflPath) u ≡ v) →
    pathOver→PathP P reflPath q ≡ eqToPath (ap (λ t → transport P t u) (sym pathToEq-reflPath) ∙ q)
  pathOver→PathP-reflPath q = pathToEq λ i →
    JPathRefl (λ y p → (v : P y) → transport P (pathToEq p) u ≡ v → PathP (λ i → P (p i)) u v)
      (λ v q → eqToPath (ap (λ r → transport P r u) (sym pathToEq-reflPath) ∙ q)) i _ q

  PathP→pathOver-reflPath : (q : PathP (λ i → P x) u v) →
    PathP→pathOver P reflPath q ≡ ap (λ t → transport P t u) pathToEq-reflPath ∙ pathToEq q
  PathP→pathOver-reflPath q = pathToEq λ i →
    JPathRefl (λ y p → (v : P y) (q : PathP (λ i → P (p i)) u v) → transport P (pathToEq p) u ≡ v)
      (λ v q → ap (λ t → transport P t u) pathToEq-reflPath ∙ pathToEq q) i _ q

apd-pathToEq≡PathP→pathOver-cong : {P : A → Type ℓ} {x y : A} (f : (x : A) → P x) (p : Path _ x y) →
  apd f (pathToEq p) ≡ PathP→pathOver P p (congPath f p)
apd-pathToEq≡PathP→pathOver-cong {P = P} {x = x} f = JPath (λ _ p → apd f (pathToEq p) ≡ PathP→pathOver P p (congPath f p))
  let step1 = sym (apd (λ (p : x ≡ x) → apd f p) (sym pathToEq-reflPath))
      step2 = transport-path (λ p → transport P p (f x)) (λ _ → f x) (sym pathToEq-reflPath) refl
      step3 = ap (λ t → sym (ap (λ p → transport P p (f x)) (sym pathToEq-reflPath)) ∙ refl ∙ t)
        (ap-const {A = x ≡ x} (sym pathToEq-reflPath) (f x))
      step4 = ap (λ t → sym t ∙ refl) (sym (sym-ap (λ p → transport P p (f x)) pathToEq-reflPath))
      step5 = ap (_∙ refl) (sym-invol (ap (λ p → transport P p (f x)) pathToEq-reflPath))
      step6 = ap (ap (λ t → transport P t (f x)) pathToEq-reflPath ∙_) (sym pathToEq-reflPath)
      step7 = sym (PathP→pathOver-reflPath P reflPath)

  in  apd f (pathToEq reflPath)                                                                                              ≡⟨ step1 ⟩
      transport (λ p → transport P p (f x) ≡ f x) (sym pathToEq-reflPath) refl                                               ≡⟨ step2 ⟩
      sym (ap (λ p → transport P p (f x)) (sym pathToEq-reflPath)) ∙ refl ∙ ap (λ (_ : x ≡ x) → f x) (sym pathToEq-reflPath) ≡⟨ step3 ⟩
      sym (ap (λ p → transport P p (f x)) (sym pathToEq-reflPath)) ∙ refl                                                    ≡⟨ step4 ⟩
      sym (sym (ap (λ p → transport P p (f x)) pathToEq-reflPath)) ∙ refl                                                    ≡⟨ step5 ⟩
      ap (λ t → transport P t (f x)) pathToEq-reflPath ∙ refl                                                                ≡⟨ step6 ⟩
      ap (λ t → transport P t (f x)) pathToEq-reflPath ∙ pathToEq reflPath                                                   ≡⟨ step7 ⟩
      PathP→pathOver P reflPath reflPath ∎

module _ (P : A → Type ℓ) {x y : A} {u : P x} {v : P y} where
  -- TODO
  -- PathP→pathOver→PathP : (p : Path _ x y) (q : PathP (λ i → P (p i)) u v) → pathOver→PathP P p (PathP→pathOver P p q) ≡ q
  -- PathP→pathOver→PathP p q = {!!}

  pathOver→PathP→pathOver : (p : Path _ x y) (q : transport P (pathToEq p) u ≡ v) → PathP→pathOver P p (pathOver→PathP P p q) ≡ q
  pathOver→PathP→pathOver p q =
    JPath (λ y p → {v : P y} (q : transport P (pathToEq p) u ≡ v) → PathP→pathOver P p (pathOver→PathP P p q) ≡ q) (λ q →
      let step1 = ap (PathP→pathOver P reflPath) (pathOver→PathP-reflPath P q)
          step2 = PathP→pathOver-reflPath P (eqToPath (ap (λ t → transport P t u) (sym pathToEq-reflPath) ∙ q))
          step3 = ap (ap (λ t → transport P t u) pathToEq-reflPath ∙_)
            (pathToEq (pathToEq-eqToPath (ap (λ t → transport P t u) (sym pathToEq-reflPath) ∙ q)))
          step4 = sym (assoc (ap (λ t → transport P t u) pathToEq-reflPath) (ap (λ t → transport P t u) (sym pathToEq-reflPath)) q)
          step5 = ap (_∙ q) (sym (ap-∙ (λ t → transport P t u) pathToEq-reflPath (sym pathToEq-reflPath)))
          step6 = ap (λ t → ap (λ t → transport P t u) t ∙ q) (invR pathToEq-reflPath)

      in  PathP→pathOver P reflPath (pathOver→PathP P reflPath q)                                                                     ≡⟨ step1 ⟩
          PathP→pathOver P reflPath (eqToPath (ap (λ t → transport P t u) (sym pathToEq-reflPath) ∙ q))                               ≡⟨ step2 ⟩
          ap (λ t → transport P t u) pathToEq-reflPath ∙ pathToEq (eqToPath (ap (λ t → transport P t u) (sym pathToEq-reflPath) ∙ q)) ≡⟨ step3 ⟩
          ap (λ t → transport P t u) pathToEq-reflPath ∙ ap (λ t → transport P t u) (sym pathToEq-reflPath) ∙ q                       ≡⟨ step4 ⟩
          (ap (λ t → transport P t u) pathToEq-reflPath ∙ ap (λ t → transport P t u) (sym pathToEq-reflPath)) ∙ q                     ≡⟨ step5 ⟩
          ap (λ t → transport P t u) (pathToEq-reflPath ∙ sym pathToEq-reflPath) ∙ q                                                  ≡⟨ step6 ⟩
          q ∎) p q


cong-PathP→apd-pathOver : (P : A → Type ℓ) {x y : A} (f : (x : A) → P x)
  → (p : Path _ x y) (q : transport P (pathToEq p) (f x) ≡ f y)
  → congPath f p ≡ pathOver→PathP P p q → apd f (pathToEq p) ≡ q
cong-PathP→apd-pathOver {A = A} P {x = x} f p q r =
  apd f (pathToEq p)                        ≡⟨ apd-pathToEq≡PathP→pathOver-cong f p ⟩
  PathP→pathOver P p (congPath f p)         ≡⟨ ap (PathP→pathOver P p) r ⟩
  PathP→pathOver P p (pathOver→PathP P p q) ≡⟨ pathOver→PathP→pathOver P p q ⟩
  q ∎
