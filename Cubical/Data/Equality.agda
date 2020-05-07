{-

This module converts between the path equality
and the inductively define equality types.

-}
{-# OPTIONS --cubical --safe #-}

module Cubical.Data.Equality where

open import Cubical.Foundations.Prelude public
  hiding ( _≡_ ; _≡⟨_⟩_ ; _∎ ; isPropIsContr)
  renaming ( refl      to reflPath
           ; transport to transportPath
           ; J         to JPath
           ; JRefl     to JPathRefl
           ; sym       to symPath
           ; _∙_       to compPath
           ; cong      to congPath
           ; funExt    to funExtPath
           ; isContr   to isContrPath
           ; isProp    to isPropPath )
open import Cubical.Foundations.Equiv
  renaming ( fiber     to fiberPath
           ; isEquiv   to isEquivPath
           ; _≃_       to EquivPath
           ; equivFun  to equivFunPath
           ; isPropIsEquiv to isPropIsEquivPath )
  hiding   ( equivCtr
           ; equivIsEquiv )
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence hiding (univalence)


open import Agda.Builtin.Equality public

private
 variable
  ℓ ℓ' : Level
  A : Set ℓ
  x y z : A

cong : ∀ {B : Type ℓ'} (f : A → B) → ∀ {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

_∙_ : x ≡ y → y ≡ z → x ≡ z
refl ∙ q = q

infix  3 _∎
infixr 2 _≡⟨_⟩_

_≡⟨_⟩_ : (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ p ⟩ q = p ∙ q

_∎ : (x : A) → x ≡ x
_ ∎ = refl

transport : ∀ (C : A → Type ℓ') {x y : A} → x ≡ y → C x → C y
transport C refl b = b


eqToPath : x ≡ y → Path A x y
eqToPath refl = reflPath

pathToEq : Path A x y → x ≡ y
pathToEq p = transportPath (congPath (λ u → _ ≡ u) p) refl

eqToPath-pathToEq : (p : Path A x y) → Path _ (eqToPath (pathToEq p)) p
eqToPath-pathToEq p =
  JPath (λ _ h → Path _ (eqToPath (pathToEq h)) h)
        (congPath eqToPath (transportRefl refl)) p

pathToEq-eqToPath : (p : x ≡ y) → Path _ (pathToEq (eqToPath p)) p
pathToEq-eqToPath refl = transportRefl refl

PathIsoEq : {x y : A} → Iso (Path A x y) (x ≡ y)
PathIsoEq = iso pathToEq eqToPath pathToEq-eqToPath eqToPath-pathToEq

PathPathEq : {x y : A} → Path _ (Path A x y) (x ≡ y)
PathPathEq = isoToPath PathIsoEq

Path≡Eq : {x y : A} → (Path A x y) ≡ (x ≡ y)
Path≡Eq = pathToEq PathPathEq

-- We get funext by going back and forth between Path and Eq
funExt : {B : A → Type ℓ} {f g : (x : A) → B x} →
         ((x : A) → f x ≡ g x) → f ≡ g
funExt p = pathToEq (λ i x → eqToPath (p x) i)

-- Equivalences expressed using Id

fiber : ∀ {A : Type ℓ} {B : Type ℓ'} (f : A → B) (y : B) → Type (ℓ-max ℓ ℓ')
fiber {A = A} f y = Σ[ x ∈ A ] f x ≡ y

isContr : Type ℓ → Type ℓ
isContr A = Σ[ x ∈ A ] (∀ y → x ≡ y)

isProp : Type ℓ → Type ℓ
isProp A = (x y : A) → x ≡ y

record isEquiv {A : Type ℓ} {B : Type ℓ'} (f : A → B) : Type (ℓ-max ℓ ℓ') where
  field
    equiv-proof : (y : B) → isContr (fiber f y)

open isEquiv public

infix 4 _≃_

_≃_ : ∀ (A : Type ℓ) (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
A ≃ B = Σ[ f ∈ (A → B) ] (isEquiv f)

equivFun : ∀ {B : Type ℓ'} → A ≃ B → A → B
equivFun e = e .fst

equivIsEquiv : ∀ {B : Type ℓ'} (e : A ≃ B) → isEquiv (equivFun e)
equivIsEquiv e = e .snd

equivCtr : ∀ {B : Type ℓ'} (e : A ≃ B) (y : B) → fiber (equivFun e) y
equivCtr e y = e .snd .equiv-proof y .fst


-- Functions for going between the various definitions. This could
-- also be achieved by making lines in the universe and transporting
-- back and forth along them.

fiberPathToFiber : {B : Type ℓ'} {f : A → B} {y : B} → fiberPath f y → fiber f y
fiberPathToFiber (x , p) = (x , pathToEq p)

fiberToFiberPath : {B : Type ℓ'} {f : A → B} {y : B} → fiber f y → fiberPath f y
fiberToFiberPath (x , p) = (x , eqToPath p)

fiberToFiber : {B : Type ℓ'} {f : A → B} {y : B} (p : fiber f y)
             → Path _ (fiberPathToFiber (fiberToFiberPath p)) p
fiberToFiber (x , p) i = x , pathToEq-eqToPath p i

fiberPathToFiberPath : {B : Type ℓ'} {f : A → B} {y : B} (p : fiberPath f y)
                     → Path _ (fiberToFiberPath (fiberPathToFiber p)) p
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

helper1 : {A B : Type ℓ} (f : A → B) (g : B → A) (h : ∀ y → Path _ (f (g y)) y)
        → isContrPath A → isContr B
helper1 f g h (x , p) =
  (f x , λ y → pathToEq (λ i → hcomp (λ j → λ { (i = i0) → f x
                                              ; (i = i1) → h y j })
                                     (f (p (g y) i))))

helper2 : {A B : Type ℓ} (f : A → B) (g : B → A) (h : ∀ y → Path _ (g (f y)) y)
        → isContr B → isContrPath A
helper2 {A = A} f g h (x , p) = (g x , λ y → eqToPath (cong g (p (f y)) ∙ pathToEq (h y)))

-- This proof is essentially the one for proving that isContr with
-- Path is a proposition, but as we are working with Eq we have to
-- insert a lof of conversion functions.
-- TODO: prove this directly?
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

equivToEquivPath : ∀ {A : Type ℓ} {B : Type ℓ'} → A ≃ B → EquivPath A B
equivToEquivPath (f , p) =
  (f , λ { .equiv-proof y → helper2 fiberPathToFiber fiberToFiberPath fiberPathToFiberPath (p .equiv-proof y) })

-- Go from a Path equivalence to an Id equivalence
equivPathToEquiv : {A : Type ℓ} {B : Type ℓ'} → EquivPath A B → A ≃ B
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
equivPath≡Equiv {ℓ} = isoToPath (iso (equivPathToEquiv {ℓ}) equivToEquivPath equivToEquiv equivPathToEquivPath)

path≡Eq : {A B : Type ℓ} → Path _ (Path _ A B) (A ≡ B)
path≡Eq = isoToPath (iso pathToEq eqToPath pathToEq-eqToPath eqToPath-pathToEq)

univalenceEq : {A B : Type ℓ} → (A ≡ B) ≃ (A ≃ B)
univalenceEq {A = A} {B = B} = equivPathToEquiv rem
  where
  rem0 : Path _ (Lift (EquivPath A B)) (Lift (A ≃ B))
  rem0 = congPath Lift equivPath≡Equiv

  rem1 : Path _ (A ≡ B) (Lift (A ≃ B))
  rem1 i = hcomp (λ j → λ { (i = i0) → path≡Eq {A = A} {B = B} j
                          ; (i = i1) → rem0 j })
                 (univalencePath {A = A} {B = B} i)

  rem : EquivPath (A ≡ B) (A ≃ B)
  rem = compEquiv (eqweqmap rem1) (invEquiv LiftEquiv)



-- Propositional truncation:

open import Cubical.HITs.PropositionalTruncation public
  renaming ( squash to squashPath
           ; rec to recPropTruncPath
           ; elim to elimPropTruncPath )

∥∥-isProp : ∀ (x y : ∥ A ∥) → x ≡ y
∥∥-isProp x y = pathToEq (squashPath x y)

∥∥-recursion : ∀ {A : Type ℓ} {P : Type ℓ} → isProp P → (A → P) → ∥ A ∥ → P
∥∥-recursion Pprop = recPropTruncPath (isPropToIsPropPath Pprop)

∥∥-induction : ∀ {A : Type ℓ} {P : ∥ A ∥ → Type ℓ} → ((a : ∥ A ∥) → isProp (P a)) →
                ((x : A) → P ∣ x ∣) → (a : ∥ A ∥) → P a
∥∥-induction Pprop = elimPropTruncPath (λ a → isPropToIsPropPath (Pprop a))


-- Circle

open import Cubical.HITs.S1 as S1
  renaming (loop to loopPath )


loop : base ≡ base
loop = pathToEq loopPath

S¹-rec : (b : A) (l : b ≡ b) → S¹ → A
S¹-rec b l = S1.rec b (eqToPath l)

foo : (C : A → Type ℓ) {x y : A} (b : C x) (p : Path _ x y) → subst C p b ≡ transport C (pathToEq p) b
foo C {x} b p = JPath (λ _ q → subst C q b ≡ transport C (pathToEq q) b) rem p
  where
  rem : transp (λ i → C x) i0 b ≡ transport C (transp (λ i → x ≡ x) i0 refl) b
  rem = transp (λ i → C x) i0 b ≡⟨ pathToEq (transportRefl b) ⟩
        b ≡⟨ refl ⟩
        transport C refl b ≡⟨ cong (λ x → transport C x b) (pathToEq (symPath (transportRefl refl))) ⟩
        transport C (transp (λ i → x ≡ x) i0 refl) b ∎

S¹-elim : (C : S¹ → Type ℓ) (b : C base) (l : transport C loop b ≡ b) → (x : S¹) → C x
S¹-elim C b l x = S1.ind C b (eqToPath (suff ∙ l)) x
  where
  suff : subst C loopPath b ≡ transport C (pathToEq loopPath) b
  suff = foo C b loopPath
