{-

This file contains:

- Id, refl and J (with definitional computation rule)

- Basic theory about Id, proved using J

- Lemmas for going back and forth between Path and Id

- Function extensionality for Id

- fiber, isContr, equiv all defined using Id

- The univalence axiom expressed using only Id ([EquivContr])

- Propositional truncation and its elimination principle

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.Core.Id where

open import Agda.Builtin.Cubical.Id public
  renaming ( conid to ⟨_,_⟩
           -- TODO: should the user really be able to access these two?
           ; primIdFace to faceId  -- ∀ {ℓ} {A : Set ℓ} {x y : A} → Id x y → I
           ; primIdPath to pathId  -- ∀ {ℓ} {A : Set ℓ} {x y : A} → Id x y → Path A x y

           ; primIdElim to elimId  -- ∀ {ℓ ℓ'} {A : Set ℓ} {x : A}
                                   -- (P : ∀ (y : A) → x ≡ y → Set ℓ')
                                   -- (h : ∀ (φ : I) (y : A [ φ ↦ (λ _ → x) ])
                                   --        (w : (Path _ x (ouc y)) [ φ ↦ (λ { (φ = i1) → λ _ → x}) ] ) →
                                   --        P (ouc y) ⟨ φ , ouc w ⟩) →
                                   -- {y : A} (w' : x ≡ y) → P y w'
           )
  hiding ( primIdJ ) -- this should not be used as it is using compCCHM
open import Cubical.Core.Primitives public  hiding ( _≡_ )
open import Cubical.Core.Prelude public
  hiding ( _≡_ ; _≡⟨_⟩_ ; _∎ )
  renaming ( refl      to reflPath
           ; transport to transportPath
           ; J         to JPath
           ; JRefl     to JPathRefl
           ; sym       to symPath
           ; _∙_       to compPath
           ; cong      to congPath
           ; funExt    to funExtPath
           ; isContr   to isContrPath
           ; isProp    to isPropPath
           ; isSet     to isSetPath
           ; fst       to pr₁ -- as in the HoTT book
           ; snd       to pr₂
           )
open import Cubical.Core.Glue
  renaming ( fiber        to fiberPath
           ; isEquiv      to isEquivPath
           ; _≃_         to EquivPath
           ; equivFun     to equivFunPath
           ; equivIsEquiv to equivIsEquivPath
           ; equivCtr     to equivCtrPath
           ; EquivContr   to EquivContrPath )
open import Cubical.Core.PropositionalTruncation public
  renaming ( squash to squashPath
           ; recPropTrunc to recPropTruncPath
           ; elimPropTrunc to elimPropTruncPath )

{- BUILTIN ID Id -}
_≡_ : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
_≡_ = Id

private
  variable
    ℓ ℓ' : Level
    A : Set ℓ

-- Version of the constructor for Id where the y is also
-- explicit. This is sometimes useful when it is needed for
-- typechecking (see JId below).
conId : ∀ {x : A} φ (y : A [ φ ↦ (λ _ → x) ])
          (w : (Path _ x (ouc y)) [ φ ↦ (λ { (φ = i1) → λ _ → x}) ]) →
          x ≡ ouc y
conId φ _ w = ⟨ φ , ouc w ⟩

-- Reflexivity
refl : ∀ {x : A} → x ≡ x
refl {x = x} = ⟨ i1 , (λ _ → x) ⟩


-- Definition of J for Id
module _ {x : A} (P : ∀ (y : A) → Id x y → Set ℓ') (d : P x refl) where
  J : ∀ {y : A} (w : x ≡ y) → P y w
  J {y = y} = elimId P (λ φ y w → comp (λ i → P _ (conId (φ ∨ ~ i) (inc (ouc w i))
                                                                   (inc (λ j → ouc w (i ∧ j)))))
                                       (λ i → λ { (φ = i1) → d}) (inc d)) {y = y}

  -- Check that J of refl is the identity function
  Jdefeq : Path _ (J refl) d
  Jdefeq _ = d


-- Basic theory about Id, proved using J
transport : ∀ (B : A → Set ℓ') {x y : A}
           → x ≡ y → B x → B y
transport B {x} p b = J (λ y p → B y) b p

_⁻¹ : {x y : A} → x ≡ y → y ≡ x
_⁻¹ {x = x} p = J (λ z _ → z ≡ x) refl p

ap : ∀ {B : Set ℓ'} (f : A → B) → ∀ {x y : A} → x ≡ y → f x ≡ f y
ap f {x} = J (λ z _ → f x ≡ f z) refl

_∙_ : ∀ {x y z : A} → x ≡ y → y ≡ z → x ≡ z
_∙_ {x = x} p = J (λ y _ → x ≡ y) p

infix  4 _∙_
infix  3 _∎
infixr 2 _≡⟨_⟩_

_≡⟨_⟩_ : (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ p ⟩ q = p ∙ q

_∎ : (x : A) → x ≡ x
_ ∎ = refl

-- Convert between Path and Id
pathToId : ∀ {x y : A} → Path _ x y → Id x y
pathToId {x = x} = JPath (λ y _ → Id x y) refl

pathToIdRefl : ∀ {x : A} → Path _ (pathToId (λ _ → x)) refl
pathToIdRefl {x = x} = JPathRefl (λ y _ → Id x y) refl

idToPath : ∀ {x y : A} → Id x y → Path _ x y
idToPath {x = x} = J (λ y _ → Path _ x y) (λ _ → x)

idToPathRefl : ∀ {x : A} → Path _ (idToPath {x = x} refl) reflPath
idToPathRefl {x = x} _ _ = x

pathToIdToPath : ∀ {x y : A} → (p : Path _ x y) → Path _ (idToPath (pathToId p)) p
pathToIdToPath {x = x} = JPath (λ y p → Path _ (idToPath (pathToId p)) p)
                               (λ i → idToPath (pathToIdRefl i))

idToPathToId : ∀ {x y : A} → (p : Id x y) → Path _ (pathToId (idToPath p)) p
idToPathToId {x = x} = J (λ b p → Path _ (pathToId (idToPath p)) p) pathToIdRefl


-- We get function extensionality by going back and forth between Path and Id
funExt : ∀ {B : A → Set ℓ'} {f g : (x : A) → B x} →
         ((x : A) → f x ≡ g x) → f ≡ g
funExt p = pathToId (λ i x → idToPath (p x) i)


-- Equivalences expressed using Id

fiber : ∀ {A : Set ℓ} {B : Set ℓ'} (f : A → B) (y : B) → Set (ℓ-max ℓ ℓ')
fiber {A = A} f y = Σ[ x ∈ A ] f x ≡ y

isContr : Set ℓ → Set ℓ
isContr A = Σ[ x ∈ A ] (∀ y → x ≡ y)

isProp : Set ℓ → Set ℓ
isProp A = (x y : A) → x ≡ y

isSet : Set ℓ → Set ℓ
isSet A = (x y : A) → isProp (x ≡ y)

record isEquiv {A : Set ℓ} {B : Set ℓ'} (f : A → B) : Set (ℓ-max ℓ ℓ') where
  field
    equiv-proof : (y : B) → isContr (fiber f y)

open isEquiv public

infix 4 _≃_

_≃_ : ∀ (A : Set ℓ) (B : Set ℓ') → Set (ℓ-max ℓ ℓ')
A ≃ B = Σ[ f ∈ (A → B) ] (isEquiv f)

equivFun : ∀ {B : Set ℓ'} → A ≃ B → A → B
equivFun e = pr₁ e

equivIsEquiv : ∀ {B : Set ℓ'} (e : A ≃ B) → isEquiv (equivFun e)
equivIsEquiv e = pr₂ e

equivCtr : ∀ {B : Set ℓ'} (e : A ≃ B) (y : B) → fiber (equivFun e) y
equivCtr e y = e .pr₂ .equiv-proof y .pr₁


-- Functions for going between the various definitions. This could
-- also be achieved by making lines in the universe and transporting
-- back and forth along them.

fiberPathToFiber : ∀ {B : Set ℓ'} {f : A → B} {y : B} →
  fiberPath f y → fiber f y
fiberPathToFiber (x , p) = (x , pathToId p)

fiberToFiberPath : ∀ {B : Set ℓ'} {f : A → B} {y : B} →
  fiber f y → fiberPath f y
fiberToFiberPath (x , p) = (x , idToPath p)

fiberToFiber : ∀ {B : Set ℓ'} {f : A → B} {y : B}
  (p : fiber f y) → Path _ (fiberPathToFiber (fiberToFiberPath p)) p
fiberToFiber (x , p) = λ i → x , idToPathToId p i

fiberPathToFiberPath : ∀ {B : Set ℓ'} {f : A → B} {y : B}
  (p : fiberPath f y) → Path _ (fiberToFiberPath (fiberPathToFiber p)) p
fiberPathToFiberPath (x , p) = λ i → x , pathToIdToPath p i

isContrPathToIsContr : isContrPath A → isContr A
isContrPathToIsContr (ctr , p) = (ctr , λ y → pathToId (p y))

isContrToIsContrPath : isContr A → isContrPath A
isContrToIsContrPath (ctr , p) = (ctr , λ y → idToPath (p y))

isPropPathToIsProp : isPropPath A → isProp A
isPropPathToIsProp H x y = pathToId (H x y)

isPropToIsPropPath : isProp A → isPropPath A
isPropToIsPropPath H x y i = idToPath (H x y) i

-- Specialized helper lemmas for going back and forth between
-- isContrPath and isContr:

helper1 : ∀ {A B : Set ℓ} (f : A → B) (g : B → A)
            (h : ∀ y → Path _ (f (g y)) y) → isContrPath A → isContr B
helper1 f g h (x , p) =
  (f x , λ y → pathToId (λ i → hcomp (λ j → λ { (i = i0) → f x
                                              ; (i = i1) → h y j })
                                     (f (p (g y) i))))

helper2 : ∀ {A B : Set ℓ} (f : A → B) (g : B → A)
            (h : ∀ y → Path _ (g (f y)) y) → isContr B → isContrPath A
helper2 {A = A} f g h (x , p) = (g x , λ y → idToPath (rem y))
  where
  rem : ∀ (y : A) → g x ≡ y
  rem y =
    g x     ≡⟨ ap g (p (f y)) ⟩
    g (f y) ≡⟨ pathToId (h y) ⟩
    y       ∎

-- This proof is essentially the one for proving that isContr with
-- Path is a proposition, but as we are working with Id we have to
-- insert a lof of conversion functions. It is still nice that is
-- works like this though.
isPropIsContr : ∀ (p1 p2 : isContr A) → Path (isContr A) p1 p2
isPropIsContr (a0 , p0) (a1 , p1) j =
  ( idToPath (p0 a1) j ,
    hcomp (λ i → λ { (j = i0) →  λ x → idToPathToId (p0 x) i
                   ; (j = i1) →  λ x → idToPathToId (p1 x) i })
          (λ x → pathToId (λ i → hcomp (λ k → λ { (i = i0) → idToPath (p0 a1) j
                                                ; (i = i1) → idToPath (p0 x) (j ∨ k)
                                                ; (j = i0) → idToPath (p0 x) (i ∧ k)
                                                ; (j = i1) → idToPath (p1 x) i })
                                       (idToPath (p0 (idToPath (p1 x) i)) j))))


-- We now prove that isEquiv is a proposition
isPropIsEquiv : ∀ {A : Set ℓ} {B : Set ℓ} → {f : A → B} → (h1 h2 : isEquiv f) → Path _ h1 h2
equiv-proof (isPropIsEquiv {f = f} h1 h2 i) y =
  isPropIsContr {A = fiber f y} (h1 .equiv-proof y) (h2 .equiv-proof y) i

-- Go from a Path equivalence to an Id equivalence
equivPathToEquiv : ∀ {A : Set ℓ} {B : Set ℓ'} → EquivPath A B → A ≃ B
equivPathToEquiv (f , p) =
  (f , λ { .equiv-proof y → helper1 fiberPathToFiber fiberToFiberPath fiberToFiber (p .equiv-proof y) })

-- Go from an Id equivalence to a Path equivalence
equivToEquivPath : ∀ {A : Set ℓ} {B : Set ℓ'} → A ≃ B → EquivPath A B
equivToEquivPath (f , p) =
  (f , λ { .equiv-proof y → helper2 fiberPathToFiber fiberToFiberPath fiberPathToFiberPath (p .equiv-proof y) })

equivToEquiv : ∀ {A : Set ℓ} {B : Set ℓ} → (p : A ≃ B) → Path _ (equivPathToEquiv (equivToEquivPath p)) p
equivToEquiv (f , p) i =
  (f , isPropIsEquiv (λ { .equiv-proof y → helper1 fiberPathToFiber fiberToFiberPath fiberToFiber
                                             (helper2 fiberPathToFiber fiberToFiberPath fiberPathToFiberPath (p .equiv-proof y)) }) p i)


-- We can finally prove univalence with Id everywhere from the one for Path
EquivContr : ∀ (A : Set ℓ) → isContr (Σ[ T ∈ Set ℓ ] (T ≃ A))
EquivContr A = helper1 f1 f2 f12 (EquivContrPath A)
  where
  f1 : ∀ {ℓ} {A : Set ℓ} → Σ[ T ∈ Set ℓ ] (EquivPath T A) → Σ[ T ∈ Set ℓ ] (T ≃ A)
  f1 (x , p) = x , equivPathToEquiv p

  f2 : ∀ {ℓ} {A : Set ℓ} → Σ[ T ∈ Set ℓ ] (T ≃ A) → Σ[ T ∈ Set ℓ ] (EquivPath T A)
  f2 (x , p) = x , equivToEquivPath p

  f12 : ∀ {ℓ} {A : Set ℓ} → (y : Σ[ T ∈ Set ℓ ] (T ≃ A)) → Path _ (f1 (f2 y)) y
  f12 (x , p) = λ i → x , equivToEquiv p i


-- Propositional truncation

∥∥-isProp : ∀ (x y : ∥ A ∥) → x ≡ y
∥∥-isProp x y = pathToId (squashPath x y)

∥∥-recursion : ∀ {A : Set ℓ} {P : Set ℓ} → isProp P → (A → P) → ∥ A ∥ → P
∥∥-recursion Pprop f x = recPropTruncPath (isPropToIsPropPath Pprop) f x

∥∥-induction : ∀ {A : Set ℓ} {P : ∥ A ∥ → Set ℓ} → ((a : ∥ A ∥) → isProp (P a)) →
                ((x : A) → P ∣ x ∣) → (a : ∥ A ∥) → P a
∥∥-induction Pprop f x = elimPropTruncPath (λ a → isPropToIsPropPath (Pprop a)) f x
