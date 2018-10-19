{-

This file contains:

- Id, refl and J (with definitional computation rule)

- Basic theory about Id, proved using J

- Lemmas for going back and forth between Path and Id

- Function extensionality for Id


It should *not* depend on the Agda standard library.

 -}

{-# OPTIONS --cubical #-}
module Cubical.Id where

open import Agda.Builtin.Cubical.Id public
  renaming ( conid to ⟨_,_⟩
           -- TODO: should the user really be able to access these two?
           ; primIdFace to faceId  -- ∀ {ℓ} {A : Set ℓ} {x y : A} → Id x y → I
           ; primIdPath to pathId  -- ∀ {ℓ} {A : Set ℓ} {x y : A} → Id x y → Path A x y
           )
  hiding ( primIdJ ) -- this should not be used as it is using compCCHM
open import Cubical.Core public hiding ( _≡_ )
open import Cubical.Prelude
  hiding ( _≡_ ; ≡-proof_ ; begin_ ; _≡⟨⟩_ ; _≡⟨_⟩_ ; _≡-qed ; _∎ )
  renaming ( refl   to reflPath
           ; J      to JPath
           ; JRefl  to JPathRefl
           ; sym    to symPath
           ; cong   to congPath
           ; funExt to funExtPath )
open import Cubical.Glue
  renaming ( fiber to fiberPath
           ; isContr to isContrPath
           ; contrFibers to contrFibersPath
           ; isEquiv to isEquivPath
           ; _≃_ to EquivPath
           ; equivFun to equivFunPath
           ; EquivContr to EquivContrPath )

{- BUILTIN ID Id -}

_≡_ : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
_≡_ = Id

-- Version of the constructor for Id where the y is also
-- explicit. This is sometimes useful when it is needed for
-- typechecking (see JId below).
conId : ∀ {ℓ} {A : Set ℓ} {x : A} φ
              (y : A [ φ ↦ (λ _ → x) ])
              (w : (Path _ x (ouc y)) [ φ ↦ (λ { (φ = i1) → λ _ → x}) ]) →
              x ≡ ouc y
conId φ _ w = ⟨ φ , ouc w ⟩

-- Reflexivity
refl : ∀ {ℓ} {A : Set ℓ} {x : A} → x ≡ x
refl {x = x} = ⟨ i1 , (λ _ → x) ⟩

-- Direct eliminator for Id
module IdPrims where
  primitive
    primIdElim : ∀ {ℓ ℓ'} {A : Set ℓ} {x : A}
                   (P : ∀ (y : A) → x ≡ y → Set ℓ')
                   (h : ∀ (φ : I) (y : A [ φ ↦ (λ _ → x) ])
                          (w : (Path _ x (ouc y)) [ φ ↦ (λ { (φ = i1) → λ _ → x}) ] ) →
                          P (ouc y) ⟨ φ , ouc w ⟩) →
                   {y : A} (w' : x ≡ y) → P y w'

open IdPrims public renaming ( primIdElim to elimId )

-- Definition of J for Id
module _ {ℓ ℓ'} {A : Set ℓ} {x : A} (P : ∀ (y : A) → Id x y → Set ℓ') (d : P x refl) where
  J : ∀ {y : A} (w : x ≡ y) → P y w
  J {y = y} = elimId P (λ φ y w → comp (λ i → P _ (conId (φ ∨ ~ i) (inc (ouc w i))
                                                                   (inc (λ j → ouc w (i ∧ j)))))
                                       (λ i → λ { (φ = i1) → d}) (inc d)) {y = y}

  -- Check that J of refl is the identity function
  Jdefeq : Path _ (J refl) d
  Jdefeq _ = d


-- Basic theory about Id, proved using J
module _ {ℓ} {A : Set ℓ} where
  sym : {x y : A} → x ≡ y → y ≡ x
  sym {x} p = J (λ z _ → z ≡ x) refl p

  cong : ∀ {ℓ'} {B : Set ℓ'} (f : A → B) → ∀ {x y : A} → x ≡ y → f x ≡ f y
  cong f {x} = J (λ z _ → f x ≡ f z) refl

  trans : ∀ {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  trans {x} p = J (λ y _ → x ≡ y) p
  
  infix  3 _≡-qed _∎
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix  1 ≡-proof_ begin_

  ≡-proof_ begin_ : {x y : A} → x ≡ y → x ≡ y
  ≡-proof x≡y = x≡y
  begin_ = ≡-proof_

  _≡⟨⟩_ : (x {y} : A) → x ≡ y → x ≡ y
  _ ≡⟨⟩ x≡y = x≡y

  _≡⟨_⟩_ : (x {y z} : A) → x ≡ y → y ≡ z → x ≡ z
  _ ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

  _≡-qed _∎ : (x : A) → x ≡ x
  _ ≡-qed  = refl
  _∎ = _≡-qed


-- Convert between Path and Id
module _ {ℓ} {A : Set ℓ} where
  pathToId : ∀ {x y : A} → Path _ x y → Id x y
  pathToId {x} = JPath (λ y _ → Id x y) refl

  pathToIdRefl : ∀ {x} → Path _ (pathToId (λ _ → x)) refl
  pathToIdRefl {x} = JPathRefl (λ y _ → Id x y) refl

  idToPath : {x y : A} → Id x y → Path _ x y
  idToPath {x} = J (λ y _ → Path _ x y) (λ _ → x)

  idToPathRefl : ∀ {x : A} → Path _ (idToPath {x} refl) reflPath
  idToPathRefl {x} _ _ = x

  pathToIdToPath : ∀ {x y : A} → (p : Path _ x y) → Path _ p (idToPath (pathToId p))
  pathToIdToPath {x} = JPath (λ y p → Path _ p (idToPath (pathToId p)))
                             (λ i → idToPath (pathToIdRefl (~ i)))

  idToPathToId : ∀ {x y : A} → (p : Id x y) → Path _ p (pathToId (idToPath p))
  idToPathToId {x} = J (λ b p → Path _ p (pathToId (idToPath p))) (symPath pathToIdRefl)


-- We get function extensionality by going back and forth between Path and Id
funExt : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} {f g : (x : A) → B x} →
         ((x : A) → f x ≡ g x) → f ≡ g
funExt p = pathToId (λ i x → idToPath (p x) i)


-- Equivalences

fiber : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) (y : B) → Set (ℓ-max ℓ ℓ')
fiber {A = A} f y = Σ[ x ∈ A ] y ≡ f x

isContr : {ℓ : Level} (A : Set ℓ) → Set ℓ
isContr A = Σ[ x ∈ A ] (∀ y → x ≡ y)

module _ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') where
  contrFibers : (A → B) → Set (ℓ-max ℓ ℓ')
  contrFibers f = (y : B) → isContr (fiber f y)

  record isEquiv (f : A → B) : Set (ℓ-max ℓ ℓ') where
    field
      equiv-proof : contrFibers f
  open isEquiv public

  infix 4 _≃_
  _≃_ = Σ _ isEquiv

equivFun : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → A ≃ B → A → B
equivFun e = fst e


-- Functions for going between the various definitions. This could
-- also be achieved by making lines in the universe and transporting
-- back and forth along them. 

fiberPathToFiber : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f : A → B} {y : B} → fiberPath f y → fiber f y
fiberPathToFiber (x , p) = (x , pathToId p)

fiberToFiberPath : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f : A → B} {y : B} → fiber f y → fiberPath f y
fiberToFiberPath (x , p) = (x , idToPath p)

fiberToFiber : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f : A → B} {y : B} (p : fiber f y) → Path _ (fiberPathToFiber (fiberToFiberPath p)) p
fiberToFiber (x , p) = λ i → x , idToPathToId p (~ i)

fiberPathToFiberPath : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f : A → B} {y : B} (p : fiberPath f y) → Path _ (fiberToFiberPath (fiberPathToFiber p)) p
fiberPathToFiberPath (x , p) = λ i → x , pathToIdToPath p (~ i)

isContrPathToIsContr : ∀ {ℓ} {A : Set ℓ} → isContrPath A → isContr A
isContrPathToIsContr (ctr , p) = (ctr , λ y → pathToId (p y))

isContrToIsContrPath : ∀ {ℓ} {A : Set ℓ} → isContr A → isContrPath A
isContrToIsContrPath (ctr , p) = (ctr , λ y → idToPath (p y))


-- Specialized helper lemma for going back and forth
helper1 : ∀ {ℓ : Level} {A B : Set ℓ} (f : A → B) (g : B → A) (h : ∀ y → Path _ (f (g y)) y) → isContrPath A → isContr B
helper1 f g h (x , p) = (f x , λ y → pathToId (λ i → hcomp (λ j → λ { (i = i0) → f x ; (i = i1) → h y j }) (f (p (g y) i))))

helper2 : ∀ {ℓ : Level} {A B : Set ℓ} (f : A → B) (g : B → A) (h : ∀ y → Path _ (g (f y)) y) → isContr B → isContrPath A
helper2 {A = A} f g h (x , p) = (g x , λ y → idToPath (rem y))
  where
  rem : ∀ (y : A) → g x ≡ y
  rem y =
    g x     ≡⟨ cong g (p (f y)) ⟩
    g (f y) ≡⟨ pathToId (h y) ⟩
    y       ∎

helper12' : ∀ {ℓ} {A B : Set ℓ} (p1 p2 : isContrPath B) → Path (isContrPath B) p1 p2
helper12' (a0 , p0) (a1 , p1) j = p0 a1 j , λ x i → hcomp (λ k → λ { (i = i0) → p0 a1 j ; (i = i1) → p0 x (j ∨ k) ; (j = i0) → p0 x (i ∧ k) ; (j = i1) → p1 x i }) (p0 (p1 x i) j)

helper12 : ∀ {ℓ} {A : Set ℓ} (p1 p2 : isContr A) → Path (isContr A) (p1 .fst , λ x → pathToId (idToPath (p1 . snd x))) (p2 .fst , λ x → pathToId (idToPath (p2 .snd x)))
helper12 {A = A} (a0 , p0) (a1 , p1) j = idToPath (p0 a1) j , λ x →
  let rem : Path A (idToPath (p0 a1) j) x
      rem i = hcomp (λ k → λ { (i = i0) → idToPath (p0 a1) j ; (i = i1) → idToPath (p0 x) (j ∨ k) ; (j = i0) → idToPath (p0 x) (i ∧ k) ; (j = i1) → idToPath (p1 x) i }) (idToPath (p0 (idToPath (p1 x) i)) j)
  in pathToId rem

helper12'' : ∀ {ℓ} {A : Set ℓ} (p1 p2 : isContr A) → Path (isContr A) p1 p2 -- (p1 .fst , λ x → p1 .snd x) (p2 .fst , λ x → p2 .snd x)
helper12'' {ℓ} {A} p1 p2 i = hcomp (λ j → λ { (i = i0) → (p1 .fst) , λ x → idToPathToId (p1 .snd x) (~ j) ; (i = i1) → (p2 .fst) , λ x → idToPathToId (p2 .snd x) (~ j) }) (helper12 {ℓ} {A} p1 p2 i)

-- Go from an Path equivalence to an Id equivalence
equivPathToEquiv : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → EquivPath A B → A ≃ B
equivPathToEquiv (f , p) =
  (f , λ { .equiv-proof y → helper1 fiberPathToFiber fiberToFiberPath fiberToFiber (p .equiv-proof y) })

-- Go from an Path equivalence to an Id equivalence
equivToEquivPath : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → A ≃ B → EquivPath A B
equivToEquivPath (f , p) =
  (f , λ { .equiv-proof y → helper2 fiberPathToFiber fiberToFiberPath fiberPathToFiberPath (p .equiv-proof y) })


-- For now we assume that isEquiv is a proposition. I'm not sure what
-- is the best way to prove this. Maybe transport the proof for
-- isEquiv with Path?
isPropIsEquiv : ∀ {ℓ} {A : Set ℓ} {B : Set ℓ} → (f : A → B) → (h1 h2 : isEquiv A B f) → Path _ h1 h2
isPropIsEquiv {ℓ} {A} {B} f h1 h2 = λ i → record { equiv-proof = λ y → helper12'' {A = fiber f y} (h1 .equiv-proof y) (h2 .equiv-proof y) i }

equivPathToEquivPath : ∀ {ℓ} {A : Set ℓ} {B : Set ℓ} → (p : A ≃ B) → Path _ (equivPathToEquiv (equivToEquivPath p)) p
equivPathToEquivPath (f , p) =
  λ i → f , isPropIsEquiv f (λ { .equiv-proof y → helper1 fiberPathToFiber fiberToFiberPath fiberToFiber (helper2 fiberPathToFiber fiberToFiberPath fiberPathToFiberPath (p .equiv-proof y)) }) p i


f1 : ∀ {ℓ} {A : Set ℓ} → Σ[ T ∈ Set ℓ ] (EquivPath T A) → Σ[ T ∈ Set ℓ ] (T ≃ A)
f1 (x , p) = x , equivPathToEquiv p

f2 : ∀ {ℓ} {A : Set ℓ} → Σ[ T ∈ Set ℓ ] (T ≃ A) → Σ[ T ∈ Set ℓ ] (EquivPath T A)
f2 (x , p) = x , equivToEquivPath p


f12 : ∀ {ℓ} {A : Set ℓ} → (y : Σ[ T ∈ Set ℓ ] (T ≃ A)) → Path _ (f1 (f2 y)) y
f12 (x , p) = λ i → x , equivPathToEquivPath p i

EquivContr : ∀ {ℓ} (A : Set ℓ) → isContr (Σ[ T ∈ Set ℓ ] (T ≃ A))
EquivContr A = helper1 f1 f2 f12 (EquivContrPath A)
