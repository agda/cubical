{-

This file contains:



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
  hiding ( primIdJ -- this should not be used as it is using compCCHM
         )

open import Cubical.Core public hiding ( _≡_ )

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


-- This is a bit sketchy as we forget where the path is constant...
funExt : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} {f g : (x : A) → B x} →
         ((x : A) → f x ≡ g x) → f ≡ g
funExt p = ⟨ i0  , (λ i x → pathId (p x) i) ⟩ 




-- Some experimenting:

JPath : ∀ {ℓ ℓ'} {A : Set ℓ} {x : A}
      (P : ∀ y → Path _ x y → Set ℓ') (d : P x (λ _ → x))
      {y : A} → (p : Path _ x y) → P y p
JPath P d p = transp (λ i → P (p i) (λ j → p (i ∧ j))) i0 d

compPath : ∀ {ℓ} {A : Set ℓ} {x y z : A} → Path _ x y → Path _ y z → Path _ x z
compPath {x = x} p q i =
    hcomp (λ j → \ { (i = i0) → x
                   ; (i = i1) → q j }) (p i)

-- TODO: define everything using J!
module _ {ℓ} {A : Set ℓ} where
  pathToId : {x y : A} → Path _ x y → Id x y
  pathToId p = ⟨ i0 , (λ i → p i) ⟩

  -- This is wrong! We forget the formula...
  idToPath : {x y : A} → Id x y → Path _ x y
  idToPath = pathId

  pathToIdToPath : ∀ {x y : A} → (p : Path _ x y) → Path _ p (idToPath (pathToId p))
  pathToIdToPath {x} = JPath (λ b p → Path _ p (idToPath (pathToId p))) (λ _ → idToPath refl)

  -- idToPathToId : ∀ {x y : A} → (p : Id x y) → Path _ p (pathToId (idToPath p))
  -- idToPathToId {x} = J (λ b p → Path _ p (pathToId (idToPath p))) goal
  --   where
  --   goal : Path _ (refl {x = x}) (pathToId (idToPath (refl {x = x})))
  --   goal = {!!} -- This is false as we forgot the formula...
