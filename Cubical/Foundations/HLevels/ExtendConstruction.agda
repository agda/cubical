{-

The Construction of `extend` Operation

To find explanation and examples, see `Cubical.Foundations.HLevels.Extend`.

-}
{-# OPTIONS --safe #-}
module Cubical.Foundations.HLevels.ExtendConstruction where

open import Cubical.Foundations.Prelude hiding (Cube)
open import Cubical.Foundations.HLevels.Base
open import Agda.Builtin.Nat renaming (Nat to ℕ)


private
  variable
    ℓ : Level


-- to conveniently present the boundary of cubes

∂ : I → I
∂ i = i ∨ ~ i



-- special cases of small hlevels

extend₀ : {X : Type ℓ} (h : isContr X) (ϕ : I) (u : Partial ϕ X) → X [ ϕ ↦ u ]
extend₀ (x , p) ϕ u = inS (hcomp (λ { j (ϕ = i1) → p (u 1=1) j }) x)

extend₁ :
  {X : I → Type ℓ}
  (h : (i : I) → isProp (X i))
  (ϕ : I) (x : (i : I) → Partial _ (X i))
  (i : I) → X i [ ϕ ∨ ∂ i ↦ x i ]
extend₁ {X = X} h ϕ x i =
  inS (hcomp (λ j → λ
    { (ϕ = i1) → h i (bottom i) (x i 1=1) j
    ; (i = i0) → h i (bottom i) (x i 1=1) j
    ; (i = i1) → h i (bottom i) (x i 1=1) j })
    (bottom i))
    where
    bottom : (i : I) → X i
    bottom i = isProp→PathP h (x i0 1=1) (x i1 1=1) i


-- The external natural number

data Metaℕ : SSet where
  zero : Metaℕ
  suc  : (n : Metaℕ) → Metaℕ

-- transform external natural numbers to internal ones

toℕ : Metaℕ → ℕ
toℕ  zero   = zero
toℕ (suc n) = suc (toℕ n)


{-

The Uncurried Version of `extend`

-}


-- A cheating version of I × I × ... × I
-- pattern matching makes things easy!

data Cube : Metaℕ → SSet where
  ∙   : Cube zero
  _,_ : {n : Metaℕ} → I → Cube n → Cube (suc n)

-- the boundary cofibration

bd :  {n : Metaℕ} → Cube n → I
bd ∙ = i0
bd (i , 𝓳) = bd 𝓳 ∨ ∂ i


-- partial elements and extension types
-- all non-fibrant

module _ {n : Metaℕ} where

  Part : (ϕ : I) → Cube n → Type ℓ → SSet ℓ
  Part ϕ 𝓲 X = Partial (ϕ ∨ bd 𝓲) X

  Ext : (X : Type ℓ) (ϕ : I) (𝓲 : Cube n) → Part ϕ 𝓲 X → SSet ℓ
  Ext X ϕ 𝓲 x = X [ ϕ ∨ bd 𝓲 ↦ x ]


-- methods to be used in induction

module _
  {X : I → Type ℓ}
  {ϕ : I} (x : (i : I) → Partial (ϕ ∨ ∂ i) (X i))
  where

  toPathPart : Partial ϕ (PathP X (x i0 1=1) (x i1 1=1))
  toPathPart 1=1 i = x i (IsOne1 _ (∂ i) 1=1)

  toPathExt :
    (p : PathP X (x i0 1=1) (x i1 1=1) [ ϕ ↦ toPathPart ])
    (i : I) → X i [ ϕ ∨ ∂ i ↦ x i ]
  toPathExt p i = inS (outS p i)


module _
  {n : Metaℕ} {X : Cube (suc n) → Type ℓ}
  (ϕ : I) (x : (𝓲 : Cube (suc n)) → Part ϕ 𝓲 (X 𝓲))
  where

  PathPFam : (𝓳 : Cube n) → Type ℓ
  PathPFam 𝓳 = PathP (λ i → X (i , 𝓳)) (x (i0 , 𝓳) 1=1) (x (i1 , 𝓳) 1=1)

  toPart :
    (𝓳 : Cube n) → Part ϕ 𝓳 (PathPFam 𝓳)
  toPart 𝓳 = toPathPart (λ i → x (i , 𝓳))

  toExt :
    (p : (𝓳 : Cube n) → Ext _ ϕ 𝓳 (toPathPart (λ i → x (i , 𝓳))))
    (𝓲 : Cube (suc n)) → Ext _ ϕ 𝓲 (x 𝓲)
  toExt p (i , 𝓳) = toPathExt (λ i → x (i , 𝓳)) (p 𝓳) i

  isOfHLevelₙPathP :
    (h : (𝓲 : Cube (suc n)) → isOfHLevel (toℕ (suc n)) (X 𝓲))
    (𝓳 : Cube n) → isOfHLevel (toℕ n) (PathPFam 𝓳)
  isOfHLevelₙPathP h 𝓳 = isOfHLevelPathP' _ (h (i1 , 𝓳)) _ _


-- the uncurried `extend`

extendUncurried :
  {n : Metaℕ} {ℓ : Level} {X : Cube n → Type ℓ}
  (h : (𝓲 : Cube n) → isOfHLevel (toℕ n) (X 𝓲))
  (ϕ : I) (x : (𝓲 : Cube n) → Part ϕ 𝓲 (X 𝓲))
  (𝓲 : Cube n) → Ext _ ϕ 𝓲 (x 𝓲)
extendUncurried {zero}  h _ _ ∙ = extend₀ (h ∙) _ _
extendUncurried {suc zerp} h ϕ x (i , ∙) =
  extend₁ (λ i → h (i , ∙)) ϕ (λ i → x (i , ∙)) i
extendUncurried {suc n} h ϕ x =
  toExt ϕ _ (extendUncurried (isOfHLevelₙPathP ϕ x h) ϕ _)


{-

The Curried Version of `extend`

-}

-- Tons of definitions to curry/uncurry things

CubeType : (ℓ : Level) → Metaℕ → Type (ℓ-suc ℓ)
CubeType ℓ  zero   = Type ℓ
CubeType ℓ (suc n) = I → CubeType ℓ n

CubeTerm : {n : Metaℕ} → CubeType ℓ n → Type ℓ
CubeTerm {n = zero}  X = X
CubeTerm {n = suc n} P = (i : I) → CubeTerm (P i)

CubeSSet : (ℓ : Level) → Metaℕ → SSet (ℓ-suc ℓ)
CubeSSet ℓ  zero   = SSet ℓ
CubeSSet ℓ (suc n) = I → CubeSSet ℓ n

CubeSTerm : {n : Metaℕ} → CubeSSet ℓ n → SSet ℓ
CubeSTerm {n = zero}  X = X
CubeSTerm {n = suc n} P = (i : I) → CubeSTerm (P i)

uncurryType : {n : Metaℕ} → CubeType ℓ n → Cube n → Type ℓ
uncurryType {n = zero}  X ∙ = X
uncurryType {n = suc n} X (i , 𝓳) = uncurryType (X i) 𝓳


isOfHLevelCubeType : (m : HLevel) {n : Metaℕ} → CubeType ℓ n → CubeType ℓ n
isOfHLevelCubeType m {zero}  X   = isOfHLevel m X
isOfHLevelCubeType m {suc n} X i = isOfHLevelCubeType m (X i)

PartCubeType : {n : Metaℕ} (ϕ : I) → CubeType ℓ n → CubeSSet ℓ n
PartCubeType {n = zero}  ϕ X   = Partial ϕ X
PartCubeType {n = suc n} ϕ X i = PartCubeType (ϕ ∨ ∂ i) (X i)

ExtCubeType : {n : Metaℕ} {ϕ : I} {X : CubeType ℓ n}
  → CubeSTerm (PartCubeType ϕ X) → CubeSSet ℓ n
ExtCubeType {n = zero}  x   = _ [ _ ↦ x ]
ExtCubeType {n = suc n} x i = ExtCubeType (x i)


uncurryIsOfHLevelCubeType :
  (m : HLevel) {n : Metaℕ}
  {X : CubeType ℓ n}
  (h : CubeTerm (isOfHLevelCubeType m X))
  (𝓲 : Cube n) → isOfHLevel m (uncurryType X 𝓲)
uncurryIsOfHLevelCubeType m h ∙ = h
uncurryIsOfHLevelCubeType m h (i , 𝓳) =
  uncurryIsOfHLevelCubeType m (h i) 𝓳

uncurryPart :
  {n : Metaℕ} {X : CubeType ℓ n}
  {ϕ : I} (u : CubeSTerm (PartCubeType ϕ X))
  (𝓲 : Cube n) → Part ϕ 𝓲 (uncurryType X 𝓲)
uncurryPart u ∙ = u
uncurryPart u (i , 𝓳) = uncurryPart (u i) 𝓳

curryExt :
  {n : Metaℕ} {X : CubeType ℓ n}
  {ϕ : I} (u : CubeSTerm (PartCubeType ϕ X))
  (x : (𝓲 : Cube n) → Ext _ ϕ 𝓲 (uncurryPart u 𝓲))
  → CubeSTerm (ExtCubeType {X = X} u)
curryExt {n = zero}  _ x = x ∙
curryExt {n = suc n} u x i = curryExt (u i) (λ 𝓳 → x (i , 𝓳))


-- the curried `extend`

extendCurried :
  (n : Metaℕ) {ℓ : Level} {X : CubeType ℓ n}
  (h : CubeTerm (isOfHLevelCubeType (toℕ n) X))
  (ϕ : I) (x : CubeSTerm (PartCubeType ϕ X))
  → CubeSTerm (ExtCubeType {X = X} x)
extendCurried n h ϕ x =
  curryExt {n = n} _
    (extendUncurried (uncurryIsOfHLevelCubeType _ h) ϕ (uncurryPart x))
