{-

The Construction of `extend` Operation

To find explanation and examples, see `Cubical.Foundations.HLevels.Extend`.

-}
{-# OPTIONS --safe #-}
module Cubical.Foundations.HLevels.ExtendConstruction where

open import Cubical.Foundations.Prelude hiding (Cube)
open import Cubical.Foundations.HLevels renaming (extend to extend₀)
open import Cubical.Data.Nat


private
  variable
    ℓ : Level


-- to conveniently present the boundary of cubes

∂ : I → I
∂ i = i ∨ ~ i


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
-- pattern matching makes things easy

data Cube : Metaℕ → SSet where
  ∙   : Cube zero
  _,_ : {n : Metaℕ} → I → Cube n → Cube (suc n)

-- The boundary cofibration

bd :  {n : Metaℕ} → Cube n → I
bd ∙ = i0
bd (i , 𝓳) = bd 𝓳 ∨ ∂ i


-- boundary with an extra cofibration, partial elements and extension types
-- all non-fibrant

module _ {n : Metaℕ} where

  bdc : (ϕ : I) → Cube n → I
  bdc ϕ 𝓲 = ϕ ∨ bd 𝓲

  Part : (ϕ : I) → Cube n → Type ℓ → SSet ℓ
  Part ϕ 𝓲 X = Partial (bdc ϕ 𝓲) X

  Ext : (X : Type ℓ) (ϕ : I) (𝓲 : Cube n) → Part ϕ 𝓲 X → SSet ℓ
  Ext X ϕ 𝓲 x = X [ bdc ϕ 𝓲 ↦ x ]


-- methods to be used in induction

module _
  {ϕ : I}
  {X : I → Type ℓ}
  (x : (i : I) → Partial (ϕ ∨ ∂ i) (X i))
  where

  toPathPart : Partial ϕ (PathP X (x i0 1=1) (x i1 1=1))
  toPathPart 1=1 i = x i (IsOne1 _ (∂ i) 1=1)

  toPathExt :
    (p : PathP X (x i0 1=1) (x i1 1=1) [ ϕ ↦ toPathPart ])
    (i : I) → X i [ ϕ ∨ ∂ i ↦ x i ]
  toPathExt p i = inS (outS p i)

module _
  {n : Metaℕ} {ϕ : I}
  (X : Cube (suc n) → Type ℓ)
  (x : (𝓲 : Cube (suc n)) → Part ϕ 𝓲 (X 𝓲))
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
  {n : Metaℕ} {ϕ : I} {X : Cube n → Type ℓ}
  (h : (𝓲 : Cube n) → isOfHLevel (toℕ n) (X 𝓲))
  (x : (𝓲 : Cube n) → Part ϕ 𝓲 (X 𝓲))
  (𝓲 : Cube n) → Ext _ ϕ 𝓲 (x 𝓲)
extendUncurried {n = zero} h _ ∙ = extend₀ (h ∙) _ _
extendUncurried {n = suc n} {ϕ} h x =
  toExt {ϕ = ϕ} _ _ (extendUncurried {ϕ = ϕ} (isOfHLevelₙPathP {ϕ = ϕ} _ x h) _)



{-

The Curried Version of `extend`

-}

-- Tons of definitions to curry things

CubeType : (ℓ : Level) → Metaℕ → Type (ℓ-suc ℓ)
CubeType ℓ zero = Type ℓ
CubeType ℓ (suc n) = I → CubeType ℓ n

CubeTerm : {n : Metaℕ} → CubeType ℓ n → Type ℓ
CubeTerm {n = zero} X = X
CubeTerm {n = suc n} P = (i : I) → CubeTerm (P i)

CubeSSet : (ℓ : Level) → Metaℕ → SSet (ℓ-suc ℓ)
CubeSSet ℓ zero = SSet ℓ
CubeSSet ℓ (suc n) = I → CubeSSet ℓ n

CubeSTerm : {n : Metaℕ} → CubeSSet ℓ n → SSet ℓ
CubeSTerm {n = zero} X = X
CubeSTerm {n = suc n} P = (i : I) → CubeSTerm (P i)

uncurryType : {n : Metaℕ} → CubeType ℓ n → Cube n → Type ℓ
uncurryType {n = zero} X ∙ = X
uncurryType {n = suc n} X (i , 𝓳) = uncurryType (X i) 𝓳


isOfHLevelCubeType : (m : HLevel) {n : Metaℕ} → CubeType ℓ n → CubeType ℓ n
isOfHLevelCubeType m {zero}  X = isOfHLevel m X
isOfHLevelCubeType m {suc n} X i = isOfHLevelCubeType m (X i)

PartCubeType : {n : Metaℕ} (ϕ : I) → CubeType ℓ n → CubeSSet ℓ n
PartCubeType {n = zero}  ϕ X = Partial ϕ X
PartCubeType {n = suc n} ϕ X i = PartCubeType (ϕ ∨ ∂ i) (X i)

ExtCubeType : {n : Metaℕ} {ϕ : I} {X : CubeType ℓ n} → CubeSTerm (PartCubeType ϕ X) → CubeSSet ℓ n
ExtCubeType {n = zero}  {ϕ} x = _ [ _ ↦ x ]
ExtCubeType {n = suc n} {ϕ} x i = ExtCubeType {ϕ = ϕ ∨ ∂ i} (x i)


uncurryIsOfHLevelCubeType :
  (m : HLevel) {n : Metaℕ}
  {X : CubeType ℓ n}
  (h : CubeTerm (isOfHLevelCubeType m X))
  (𝓲 : Cube n) → isOfHLevel m (uncurryType X 𝓲)
uncurryIsOfHLevelCubeType m {n = zero} h ∙ = h
uncurryIsOfHLevelCubeType m {n = suc n} h (i , 𝓳) =
  uncurryIsOfHLevelCubeType m {n = n} (h i) _

uncurryPart :
  {ϕ : I} {n : Metaℕ}
  {X : CubeType ℓ n}
  (u : CubeSTerm (PartCubeType ϕ X))
  (𝓲 : Cube n) → Part ϕ 𝓲 (uncurryType X 𝓲)
uncurryPart {ϕ = ϕ} {zero} {X} u ∙ = u
uncurryPart {ϕ = ϕ} {n = suc n} {X} u (i , 𝓳) = uncurryPart (u i) 𝓳

curryExt :
  {ϕ : I} {n : Metaℕ}
  {X : CubeType ℓ n}
  (u : CubeSTerm (PartCubeType ϕ X))
  (x : (𝓲 : Cube n) → Ext _ ϕ 𝓲 (uncurryPart u 𝓲))
  → CubeSTerm (ExtCubeType {X = X} u)
curryExt {n = zero} _ x = x ∙
curryExt {n = suc n} u x i = curryExt (u i) (λ 𝓳 → x (i , 𝓳))


-- the curried `extend`

extendCurried :
  (n : Metaℕ) {ℓ : Level} {X : CubeType ℓ n}
  (h : CubeTerm  (isOfHLevelCubeType (toℕ n) X))
  (ϕ : I) (x : CubeSTerm (PartCubeType ϕ X))
  → CubeSTerm (ExtCubeType {X = X} x)
extendCurried n {X = X} h ϕ x =
  curryExt {X = X} _ (extendUncurried {ϕ = ϕ} (uncurryIsOfHLevelCubeType _ h) (uncurryPart x))
