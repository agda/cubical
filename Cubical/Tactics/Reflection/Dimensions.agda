{-

This module provides utilities for working with interval expressions (`IExpr`) in a reflected syntax.
It introduces an abstract representation of interval expressions and face expressions (`FExpr`).

1. **Interval Expressions (IExpr)**
   - Defined as `List (List (Bool × ℕ))`.
   - Operations:
     - `∨'` (disjunction)
     - `∧'` (conjunction)
     - `~'` (negation)
     - `ie[ _ ]` (singleton interval expression)
   - Normalization using `normIExpr`.
   - Conversion between `IExpr` and terms (`IExpr→Term`).

2. **Face Expressions (FExpr)**
   - Defined as `List SubFace`.
   - Operations:
     - `fe∷` (face extension)
     - `fe∷×` (face extension with additional data)
     - `++fe` (concatenation for `FExpr`)
     - `++fe×` (concatenation for `FExpr` with additional data)
   - Conversion between `IExpr` and `FExpr` via `I→F`.

3. **SubFaces and Constraints**
   - Definition and manipulation of faces and subfaces in the interval (e.g., `allSubFacesOfDim`, `subFaceConstraints`).
   - Operations and relations between subfaces (`<SF>`, `sf∩`, `<sf>`).

4. **Contextual Operations**
   - Addition of interval dimensions to contexts (`addNDimsToCtx`).
   - Handling and applying face constraints within contexts.

5. **Utility Functions**
   - Extraction and manipulation of interval expressions from terms (`extractIExpr`, `extractIExprM`).
   - Lifting and dropping variables in terms based on boolean masks (`liftWhere`, `dropWhere`).

6. **Non-Degenerate Faces**
   - Check and filter for non-degenerate faces and expressions (`nonDegFExpr`, `isNonDegen`).


The current representations of interval and face expressions are not very type-safe.
While functions for manipulating and combining expressions typically produce normalized versions,
this is not enforced at the type level. Additionally, the representations are not parameterized
by context, meaning the well-scopedness of these expressions is not enforced.
Making these aspects type-safe should not be difficult, would be a natural progression and should be a focus
for future refactoring.

-}

{-# OPTIONS --safe  #-}

module Cubical.Tactics.Reflection.Dimensions where

import Agda.Builtin.Reflection as R

open import Agda.Builtin.String
open import Agda.Builtin.Nat using () renaming (_==_ to _=ℕ_ ; _<_ to _<ℕ_)


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Reflection.Base
open import Cubical.Reflection.Sugar

open import Cubical.Data.List as L
open import Cubical.Data.Bool as 𝟚
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Nat
open import Cubical.Data.Empty
open import Cubical.Data.Maybe as Mb

open import Cubical.Relation.Nullary

open import Cubical.Tactics.Reflection.Variables
open import Cubical.Tactics.Reflection.Utilities
open import Cubical.Tactics.Reflection.Error

IExpr : Type
IExpr = List (List (Bool × ℕ))

private
  variable
    ℓ : Level
    A : Type ℓ



_∨'_ : IExpr → IExpr → IExpr
_∨'_ = _++_


_∧'_ : IExpr → IExpr → IExpr
x ∧' y = L.map (uncurry _++_) (cart x y)


~' : IExpr → IExpr
~' = foldl (λ x y → x ∧' L.map ([_] ∘S map-fst not) y) [ [] ]

ie[_] : ℕ → IExpr
ie[ x ] = [ [ true , x ] ]




normIExpr : IExpr → IExpr
normIExpr = norm∨ ∘S L.map norm∧
 where
  disc𝟚×ℕ = (discreteΣ 𝟚._≟_ λ _ → discreteℕ)

  norm∧ : List (Bool × ℕ) → List (Bool × ℕ)
  norm∧ = nub disc𝟚×ℕ

  norm∨ : IExpr → IExpr

  norm∨' : List (Bool × ℕ) → IExpr → IExpr
  norm∨' x [] = [ x ]
  norm∨' x (x' ∷ xs) with subs? disc𝟚×ℕ x x' | subs? disc𝟚×ℕ x' x
  ... | false | false = x' ∷ norm∨' x xs
  ... | false | true = norm∨' x' xs
  ... | true | b' = norm∨' x xs



  norm∨ [] = []
  norm∨ (x ∷ x₁) = norm∨' x x₁


vlamⁿ : ℕ → R.Term → R.Term
vlamⁿ zero t = t
vlamⁿ (suc n) t = vlam "𝒊" (vlamⁿ n t)



$i : ∀ {ℓ} {A : Type ℓ} → (I → A) → I → A
$i = λ f i → f i

$≡ : ∀ {ℓ} {A : I → Type ℓ} {x : A i0} {y : A i1} → (PathP A x y) → ∀ i → A i
$≡ f i = f i


$PI : ∀ {ℓ} (A : Type ℓ) → (I → (Partial i1 A)) → I → A
$PI _ f i = f i 1=1


appNDimsI : ℕ → R.Term → R.Term
appNDimsI zero t = t
appNDimsI (suc n) t =
 appNDimsI n $ R.def (quote $i) ( t v∷ v[ R.var n [] ])

SubFace = List (Maybe Bool)

allSubFacesOfDim : ℕ → List SubFace
allSubFacesOfDim zero = [ [] ]
allSubFacesOfDim (suc x) =
 let l = allSubFacesOfDim x
 in    L.map (nothing ∷_) l
    ++ L.map (just false ∷_) l
    ++ L.map (just true ∷_) l

sfDim : SubFace → ℕ
sfDim sf = length sf ∸ length (filter (λ { (just _) → true ; _ → false} ) sf)

allSubFacesOfSfDim : ℕ → ℕ → List SubFace
allSubFacesOfSfDim n k = filter ((_=ℕ k) ∘S sfDim) $ allSubFacesOfDim n

subFaceConstraints : SubFace → List (Bool × ℕ)
subFaceConstraints [] = []
subFaceConstraints (x ∷ xs) =
  Mb.rec (idfun _) (_∷_ ∘S (_, zero)) x $
    (L.map (map-snd suc) (subFaceConstraints xs))



injSF : SubFace → SubFace → SubFace
injSF [] y = []
injSF (x ∷ x₁) [] = []
injSF (nothing ∷ x₁) (x₂ ∷ y) = x₂ ∷ injSF x₁ y
injSF (just x ∷ x₁) (x₂ ∷ y) = injSF x₁ y


data <SF> : Type where
 ⊂ ⊃ ⊃⊂ ⊂⊃ : <SF>

⊂⊃? : <SF> → Bool
⊂⊃? ⊂⊃ = true
⊂⊃? _ = false



SF⊃⊂ : <SF> → Type
SF⊃⊂ ⊃⊂ = Unit
SF⊃⊂ _ = ⊥

_<⊕>_ : <SF> → <SF> → <SF>
⊃⊂ <⊕> x₁ = ⊃⊂
⊂⊃ <⊕> x₁ = x₁

⊂ <⊕> ⊂ = ⊂
⊂ <⊕> ⊂⊃ = ⊂
⊂ <⊕> _ = ⊃⊂

⊃ <⊕> ⊂⊃ = ⊃
⊃ <⊕> ⊃ = ⊃
⊃ <⊕> _ = ⊃⊂

_<mb>_ : Maybe Bool → Maybe Bool → <SF>
nothing <mb> nothing = ⊂⊃
nothing <mb> just x = ⊃
just x <mb> nothing = ⊂
just x <mb> just x₁ = if (x ⊕ x₁) then ⊃⊂ else ⊂⊃

_<sf>_ : SubFace → SubFace → <SF>
[] <sf> [] = ⊂⊃
[] <sf> (y ∷ ys) = (nothing <mb> y) <⊕> ([] <sf> ys)
(x ∷ xs) <sf> [] =  (x <mb> nothing) <⊕> (xs <sf> [])
(x ∷ xs) <sf> (y ∷ ys) = (x <mb> y) <⊕> (xs <sf> ys)

_sf∩_ : SubFace → SubFace → Maybe SubFace
[] sf∩ [] = just []
[] sf∩ (x ∷ x₁) = nothing
(x ∷ x₁) sf∩ [] = nothing
(nothing ∷ x₁) sf∩ (x₂ ∷ x₃) =
   map-Maybe (x₂ ∷_) (x₁ sf∩ x₃ )
(just x ∷ x₁) sf∩ (nothing ∷ x₃) =  map-Maybe (just x ∷_) (x₁ sf∩ x₃ )
(just x ∷ x₁) sf∩ (just x₂ ∷ x₃) =
  if (x ⊕ x₂)
  then nothing
  else map-Maybe (just x ∷_) (x₁ sf∩ x₃ )

FExpr = List SubFace





infixr 5 _fe∷_ _fe∷×_

_fe∷_ : SubFace → FExpr → FExpr
x fe∷ [] = x ∷ []
x fe∷ y@(sf ∷ x₁) with sf <sf> x
... | ⊂ = x fe∷ x₁
... | ⊃ = y
... | ⊃⊂ = sf ∷ (x fe∷ x₁)
... | ⊂⊃ = y


_fe∷×_ : ∀ {ℓ} {A : Type ℓ} → (SubFace × A) → List (SubFace × A)  → List (SubFace × A)
(x , a) fe∷× [] = (x , a) ∷ []
(x , a) fe∷× y@((sf , a') ∷ x₁) with sf <sf> x
... | ⊂ = (x , a) fe∷× x₁
... | ⊃ = y
... | ⊃⊂ = (sf , a') ∷ ((x , a) fe∷× x₁)
... | ⊂⊃ = y


_++fe_ : FExpr → FExpr → FExpr
x ++fe y = foldr _fe∷_ y x

_++fe×_ : List (SubFace × A) → List (SubFace × A)  → List (SubFace × A)
x ++fe× y = foldr _fe∷×_ y x


_⊂?_ : SubFace → FExpr → Bool
x ⊂? [] = false
x ⊂? (y ∷ sf) with x <sf> y
... | ⊂ = true
... | ⊃ = x ⊂? sf
... | ⊃⊂ = x ⊂? sf
... | ⊂⊃ = true


¬⊃⊂? : <SF> → Bool
¬⊃⊂? ⊃⊂ = false
¬⊃⊂? _ = true


mkFace : Bool → ℕ → SubFace
mkFace b k = iter k (nothing ∷_ ) (just b ∷ [])

_∪Mb_ : Maybe Bool → Maybe Bool → Maybe (Maybe Bool)
nothing ∪Mb x₁ = just x₁
just x ∪Mb nothing = just (just x)
just x ∪Mb just x₁ = if (x ⊕ x₁) then nothing else just (just x)

_∪SF_ : SubFace → SubFace → Maybe SubFace
[] ∪SF x₁ = just x₁
(x ∷ x₂) ∪SF [] = just ((x ∷ x₂))
(x ∷ x₂) ∪SF (x₁ ∷ x₃) =
 map2-Maybe _∷_  (x ∪Mb x₁) (x₂ ∪SF x₃)

fromSF : (List (Bool × ℕ)) → Maybe SubFace
fromSF [] = nothing
fromSF (x ∷ xs) =
 foldr (flip (Mb.rec (λ _ → nothing) _∪SF_ ) ∘S uncurry mkFace) (just (mkFace (fst x) (snd x))) xs


withAllIncluded : ℕ → FExpr → FExpr
withAllIncluded dim x =
  filter (_⊂? x) (allSubFacesOfDim dim)


SubFace→Term : SubFace → R.Term
SubFace→Term = h 0
 where
 h : ℕ → SubFace → R.Term
 h k [] = R.con (quote i1) []
 h k (nothing ∷ xs) = h (suc k) xs
 h k (just x ∷ xs) =
  let x' = R.var k []
      x'' = if x then x' else R.def (quote ~_) v[ x' ]
  in R.def (quote _∧_) (x'' v∷ v[ h (suc k) xs ])


I→F : IExpr → FExpr
I→F [] = []
I→F (x ∷ x₁) =
 Mb.rec
   (I→F x₁)
   (λ x → x fe∷ I→F x₁)
   (fromSF x)



endTerm : Bool → R.Term
endTerm = (if_then R.con (quote i1) [] else R.con (quote i0) [])


IExpr∧→Term : List (Bool × ℕ) → R.Term
IExpr∧→Term [] = endTerm true
IExpr∧→Term ((b , k) ∷ []) = (let x' = R.var (k) [] in  if b then x' else R.def (quote ~_) v[ x' ])
IExpr∧→Term ((b , k) ∷ xs) =
  R.def (quote _∧_)
    ((let x' = R.var (k) [] in  if b then x' else R.def (quote ~_) v[ x' ]) v∷ v[ IExpr∧→Term xs ])


getMaxVar : IExpr → ℕ
getMaxVar = maximum ∘S L.map snd ∘S join
 where
  maximum : List ℕ → ℕ
  maximum = foldr max zero



IExpr→Term : IExpr → R.Term
IExpr→Term [] = endTerm false
IExpr→Term (xs ∷ []) = IExpr∧→Term xs
IExpr→Term (xs ∷ xxs) = R.def (quote _∨_) (IExpr∧→Term xs v∷ v[ IExpr→Term xxs ])


mapVarsInIExpr : (ℕ → ℕ) → IExpr → IExpr
mapVarsInIExpr f = L.map (L.map (map-snd f))

interpolateIExpr : IExpr → IExpr → IExpr → IExpr
interpolateIExpr t ie0 ie1 = normIExpr $
  (((~' t) ∧' ie0) ∨' ((t) ∧' ie1)) ∨' (ie0 ∧' ie1)

IExpr→MaybeEnd : IExpr → Maybe Bool
IExpr→MaybeEnd = (λ { [] -> just false ; ([] ∷ []) → just true ; _ → nothing } ) ∘S normIExpr

evalIExprOnFace : SubFace → IExpr → IExpr
evalIExprOnFace sf = catMaybes ∘S L.map (h (zipWithIndex sf))

 where

  hh : ℕ × Maybe Bool → Maybe (List (Bool × ℕ)) → Maybe (List (Bool × ℕ))
  hh (_ , nothing) l = l
  hh _ nothing = nothing
  hh (k , just b) (just xs) =
     if elem? (discreteΣ 𝟚._≟_ λ _ → discreteℕ) (not b , k) xs
      then nothing
      else just (filter (not ∘S Dec→Bool ∘ (discreteΣ 𝟚._≟_ λ _ → discreteℕ) (b , k)) xs)

  h : List (ℕ × Maybe Bool) → (List (Bool × ℕ)) → Maybe (List (Bool × ℕ))
  h sf xs = foldr hh (just xs) sf




module _ (s : String) where

 addNDimsToCtx' : ℕ → R.TC A → R.TC A
 addNDimsToCtx' zero f = f
 addNDimsToCtx' (suc k) =
  R.extendContext (mkNiceVar' s k) (varg (R.def (quote I) []))
    ∘S (addNDimsToCtx' k)

addNDimsToCtx = addNDimsToCtx' "𝓲"



-- works under assumption, that all free variables in term are of Interval type
-- (wont work for term like (f 1) where (f : ℕ → I))

extractIExpr : R.Term → Maybe IExpr
extractIExpr (R.var x []) = ⦇  ( ie[ x ] )  ⦈
extractIExpr (R.con (quote i0) []) = ⦇ [] ⦈
extractIExpr (R.con (quote i1) []) = ⦇ ([ [] ]) ⦈
extractIExpr (R.def (quote _∨_) (x v∷ v[ y ])) =
  ⦇ extractIExpr x ∨' extractIExpr y ⦈
extractIExpr (R.def (quote _∧_) (x v∷ v[ y ])) =
  ⦇ extractIExpr x ∧' extractIExpr y ⦈
extractIExpr (R.def (quote ~_) v[ x ] ) =
    ⦇ ~' (extractIExpr x) ⦈
extractIExpr _ = nothing


extractIExprM : R.Term → R.TC IExpr
extractIExprM t = Mb.rec (R.typeError ("extractIExpr fail:" ∷ₑ [ t ]ₑ )) pure (extractIExpr t)

CuCtx = List (String × Maybe Bool)

defaultCtx : ℕ → CuCtx
defaultCtx dim = L.map ((_, nothing) ∘S mkNiceVar' "𝓲") $ range dim

inCuCtx : CuCtx → R.TC A → R.TC A
inCuCtx ctx x = foldl (λ x → uncurry
  λ v → Mb.caseMaybe (R.extendContext v ((varg (R.def (quote I) []))) x) x) x ctx

inCuCtx' : CuCtx → R.TC A → R.TC A
inCuCtx' ctx x = foldl (λ x → uncurry
  λ v _ → R.extendContext v ((varg (R.def (quote I) []))) x) x ctx





SubFace→TermInCtx : CuCtx → SubFace → R.Term
SubFace→TermInCtx ctx = h 0
 where

 kInCtx : CuCtx → ℕ → ℕ
 kInCtx [] k = k
 kInCtx ((fst₁ , nothing) ∷ xs) zero = zero
 kInCtx ((fst₁ , nothing) ∷ xs) (suc k) = suc (kInCtx xs k)
 kInCtx ((fst₁ , just x) ∷ xs) k = suc (kInCtx (xs) k)

 h : ℕ → SubFace → R.Term
 h k [] = R.con (quote i1) []
 h k (nothing ∷ xs) = h (suc k) xs
 h k (just x ∷ xs) =
  let x' = R.var (kInCtx ctx k) []
      x'' = if x then x' else R.def (quote ~_) v[ x' ]
  in R.def (quote _∧_) (x'' v∷ v[ h (suc k) xs ])

IExpr→TermInCtx : CuCtx → IExpr → R.Term
IExpr→TermInCtx ctx =
   foldl (λ x y → R.def (quote _∨_) (x v∷
       v[ foldl (λ x (b , k) → R.def (quote _∧_) (x v∷
              v[ (let x' = R.var (kInCtx ctx k) []
                      x'' = if b then x' else R.def (quote ~_) v[ x' ]
                  in x'')
                  ] ))
               (R.con (quote i1) []) y ] ))
     (R.con (quote i0) [])
 where

 kInCtx : CuCtx → ℕ → ℕ
 kInCtx [] k = k
 kInCtx ((fst₁ , nothing) ∷ xs) zero = zero
 kInCtx ((fst₁ , nothing) ∷ xs) (suc k) = suc (kInCtx xs k)
 kInCtx ((fst₁ , just x) ∷ xs) k = suc (kInCtx (xs) k)


applyFaceConstraints : SubFace → CuCtx → CuCtx
applyFaceConstraints sf [] = []
applyFaceConstraints [] ctx@(_ ∷ _) = ctx
applyFaceConstraints sf@(_ ∷ _) (c@(_ , just _) ∷ ctx) =
  c ∷ applyFaceConstraints sf ctx
applyFaceConstraints (mbC ∷ sf) ((v , nothing) ∷ ctx) =
  (v , mbC) ∷ applyFaceConstraints sf ctx


freeVars : CuCtx → List String
freeVars = L.map fst ∘S filter (λ { (_ , (nothing)) → true ; _ → false} )

boundedDims : CuCtx → List (String × Bool)
boundedDims = catMaybes ∘S L.map (uncurry λ s → map-Maybe (s ,_))



dropWhere : List Bool → R.Term → R.Term
dropWhere = dw ∘S rev
 where
 dw : List Bool → R.Term → R.Term
 dw [] t = t
 dw (b ∷ xs) t = dw xs (if b then dropVar (length xs) t else t)

liftWhere : List Bool → R.Term → R.Term
liftWhere = lw ∘S rev
 where
 lw : List Bool → R.Term → R.Term
 lw [] t = t
 lw (b ∷ xs) t =
  let t' = lw xs t
  in (if b then (liftVarsFrom 1 (length xs) t') else t')


subfaceCell : SubFace → R.Term → R.Term
subfaceCell sf = dropWhere (L.map (λ {(just _) → true ; _ → false }) sf) ∘S replaceVarWithCon (r sf)
 where
 r : SubFace → ℕ → Maybe R.Name
 r sf = map-Maybe (if_then quote i1 else quote i0) ∘S lookupAlways nothing sf

subfaceCellNoDrop : SubFace → R.Term → R.Term
subfaceCellNoDrop sf = replaceVarWithCon (r sf)
 where
 r : SubFace → ℕ → Maybe R.Name
 r sf = map-Maybe (if_then quote i1 else quote i0) ∘S lookupAlways nothing sf




feMask : FExpr → List Bool
feMask = foldr (alwaysZipWith
      (λ x y → (fromJust-def false x) or (fromJust-def false y)) ∘S L.map (caseMaybe false true)) []




degenRoughPrecheck : ℕ → IExpr → Bool
degenRoughPrecheck n xs =
 let h = flip (elem? (discreteΣ 𝟚._≟_ λ _ → discreteℕ)) (join xs) in
 foldr
  (_or_ ∘S λ k → (h (true , k)) and (h (false , k)))
  false (range n)

F→I : ℕ → FExpr → IExpr
F→I n =
  L.map (catMaybes ∘S L.map (λ (k , mbB) → map-Maybe (_, k) mbB) ∘S zipWithIndex)


allVertsOfSF : SubFace → List SubFace
allVertsOfSF sf = filter
 (λ sf' → Dec→Bool (discreteℕ (sfDim sf') 0) and (sf' ⊂? [ sf ]))
  (allSubFacesOfDim (length sf))


undegen' : ℕ → IExpr → List (SubFace × List (List (Bool × ℕ)) × String × Bool)
undegen' n ie' =

 let ie = normIExpr ie'
     h sf =  sf , normIExpr (evalIExprOnFace sf ie) ,
                 foldr _<>_ "" (L.map
                  (λ l → "[" <> foldr _<>_ "" (L.map (λ (b , k) →
                         let vv = mkNiceVar' "𝓲" k
                          in "(" <> (if b then vv else "~" <> vv) <> ")" ) l) <> "]"

                    )
                  (normIExpr (evalIExprOnFace sf ie))) ,
                     let sfs = allVertsOfSF sf
                     in foldr
                          _and_
                            true (L.map (λ sf' → Mb.fromJust-def false (IExpr→MaybeEnd (evalIExprOnFace sf' ie))) sfs)


 in  L.map h (allSubFacesOfDim n)


instance
 ToErrorPartSubFace : ToErrorPart SubFace
 ToErrorPart.toErrorPart ToErrorPartSubFace sf =
   R.strErr (foldr (λ (i , mBb) s →
      "(" <> Mb.rec "__" (if_then "i1" else "i0") mBb <> ")" <> s)
      "" (zipWithIndex sf) )




unifyTest : ℕ → R.Term → R.Term → R.TC Bool
unifyTest dim t t' = addNDimsToCtx dim $
 (R.unify t t' >> pure true)  <|> (pure false)






nonDegFExpr : ℕ → IExpr → FExpr
nonDegFExpr n ie' =
  let ie = normIExpr ie'
      h sf =
         let sfs = allVertsOfSF sf
         in foldr
            _and_
              true (L.map (λ sf' → Mb.fromJust-def false (IExpr→MaybeEnd (evalIExprOnFace sf' ie))) sfs)
   in foldr _fe∷_ [] (filter h (allSubFacesOfDim n))


undegen : Bool → ℕ → IExpr → IExpr
undegen onEnd n ie' =

 let ie = normIExpr ie'
     w = nonDegFExpr n ie'

 in if onEnd
    then (F→I n w)
    else interpolateIExpr ie[ n ] ie (F→I n w)

undegen2 : Bool → ℕ → IExpr → IExpr
undegen2 onEnd n ie' =

 let ie = normIExpr ie'
     w = nonDegFExpr n ie'

 in if onEnd
    then (F→I n w)
    else interpolateIExpr ie[ zero ] (mapVarsInIExpr suc (F→I n w)) (mapVarsInIExpr suc ie)



isNonDegen : ℕ → IExpr → R.TC Bool
isNonDegen dim iexpr =
   unifyTest dim (IExpr→Term iexpr) (IExpr→Term (undegen true dim iexpr))


undegenFcs : ℕ → List IExpr → (R.TC (FExpr))
undegenFcs dim l = do
  do
     foldrM (λ sf fe → _++fe fe <$> (if ((sfDim sf) =ℕ 0) then pure [ sf ] else do
        isNonDegForEvery ← foldrM
            (\ie b →  (b and_)  <$> (isNonDegen dim (evalIExprOnFace sf ie)))
              true l
        pure $ if isNonDegForEvery then [ sf ] else []))
      [] (filter ((_<ℕ dim) ∘ sfDim) (allSubFacesOfDim dim))


normIExprInTerm : ℕ → R.Term → R.TC R.Term
normIExprInTerm offset =
    atVarOrDefM.rv
      (λ n k _ args → R.var (n + k) <$> args)
      h
      zero

 where

  g :  R.Name → List (R.Arg R.Term) → R.Term → Maybe R.Term
  g (quote _∨_) a@(_ v∷ v[ _ ]) tm = just tm
  g (quote _∧_) a@(_ v∷ v[ _ ]) tm = just tm
  g (quote ~_) a@(v[ _ ]) tm = just tm
  g _ _ _ = nothing

  h : ℕ →
        R.Name →
        List (R.Arg R.Term) → R.TC (List (R.Arg R.Term)) → R.TC R.Term
  h _ nm arg argM =
     Mb.rec (R.def nm <$> argM)
            ((extractIExprM >=&
              (IExpr→Term
              ∘ mapVarsInIExpr (_+ offset)
              ∘ normIExpr
              ∘ mapVarsInIExpr (_∸ offset) )))
       (g nm arg (R.def nm arg))


macro
 normIExprInTermM : R.Term → R.Term → R.TC Unit
 normIExprInTermM t h =
    normIExprInTerm zero t >>= flip R.unify h



extractAllIExprs : R.Term → List IExpr
extractAllIExprs tm =
  snd $ runIdentity $ unwrap (atVarOrDefM.rv {M = [ State₀T (List IExpr) RMT IdentityF ]_ }
        (λ _ v _ argM → R.var v <$> argM)
        gg zero tm) []
  where

  g :  R.Name → List (R.Arg R.Term) → Bool
  g (quote _∨_) a@(_ v∷ v[ _ ]) = true
  g (quote _∧_) a@(_ v∷ v[ _ ]) = true
  g (quote ~_) a@(v[ _ ]) = true
  g _ _  = false


  gg : _
  gg n nm arg argM = let t = R.def nm arg in
    if (g nm arg)
    then (Mb.rec (liftM (identity tt))
      (λ ie → modify ((mapVarsInIExpr (_∸ n) ie) ∷_)) (extractIExpr t) ) >> pure t
    else R.def nm <$> argM

mapIExprs : ℕ -> ℕ → (IExpr → IExpr) → R.Term → R.TC R.Term
mapIExprs dim offset fn =
    atVarOrDefM.rv
      (λ n k _ args →
        if (n <ℕ (suc k)) and (k <ℕ (n + dim))
        then (pure ((IExpr→Term
              ∘S mapVarsInIExpr (_+ (offset + n))
              ∘S fn
              ∘S mapVarsInIExpr (_∸ (offset + n))) (ie[ k ])))
        else (R.var k <$> args))
      h
      zero

 where

  g :  R.Name → List (R.Arg R.Term) → R.Term → Maybe R.Term
  g (quote _∨_) a@(_ v∷ v[ _ ]) tm = just tm
  g (quote _∧_) a@(_ v∷ v[ _ ]) tm = just tm
  g (quote ~_) a@(v[ _ ]) tm = just tm
  g _ _ _ = nothing

  h : ℕ →
        R.Name →
        List (R.Arg R.Term) → R.TC (List (R.Arg R.Term)) → R.TC R.Term
  h n nm arg argM =
     Mb.rec (R.def nm <$> argM)
            ((extractIExprM >=&
              (IExpr→Term
              ∘ mapVarsInIExpr (_+ (offset + n))
              ∘ fn
              ∘ mapVarsInIExpr (_∸ (offset + n)) )))
       (g nm arg (R.def nm arg))


icConnFree' : IExpr → Bool
icConnFree' [] = true
icConnFree' ([] ∷ []) = true
icConnFree' ((x ∷ []) ∷ []) = true
icConnFree' _ = false

icConnFree : IExpr → Bool
icConnFree = icConnFree' ∘ normIExpr

missingSubFaces : ℕ → FExpr → List SubFace
missingSubFaces dim fe = filter (not ∘S _⊂? fe) (allSubFacesOfDim dim)

getCuCtx : R.TC CuCtx
getCuCtx =
  takeWhile
   (λ { (s , varg (R.def (quote I) [])) → just (s , nothing)
       ; _ → nothing })
    <$> R.getContext
