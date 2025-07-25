{-

This file contains:
  - Pushout-products of two maps;
  - The connectivity of pushout-product maps.

-}
module Cubical.HITs.Pushout.PushoutProduct where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat
open import Cubical.Data.Sigma

open import Cubical.HITs.Pushout.Base
open import Cubical.HITs.Pushout.Properties

open import Cubical.Homotopy.Connected

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    A : Type ℓ
    B : Type ℓ'
    X : Type ℓ''
    Y : Type ℓ'''


-- The definition of pushout-product

PushProd : (f : X → A)(g : Y → B) → Type _
PushProd f g = Pushout (map-× (idfun _) g) (map-× f (idfun _))

_×̂_ : (f : X → A)(g : Y → B) → PushProd f g → A × B
(f ×̂ g) (inl (x , b)) = f x , b
(f ×̂ g) (inr (a , y)) = a , g y
(f ×̂ g) (push (x , y) i) = f x , g y

infixr 5 _×̂_


module _
  (m n : ℕ)(f : X → A)(g : Y → B)
  (connf : isConnectedFun m f)
  (conng : isConnectedFun n g)
  (P : A × B → TypeOfHLevel ℓ (m + n)) where

  module _
    (sec : (x : PushProd f g) → P ((f ×̂ g) x) .fst) where

    private
      fam : A → Type _
      fam a = Σ[ k ∈ ((b : B) → P (a , b) .fst) ] ((y : Y) → k (g y) ≡ sec (inr (a , y)))

      open Iso

      fiberEquiv : (a : A)
        → fam a ≃ fiber (λ(s : (b : B) → P (a , b) .fst) → s ∘ g) (λ y → sec (inr (a , y)))
      fiberEquiv a =  isoToEquiv
        (iso (λ (k , p) → k , λ i y → p y i)
             (λ (k , p) → k , λ y i → p i y)
             (λ _ → refl) (λ _ → refl))

      is-m-trunc-fam : (a : A) → isOfHLevel m (fam a)
      is-m-trunc-fam a =
        isOfHLevelRespectEquiv _ (invEquiv (fiberEquiv a))
          (isOfHLevelPrecomposeConnected m n (λ b → P (a , b)) g conng _)

      sec-fam : (x : X) → fam (f x)
      sec-fam x = (λ b → sec (inl (x , b))) , (λ y i → sec (push (x , y) i))

      map-iso = elim.isIsoPrecompose f _ (λ a → fam a , is-m-trunc-fam a) connf

      k = map-iso .inv sec-fam
      ϕ = map-iso .rightInv sec-fam

    ext : (x : A × B) → P x .fst
    ext (a , b) = k a .fst b

    ext-path : (x : PushProd f g) → ext ((f ×̂ g) x) ≡ sec x
    ext-path (inl (x , b)) i = ϕ i x .fst b
    ext-path (inr (a , y)) i = k a .snd y i
    ext-path (push (x , y) i) j =
      hcomp (λ k → λ
        { (i = i0) → ϕ j x .snd y i0
        ; (i = i1) → ϕ i0 x .snd y (j ∨ ~ k)
        ; (j = i0) → ϕ i0 x .snd y (i ∧ ~ k)
        ; (j = i1) → ϕ i1 x .snd y i })
      (ϕ j x .snd y i)

  lifting : hasSection (λ(s : (x : A × B) → P x .fst) → s ∘ (f ×̂ g))
  lifting .fst sec = ext sec
  lifting .snd sec i x = ext-path sec x i

-- The connectivity of pushout-product

isConnected×̂ : {m n : ℕ}{f : A → B}{g : X → Y}
  → isConnectedFun m f → isConnectedFun n g
  → isConnectedFun (m + n) (f ×̂ g)
isConnected×̂ congf congg =
  elim.isConnectedPrecompose _ _ (lifting _ _ _ _ congf congg)
