{-# OPTIONS --safe #-}
module Cubical.Categories.Instances.CommRing where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Ring -- TODO: remove this dependency once code has been upstreamed

open Precategory

module _ ℓ where

  -- Lemmas about CommRingHom. TODO: upstream
  idCommRingHom : (x : CommRing ℓ) → CommRingHom x x
  idCommRingHom x = idRingHom (CommRing→Ring x)

  compCommRingHom : (x y z : CommRing ℓ)
                  → CommRingHom x y → CommRingHom y z → CommRingHom x z
  compCommRingHom x y z = compRingHom {x = CommRing→Ring x} {CommRing→Ring y} {CommRing→Ring z}

  compIdCommRingHom : {x y : CommRing ℓ} (f : CommRingHom x y) → compCommRingHom x x y (idCommRingHom x) f ≡ f
  compIdCommRingHom = compIdRingHom

  idCompCommRingHom : {x y : CommRing ℓ} (f : CommRingHom x y) → compCommRingHom x y y f (idCommRingHom y) ≡ f
  idCompCommRingHom = idCompRingHom

  compAssocCommRingHom : {x y z w : CommRing ℓ} (f : CommRingHom x y) (g : CommRingHom y z) (h : CommRingHom z w) →
                         compCommRingHom x z w (compCommRingHom x y z f g) h ≡
                         compCommRingHom x y w f (compCommRingHom y z w g h)
  compAssocCommRingHom = compAssocRingHom

  CommRingPrecategory : Precategory (ℓ-suc ℓ) ℓ
  ob CommRingPrecategory                     = CommRing ℓ
  Hom[_,_] CommRingPrecategory               = CommRingHom
  id CommRingPrecategory                     = idCommRingHom
  _⋆_ CommRingPrecategory {x} {y} {z}        = compCommRingHom x y z
  ⋆IdL CommRingPrecategory {x} {y}           = compIdCommRingHom {x} {y}
  ⋆IdR CommRingPrecategory {x} {y}           = idCompCommRingHom {x} {y}
  ⋆Assoc CommRingPrecategory {x} {y} {z} {w} = compAssocCommRingHom {x} {y} {z} {w}
