{-# OPTIONS --safe #-}

module Cubical.WildCat.UnderlyingGraph where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Graph.Base
open import Cubical.Data.Graph.Reflexive

open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor

private
  variable
    ℓc ℓc' ℓd ℓd' ℓe ℓe' ℓg ℓg' : Level

open WildCat

-- Underlying graph of a category
Cat→Graph : ∀ {ℓc ℓc'} (𝓒 : WildCat ℓc ℓc') → Graph ℓc ℓc'
Cat→Graph 𝓒 .Node = 𝓒 .ob
Cat→Graph 𝓒 .Edge = 𝓒 .Hom[_,_]

Functor→GraphHom : ∀ {ℓc ℓc' ℓd ℓd'} {𝓒 : WildCat ℓc ℓc'} {𝓓 : WildCat ℓd ℓd'}
       (F : WildFunctor 𝓒 𝓓) → GraphHom (Cat→Graph 𝓒) (Cat→Graph 𝓓)
Functor→GraphHom F ._$g_ = WildFunctor.F-ob F
Functor→GraphHom F ._<$g>_ = WildFunctor.F-hom F


-- Underlying reflexive graph of a category
Cat→RGraph : ∀ {ℓc ℓc'} (𝓒 : WildCat ℓc ℓc') → RGraph ℓc ℓc'
Cat→RGraph 𝓒 .Node = 𝓒 .ob
Cat→RGraph 𝓒 .Edge = 𝓒 .Hom[_,_]
Cat→RGraph 𝓒 .Refl = λ n → 𝓒 .id {n}

Functor→RGraphHom : ∀ {ℓc ℓc' ℓd ℓd'} {𝓒 : WildCat ℓc ℓc'} {𝓓 : WildCat ℓd ℓd'}
       (F : WildFunctor 𝓒 𝓓) → RGraphHom (Cat→RGraph 𝓒) (Cat→RGraph 𝓓)
Functor→RGraphHom F ._$g_ = WildFunctor.F-ob F
Functor→RGraphHom F ._<$g>_ = WildFunctor.F-hom F
Functor→RGraphHom F .presRefl =  λ x → WildFunctor.F-id F {x}
