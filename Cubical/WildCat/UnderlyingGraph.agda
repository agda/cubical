
module Cubical.WildCat.UnderlyingGraph where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Graph.Base

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


module _ (G : Graph ℓg ℓg') (𝓒 : WildCat ℓc ℓc') where
  -- Interpretation of a graph in a wild category
  Interpret : Type _
  Interpret = GraphHom G (Cat→Graph 𝓒)


_⋆Interpret_ : ∀ {G : Graph ℓg ℓg'}
              {𝓒 : WildCat ℓc ℓc'}
              {𝓓 : WildCat ℓd ℓd'}
              (ı : Interpret G 𝓒)
              (F : WildFunctor 𝓒 𝓓)
              → Interpret G 𝓓
(ı ⋆Interpret F) ._$g_ x = WildFunctor.F-ob F (ı $g x)
(ı ⋆Interpret F) ._<$g>_ e = WildFunctor.F-hom F (ı <$g> e)

_∘Interpret_ : ∀ {G : Graph ℓg ℓg'}
              {𝓒 : WildCat ℓc ℓc'}
              {𝓓 : WildCat ℓd ℓd'}
              (F : WildFunctor 𝓒 𝓓)
              (ı : Interpret G 𝓒)
              → Interpret G 𝓓
F ∘Interpret ı = ı ⋆Interpret F
