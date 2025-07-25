module Cubical.Data.Graph.Displayed where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Graph.Base
open import Cubical.Data.Sigma
open import Cubical.Categories.Category.Base
open import Cubical.Categories.UnderlyingGraph
open import Cubical.Categories.Displayed.Base

private
  variable
    ℓc ℓc' ℓcᴰ ℓcᴰ' ℓd ℓd' ℓg ℓg' ℓgᴰ ℓgᴰ' ℓh ℓh' ℓhᴰ ℓhᴰ' ℓj ℓ : Level

open Graph
module _ (G : Graph ℓg ℓg') where
  record Graphᴰ ℓgᴰ ℓgᴰ' : Type (ℓ-max (ℓ-max ℓg ℓg') (ℓ-suc (ℓ-max ℓgᴰ ℓgᴰ')))
         where
    no-eta-equality
    field
      Node[_] : G .Node → Type ℓgᴰ
      Edge[_][_,_] : ∀ {u v} (e : G .Edge u v) (uᴰ : Node[ u ]) (vᴰ : Node[ v ])
                   → Type ℓgᴰ'

open Graphᴰ
open Categoryᴰ

module _ {G : Graph ℓg ℓg'}{H : Graph ℓh ℓh'}
         (ϕ : GraphHom G H)
         (Hᴰ : Graphᴰ H ℓhᴰ ℓhᴰ')
         where
  private
    module G = Graph G
    module Hᴰ = Graphᴰ Hᴰ
  open GraphHom
  record Section : Type (ℓ-max (ℓ-max ℓg ℓg')
                        (ℓ-max (ℓ-max ℓh ℓh')
                        (ℓ-max ℓhᴰ ℓhᴰ'))) where
    field
      _$gᴰ_ : ∀ (u : G.Node) → Hᴰ.Node[ ϕ $g u ]
      _<$g>ᴰ_ :
        ∀ {u v : G.Node} → (e : G.Edge u v)
        → Hᴰ.Edge[ ϕ <$g> e ][ _$gᴰ_ u , _$gᴰ_ v ]

Categoryᴰ→Graphᴰ : {C : Category ℓc ℓc'}(Cᴰ : Categoryᴰ C ℓcᴰ ℓcᴰ')
                 → Graphᴰ (Cat→Graph C) ℓcᴰ ℓcᴰ'
Categoryᴰ→Graphᴰ Cᴰ .Node[_] = Cᴰ .ob[_]
Categoryᴰ→Graphᴰ Cᴰ .Edge[_][_,_] = Cᴰ .Hom[_][_,_]

-- TODO: CatSection→GrSection

