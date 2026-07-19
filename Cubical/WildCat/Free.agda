{-
  This file defines a wild category, which might be the free wild category over a
  directed graph (I do not know). This is intended to be used in a solver for
  wild categories.
-}

module Cubical.WildCat.Free where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Graph.Base
open import Cubical.Data.Graph.Path renaming (Path to GPath)

open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor
open import Cubical.WildCat.UnderlyingGraph

open WildCat
open WildFunctor
open Graph

private
  variable
    ℓc ℓc' ℓd ℓd' ℓg ℓg' : Level

Free : (G : Graph ℓg ℓg') → WildCat ℓg (ℓ-max ℓg ℓg')
ob (Free G) = G .Node
Hom[_,_] (Free G) x y = GPath G x y
id (Free G) = pnil
_⋆_ (Free G) f g = f ++ g
⋆IdL (Free G) = λ _ → refl
⋆IdR (Free G) = ++pnil
⋆Assoc (Free G) f g h = ++assoc f g h

composeAll : (C : WildCat ℓc ℓc') {x y : ob C} → GPath (Cat→Graph C) x y → C [ x , y ]
composeAll C pnil = id C
composeAll C (pcons m path) = m ⋆⟨ C ⟩ composeAll C path


composeAll++ : (C : WildCat ℓc ℓc') {x y z : ob C}
               → (p : GPath (Cat→Graph C) x y) → (q : GPath (Cat→Graph C) y z)
               → composeAll C (p ++ q) ≡ composeAll C p ⋆⟨ C ⟩ composeAll C q
composeAll++ C pnil q = sym (⋆IdL C (composeAll C q))
composeAll++ C (pcons m p) q =
  composeAll C (pcons m p ++ q)                       ≡⟨ step1 ⟩
  m ⋆⟨ C ⟩ ((composeAll C p) ⋆⟨ C ⟩ (composeAll C q)) ≡⟨ sym (⋆Assoc C m (composeAll C p) (composeAll C q)) ⟩
  (m ⋆⟨ C ⟩ (composeAll C p)) ⋆⟨ C ⟩ (composeAll C q) ∎
  where step1 = cong (λ z → concatMor C m z) (composeAll++ C p q)

module UniversalProperty (G : Graph ℓg ℓg') where


  incFree : GraphHom G (Cat→Graph (Free G))
  incFree $g x = x
  incFree <$g> e = pcons e pnil

  {-
     G ──→ Free G
      \    ∣
   ∀ F \   ∣ ∃ F'
        ↘  ↓
          C
  -}
  inducedMorphism : (C : WildCat ℓc ℓc') → GraphHom G (Cat→Graph C) → WildFunctor (Free G) C
  inducedMorphism C F = F'
    where F' : WildFunctor (Free G) C
          F-ob F' x = F $g x
          F-hom F' m = composeAll C (map F m)
          F-id F' = refl
          F-seq F' f g =
            composeAll C (map F (f ⋆⟨ Free G ⟩ g))                  ≡⟨ cong (λ u → composeAll C u) (map++ F f g) ⟩
            composeAll C (map F f ++ map F g)                       ≡⟨ composeAll++ C (map F f) (map F g) ⟩
            (composeAll C (map F f)) ⋆⟨ C ⟩ (composeAll C (map F g)) ∎
