------------------------------------------------------------------------
-- Descending lists
------------------------------------------------------------------------


open import Cubical.Foundations.Prelude


module Cubical.Data.DescendingList.Base
 (A : Type₀)
 (_≥_ : A → A → Type₀)
 where

------------------------------------------------------------------------
-- Descending lists
--
-- Defined simultaneously with the relation "x ≥ the HEAD of u"

data DL : Type₀
data _≥ᴴ_ (x : A) : DL → Type₀

data DL where
 []   : DL
 cons : (x : A) (u : DL) → x ≥ᴴ u → DL

data _≥ᴴ_ x where
 ≥ᴴ[]   : x ≥ᴴ []
 ≥ᴴcons : {y : A} {u : DL} {r : y ≥ᴴ u}
         → x ≥ y → x ≥ᴴ (cons y u r)

[_] : A → DL
[ x ] = cons x [] ≥ᴴ[]
