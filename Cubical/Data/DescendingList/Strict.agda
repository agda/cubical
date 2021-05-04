------------------------------------------------------------------------
-- Strictly descending lists
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Cubical.Core.Everything

module Cubical.Data.DescendingList.Strict
 (A : Type₀)
 (_>_ : A → A → Type₀)
 where

open import Cubical.Data.DescendingList.Base A _>_ renaming (_≥ᴴ_ to _>ᴴ_; ≥ᴴ[] to >ᴴ[]; ≥ᴴcons to >ᴴcons; DL to SDL) using ([]; cons) public
