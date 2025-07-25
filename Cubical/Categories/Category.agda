{-
  Definition of various kinds of categories.

  This library partially follows the UniMath terminology:

  Concept              Ob C   Hom C  Univalence

  Wild Category        Type   Type   No           (called precategory in UniMath)
  Category             Type   Set    No
  Univalent Category   Type   Set    Yes

  The most useful notion is Category and the library is hence based on
  them. If one needs wild categories then they can be found in
  Cubical.WildCat (so it's not considered part of the Categories sublibrary!)

-}
module Cubical.Categories.Category where

open import Cubical.Categories.Category.Base public
open import Cubical.Categories.Category.Properties public
