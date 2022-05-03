{-
  Definition of various kinds of categories.

  This library follows the UniMath terminology, that is:

  Concept              Ob C   Hom C  Univalence

  Precategory          Type   Type   No
  Category             Type   Set    No
  Univalent Category   Type   Set    Yes

  The most useful notion is Category and the library is hence based on
  them. If one needs precategories then they can be found in
  Cubical.Categories.Category.Precategory

-}
{-# OPTIONS --safe #-}
module Cubical.Categories.Category where

open import Cubical.Categories.Category.Base public
open import Cubical.Categories.Category.Properties public
