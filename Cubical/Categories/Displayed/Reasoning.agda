{-
Helping equational reasoning in displayed categories.

The main proof engineering insight here is that we don't want to let Agda infer
metavariables all the time for the base paths.
The naive approach would be to work with the indexed (f ≡[ p ] g), where the p
ends up being inferred for every operation (we don't want to supply the
equations over which the displayed ones live). However, the performance hit is
enormous, making it completely unusable for longer chains of equalities!

Instead, we just work in the total category (∫C Cᴰ), giving access to the
usual categorical reasoning tools, and project out at the end. This way, we
carry around the base morphisms and paths as *data* rather than just re-inferring
them all the time. This has very good performance while letting us freely use
implicit arguments for e.g. ⋆Assoc.
-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Transport

open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.TotalCategory.Base
open import Cubical.Categories.Displayed.Base

module Cubical.Categories.Displayed.Reasoning
  {ℓC ℓ'C ℓCᴰ ℓ'Cᴰ : Level}
  {C : Category ℓC ℓ'C}
  (Cᴰ : Categoryᴰ C ℓCᴰ ℓ'Cᴰ)
  where

  open Categoryᴰ Cᴰ
  private module C = Category C
  open Category hiding (_∘_)

  -- We give access to usual categorical operations of the total category
  -- directly through this module.
  open Category (∫C Cᴰ) public

  -- Shorthand to introduce a displayed equality into the reasoning machine
  ≡in : {a b : C.ob} {f g : C [ a , b ]}
        {aᴰ : ob[ a ]} {bᴰ : ob[ b ]}
        {fᴰ : Hom[ f ][ aᴰ , bᴰ ]}
        {gᴰ : Hom[ g ][ aᴰ , bᴰ ]}
        {p : f ≡ g}
      → (fᴰ ≡[ p ] gᴰ)
      → (f , fᴰ) ≡ (g , gᴰ)
  ≡in e = ΣPathP (_ , e)

  -- Shorthand to produce a displayed equality out of the reasoning machine
  ≡out : {a b : C.ob} {f g : C [ a , b ]}
         {aᴰ : ob[ a ]} {bᴰ : ob[ b ]}
         {fᴰ : Hom[ f ][ aᴰ , bᴰ ]}
         {gᴰ : Hom[ g ][ aᴰ , bᴰ ]}
       → (e : (f , fᴰ) ≡ (g , gᴰ))
       → (fᴰ ≡[ fst (PathPΣ e) ] gᴰ)
  ≡out e = snd (PathPΣ e)

  -- Reindexing displayed morphisms along an equality in the base
  reind : {a b : C.ob} {f g : C [ a , b ]} (p : f ≡ g)
      {aᴰ : ob[ a ]} {bᴰ : ob[ b ]}
    → Hom[ f ][ aᴰ , bᴰ ] → Hom[ g ][ aᴰ , bᴰ ]
  reind p = subst Hom[_][ _ , _ ] p

  -- Filler for the above, directly in the reasoning machine
  reind-filler : {a b : C.ob} {f g : C [ a , b ]} (p : f ≡ g)
      {aᴰ : ob[ a ]} {bᴰ : ob[ b ]}
      (fᴰ : Hom[ f ][ aᴰ , bᴰ ])
    → (f , fᴰ) ≡ (g , reind p fᴰ)
  reind-filler p fᴰ = ΣPathP (p , subst-filler Hom[_][ _ , _ ] p fᴰ)

  -- Rectify the base equality of dependent equalities to whatever we want
  rectify : {a b : C.ob} {f g : C [ a , b ]} {p p' : f ≡ g}
      {aᴰ : ob[ a ]} {bᴰ : ob[ b ]}
      {fᴰ : Hom[ f ][ aᴰ , bᴰ ]}
      {gᴰ : Hom[ g ][ aᴰ , bᴰ ]}
    → fᴰ ≡[ p ] gᴰ → fᴰ ≡[ p' ] gᴰ
  rectify {fᴰ = fᴰ} {gᴰ = gᴰ} = subst (fᴰ ≡[_] gᴰ) (C.isSetHom _ _ _ _)
