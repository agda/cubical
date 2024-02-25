-- | A Relator contravariant in C and covariant in D is
-- | a bifunctor C ^op x D → Set.

-- | This is equivalent to a functor D → Psh(C), but some concepts are
-- | more naturally formulated in these terms.

-- | Furthermore, we use the Redundant definition of Bifunctors,
-- | whereas the category of presheaves as defined currently in the
-- | library only gives the "separate" functorial action. In practice,
-- | relators tend to only come with a separate action anyway (e.g.,
-- | Hom) but in principle
{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.Profunctor.Relator where

open import Cubical.Reflection.RecordEquiv

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function renaming (_∘_ to _∘f_)

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Functor
open import Cubical.Categories.Bifunctor.Redundant
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Constructions.BinProduct.More
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Data.Sigma

open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Instances.Functors.More

private
  variable
    ℓB ℓB' ℓC ℓC' ℓD ℓD' ℓS ℓR : Level

_o-[_]-*_ : (C : Category ℓC ℓC') → ∀ ℓS → (D : Category ℓD ℓD') → Type _
C o-[ ℓS ]-* D = Bifunctor (C ^op) D (SET ℓS)

Relatoro* : (C : Category ℓC ℓC') → ∀ ℓS → (D : Category ℓD ℓD') → Type _
Relatoro* C ℓS D = C o-[ ℓS ]-* D

module _ {C : Category ℓC ℓC'} {ℓS} {D : Category ℓD ℓD'} where
  Profunctor→Relator : Profunctor C D ℓS → D o-[ ℓS ]-* C
  Profunctor→Relator P = Sym (CurriedToBifunctor P)

  Relator→Profunctor : D o-[ ℓS ]-* C → Profunctor C D ℓS
  Relator→Profunctor R = CurryBifunctor (Sym R)

module _ {C : Category ℓC ℓC'} (R : C o-[ ℓS ]-* C) where
  private
    module C = Category C
    module R = Bifunctor R
  -- Natural Element of a profunctor
  -- Example: A natural transformation F ⇒ G is
  -- a natural element of Hom[ F , G ]

  -- Note this is a "redundant" definition, it specifies an action on
  -- objects and an action on morphisms and asks that they agree up to
  -- Path
  record NatElt : Type (ℓ-max (ℓ-max ℓC ℓC') ℓS) where
    field
      N-ob  : (x : C.ob) → ⟨ R ⟅ x , x ⟆b ⟩
      -- It may be useful to include this
      N-hom× : {x y : C.ob}(f : C [ x , y ]) → ⟨ R ⟅ x , y ⟆b ⟩

      N-ob-hom×-agree : {x : C.ob} → N-hom× C.id ≡ N-ob x

      N-natL : {x y : C.ob}(f : C [ x , y ])
             → R.Bif-homL f y (N-ob y) ≡ N-hom× f

      N-natR : {x y : C.ob}(f : C [ x , y ])
             → N-hom× f ≡ R.Bif-homR x f (N-ob x)

    N-LR-agree : {x y : C.ob}(f : C [ x , y ])
               → R.Bif-homL f y (N-ob y) ≡ R.Bif-homR x f (N-ob x)
    N-LR-agree f = N-natL f ∙ N-natR f

    N-hom×-fuseL : {w x y : C.ob}(e : C [ w , x ])(f : C [ x , y ])
                 → R.Bif-homL e y (N-hom× f) ≡ N-hom× (e C.⋆ f)
    N-hom×-fuseL e f =
      cong (R.Bif-homL e _) (sym (N-natL f))
      ∙ sym (funExt⁻ (R.Bif-L-seq _ _) (N-ob _))
      ∙ N-natL _

    N-hom×-fuseR : {x y z : C.ob}(f : C [ x , y ])(g : C [ y , z ])
                 → R.Bif-homR x g (N-hom× f) ≡ N-hom× (f C.⋆ g)
    N-hom×-fuseR f g =
      cong (R.Bif-homR _ _) (N-natR f)
      ∙ sym (funExt⁻ (R.Bif-R-seq _ _) (N-ob _))
      ∙ sym (N-natR _)

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
         {R : D o-[ ℓS ]-* D}
         (α : NatElt R) (F : Functor C D) where
  private
    module F = Functor F
    module α = NatElt α
  whisker : NatElt (R ∘Flr (F ^opF , F))
  whisker .NatElt.N-ob c = α.N-ob (F ⟅ c ⟆)
  whisker .NatElt.N-hom× f = α.N-hom× (F ⟪ f ⟫)
  whisker .NatElt.N-ob-hom×-agree =
    cong α.N-hom× F.F-id
    ∙ α.N-ob-hom×-agree
  whisker .NatElt.N-natL f = α.N-natL _
  whisker .NatElt.N-natR f = α.N-natR _

Hom : (C : Category ℓC ℓC') → C o-[ ℓC' ]-* C
Hom = HomBif

NatElt→NatTrans :
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  {F : Functor C D}{G : Functor C D}
  → NatElt (Hom D ∘Flr (F ^opF , G)) → NatTrans F G
NatElt→NatTrans ε .NatTrans.N-ob = ε .NatElt.N-ob
NatElt→NatTrans ε .NatTrans.N-hom = NatElt.N-LR-agree ε
