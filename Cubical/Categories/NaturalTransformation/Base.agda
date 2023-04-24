{-# OPTIONS --safe #-}
module Cubical.Categories.NaturalTransformation.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism renaming (iso to iIso)
open import Cubical.Data.Sigma
open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functor.Properties
open import Cubical.Categories.Commutativity
open import Cubical.Categories.Morphism
open import Cubical.Categories.Isomorphism

private
  variable
    ℓA ℓA' ℓB ℓB' ℓC ℓC' ℓD ℓD' : Level

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} where
  -- syntax for sequencing in category D
  infixl 15 _⋆ᴰ_
  private
    _⋆ᴰ_ : ∀ {x y z} (f : D [ x , y ]) (g : D [ y , z ]) → D [ x , z ]
    f ⋆ᴰ g = f ⋆⟨ D ⟩ g

  open Category
  open Functor

  -- type aliases because it gets tedious typing it out all the time
  N-ob-Type : (F G : Functor C D) → Type _
  N-ob-Type F G = (x : C .ob) → D [(F .F-ob x) , (G .F-ob x)]

  N-hom-Type : (F G : Functor C D) → N-ob-Type F G → Type _
  N-hom-Type F G ϕ = {x y : C .ob} (f : C [ x , y ]) → (F .F-hom f) ⋆ᴰ (ϕ y) ≡ (ϕ x) ⋆ᴰ (G .F-hom f)

  record NatTrans (F G : Functor C D) : Type (ℓ-max (ℓ-max ℓC ℓC') ℓD') where
    constructor natTrans
    field
      -- components of the natural transformation
      N-ob : N-ob-Type F G
      -- naturality condition
      N-hom :  N-hom-Type F G N-ob

  record NatIso (F G : Functor C D): Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
    field
      trans : NatTrans F G
    open NatTrans trans

    field
      nIso : ∀ (x : C .ob) → isIsoC D (N-ob x)

    open isIsoC

    -- the three other commuting squares
    sqRL : ∀ {x y : C .ob} {f : C [ x , y ]}
         → F ⟪ f ⟫ ≡ (N-ob x) ⋆ᴰ G ⟪ f ⟫ ⋆ᴰ (nIso y) .inv
    sqRL {x} {y} {f} = invMoveR (isIso→areInv (nIso y)) (N-hom f)

    sqLL : ∀ {x y : C .ob} {f : C [ x , y ]}
         → G ⟪ f ⟫ ⋆ᴰ (nIso y) .inv ≡ (nIso x) .inv ⋆ᴰ F ⟪ f ⟫
    sqLL {x} {y} {f} = invMoveL (isIso→areInv (nIso x)) (sym sqRL')
      where
        sqRL' : F ⟪ f ⟫ ≡ (N-ob x) ⋆ᴰ ( G ⟪ f ⟫ ⋆ᴰ (nIso y) .inv )
        sqRL' = sqRL ∙ (D .⋆Assoc _ _ _)

    sqLR : ∀ {x y : C .ob} {f : C [ x , y ]}
         → G ⟪ f ⟫ ≡ (nIso x) .inv ⋆ᴰ F ⟪ f ⟫ ⋆ᴰ (N-ob y)
    sqLR {x} {y} {f} = invMoveR (symAreInv (isIso→areInv (nIso y))) sqLL

  open NatTrans
  open NatIso

  infix 10 NatTrans
  syntax NatTrans F G = F ⇒ G

  infix 9 NatIso
  syntax NatIso F G = F ≅ᶜ G -- c superscript to indicate that this is in the context of categories

  -- component of a natural transformation
  infix 30 _⟦_⟧
  _⟦_⟧ : ∀ {F G : Functor C D} → F ⇒ G → (x : C .ob) → D [ F .F-ob x , G .F-ob x ]
  _⟦_⟧ = N-ob

  idTrans : (F : Functor C D) → NatTrans F F
  idTrans F .N-ob x  = D .id
  idTrans F .N-hom f =
      (F .F-hom f) ⋆ᴰ (idTrans F .N-ob _)
    ≡⟨ D .⋆IdR _ ⟩
      F .F-hom f
    ≡⟨ sym (D .⋆IdL _) ⟩
      (D .id) ⋆ᴰ (F .F-hom f)
    ∎

  syntax idTrans F = 1[ F ]

  idNatIso : (F : Functor C D) → NatIso F F
  idNatIso F .trans = idTrans F
  idNatIso F .nIso _ = idCatIso .snd


  -- Natural isomorphism induced by path of functors

  pathToNatTrans : {F G : Functor C D} → F ≡ G → NatTrans F G
  pathToNatTrans p .N-ob x = pathToIso {C = D} (λ i → p i .F-ob x) .fst
  pathToNatTrans {F = F} {G = G} p .N-hom {x = x} {y = y} f =
    pathToIso-Comm {C = D} _ _ _ _ (λ i → p i .F-hom f)

  pathToNatIso : {F G : Functor C D} → F ≡ G → NatIso F G
  pathToNatIso p .trans = pathToNatTrans p
  pathToNatIso p .nIso x = pathToIso {C = D} _ .snd


  -- vertical sequencing
  seqTrans : {F G H : Functor C D} (α : NatTrans F G) (β : NatTrans G H) → NatTrans F H
  seqTrans α β .N-ob x = (α .N-ob x) ⋆ᴰ (β .N-ob x)
  seqTrans {F} {G} {H} α β .N-hom f =
    (F .F-hom f) ⋆ᴰ ((α .N-ob _) ⋆ᴰ (β .N-ob _))
      ≡⟨ sym (D .⋆Assoc _ _ _) ⟩
    ((F .F-hom f) ⋆ᴰ (α .N-ob _)) ⋆ᴰ (β .N-ob _)
      ≡[ i ]⟨ (α .N-hom f i) ⋆ᴰ (β .N-ob _) ⟩
    ((α .N-ob _) ⋆ᴰ (G .F-hom f)) ⋆ᴰ (β .N-ob _)
      ≡⟨ D .⋆Assoc _ _ _ ⟩
    (α .N-ob _) ⋆ᴰ ((G .F-hom f) ⋆ᴰ (β .N-ob _))
      ≡[ i ]⟨ (α .N-ob _) ⋆ᴰ (β .N-hom f i) ⟩
    (α .N-ob _) ⋆ᴰ ((β .N-ob _) ⋆ᴰ (H .F-hom f))
      ≡⟨ sym (D .⋆Assoc _ _ _) ⟩
    ((α .N-ob _) ⋆ᴰ (β .N-ob _)) ⋆ᴰ (H .F-hom f)
      ∎

  compTrans : {F G H : Functor C D} (β : NatTrans G H) (α : NatTrans F G) → NatTrans F H
  compTrans β α = seqTrans α β

  infixl 8 seqTrans
  syntax seqTrans α β = α ●ᵛ β


  -- vertically sequence natural transformations whose
  -- common functor is not definitional equal
  seqTransP : {F G G' H : Functor C D} (p : G ≡ G')
            → (α : NatTrans F G) (β : NatTrans G' H)
            → NatTrans F H
  seqTransP {F} {G} {G'} {H} p α β .N-ob x
    -- sequence morphisms with non-judgementally equal (co)domain
    = seqP {C = D} {p = Gx≡G'x} (α ⟦ x ⟧) (β ⟦ x ⟧)
    where
      Gx≡G'x : ∀ {x} → G ⟅ x ⟆ ≡ G' ⟅ x ⟆
      Gx≡G'x {x} i = F-ob (p i) x
  seqTransP {F} {G} {G'} {H} p α β .N-hom {x = x} {y} f
    -- compose the two commuting squares
    -- 1. α's commuting square
    -- 2. β's commuting square, but extended to G since β is only G' ≡> H
    = compSq {C = D} (α .N-hom f) βSq
    where
      -- functor equality implies equality of actions on objects and morphisms
      Gx≡G'x : G ⟅ x ⟆ ≡ G' ⟅ x ⟆
      Gx≡G'x i = F-ob (p i) x

      Gy≡G'y : G ⟅ y ⟆ ≡ G' ⟅ y ⟆
      Gy≡G'y i = F-ob (p i) y

      Gf≡G'f : PathP (λ i → D [ Gx≡G'x i , Gy≡G'y i ]) (G ⟪ f ⟫) (G' ⟪ f ⟫)
      Gf≡G'f i = p i ⟪ f ⟫

      -- components of β extended out to Gx and Gy respectively
      βx' = subst (λ a → D [ a , H ⟅ x ⟆ ]) (sym Gx≡G'x) (β ⟦ x ⟧)
      βy' = subst (λ a → D [ a , H ⟅ y ⟆ ]) (sym Gy≡G'y) (β ⟦ y ⟧)

      -- extensions are equal to originals
      βy'≡βy : PathP (λ i → D [ Gy≡G'y i , H ⟅ y ⟆ ]) βy' (β ⟦ y ⟧)
      βy'≡βy = symP (toPathP {A = λ i → D [ Gy≡G'y (~ i) , H ⟅ y ⟆ ]} refl)

      βx≡βx' : PathP (λ i → D [ Gx≡G'x (~ i) , H ⟅ x ⟆ ]) (β ⟦ x ⟧) βx'
      βx≡βx' = toPathP refl

      -- left wall of square
      left : PathP (λ i → D [ Gx≡G'x i , H ⟅ y ⟆ ]) (G ⟪ f ⟫ ⋆⟨ D ⟩ βy') (G' ⟪ f ⟫ ⋆⟨ D ⟩ β ⟦ y ⟧)
      left i = Gf≡G'f i ⋆⟨ D ⟩ βy'≡βy i

      -- right wall of square
      right : PathP (λ i → D [ Gx≡G'x (~ i) , H ⟅ y ⟆ ]) (β ⟦ x ⟧ ⋆⟨ D ⟩ H ⟪ f ⟫) (βx' ⋆⟨ D ⟩ H ⟪ f ⟫)
      right i = βx≡βx' i ⋆⟨ D ⟩ refl {x = H ⟪ f ⟫} i

      -- putting it all together
      βSq : G ⟪ f ⟫ ⋆⟨ D ⟩ βy' ≡ βx' ⋆⟨ D ⟩ H ⟪ f ⟫
      βSq i = comp (λ k → D [ Gx≡G'x (~ k) , H ⟅ y ⟆ ])
                   (λ j → λ { (i = i0) → left (~ j)
                            ; (i = i1) → right j })
                   (β .N-hom f i)

  module _ {F G : Functor C D} {α β : NatTrans F G} where
    open Category
    open Functor
    open NatTrans

    makeNatTransPath : α .N-ob ≡ β .N-ob → α ≡ β
    makeNatTransPath p i .N-ob = p i
    makeNatTransPath p i .N-hom f = rem i
      where
        rem : PathP (λ i → (F .F-hom f) ⋆ᴰ (p i _) ≡ (p i _) ⋆ᴰ (G .F-hom f))
                    (α .N-hom f) (β .N-hom f)
        rem = toPathP (D .isSetHom _ _ _ _)


  -- `constructor` for path of natural isomorphisms
  NatIso≡ : {F G : Functor C D}{f g : NatIso F G} → f .trans .N-ob ≡ g .trans .N-ob → f ≡ g
  NatIso≡ {f = f} {g} p i .trans = makeNatTransPath {α = f .trans} {β = g .trans} p i
  NatIso≡ {f = f} {g} p i .nIso x =
    isProp→PathP (λ i → isPropIsIso (NatIso≡ {f = f} {g} p i .trans .N-ob x)) (f .nIso _) (g .nIso _) i


  module _  {F F' G G' : Functor C D} {α : NatTrans F G} {β : NatTrans F' G'} where
    open Category
    open Functor
    open NatTrans
    makeNatTransPathP : ∀ (p : F ≡ F') (q : G ≡ G')
                      → PathP (λ i → (x : C .ob) → D [ (p i) .F-ob x , (q i) .F-ob x ])
                              (α .N-ob) (β .N-ob)
                      → PathP (λ i → NatTrans (p i) (q i)) α β
    makeNatTransPathP p q P i .N-ob = P i
    makeNatTransPathP p q P i .N-hom f = rem i
      where
        rem : PathP (λ i → ((p i) .F-hom f) ⋆ᴰ (P i _) ≡ (P i _) ⋆ᴰ ((q i) .F-hom f))
                    (α .N-hom f) (β .N-hom f)
        rem = toPathP (D .isSetHom _ _ _ _)

module _ {B : Category ℓB ℓB'} {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} where
  open NatTrans
  -- whiskering
  -- αF
  _∘ˡ_ : ∀ {G H : Functor C D} (α : NatTrans G H) → (F : Functor B C)
        → NatTrans (G ∘F F) (H ∘F F)
  (_∘ˡ_ {G} {H} α F) .N-ob x = α ⟦ F ⟅ x ⟆ ⟧
  (_∘ˡ_ {G} {H} α F) .N-hom f = (α .N-hom) _

  -- Kβ
  _∘ʳ_ : ∀ (K : Functor C D) → {G H : Functor B C} (β : NatTrans G H)
       → NatTrans (K ∘F G) (K ∘F H)
  (_∘ʳ_ K {G} {H} β) .N-ob x = K ⟪ β ⟦ x ⟧ ⟫
  (_∘ʳ_ K {G} {H} β) .N-hom f = preserveCommF {C = C} {D = D} {K} (β .N-hom f)

  whiskerTrans : {F F' : Functor B C} {G G' : Functor C D} (β : NatTrans G G') (α : NatTrans F F')
    → NatTrans (G ∘F F) (G' ∘F F')
  whiskerTrans {F}{F'}{G}{G'} β α = compTrans (β ∘ˡ F') (G ∘ʳ α)
