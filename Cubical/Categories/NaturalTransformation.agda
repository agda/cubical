{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Categories.NaturalTransformation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism renaming (iso to iIso)
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Commutativity
open import Cubical.Categories.Morphism renaming (isIso to isIsoC)

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

module _ {C : Precategory ℓC ℓC'} {D : Precategory ℓD ℓD'} where
  -- syntax for sequencing in category D
  infixl 15 _⋆ᴰ_
  _⋆ᴰ_ : ∀ {x y z} (f : D [ x , y ]) (g : D [ y , z ]) → D [ x , z ]
  f ⋆ᴰ g = f ⋆⟨ D ⟩ g

  open Precategory
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
      nIso : ∀ (x : C .ob) → isIsoC {C = D} (N-ob x)

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

  open isIsoC

  -- natural isomorphism is symmetric
  symNatIso : ∀ {F G : Functor C D}
            → F ≅ᶜ G
            → G ≅ᶜ F
  symNatIso η@record { trans = record { N-ob = N-ob ; N-hom = N-hom }
                     ; nIso = nIso } = record { trans = record { N-ob = λ x → (nIso x) .inv ; N-hom = λ _ → sqLL η }
                                            ; nIso = λ x → record { inv = N-ob x ; sec = (nIso x) .ret ; ret = (nIso x) .sec } }

  -- component of a natural transformation
  infix 30 _⟦_⟧
  _⟦_⟧ : ∀ {F G : Functor C D} → (F ⇒ G) → (x : C .ob) → D [(F .F-ob x) , (G .F-ob x)]
  _⟦_⟧ = N-ob

  idTrans : (F : Functor C D) → NatTrans F F
  idTrans F .N-ob x = D .id (F .F-ob x)
  idTrans F .N-hom f =
     (F .F-hom f) ⋆ᴰ (idTrans F .N-ob _)
       ≡⟨ D .⋆IdR _ ⟩
     F .F-hom f
       ≡⟨ sym (D .⋆IdL _) ⟩
     (D .id (F .F-ob _)) ⋆ᴰ (F .F-hom f)
       ∎

  syntax idTrans F = 1[ F ]

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
  seqTransP : {F G G' H : Functor C D} {p : G ≡ G'}
            → (α : NatTrans F G) (β : NatTrans G' H)
            → NatTrans F H
  seqTransP {F} {G} {G'} {H} {p} α β .N-ob x
    -- sequence morphisms with non-judgementally equal (co)domain
    = seqP {C = D} {p = Gx≡G'x} (α ⟦ x ⟧) (β ⟦ x ⟧)
    where
      Gx≡G'x : ∀ {x} → G ⟅ x ⟆ ≡ G' ⟅ x ⟆
      Gx≡G'x {x} i = F-ob (p i) x
  seqTransP {F} {G} {G'} {H} {p} α β .N-hom {x = x} {y} f
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

  -- hmm are these judgementally equal when refl?
  -- nope
  -- does that matter? is there way to make it judgementally equal?
  -- hmm : {F G H : Functor C D} {α : NatTrans F G} {β : NatTrans G H}
  --     → seqTrans α β ≡ seqTransP {p = refl} α β
  -- hmm = {!refl!}


  module _  ⦃ D-category : isCategory D ⦄ {F G : Functor C D} {α β : NatTrans F G} where
    open Precategory
    open Functor
    open NatTrans

    makeNatTransPath : α .N-ob ≡ β .N-ob → α ≡ β
    makeNatTransPath p i .N-ob = p i
    makeNatTransPath p i .N-hom f = rem i
      where
        rem : PathP (λ i → (F .F-hom f) ⋆ᴰ (p i _) ≡ (p i _) ⋆ᴰ (G .F-hom f)) (α .N-hom f) (β .N-hom f)
        rem = toPathP (D-category .isSetHom _ _ _ _)

  module _  ⦃ D-category : isCategory D ⦄ {F F' G G' : Functor C D}
            {α : NatTrans F G}
            {β : NatTrans F' G'} where
    open Precategory
    open Functor
    open NatTrans
    makeNatTransPathP : ∀ (p : F ≡ F') (q : G ≡ G')
                      → PathP (λ i → (x : C .ob) → D [ (p i) .F-ob x , (q i) .F-ob x ]) (α .N-ob) (β .N-ob)
                      → PathP (λ i → NatTrans (p i) (q i)) α β
    makeNatTransPathP p q P i .N-ob = P i
    makeNatTransPathP p q P i .N-hom f = rem i
      where
        rem : PathP (λ i → ((p i) .F-hom f) ⋆ᴰ (P i _) ≡ (P i _) ⋆ᴰ ((q i) .F-hom f)) (α .N-hom f) (β .N-hom f)
        rem = toPathP (D-category .isSetHom _ _ _ _)
    -- makeNatTransPathP p i .N-ob = p i
    -- makeNatTransPathP p i .N-hom f = rem i
    --   where
    --     rem : PathP (λ i → (F .F-hom f) ⋆ᴰ (p i _) ≡ (p i _) ⋆ᴰ (G .F-hom f)) (α .N-hom f) (β .N-hom f)
    --     rem = toPathP (D-category .isSetHom _ _ _ _)

  -- Properties

  -- path helpers
  module NatTransP where

    module _ {F G : Functor C D} where
      open Iso

      -- same as Sigma version
      NatTransΣ = Σ[ ob ∈ ((x : C .ob) → D [(F .F-ob x) , (G .F-ob x)]) ]
                     ({x y : _ } (f : C [ x , y ]) → (F .F-hom f) ⋆ᴰ (ob y) ≡ (ob x) ⋆ᴰ (G .F-hom f))

      NatTransIsoΣ : Iso (NatTrans F G) NatTransΣ
      NatTransIsoΣ .fun (natTrans N-ob N-hom) = N-ob , N-hom
      NatTransIsoΣ .inv (N-ob , N-hom) = (natTrans N-ob N-hom)
      NatTransIsoΣ .rightInv _ = refl
      NatTransIsoΣ .leftInv _ = refl

      NatTrans≡Σ = ua (isoToEquiv NatTransIsoΣ)

      -- introducing paths
      NatTrans-≡-intro : ∀ {αo βo : N-ob-Type F G}
                           {αh : N-hom-Type F G αo}
                           {βh : N-hom-Type F G βo}
                       → (p : αo ≡ βo)
                       → PathP (λ i → ({x y : C .ob} (f : C [ x , y ]) → (F .F-hom f) ⋆ᴰ (p i y) ≡ (p i x) ⋆ᴰ (G .F-hom f))) αh βh
                       → natTrans {F = F} {G} αo αh ≡ natTrans βo βh
      NatTrans-≡-intro p q i = natTrans (p i) (q i)
    module _ {F G : Functor C D} {α β : NatTrans F G} where
      open Iso
      private
        αOb = α .N-ob
        βOb = β .N-ob
        αHom = α .N-hom
        βHom = β .N-hom
      -- path between natural transformations is the same as a pair of paths (between ob and hom)
      NTPathIsoPathΣ : Iso (α ≡ β)
                         (Σ[ p ∈ (αOb ≡ βOb) ]
                              (PathP (λ i → ({x y : _} (f : _) → F ⟪ f ⟫ ⋆ᴰ (p i y) ≡ (p i x) ⋆ᴰ G ⟪ f ⟫))
                                  αHom
                                  βHom))
      NTPathIsoPathΣ .fun p = (λ i → p i .N-ob) , (λ i → p i .N-hom)
      NTPathIsoPathΣ .inv (po , ph) i = record { N-ob = po i ; N-hom = ph i }
      NTPathIsoPathΣ .rightInv pσ = refl
      NTPathIsoPathΣ .leftInv p = refl

      NTPath≃PathΣ = isoToEquiv NTPathIsoPathΣ

      NTPath≡PathΣ = ua NTPath≃PathΣ

  module _ ⦃ isCatD : isCategory D ⦄ where
    open NatTransP

    -- if the target category has hom Sets, then any natural transformation is a set
    isSetNat : ∀ {F G : Functor C D}
             → isSet (NatTrans F G)
    isSetNat {F} {G} α β p1 p2 i = comp (λ i → NTPath≡PathΣ {F = F} {G} {α} {β} (~ i))
                                        (λ j → λ {(i = i0) → transport-filler NTPath≡PathΣ p1 (~ j) ;
                                                  (i = i1) → transport-filler NTPath≡PathΣ p2 (~ j)})
                                        (p1Σ≡p2Σ i)
      where
        αOb = α .N-ob
        βOb = β .N-ob
        αHom = α .N-hom
        βHom = β .N-hom

        -- convert to sigmas so we can reason about constituent paths separately
        p1Σ : Σ[ p ∈ (αOb ≡ βOb) ]
                (PathP (λ i → ({x y : _} (f : _) → F ⟪ f ⟫ ⋆ᴰ (p i y) ≡ (p i x) ⋆ᴰ G ⟪ f ⟫))
                      αHom
                      βHom)
        p1Σ = transport NTPath≡PathΣ p1

        p2Σ : Σ[ p ∈ (αOb ≡ βOb) ]
                (PathP (λ i → ({x y : _} (f : _) → F ⟪ f ⟫ ⋆ᴰ (p i y) ≡ (p i x) ⋆ᴰ G ⟪ f ⟫))
                       αHom
                       βHom)
        p2Σ = transport NTPath≡PathΣ p2

        -- type aliases
        typeN-ob = (x : C .ob) → D [(F .F-ob x) , (G .F-ob x)]
        typeN-hom : typeN-ob → Type _
        typeN-hom ϕ = {x y : C .ob} (f : C [ x , y ]) → (F .F-hom f) ⋆ᴰ (ϕ y) ≡ (ϕ x) ⋆ᴰ (G .F-hom f)

        -- the Ob function is a set
        isSetN-ob : isSet ((x : C .ob) → D [(F .F-ob x) , (G .F-ob x)])
        isSetN-ob = isOfHLevelΠ 2 λ _ → isCatD .isSetHom
        -- isSetN-ob f g q1 q2 i = funExt λ x → isCatD .isSetHom _ _ (q1' x) (q2' x) i
        --   where
        --     q1' = funExt⁻ q1
        --     q2' = funExt⁻ q2

        -- the Hom function is a set
        isSetN-hom : (ϕ : typeN-ob) → isSet (typeN-hom ϕ)
        isSetN-hom γ = isProp→isSet (isPropImplicitΠ λ x → isPropImplicitΠ λ y → isPropΠ λ f → isCatD .isSetHom _ _)

        -- in fact it's a dependent Set, which we need because N-hom depends on N-ob
        isSetN-homP : isOfHLevelDep 2 (λ γ → {x y : C .ob} (f : C [ x , y ]) → (F .F-hom f) ⋆ᴰ (γ y) ≡ (γ x) ⋆ᴰ (G .F-hom f))
        isSetN-homP = isOfHLevel→isOfHLevelDep 2 isSetN-hom

        -- components of the equality
        p1Ob≡p2Ob : fst p1Σ ≡ fst p2Σ
        p1Ob≡p2Ob = isSetN-ob _ _ (fst p1Σ) (fst p2Σ)

        p1Hom≡p2Hom : PathP (λ i → PathP (λ j → typeN-hom (p1Ob≡p2Ob i j)) αHom βHom)
                            (snd p1Σ) (snd p2Σ)
        p1Hom≡p2Hom = isSetN-homP _ _ (snd p1Σ) (snd p2Σ) p1Ob≡p2Ob

        p1Σ≡p2Σ : p1Σ ≡ p2Σ
        p1Σ≡p2Σ = ΣPathP (p1Ob≡p2Ob , p1Hom≡p2Hom)


private
  variable
    ℓA ℓA' ℓB ℓB' : Level

module _ {B : Precategory ℓB ℓB'} {C : Precategory ℓC ℓC'} {D : Precategory ℓD ℓD'} where
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
  (_∘ʳ_ K {G} {H} β) .N-hom f = preserveCommF {C = C} {D} {K} (β .N-hom f)





module _ (C : Precategory ℓC ℓC') (D : Precategory ℓD ℓD') ⦃ isCatD : isCategory D ⦄ where
  open Precategory
  open NatTrans
  open Functor

  FUNCTOR : Precategory (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) (ℓ-max (ℓ-max ℓC ℓC') ℓD')
  FUNCTOR .ob = Functor C D
  FUNCTOR .Hom[_,_] = NatTrans
  FUNCTOR .id = idTrans
  FUNCTOR ._⋆_ = seqTrans
  FUNCTOR .⋆IdL α = makeNatTransPath λ i x → D .⋆IdL (α .N-ob x) i
  FUNCTOR .⋆IdR α = makeNatTransPath λ i x → D .⋆IdR (α .N-ob x) i
  FUNCTOR .⋆Assoc α β γ = makeNatTransPath λ i x → D .⋆Assoc (α .N-ob x) (β .N-ob x) (γ .N-ob x) i

  instance
    isCatFUNCTOR : isCategory FUNCTOR
    isCatFUNCTOR .isSetHom = isSetNat

  open isIsoC renaming (inv to invC)
  -- component wise iso is an iso in Functor
  FUNCTORIso : ∀ {F G : Functor C D} (α : F ⇒ G)
             → (∀ (c : C .ob) → isIsoC {C = D} (α ⟦ c ⟧))
             → isIsoC {C = FUNCTOR} α
  FUNCTORIso α is .invC .N-ob c = (is c) .invC
  FUNCTORIso {F} {G} α is .invC .N-hom {c} {d} f
    = invMoveL areInv-αc
               ( α ⟦ c ⟧ ⋆⟨ D ⟩ (G ⟪ f ⟫ ⋆⟨ D ⟩ is d .invC)
               ≡⟨ sym (D .⋆Assoc _ _ _) ⟩
                 (α ⟦ c ⟧ ⋆⟨ D ⟩ G ⟪ f ⟫) ⋆⟨ D ⟩ is d .invC
               ≡⟨ sym (invMoveR areInv-αd (α .N-hom f)) ⟩
                 F ⟪ f ⟫
               ∎ )
    where
      areInv-αc : areInv (α ⟦ c ⟧) ((is c) .invC)
      areInv-αc = isIso→areInv (is c)

      areInv-αd : areInv (α ⟦ d ⟧) ((is d) .invC)
      areInv-αd = isIso→areInv (is d)
  FUNCTORIso α is .sec = makeNatTransPath (funExt (λ c → (is c) .sec))
  FUNCTORIso α is .ret = makeNatTransPath (funExt (λ c → (is c) .ret))
