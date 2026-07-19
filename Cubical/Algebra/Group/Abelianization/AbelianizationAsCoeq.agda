{-

This file contains:
    - the abelianization of groups as a coequalizer of sets as performed
      in https://1lab.dev/Algebra.Group.Ab.Free.html
    - the proof that this way of defining the abelianization of groups is equivalent to defining
      it as a HIT, more precisely that there is a unique isomorphism between the resulting
      abelian groups

-}
module Cubical.Algebra.Group.Abelianization.AbelianizationAsCoeq where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
  using (isPropIsGroupHom; compGroupHom; idGroupHom; compGroupHomAssoc; invGroupIso;
         compGroupHomId; GroupIso≡; GroupIso→GroupHom)

open import Cubical.Algebra.AbGroup.Base

open import Cubical.HITs.SetCoequalizer

open import Cubical.Algebra.Group.Abelianization.Base
  renaming (Abelianization to HITAbelianization;
            η to HITη;
            comm to HITcomm;
            isset to HITisset)

open import Cubical.Algebra.Group.Abelianization.Properties
  hiding (elimProp; elimProp2; elimProp3; elimContr; elimContr2; rec; rec2)
  renaming (AbelianizationAbGroup to HITasAbelianGroup;
            AbelianizationHom to HITηAsGroupHom)
open Cubical.Algebra.Group.Abelianization.Properties.UniversalProperty
  renaming (inducedHom to HITinducedHom;
            commutativity to HITcommutativity;
            uniqueness to HITuniqueness)

private
  variable
    ℓ : Level
    G : Group ℓ

module AbelianizationAsCoeq (G : Group ℓ) where
  open GroupStr {{...}}
  open GroupTheory G
  private
    instance
      _ = snd G
    G' = fst G

  {-
    The definition of the abelianization of a group as a coequalizer of sets. The generality
    of the coequalized functions will be needed to define the group structure on the
    abelianization.
  -}
  Abelianization : Type ℓ
  Abelianization =
    SetCoequalizer {A = G' × G' × G'} {B = G'}
      (λ (x , y , z) → x · y · z)
      (λ (x , y , z) → x · z · y)

  -- some convenient relabellings, so it looks more similar to the abelianization as a HIT.
  incAb : G' → Abelianization
  incAb = inc

  comm : (x y z : G') → incAb (x · (y · z)) ≡ incAb (x · (z · y))
  comm = λ x y z → coeq (x , y , z)

  {-
    Definition of the group structure on the abelianization. Here the generality of the
    coequalized functions is used.
  -}
  _·Ab_ : Abelianization → Abelianization → Abelianization
  _·Ab_ =
    rec2
      squash
      (λ x y → incAb (x · y))
      (λ (a , b , c) d →
        incAb ((a · (b · c)) · d) ≡⟨ cong (λ x → incAb (x · d)) (·Assoc _ _ _) ⟩
        incAb (((a · b) · c) · d) ≡⟨ cong incAb (sym (·Assoc (a · b) c d)) ⟩
        incAb ((a · b) · (c · d)) ≡⟨ comm (a · b) c d ⟩
        incAb ((a · b) · (d · c)) ≡⟨ cong incAb (sym (·Assoc _ _ _)) ⟩
        incAb (a · (b · (d · c))) ≡⟨ cong (λ x → incAb (a · x)) (·Assoc _ _ _) ⟩
        incAb (a · ((b · d) · c)) ≡⟨ comm a (b · d) c ⟩
        incAb (a · (c · (b · d))) ≡⟨ cong (λ x → incAb (a · x)) (·Assoc _ _ _) ⟩
        incAb (a · ((c · b) · d)) ≡⟨ cong incAb (·Assoc a (c · b) d) ⟩
        incAb ((a · (c · b)) · d) ∎)
      (λ (b , c , d) a →
        incAb (a · (b · (c · d))) ≡⟨ cong incAb (·Assoc _ _ _) ⟩
        incAb ((a · b) · (c · d)) ≡⟨ comm (a · b) c d ⟩
        incAb ((a · b) · (d · c)) ≡⟨ cong incAb (sym (·Assoc _ _ _)) ⟩
        incAb (a · (b · (d · c))) ∎)

  1Ab : Abelianization
  1Ab = incAb 1g

  invAb : Abelianization → Abelianization
  invAb =
    rec
      squash
      (λ x → incAb (inv x))
      (λ (a , b , c) →
        incAb (inv (a · (b · c)))              ≡⟨ cong incAb (invDistr a (b · c)) ⟩
        incAb (inv (b · c) · inv a)            ≡⟨ cong (λ x → incAb (x · inv a)) (invDistr b c) ⟩
        incAb ((inv c · inv b) · inv a)        ≡⟨ cong
                                                    incAb
                                                    (sym (·IdL ((inv c · inv b) · inv a))) ⟩
        incAb (1g · ((inv c · inv b) · inv a)) ≡⟨ comm 1g (inv c · inv b) (inv a) ⟩
        incAb (1g · (inv a · (inv c · inv b))) ≡⟨ cong incAb (·IdL (inv a · (inv c · inv b))) ⟩
        incAb (inv a · (inv c · inv b))        ≡⟨ comm (inv a) (inv c) (inv b) ⟩
        incAb (inv a · (inv b · inv c))        ≡⟨ cong
                                                    incAb
                                                    (sym (·IdL (inv a · (inv b · inv c)))) ⟩
        incAb (1g · (inv a · (inv b · inv c))) ≡⟨ comm 1g (inv a) (inv b · inv c) ⟩
        incAb (1g · ((inv b · inv c) · inv a)) ≡⟨ cong incAb (·IdL ((inv b · inv c) · inv a)) ⟩
        incAb ((inv b · inv c) · inv a)        ≡⟨ cong
                                                    (λ x → incAb (x · inv a))
                                                    (sym (invDistr c b)) ⟩
        incAb (inv (c · b) · inv a)            ≡⟨ cong incAb (sym (invDistr a (c · b))) ⟩
        incAb (inv (a · (c · b))) ∎)

  assocAb : (x y z : Abelianization) → x ·Ab (y ·Ab z) ≡ (x ·Ab y) ·Ab z
  assocAb =
    elimProp3
      (λ x y z → squash (x ·Ab (y ·Ab z))
      ((x ·Ab y) ·Ab z))
      (λ x y z → cong incAb (·Assoc x y z))

  ridAb : (x : Abelianization) → x ·Ab 1Ab ≡ x
  ridAb =
    elimProp
      (λ x → squash (x ·Ab 1Ab) x)
      (λ x → cong incAb (·IdR x))

  rinvAb : (x : Abelianization) → x ·Ab (invAb x) ≡ 1Ab
  rinvAb =
    elimProp
      (λ x → squash (x ·Ab (invAb x)) 1Ab)
      (λ x → (incAb x) ·Ab (invAb (incAb x)) ≡⟨ refl ⟩
             (incAb x) ·Ab (incAb (inv x))   ≡⟨ refl ⟩
             incAb (x · (inv x))             ≡⟨ cong incAb (·InvR x) ⟩
             incAb 1g                        ≡⟨ refl ⟩
             1Ab ∎)

  commAb : (x y : Abelianization) → x ·Ab y ≡ y ·Ab x
  commAb =
    elimProp2
      (λ x y → squash (x ·Ab y) (y ·Ab x))
      (λ x y → (incAb x) ·Ab (incAb y) ≡⟨ refl ⟩
               incAb (x · y)           ≡⟨ cong incAb (sym (·IdL (x · y))) ⟩
               incAb (1g · (x · y))    ≡⟨ comm 1g x y ⟩
               incAb (1g · (y · x))    ≡⟨ cong incAb (·IdL (y · x)) ⟩
               incAb (y · x)           ≡⟨ refl ⟩
               (incAb y) ·Ab (incAb x) ∎)

  -- The proof that the abelianization is in fact an abelian group.
  asAbelianGroup : AbGroup ℓ
  asAbelianGroup = makeAbGroup 1Ab _·Ab_ invAb squash assocAb ridAb rinvAb commAb

  -- The proof that incAb can be seen as a group homomorphism
  incAbAsGroupHom : GroupHom G (AbGroup→Group asAbelianGroup)
  incAbAsGroupHom = f , fIsHom
    where
    f = λ x → incAb x
    fIsHom : IsGroupHom (snd G) f (snd (AbGroup→Group asAbelianGroup))
    IsGroupHom.pres· fIsHom = λ x y → refl
    IsGroupHom.pres1 fIsHom = refl
    IsGroupHom.presinv fIsHom = λ x → refl

AbelianizationAbGroup : (G : Group ℓ) → AbGroup ℓ
AbelianizationAbGroup G = AbelianizationAsCoeq.asAbelianGroup G

AbelianizationHom : (G : Group ℓ) → GroupHom G (AbGroup→Group (AbelianizationAbGroup G))
AbelianizationHom G = AbelianizationAsCoeq.incAbAsGroupHom G

module UniversalPropertyCoeq (G : Group ℓ) where
  open GroupStr {{...}}
  open GroupTheory G
  open AbelianizationAsCoeq G
  private
    instance
      _ = snd G
    G' = fst G
  abstract
    {- The proof of the universal property of the abelianization.

    G -incAb-> Abelianization
    \         .
      \       .
        f   ∃! inducedHom
          \   .
            \ .
              H
    commuting diagram
    -}
    inducedHom : (H : AbGroup ℓ)
              → (f : GroupHom G (AbGroup→Group H))
              → AbGroupHom asAbelianGroup H
    inducedHom H f = g , gIsHom
      where open IsGroupHom
            instance
              _ : GroupStr (fst H)
              _ = snd (AbGroup→Group H)
            f' : fst G → fst H
            f' = fst f
            g : Abelianization → fst H
            g = rec
                  is-set
                  (λ x → (f') x)
                  (λ (a , b , c) →
                    f' (a · b · c)           ≡⟨ (snd f).pres· a (b · c) ⟩
                    (f' a) · (f' (b · c))    ≡⟨ cong (λ x → (f' a) · x) ((snd f).pres· b c) ⟩
                    (f' a) · (f' b) · (f' c) ≡⟨ cong (λ x → (f' a) · x)
                                                     ((snd H).AbGroupStr.+Comm (f' b) (f' c)) ⟩
                    (f' a) · (f' c) · (f' b) ≡⟨ cong (λ x → (f' a) · x)
                                                     (sym ((snd f).pres· c b)) ⟩
                    (f' a) · (f' (c · b))    ≡⟨ sym ((snd f).pres· a (c · b)) ⟩
                    f' (a · c · b) ∎)
            gIsHom : IsGroupHom (snd (AbGroup→Group asAbelianGroup)) g (snd (AbGroup→Group H))
            pres· gIsHom =
              elimProp2
                (λ x y → is-set _ _)
                ((snd f).pres·)
            pres1 gIsHom = (snd f).pres1
            presinv gIsHom =
              elimProp
                (λ x → is-set _ _)
                ((snd f).presinv)

    commutativity : (H : AbGroup ℓ)
                  → (f : GroupHom G (AbGroup→Group H))
                  → (compGroupHom incAbAsGroupHom (inducedHom H f) ≡ f)
    commutativity H f =
        Σ≡Prop
          (λ _ → isPropIsGroupHom _ _)
          (λ i x → q x i)
      where q : (x : fst  G)
                → fst (compGroupHom incAbAsGroupHom (inducedHom H f)) x ≡ fst f x
            q = (λ x → refl)

    uniqueness : (H : AbGroup ℓ)
              → (f : GroupHom G (AbGroup→Group H))
              → (g : AbGroupHom asAbelianGroup H)
              → (p : compGroupHom incAbAsGroupHom g ≡ f)
              → (g ≡ inducedHom H f)
    uniqueness H f g p =
        Σ≡Prop
          (λ _ → isPropIsGroupHom _ _)
          (λ i x →  q x i)
      where
      module H = AbGroupStr (str H)
      q : (x : Abelianization) →  fst g x ≡ fst (inducedHom H f) x
      q = elimProp
            (λ _ → H.is-set _ _)
            (λ x → fst g (incAb x) ≡⟨ cong (λ f → f x) (cong fst p) ⟩
                  (fst f) x       ≡⟨ refl ⟩
                  fst (inducedHom H f) (incAb x)∎)

module IsoCoeqHIT (G : Group ℓ) where
  open GroupStr {{...}}
  open GroupTheory G
  open AbelianizationAsCoeq G
  open UniversalPropertyCoeq G
  private
    instance
      _ = snd G
    G' = fst G

  {- The proof that defining the abelianization of groups as a coequalizer of sets is equivalent
  to defining it as a HIT, more precisely that there is an isomorphism between the resulting
  abelian groups unique with respect to commuting with the constructors η and inc.

  G -incAb-> abelianization as coequalizer
   \         .
     \       .
       η   ∃! isomorphism
         \   .
           \ .
             abelianization as HIT
  commuting diagram
  -}
  isomorphism : AbGroupIso asAbelianGroup (HITasAbelianGroup G)
  isomorphism = h , hIsHomo
    where
    f = inducedHom (HITasAbelianGroup G) (HITηAsGroupHom G)
    g = HITinducedHom G asAbelianGroup incAbAsGroupHom

    HITgfcomm : compGroupHom (HITηAsGroupHom G) (compGroupHom g f) ≡ (HITηAsGroupHom G)
    HITgfcomm =
      compGroupHom (HITηAsGroupHom G) (compGroupHom g f)
        ≡⟨ sym (compGroupHomAssoc (HITηAsGroupHom G) g f) ⟩
      compGroupHom (compGroupHom (HITηAsGroupHom G) g) f
        ≡⟨ cong (λ x → compGroupHom x f) (HITcommutativity G asAbelianGroup incAbAsGroupHom) ⟩
      compGroupHom incAbAsGroupHom f
        ≡⟨ commutativity (HITasAbelianGroup G) (HITηAsGroupHom G) ⟩
      (HITηAsGroupHom G) ∎

    HITidcomm : compGroupHom (HITηAsGroupHom G) idGroupHom ≡ HITηAsGroupHom G
    HITidcomm = compGroupHomId (HITηAsGroupHom G)

    HITidIsInduced : HITinducedHom G (HITasAbelianGroup G) (HITηAsGroupHom G) ≡ idGroupHom
    HITidIsInduced = sym (HITuniqueness G
                           (HITasAbelianGroup G)
                           (HITηAsGroupHom G)
                           idGroupHom
                           HITidcomm)

    HITgfIsInduced : HITinducedHom G (HITasAbelianGroup G) (HITηAsGroupHom G) ≡ compGroupHom g f
    HITgfIsInduced = sym (HITuniqueness G
                           (HITasAbelianGroup G)
                           (HITηAsGroupHom G)
                           (compGroupHom g f)
                           HITgfcomm)

    i : idGroupHom ≡ compGroupHom g f
    i = idGroupHom ≡⟨ sym HITidIsInduced ⟩
        HITinducedHom G (HITasAbelianGroup G) (HITηAsGroupHom G) ≡⟨ HITgfIsInduced ⟩
        compGroupHom g f ∎

    fgcomm : compGroupHom incAbAsGroupHom (compGroupHom f g) ≡ incAbAsGroupHom
    fgcomm =
      compGroupHom incAbAsGroupHom (compGroupHom f g)
        ≡⟨ sym (compGroupHomAssoc incAbAsGroupHom f g) ⟩
      compGroupHom (compGroupHom incAbAsGroupHom f) g
        ≡⟨ cong (λ x → compGroupHom x g) (commutativity (HITasAbelianGroup G) (HITηAsGroupHom G)) ⟩
      compGroupHom (HITηAsGroupHom G) g
        ≡⟨ (HITcommutativity G) asAbelianGroup incAbAsGroupHom ⟩
      incAbAsGroupHom ∎

    idcomm : compGroupHom incAbAsGroupHom idGroupHom ≡ incAbAsGroupHom
    idcomm = compGroupHomId incAbAsGroupHom

    idIsInduced : inducedHom asAbelianGroup incAbAsGroupHom ≡ idGroupHom
    idIsInduced = sym (uniqueness asAbelianGroup incAbAsGroupHom idGroupHom idcomm)

    fgIsInduced : inducedHom asAbelianGroup incAbAsGroupHom ≡ compGroupHom f g
    fgIsInduced = sym (uniqueness asAbelianGroup incAbAsGroupHom (compGroupHom f g) fgcomm)

    j : idGroupHom ≡ compGroupHom f g
    j = idGroupHom ≡⟨ sym idIsInduced ⟩
        inducedHom asAbelianGroup incAbAsGroupHom ≡⟨ fgIsInduced ⟩
        compGroupHom f g ∎

    h = iso
          (fst f)
          (fst g)
          (λ b → cong (λ e → e b) (cong fst (sym i)))
          (λ a → cong (λ e → e a) (cong fst (sym j)))
    hIsHomo = snd f

  isomorphismCommutativity : compGroupHom incAbAsGroupHom (GroupIso→GroupHom isomorphism)
                               ≡ (HITηAsGroupHom G)
  isomorphismCommutativity = commutativity (HITasAbelianGroup G) (HITηAsGroupHom G)

  isomorphismUniqueness : (h : AbGroupIso asAbelianGroup (HITasAbelianGroup G))
    → (hcomm : compGroupHom incAbAsGroupHom (GroupIso→GroupHom h) ≡ (HITηAsGroupHom G))
    → h ≡ isomorphism
  isomorphismUniqueness h hcomm = GroupIso≡ p
    where
      r : (x : fst asAbelianGroup)
        → fst (compGroupHom (GroupIso→GroupHom h) (GroupIso→GroupHom (invGroupIso h))) x ≡ x
      r = λ x → (h .fst .Iso.leftInv) x

      leftInvGroupHom : (compGroupHom
                          (GroupIso→GroupHom h)
                          (GroupIso→GroupHom (invGroupIso h))) ≡ idGroupHom
      leftInvGroupHom =
        Σ≡Prop
          (λ _ → isPropIsGroupHom _ _)
          (λ i x → r x i)

      q : (g : fst  G)
        → fst (compGroupHom
                (HITηAsGroupHom G)
                (GroupIso→GroupHom (invGroupIso h))) g ≡ fst incAbAsGroupHom g
      q = λ g
        → fst (compGroupHom (HITηAsGroupHom G) (GroupIso→GroupHom (invGroupIso h))) g
            ≡⟨ cong
                 (λ f → f g)
                 (cong fst (cong
                             (λ f → compGroupHom f (GroupIso→GroupHom (invGroupIso h)))
                             (sym hcomm))) ⟩
          fst (compGroupHom
                (compGroupHom incAbAsGroupHom (GroupIso→GroupHom h))
                (GroupIso→GroupHom (invGroupIso h))) g
            ≡⟨ cong
                 (λ f → f g)
                 (cong fst (compGroupHomAssoc
                              incAbAsGroupHom
                              (GroupIso→GroupHom h)
                              (GroupIso→GroupHom (invGroupIso h)))) ⟩
          fst (compGroupHom
                incAbAsGroupHom
                (compGroupHom (GroupIso→GroupHom h) (GroupIso→GroupHom (invGroupIso h)))) g
            ≡⟨ cong
                (λ f → f g)
                (cong fst (cong (λ f → (compGroupHom incAbAsGroupHom f)) leftInvGroupHom)) ⟩
          fst incAbAsGroupHom g ∎

      isocomm : compGroupHom
                  (HITηAsGroupHom G)
                  (GroupIso→GroupHom (invGroupIso h)) ≡ incAbAsGroupHom
      isocomm =
        Σ≡Prop
          (λ _ → isPropIsGroupHom _ _)
          (λ i x → q x i)

      p : h .fst ≡ isomorphism .fst
      p =
        Iso≡Set
          (AbGroupStr.is-set (str asAbelianGroup))
          (AbGroupStr.is-set (str (HITasAbelianGroup G)))
          (h .fst)
          (isomorphism .fst)
          (λ x → cong
                   (λ f → f x)
                   (cong fst (uniqueness
                               (HITasAbelianGroup G)
                               (HITηAsGroupHom G)
                               (GroupIso→GroupHom h)
                               hcomm)))
          (λ x → cong
                   (λ f → f x)
                   (cong fst (HITuniqueness G
                                asAbelianGroup
                                incAbAsGroupHom
                                (GroupIso→GroupHom (invGroupIso h))
                                isocomm)))

AbelianizationComparisonIsomorphism : (G : Group ℓ)
                                    → AbGroupIso (AbelianizationAbGroup G) (HITasAbelianGroup G)
AbelianizationComparisonIsomorphism G = IsoCoeqHIT.isomorphism G
