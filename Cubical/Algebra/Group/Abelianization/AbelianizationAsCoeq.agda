{-

This file contains:
    - the abelianization of groups as a coequalizer of sets as performed in https://1lab.dev/Algebra.Group.Ab.Free.html
    - the proof that this way of defining the abelianization of groups is equivalent to defining it as a HIT,
      more precisely that there is a unique isomorphism between the resulting abelian groups

-}
{-# OPTIONS --safe #-}
module Cubical.Algebra.Group.Abelianization.AbelianizationAsCoeq where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
  using (isPropIsGroupHom; compGroupHom; idGroupHom; compGroupHomAssoc; GroupEquiv→GroupHom; GroupIso→GroupEquiv; GroupEquiv→GroupIso; invGroupIso; GroupEquiv≡)

open import Cubical.Algebra.AbGroup.Base

open import Cubical.HITs.SetCoequalizer hiding (inducedHom; commutativity; uniqueness)

open import Cubical.Algebra.Group.Abelianization.Base
  renaming (Abelianization to HITAbelianization;
            η to HITη;
            comm to HITcomm;
            isset to HITisset)

open import Cubical.Algebra.Group.Abelianization.Properties
  renaming (asAbelianGroup to HITasAbelianGroup;
            ηAsGroupHom to HITηAsGroupHom;
            inducedHom to HITinducedHom;
            commutativity to HITcommutativity;
            uniqueness to HITuniqueness)
  hiding (elimProp; elimProp2; elimProp3; elimContr; elimContr2; rec; rec2; _·Ab_; 1Ab; invAb; assocAb; ridAb; rinvAb; commAb)

private
  variable
    ℓ : Level
    G : Group ℓ

module _ (G : Group ℓ) where
  open GroupStr {{...}}
  open GroupTheory G
  private
    instance
      _ = snd G
    G' = fst G

  {-
    The definition of the abelianization of a group as a coequalizer of sets.
    The generality of the glued functions will be needed to define the group structure on the abelianization.
  -}
  Abelianization : Type ℓ
  Abelianization = SetCoequalizer {A = G' × G' × G'} {B = G'} (λ (x , y , z) → x · y · z) (λ (x , y , z) → x · z · y)

  -- some convenient relabellings, so it looks more similar to the abelianization as a HIT.
  incAb : G' → Abelianization
  incAb = inc

  comm : (x y z : G') → incAb (x · (y · z)) ≡ incAb (x · (z · y))
  comm = λ x y z → glue (x , y , z)

  -- Definition of the group structure on the abelianization. Here the generality of the glued functions is used.
  _·Ab_ : Abelianization → Abelianization → Abelianization
  _·Ab_ =
    rec2
      squash
      (λ x y → incAb (x · y))
      (λ (a , b , c) d → incAb ((a · (b · c)) · d) ≡⟨ cong (λ x → incAb (x · d)) (assoc _ _ _) ⟩
                         incAb (((a · b) · c) · d) ≡⟨ cong incAb (sym (assoc (a · b) c d)) ⟩
                         incAb ((a · b) · (c · d)) ≡⟨ comm (a · b) c d ⟩
                         incAb ((a · b) · (d · c)) ≡⟨ cong incAb (sym (assoc _ _ _)) ⟩
                         incAb (a · (b · (d · c))) ≡⟨ cong (λ x → incAb (a · x)) (assoc _ _ _) ⟩
                         incAb (a · ((b · d) · c)) ≡⟨ comm a (b · d) c ⟩
                         incAb (a · (c · (b · d))) ≡⟨ cong (λ x → incAb (a · x)) (assoc _ _ _) ⟩
                         incAb (a · ((c · b) · d)) ≡⟨ cong incAb (assoc a (c · b) d) ⟩
                         incAb ((a · (c · b)) · d) ∎)
      (λ (b , c , d) a → incAb (a · (b · (c · d))) ≡⟨ cong incAb (assoc _ _ _) ⟩
                         incAb ((a · b) · (c · d)) ≡⟨ comm (a · b) c d ⟩
                         incAb ((a · b) · (d · c)) ≡⟨ cong incAb (sym (assoc _ _ _)) ⟩
                         incAb (a · (b · (d · c))) ∎)

  1Ab : Abelianization
  1Ab = incAb 1g

  invAb : Abelianization → Abelianization
  invAb =
    rec
      squash
      (λ x → incAb (inv x))
      (λ (a , b , c) → incAb (inv (a · (b · c)))              ≡⟨ cong incAb (invDistr a (b · c)) ⟩
                       incAb (inv (b · c) · inv a)            ≡⟨ cong (λ x → incAb (x · inv a)) (invDistr b c) ⟩
                       incAb ((inv c · inv b) · inv a)        ≡⟨ cong incAb (sym (lid ((inv c · inv b) · inv a))) ⟩
                       incAb (1g · ((inv c · inv b) · inv a)) ≡⟨ comm 1g (inv c · inv b) (inv a) ⟩
                       incAb (1g · (inv a · (inv c · inv b))) ≡⟨ cong incAb (lid (inv a · (inv c · inv b))) ⟩
                       incAb (inv a · (inv c · inv b))        ≡⟨ comm (inv a) (inv c) (inv b) ⟩
                       incAb (inv a · (inv b · inv c))        ≡⟨ cong incAb (sym (lid (inv a · (inv b · inv c)))) ⟩
                       incAb (1g · (inv a · (inv b · inv c))) ≡⟨ comm 1g (inv a) (inv b · inv c) ⟩
                       incAb (1g · ((inv b · inv c) · inv a)) ≡⟨ cong incAb (lid ((inv b · inv c) · inv a)) ⟩
                       incAb ((inv b · inv c) · inv a)        ≡⟨ cong (λ x → incAb (x · inv a)) (sym (invDistr c b)) ⟩
                       incAb (inv (c · b) · inv a)            ≡⟨ cong incAb (sym (invDistr a (c · b))) ⟩
                       incAb (inv (a · (c · b))) ∎)

  assocAb : (x y z : Abelianization) → x ·Ab (y ·Ab z) ≡ (x ·Ab y) ·Ab z
  assocAb =
    elimProp3
      (λ x y z → squash (x ·Ab (y ·Ab z))
      ((x ·Ab y) ·Ab z))
      (λ x y z → cong incAb (assoc x y z))

  ridAb : (x : Abelianization) → x ·Ab 1Ab ≡ x
  ridAb =
    elimProp
      (λ x → squash (x ·Ab 1Ab) x)
      (λ x → cong incAb (rid x))

  rinvAb : (x : Abelianization) → x ·Ab (invAb x) ≡ 1Ab
  rinvAb =
    elimProp
      (λ x → squash (x ·Ab (invAb x)) 1Ab)
      (λ x → (incAb x) ·Ab (invAb (incAb x)) ≡⟨ refl ⟩
             (incAb x) ·Ab (incAb (inv x))   ≡⟨ refl ⟩
             incAb (x · (inv x))             ≡⟨ cong incAb (fst (inverse x)) ⟩
             incAb 1g                        ≡⟨ refl ⟩
             1Ab ∎)

  commAb : (x y : Abelianization) → x ·Ab y ≡ y ·Ab x
  commAb =
    elimProp2
      (λ x y → squash (x ·Ab y) (y ·Ab x))
      (λ x y → (incAb x) ·Ab (incAb y) ≡⟨ refl ⟩
               incAb (x · y)           ≡⟨ cong incAb (sym (lid (x · y))) ⟩
               incAb (1g · (x · y))    ≡⟨ comm 1g x y ⟩
               incAb (1g · (y · x))    ≡⟨ cong incAb (lid (y · x)) ⟩
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
            _ = snd (AbGroup→Group H)
          f' = fst f
          g = rec
                (isSetAbGroup H)
                (λ x → (f') x)
                (λ (a , b , c) → f' (a · b · c)     ≡⟨ (snd f).pres· a (b · c) ⟩
                           (f' a) · (f' (b · c))    ≡⟨ cong (λ x → (f' a) · x) ((snd f).pres· b c) ⟩
                           (f' a) · (f' b) · (f' c) ≡⟨ cong (λ x → (f' a) · x) ((snd H).AbGroupStr.comm (f' b) (f' c)) ⟩
                           (f' a) · (f' c) · (f' b) ≡⟨ cong (λ x → (f' a) · x) (sym ((snd f).pres· c b)) ⟩
                           (f' a) · (f' (c · b))    ≡⟨ sym ((snd f).pres· a (c · b)) ⟩
                           f' (a · c · b) ∎)
          gIsHom : IsGroupHom (snd (AbGroup→Group asAbelianGroup)) g (snd (AbGroup→Group H))
          pres· gIsHom =
            elimProp2
              (λ x y → isSetAbGroup H _ _)
              ((snd f).pres·)
          pres1 gIsHom = (snd f).pres1
          presinv gIsHom =
            elimProp
              (λ x → isSetAbGroup H _ _)
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
    where q : (x : Abelianization)
              →  fst g x ≡ fst (inducedHom H f) x
          q = elimProp
                (λ _ → isSetAbGroup H _ _)
                (λ x → fst g (incAb x) ≡⟨ cong (λ f → f x) (cong fst p) ⟩
                       (fst f) x       ≡⟨ refl ⟩
                       fst (inducedHom H f) (incAb x)∎)

  {- The proof that defining the abelianization of groups as a coequalizer of sets is equivalent to defining it as a HIT,
  more precisely that there is an isomorphism between the resulting abelian groups unique with respect to commuting with
  the constructors η and inc. -}
  isomorphism : AbGroupIso asAbelianGroup (HITasAbelianGroup G)
  isomorphism = h , hIsHomo
    where
    f = inducedHom (HITasAbelianGroup G) (HITηAsGroupHom G)
    g = HITinducedHom G asAbelianGroup incAbAsGroupHom

    HITgfcomm : compGroupHom (HITηAsGroupHom G) (compGroupHom g f) ≡ (HITηAsGroupHom G)
    {-HITgfcomm = compGroupHom (HITηAsGroupHom G) (compGroupHom g f) ≡⟨ sym (compGroupHomAssoc (HITηAsGroupHom G) g f) ⟩
                compGroupHom (compGroupHom (HITηAsGroupHom G) g) f ≡⟨ cong (λ x → compGroupHom x f) (HITcommutativity G asAbelianGroup incAbAsGroupHom) ⟩
                compGroupHom incAbAsGroupHom f ≡⟨ commutativity (HITasAbelianGroup G) (HITηAsGroupHom G) ⟩
                (HITηAsGroupHom G) ∎ -}
    HITgfcomm = Σ≡Prop
        (λ _ → isPropIsGroupHom _ _)
        (λ i x → q x i)
      where q : (x : fst G) → fst (compGroupHom (compGroupHom (HITηAsGroupHom G) g) f) x ≡ fst (HITηAsGroupHom G) x
            q = (λ x → refl)

    HITidcomm : compGroupHom (HITηAsGroupHom G) idGroupHom ≡ HITηAsGroupHom G
    HITidcomm = Σ≡Prop
        (λ _ → isPropIsGroupHom _ _)
        (λ i x → q x i)
      where q : (x : fst G) → fst (compGroupHom (HITηAsGroupHom G) idGroupHom) x ≡ fst (HITηAsGroupHom G) x
            q = (λ x → refl)

    HITidIsInduced : HITinducedHom G (HITasAbelianGroup G) (HITηAsGroupHom G) ≡ idGroupHom
    HITidIsInduced = sym (HITuniqueness G (HITasAbelianGroup G) (HITηAsGroupHom G) idGroupHom HITidcomm)

    HITgfIsInduced : HITinducedHom G (HITasAbelianGroup G) (HITηAsGroupHom G) ≡ compGroupHom g f
    HITgfIsInduced = sym (HITuniqueness G (HITasAbelianGroup G) (HITηAsGroupHom G) (compGroupHom g f) HITgfcomm)

    i : idGroupHom ≡ compGroupHom g f
    i = idGroupHom ≡⟨ sym HITidIsInduced ⟩
        HITinducedHom G (HITasAbelianGroup G) (HITηAsGroupHom G) ≡⟨ HITgfIsInduced ⟩
        compGroupHom g f ∎

    fgcomm : compGroupHom incAbAsGroupHom (compGroupHom f g) ≡ incAbAsGroupHom
    fgcomm = Σ≡Prop
        (λ _ → isPropIsGroupHom _ _)
        (λ i x → q x i)
      where q : (x : fst G) → fst (compGroupHom (compGroupHom incAbAsGroupHom f) g) x ≡ fst incAbAsGroupHom x
            q = (λ x → refl)

    idcomm : compGroupHom incAbAsGroupHom idGroupHom ≡ incAbAsGroupHom
    idcomm = Σ≡Prop
        (λ _ → isPropIsGroupHom _ _)
        (λ i x → q x i)
      where q : (x : fst G) → fst (compGroupHom incAbAsGroupHom idGroupHom) x ≡ fst incAbAsGroupHom x
            q = (λ x → refl)

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

  isomorphismCommutativity : compGroupHom incAbAsGroupHom (GroupEquiv→GroupHom (GroupIso→GroupEquiv isomorphism)) ≡ (HITηAsGroupHom G)
  isomorphismCommutativity = HITcommutativity G (HITasAbelianGroup G) (HITηAsGroupHom G)

  -- isomorphismCommutativity2 : compGroupHom (HITηAsGroupHom G) (GroupEquiv→GroupHom (GroupIso→GroupEquiv (invGroupIso isomorphism))) ≡ incAbAsGroupHom
  -- isomorphismCommutativity2 = {! commutativity asAbelianGroup incAbAsGroupHom !}

  {-isomorphismUniqueness : (h : AbGroupIso asAbelianGroup (HITasAbelianGroup G))
                        → (hcomm : compGroupHom incAbAsGroupHom (GroupEquiv→GroupHom (GroupIso→GroupEquiv h)) ≡ HITηAsGroupHom G)
                        → h ≡ isomorphism
  isomorphismUniqueness h hcomm = {! cong GroupEquiv→GroupIso (GroupEquiv≡ (GroupIso→GroupEquiv h) (GroupIso→GroupEquiv isomorphism) ?)  !}
  -}
  -- HITuniqueness G (HITasAbelianGroup G) (HITηAsGroupHom G) (GroupEquiv→GroupHom (GroupIso→GroupEquiv h)) hcomm
