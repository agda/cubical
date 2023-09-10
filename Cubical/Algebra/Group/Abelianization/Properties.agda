{-

This file contains:
    - the abelianization of groups as a HIT as proposed in https://arxiv.org/abs/2007.05833

The definition of the abelianization is not as a set-quotient, since the relation of
abelianization is cumbersome to work with.

-}
{-# OPTIONS --safe #-}
module Cubical.Algebra.Group.Abelianization.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
  using (isPropIsGroupHom; compGroupHom; idGroupHom)

open import Cubical.Algebra.AbGroup.Base

open import Cubical.Algebra.Group.Abelianization.Base

private
  variable
    ℓ : Level

module _ (G : Group ℓ) where
  open GroupStr {{...}}
  open GroupTheory G
  private
    instance
      _ = snd G

  -- Some helpful lemmas, similar to those in Cubical/HITs/SetQuotients/Properties.agda
  elimProp : {B : Abelianization G → Type ℓ}
        → (Bprop : (x : Abelianization G) → isProp (B x))
        → (f : (g : fst G) → B (η g))
        → (x : Abelianization G)
        → B x
  elimProp Bprop f (η g) = f g
  elimProp {B = B} Bprop f (comm a b c i) =
    isProp→PathP (λ i → Bprop (comm a b c i)) (f (a · (b · c))) (f (a · (c · b))) i
  elimProp Bprop f (isset x y p q i j) =
    isOfHLevel→isOfHLevelDep
      2 (λ x → isProp→isSet (Bprop x)) (g x) (g y) (cong g p) (cong g q) (isset x y p q) i j
    where
    g = elimProp Bprop f

  elimProp2 : {C : Abelianization G → Abelianization G → Type ℓ}
        → (Cprop : (x y : Abelianization G) → isProp (C x y))
        → (f : (a b : fst G) → C (η a) (η b))
        → (x y : Abelianization G)
        → C x y
  elimProp2 Cprop f = elimProp (λ x → isPropΠ (λ y → Cprop x y))
                               (λ x → elimProp (λ y → Cprop (η x) y) (f x))

  elimProp3 : {D : Abelianization G → Abelianization G → Abelianization G → Type ℓ}
        → (Dprop : (x y z : Abelianization G) → isProp (D x y z))
        → ((a b c : fst G) → D (η a) (η b) (η c))
        → (x y z : Abelianization G)
        → D x y z
  elimProp3 Dprop f = elimProp (λ x → isPropΠ2 (λ y z → Dprop x y z))
                               (λ x → elimProp2 (λ y z → Dprop (η x) y z) (f x))

  elimContr : {B : Abelianization G → Type ℓ}
        → (Bcontr : ∀ (a : fst G) → isContr (B (η a)))
        → (x : Abelianization G)
        → B x
  elimContr Bcontr = elimProp (elimProp (λ _ → isPropIsProp) λ _ → isContr→isProp (Bcontr _))
                              λ _ → Bcontr _ .fst

  elimContr2 : {C : Abelianization G → Abelianization G → Type ℓ}
        → (Ccontr : ∀ (a b : fst G) → isContr (C (η a) (η b)))
        → (x y : Abelianization G)
        → C x y
  elimContr2 Ccontr = elimContr λ _ → isOfHLevelΠ 0
                     (elimContr λ _ → inhProp→isContr (Ccontr _ _) isPropIsContr)

  rec : {M : Type ℓ}
        (Mset : isSet M)
        (f : fst G → M)
        (fcomm : (a b c : fst G) → f (a · (b · c)) ≡ f (a · (c · b)))
      → Abelianization G → M
  rec Mset f fcomm (η g) = f g
  rec Mset f fcomm (comm a b c i) = fcomm a b c i
  rec Mset f fcomm (isset a b p q i j) = Mset (g a) (g b) (cong g p) (cong g q) i j
    where
    g = rec Mset f fcomm

  rec2 : {M : Type ℓ}
        (Mset : isSet M)
        (f : fst G → fst G → M)
        (fcomml : (a b c d : fst G) → f (a · (b · c)) d ≡ f (a · (c · b)) d)
        (fcommr : (a b c d : fst G) → f a (b · (c · d)) ≡ f a (b · (d · c)))
      → Abelianization G → Abelianization G → M
  rec2 Mset f fcomml fcommr =
    rec
      (isSetΠ (λ _ → Mset))
      (λ g → rec Mset (λ h → f g h) (fcommr g))
      (λ a b c → funExt (elimProp (λ _ → Mset _ _) (λ d → fcomml a b c d)))

module AbelianizationGroupStructure (G : Group ℓ) where
  open GroupStr {{...}}
  open GroupTheory G
  private
    instance
      _ = snd G

  {-
    Definition of the group structure on the abelianization. Here the generality of the comm
    relation is used.
  -}
  _·Ab_ : Abelianization G → Abelianization G → Abelianization G
  _·Ab_ =
    (rec2 G)
      isset
      (λ x y → η (x · y))
      (λ a b c d → η ((a · (b · c)) · d) ≡⟨ cong η (cong (λ x → (x · d)) (·Assoc _ _ _)) ⟩
                   η (((a · b) · c) · d) ≡⟨ cong η (sym (·Assoc (a · b) c d)) ⟩
                   η ((a · b) · (c · d)) ≡⟨ comm (a · b) c d ⟩
                   η ((a · b) · (d · c)) ≡⟨ cong η (sym (·Assoc _ _ _)) ⟩
                   η (a · (b · (d · c))) ≡⟨ cong η (cong (λ x → (a · x)) (·Assoc _ _ _)) ⟩
                   η (a · ((b · d) · c)) ≡⟨ comm a (b · d) c ⟩
                   η (a · (c · (b · d))) ≡⟨ cong η (cong (λ x → (a · x)) (·Assoc _ _ _)) ⟩
                   η (a · ((c · b) · d)) ≡⟨ cong η (·Assoc a (c · b) d) ⟩
                   η ((a · (c · b)) · d) ∎)
      (λ a b c d → η (a · (b · (c · d))) ≡⟨ cong η (·Assoc _ _ _) ⟩
                   η ((a · b) · (c · d)) ≡⟨ comm (a · b) c d ⟩
                   η ((a · b) · (d · c)) ≡⟨ cong η (sym (·Assoc _ _ _)) ⟩
                   η (a · (b · (d · c))) ∎)

  1Ab : Abelianization G
  1Ab = η 1g

  invAb : Abelianization G → Abelianization G
  invAb =
    (rec G)
      isset
      ((λ x → η (inv x)))
      (λ a b c → η (inv (a · (b · c)))         ≡⟨ cong η (invDistr a (b · c)) ⟩
      η ((inv (b · c)) · (inv a))              ≡⟨ cong (λ x → η (x · (inv a))) (invDistr b c) ⟩
      η (((inv c) · (inv b)) · (inv a))        ≡⟨ cong
                                                    η
                                                    ((sym (·IdL (((inv c) · (inv b)) · (inv a))))) ⟩
      η (1g · (((inv c) · (inv b)) · (inv a))) ≡⟨ comm 1g ((inv c) · (inv b)) (inv a) ⟩
      η (1g · ((inv a) · ((inv c) · (inv b)))) ≡⟨ cong η (·IdL ((inv a) · ((inv c) · (inv b)))) ⟩
      η ((inv a) · ((inv c) · (inv b)))        ≡⟨ comm (inv a) (inv c) (inv b) ⟩
      η ((inv a) · ((inv b) · (inv c)))        ≡⟨ cong
                                                    η
                                                    ((sym (·IdL ((inv a) · ((inv b) · (inv c)))))) ⟩
      η (1g · ((inv a) · ((inv b) · (inv c)))) ≡⟨ comm 1g (inv a) ((inv b) · (inv c)) ⟩
      η (1g · (((inv b) · (inv c)) · (inv a))) ≡⟨ cong η (·IdL (((inv b) · (inv c)) · (inv a))) ⟩
      η (((inv b) · (inv c)) · (inv a))        ≡⟨ cong
                                                    (λ x → η (x · (inv a)))
                                                    (sym (invDistr c b)) ⟩
      η ((inv (c · b)) · (inv a))              ≡⟨ cong η (sym (invDistr a (c · b))) ⟩
      η (inv (a · (c · b))) ∎)

  assocAb : (x y z : Abelianization G) → x ·Ab (y ·Ab z) ≡ (x ·Ab y) ·Ab z
  assocAb =
    (elimProp3 G)
      (λ x y z → isset (x ·Ab (y ·Ab z)) ((x ·Ab y) ·Ab z))
      (λ x y z → cong η (·Assoc x y z))

  ridAb : (x : Abelianization G) → x ·Ab 1Ab ≡ x
  ridAb =
    (elimProp G)
      (λ x → isset (x ·Ab 1Ab) x)
      (λ x → cong η (·IdR x))

  rinvAb : (x : Abelianization G) → x ·Ab (invAb x) ≡ 1Ab
  rinvAb =
    (elimProp G)
      (λ x → isset (x ·Ab (invAb x)) 1Ab)
      (λ x → (η x) ·Ab (invAb (η x)) ≡⟨ refl ⟩
             (η x) ·Ab (η (inv x))   ≡⟨ refl ⟩
             η (x · (inv x))         ≡⟨ cong η (·InvR x) ⟩
             η 1g                    ≡⟨ refl ⟩
             1Ab ∎)

  commAb : (x y : Abelianization G) → x ·Ab y ≡ y ·Ab x
  commAb =
    (elimProp2 G)
      (λ x y → isset (x ·Ab y) (y ·Ab x))
      (λ x y → (η x) ·Ab (η y)  ≡⟨ refl ⟩
               η (x · y)        ≡⟨ cong η (sym (·IdL (x · y))) ⟩
               η (1g · (x · y)) ≡⟨ comm 1g x y ⟩
               η (1g · (y · x)) ≡⟨ cong η (·IdL (y · x)) ⟩
               η (y · x)        ≡⟨ refl ⟩
               (η y) ·Ab (η x) ∎)

  -- The proof that the abelianization is in fact an abelian group.
  asAbelianGroup : AbGroup ℓ
  asAbelianGroup = makeAbGroup 1Ab _·Ab_ invAb isset assocAb ridAb rinvAb commAb

  -- The proof that η can be seen as a group homomorphism
  ηAsGroupHom : GroupHom G (AbGroup→Group asAbelianGroup)
  ηAsGroupHom = f , fIsHom
    where
    f = λ x → η x
    fIsHom : IsGroupHom (snd G) f (snd (AbGroup→Group asAbelianGroup))
    IsGroupHom.pres· fIsHom = λ x y → refl
    IsGroupHom.pres1 fIsHom = refl
    IsGroupHom.presinv fIsHom = λ x → refl

AbelianizationAbGroup : (G : Group ℓ) → AbGroup ℓ
AbelianizationAbGroup G = AbelianizationGroupStructure.asAbelianGroup G

AbelianizationHom : (G : Group ℓ) → GroupHom G (AbGroup→Group (AbelianizationAbGroup G))
AbelianizationHom G = AbelianizationGroupStructure.ηAsGroupHom G

module UniversalProperty (G : Group ℓ) where
  open GroupStr {{...}}
  open GroupTheory G
  open AbelianizationGroupStructure G
  private
    instance
      _ = snd G
  abstract
    {- The proof of the universal property of the abelianization.

    G --η--> abelianization
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
            g : Abelianization G → fst H
            g = (rec G)
                  is-set
                  (λ x → (f') x)
                  (λ a b c → f' (a · b · c)           ≡⟨ (snd f).pres· a (b · c) ⟩
                             (f' a) · (f' (b · c))    ≡⟨ cong
                                                           (λ x → (f' a) · x)
                                                           ((snd f).pres· b c) ⟩
                             (f' a) · (f' b) · (f' c) ≡⟨ cong
                                                           (λ x → (f' a) · x)
                                                           ((snd H).AbGroupStr.+Comm (f' b) (f' c)) ⟩
                             (f' a) · (f' c) · (f' b) ≡⟨ cong
                                                           (λ x → (f' a) · x)
                                                           (sym ((snd f).pres· c b)) ⟩
                             (f' a) · (f' (c · b))    ≡⟨ sym ((snd f).pres· a (c · b)) ⟩
                             f' (a · c · b) ∎)
            gIsHom : IsGroupHom (snd (AbGroup→Group asAbelianGroup)) g (snd (AbGroup→Group H))
            pres· gIsHom =
              (elimProp2 G)
                (λ x y → is-set _ _)
                ((snd f).pres·)
            pres1 gIsHom = (snd f).pres1
            presinv gIsHom =
              (elimProp G)
                (λ x → is-set _ _)
                ((snd f).presinv)

    commutativity : (H : AbGroup ℓ)
                  → (f : GroupHom G (AbGroup→Group H))
                  → (compGroupHom ηAsGroupHom (inducedHom H f) ≡ f)
    commutativity H f =
        Σ≡Prop
          (λ _ → isPropIsGroupHom _ _)
          (λ i x → q x i)
      where q : (x : fst  G)
              → fst (compGroupHom ηAsGroupHom (inducedHom H f)) x ≡ fst f x
            q = (λ x → refl)

    uniqueness : (H : AbGroup ℓ)
               → (f : GroupHom G (AbGroup→Group H))
               → (g : AbGroupHom asAbelianGroup H)
               → (p : compGroupHom ηAsGroupHom g ≡ f)
               → (g ≡ inducedHom H f)
    uniqueness H f g p =
        Σ≡Prop
          (λ _ → isPropIsGroupHom _ _)
          (λ i x →  q x i)
      where
      module H = AbGroupStr (str H)
      q : (x : Abelianization G) → fst g x ≡ fst (inducedHom H f) x
      q = (elimProp G)
            (λ _ → H.is-set _ _)
            (λ x → fst g (η x) ≡⟨ cong (λ f → f x) (cong fst p) ⟩
                   (fst f) x   ≡⟨ refl ⟩
                   fst (inducedHom H f) (η x)∎)
