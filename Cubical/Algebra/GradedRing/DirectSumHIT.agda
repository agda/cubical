module Cubical.Algebra.GradedRing.DirectSumHIT where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Algebra.Monoid
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.DirectSumHIT
open import Cubical.Algebra.DirectSum.DirectSumHIT.Base
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing

private variable
  ℓ ℓ' : Level


-----------------------------------------------------------------------------
-- Def, notation, lemma

module GradedRing-⊕HIT-index
  (IdM@(Idx , IdxStr) : Monoid ℓ)
  (G : (n : Idx) → Type ℓ')
  (Gstr : (n : Idx) → AbGroupStr (G n))
  where

  ⊕G-AbGroup = ⊕HIT-AbGr Idx G Gstr
  ⊕G = ⊕HIT Idx G Gstr

  open MonoidStr IdxStr renaming (is-set to isSetIdx)
  open AbGroupStr (snd ⊕G-AbGroup)
    renaming
    ( 0g     to 0⊕
    ; _+_    to _+⊕_
    ; -_     to -⊕_
    ; +Assoc to +⊕Assoc
    ; +IdR   to +⊕IdR
    ; +IdL   to +⊕IdL
    ; +InvR  to +⊕InvR
    ; +InvL  to +⊕InvL
    ; +Comm  to +⊕Comm
    ; is-set to isSet⊕G )
  open AbGroupTheory ⊕G-AbGroup

  open AbGroupStr
    renaming
    ( +Assoc to +Assoc
    ; +IdR   to +IdR
    ; +IdL   to +IdL
    ; +InvR  to +InvR
    ; +InvL  to +InvL
    ; +Comm  to +Comm
    ; is-set to isSetG )

  module GradedRing-⊕HIT-⋆
    (1⋆      : G ε)
    (_⋆_     : {k l : Idx} → G k → G l → G (k · l))
    (0-⋆     : {k l : Idx} → (b : G l) → (0g (Gstr k)) ⋆ b ≡ 0g (Gstr (k · l)))
    (⋆-0     : {k l : Idx} → (a : G k) → a ⋆ (0g (Gstr l)) ≡ 0g (Gstr (k · l)))
    (⋆Assoc  : {k l m : Idx} → (a : G k) → (b : G l) → (c : G m) →
                _≡_ {A = Σ[ k ∈ Idx ] G k} ((k · (l · m)) , (a ⋆ (b ⋆ c))) (((k · l) · m) , ((a ⋆ b) ⋆ c)))
    (⋆IdR    : {k : Idx} → (a : G k) → _≡_ {A = Σ[ k ∈ Idx ] G k} ( k · ε , a ⋆ 1⋆ ) (k , a))
    (⋆IdL    : {l : Idx} → (b : G l) → _≡_ {A = Σ[ k ∈ Idx ] G k} ( ε · l , 1⋆ ⋆ b ) (l , b))
    (⋆DistR+ : {k l : Idx} → (a : G k) → (b c : G l) →
               a ⋆ ((Gstr l) ._+_ b c) ≡ Gstr (k · l) ._+_ (a ⋆ b) (a ⋆ c))
    (⋆DistL+ : {k l : Idx} → (a b : G k) → (c : G l) →
               ((Gstr k) ._+_ a b) ⋆ c ≡ Gstr (k · l) ._+_ (a ⋆ c) (b ⋆ c))
    where


-----------------------------------------------------------------------------
-- Ring Properties

    _prod_ : ⊕G → ⊕G → ⊕G
    _prod_ = DS-Rec-Set.f _ _ _ _ (isSetΠ λ _ → isSet⊕G)
             (λ _ → 0⊕)
             (λ k a → DS-Rec-Set.f _ _ _ _ isSet⊕G
                       0⊕
                       (λ l b → base (k · l) (a ⋆ b))
                       _+⊕_
                       +⊕Assoc
                       +⊕IdR
                       +⊕Comm
                       (λ l → cong (base (k · l)) (⋆-0 a) ∙ base-neutral _)
                       λ l b c → base-add _ _ _ ∙ cong (base (k · l)) (sym (⋆DistR+ _ _ _)))
             (λ xs ys y → (xs y) +⊕ (ys y))
             (λ xs ys zs i y → +⊕Assoc (xs y) (ys y) (zs y) i)
             (λ xs i y       → +⊕IdR (xs y) i)
             (λ xs ys i y    → +⊕Comm (xs y) (ys y) i)
             (λ k → funExt (DS-Ind-Prop.f _ _ _ _ (λ _ → isSet⊕G _ _)
                     refl
                     (λ l b → cong (base (k · l)) (0-⋆ _) ∙ base-neutral _)
                     λ {U V} ind-U ind-V → cong₂ _+⊕_ ind-U ind-V ∙ +⊕IdR _))
             λ k a b → funExt (DS-Ind-Prop.f _ _ _ _ (λ _ → isSet⊕G _ _)
                        (+⊕IdR _)
                        (λ l c → base-add _ _ _ ∙ cong (base (k · l)) (sym (⋆DistL+ _ _ _)))
                        (λ {U V} ind-U ind-V → comm-4 _ _ _ _ ∙ cong₂ _+⊕_ ind-U ind-V))

    1⊕ : ⊕G
    1⊕ = base ε 1⋆

    prodAssoc : (x y z : ⊕G) → x prod (y prod z) ≡ (x prod y) prod z
    prodAssoc = DS-Ind-Prop.f _ _ _ _ (λ _ → isPropΠ2 λ _ _ → isSet⊕G _ _)
                (λ _ _ → refl)
                (λ k a → DS-Ind-Prop.f _ _ _ _ (λ _ → isPropΠ (λ _ → isSet⊕G _ _))
                          (λ z → refl)
                          (λ l b → DS-Ind-Prop.f _ _ _ _ (λ _ → isSet⊕G _ _)
                                    refl
                                    (λ m c → cong₂ base (cong fst (⋆Assoc _ _ _)) (cong snd (⋆Assoc _ _ _)))
                                    λ {U V} ind-U ind-V → cong₂ _+⊕_ ind-U ind-V)
                          λ {U V} ind-U ind-V z → cong₂ _+⊕_ (ind-U z) (ind-V z))
                λ {U V} ind-U ind-V y z → cong₂ _+⊕_ (ind-U y z) (ind-V y z)


    prodIdR : (x : ⊕G) → x prod 1⊕ ≡ x
    prodIdR = DS-Ind-Prop.f _ _ _ _ (λ _ → isSet⊕G _ _)
              refl
              (λ k a → cong₂ base (cong fst (⋆IdR _)) (cong snd (⋆IdR _)) )
              λ {U V} ind-U ind-V → (cong₂ _+⊕_ ind-U ind-V)

    prodIdL : (y : ⊕G) → 1⊕ prod y ≡ y
    prodIdL = DS-Ind-Prop.f _ _ _ _ (λ _ → isSet⊕G _ _)
              refl
              (λ l b → cong₂ base (cong fst (⋆IdL _)) (cong snd (⋆IdL _)) )
              λ {U V} ind-U ind-V → (cong₂ _+⊕_ ind-U ind-V)


    prodDistR+ : (x y z : ⊕G) → x prod (y +⊕ z) ≡ (x prod y) +⊕ (x prod z)
    prodDistR+ = DS-Ind-Prop.f _ _ _ _ (λ _ → isPropΠ2 (λ _ _ → isSet⊕G _ _))
                 (λ _ _ → sym (+⊕IdR _))
                 (λ k a y z → refl)
                 λ {U V} ind-U ind-V y z → cong₂ _+⊕_ (ind-U y z) (ind-V y z) ∙ comm-4 _ _ _ _

    prodDistL+ : (x y z : ⊕G) → (x +⊕ y) prod z ≡ (x prod z) +⊕ (y prod z)
    prodDistL+ = λ x y z → refl

-----------------------------------------------------------------------------
-- Ring Instances

    ⊕HITgradedRing-Ring : Ring (ℓ-max ℓ ℓ')
    fst ⊕HITgradedRing-Ring = ⊕G
    RingStr.0r (snd ⊕HITgradedRing-Ring) = 0⊕
    RingStr.1r (snd ⊕HITgradedRing-Ring) = 1⊕
    RingStr._+_ (snd ⊕HITgradedRing-Ring) = _+⊕_
    RingStr._·_ (snd ⊕HITgradedRing-Ring) = _prod_
    RingStr.- snd ⊕HITgradedRing-Ring = -⊕_
    RingStr.isRing (snd ⊕HITgradedRing-Ring) = makeIsRing isSet⊕G
                                               +⊕Assoc +⊕IdR +⊕InvR +⊕Comm
                                               prodAssoc prodIdR prodIdL prodDistR+ prodDistL+

-----------------------------------------------------------------------------
-- CommRing extension

    module ExtensionCommRing
      (⋆Comm : {k l : Idx} → (a : G k) → (b : G l) →
               _≡_ {A = Σ[ k ∈ Idx ] G k} ((k · l) , (a ⋆ b)) ((l · k) , (b ⋆ a)))
      where

      open RingTheory ⊕HITgradedRing-Ring

      prodComm : (x y : ⊕G) → x prod y ≡ y prod x
      prodComm = DS-Ind-Prop.f _ _ _ _ (λ _ → isPropΠ (λ _ → isSet⊕G _ _))
                 (λ y → sym (0RightAnnihilates y))
                 (λ k a → DS-Ind-Prop.f _ _ _ _ (λ _ → isSet⊕G _ _)
                           refl
                           (λ l b → cong₂ base (cong fst (⋆Comm _ _)) (cong snd (⋆Comm _ _)))
                           λ {U V} ind-U ind-V → cong₂ _+⊕_ ind-U ind-V)
                 λ {U V} ind-U ind-V Q → ((cong₂ _+⊕_ (ind-U Q) (ind-V Q)) ∙ sym (prodDistR+ Q U V))

      ⊕HITgradedRing-CommRing : CommRing (ℓ-max ℓ ℓ')
      ⊕HITgradedRing-CommRing = Ring→CommRing ⊕HITgradedRing-Ring prodComm
