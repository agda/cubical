{-# OPTIONS --safe #-}
module Cubical.Homotopy.Hopf where

open import Cubical.Homotopy.HSpace

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Function
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.HITs.Pushout.Flattening
open import Cubical.HITs.Pushout
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.S1 renaming (_·_ to _*_)
open import Cubical.HITs.PropositionalTruncation
  renaming (rec to pRec ; elim to pElim)
open import Cubical.HITs.Join

open Iso
open HSpace
open AssocHSpace

private
  retEq≡secEq : ∀ {ℓ} {A B : Type ℓ} (e : A ≃ B)
                  → (x : _) → secEq e (e .fst x) ≡ cong (e .fst) (retEq e x)
  retEq≡secEq {A = A} =
    EquivJ (λ B e → (x : _) → secEq e (e .fst x) ≡ cong (e .fst) (retEq e x))
           λ _ → refl

module Hopf {ℓ : Level} {A : Pointed ℓ} {e : HSpace A}
            (e-ass : AssocHSpace e) (conA : ((x y : typ A) → ∥ x ≡ y ∥)) where
  isEquiv-μ : (x : typ A) → isEquiv (λ z → (μ e z x))
  isEquiv-μ x = pRec (isPropIsEquiv _)
                     (J (λ x _ → isEquiv (λ z → μ e z x))
                       (subst isEquiv (funExt (λ z → sym (μᵣ e z)))
                                      (idIsEquiv (typ A))))
                     (conA (pt A) x)

  isEquiv-μ' : (x : typ A) → isEquiv (μ e x)
  isEquiv-μ' x =
    pRec (isPropIsEquiv _)
          (J (λ x _ → isEquiv (μ e x))
            (subst isEquiv (funExt (λ x → sym (μₗ e x))) (idIsEquiv (typ A))))
          (conA (pt A) x)

  μ-eq : (x : typ A) → typ A ≃ typ A
  μ-eq x = (λ z → μ e z x) , (isEquiv-μ x)

  μ-eq' : (x : typ A) → typ A ≃ typ A
  μ-eq' x = μ e x , isEquiv-μ' x

  Hopf : Susp (typ A) → Type ℓ
  Hopf north = typ A
  Hopf south = typ A
  Hopf (merid a i₁) = ua (μ-eq a) i₁

  TotalSpaceHopfPush : Type _
  TotalSpaceHopfPush =
    Pushout {A = typ A × typ A} fst λ x → μ e (fst x) (snd x)

  TotalSpaceHopfPush→TotalSpace :
    TotalSpaceHopfPush → Σ[ x ∈ Susp (typ A) ] Hopf x
  TotalSpaceHopfPush→TotalSpace (inl x) = north , x
  TotalSpaceHopfPush→TotalSpace (inr x) = south , x
  TotalSpaceHopfPush→TotalSpace (push (x , y) i₁) =
    merid y i₁ , ua-gluePt (μ-eq y) i₁ x

  joinIso₁ : Iso (TotalSpaceHopfPush) (join (typ A) (typ A))
  joinIso₁ = iso F G s r
    where
    F : TotalSpaceHopfPush → join (typ A) (typ A)
    F (inl x) = inl x
    F (inr x) = inr x
    F (push (a , x) i) = push a (μ e a x) i

    G : join (typ A) (typ A) → TotalSpaceHopfPush
    G (inl x) = inl x
    G (inr x) = inr x
    G (push a b i) =
      (push (a , invEq (μ-eq' a) b) ∙ cong inr (secEq (μ-eq' a) b)) i

    s : section F G
    s (inl x) = refl
    s (inr x) = refl
    s (push a b i) j =
      hcomp (λ k → λ { (i = i0) → inl a
                      ; (i = i1) → inr (secEq (μ-eq' a) b (j ∨ k))
                      ; (j = i0) → F (compPath-filler
                                       (push (a , invEq (μ-eq' a) b))
                                       (cong inr (secEq (μ-eq' a) b)) k i)
                      ; (j = i1) → push a b i})
        (hcomp (λ k → λ { (i = i0) → inl a
                      ; (i = i1) → inr (secEq (μ-eq' a) b (~ k ∨ j))
                      ; (j = i0) → push a (secEq (μ-eq' a) b (~ k)) i
                      ; (j = i1) → push a b i})
               (push a b i))

    r : retract F G
    r (inl x) = refl
    r (inr x) = refl
    r (push (x , y) i) j =
      hcomp (λ k → λ { (i = i0) → inl x
                      ; (i = i1) → inr (μ e x y)
                      ; (j = i0) → (push (x , invEq (μ-eq' x) (μ e x y))
                                  ∙ (λ i₁ → inr (retEq≡secEq (μ-eq' x) y (~ k) i₁))) i
                      ; (j = i1) → push (x , y) i})
         (hcomp (λ k → λ { (i = i0) → inl x
                      ; (i = i1) → inr (μ e x (retEq (μ-eq' x) y k))
                      ; (j = i1) → push (x , retEq (μ-eq' x) y k) i})
                ((push (x , invEq (μ-eq' x) (μ e x y))) i))

  isEquivTotalSpaceHopfPush→TotalSpace :
    isEquiv TotalSpaceHopfPush→TotalSpace
  isEquivTotalSpaceHopfPush→TotalSpace =
    isoToIsEquiv (iso _ inv' sect retr)
    where
    inv' : _ → _
    inv' (north , y) = inl y
    inv' (south , y) = inr y
    inv' (merid a i , y) =
      hcomp (λ k → λ { (i = i0) → push (y , a) (~ k)
                      ; (i = i1) → inr y})
            (inr (ua-unglue (μ-eq a) i y))
      where

      pp : PathP (λ i → ua (μ-eq a) i → TotalSpaceHopfPush)
                 inl inr
      pp = ua→ {e = μ-eq a} {B = λ _ → TotalSpaceHopfPush} λ b → push (b , a)

    sect : (x : _) → TotalSpaceHopfPush→TotalSpace (inv' x) ≡ x
    sect (north , x) = refl
    sect (south , x) = refl
    sect (merid a i , y) j =
      hcomp (λ k → λ { (i = i0) → merid a (~ k ∧ ~ j)
                                  , ua-gluePt (μ-eq a) (~ k ∧ ~ j) y
                      ; (i = i1) → south , y
                      ; (j = i0) →
                        TotalSpaceHopfPush→TotalSpace
                         (hfill (λ k → λ { (i = i0) → push (y , a) (~ k)
                                          ; (i = i1) → inr y})
                                (inS (inr (ua-unglue (μ-eq a) i y)))
                                k)
                      ; (j = i1) → merid a i , y})
            ((merid a (i ∨ ~ j)) , lem (μ-eq a) i j y)
      where
      lem : ∀ {ℓ} {A B : Type ℓ} (e : A ≃ B) →
                PathP (λ i → PathP (λ j → (y : ua e i) → ua e (i ∨ ~ j))
                 (λ y → ua-unglue e i y)
                 λ y → y)
                 (λ j y → ua-gluePt e (~ j) y)
                 refl
      lem {A = A} {B = B} =
        EquivJ (λ B e → PathP (λ i → PathP (λ j → (y : ua e i) → ua e (i ∨ ~ j))
          (λ y → ua-unglue e i y)
           λ y → y)
           (λ j y → ua-gluePt e (~ j) y)
           refl)
           λ i j a → ua-gluePt (idEquiv B) (i ∨ ~ j) (ua-unglue (idEquiv B) i a)

    retr : retract TotalSpaceHopfPush→TotalSpace inv'
    retr (inl x) = refl
    retr (inr x) = refl
    retr (push (x , y) i) j =
      hcomp (λ k → λ { (i = i0) → push (x , y) (~ k)
                      ; (i = i1) → inr (μ e x y)
                      ; (j = i1) → push (x , y) (i ∨ ~ k)})
            (inr (μ e x y))

  IsoTotalSpaceJoin : Iso (Σ[ x ∈ Susp (typ A) ] Hopf x) (join (typ A) (typ A))
  IsoTotalSpaceJoin =
    compIso (equivToIso (invEquiv (_ , isEquivTotalSpaceHopfPush→TotalSpace)))
            joinIso₁

  induced : TotalSpaceHopfPush → Susp (typ A)
  induced = fst ∘ TotalSpaceHopfPush→TotalSpace

  ua-lem : (x y z : typ A) → (i j : I) → ua (μ-eq y) i
  ua-lem x y z i j =
    fill (λ k → ua (μ-eq y) i)
         (λ j → λ { (i = i0) → μ e z x
                  ; (i = i1) → μ-assoc e-ass z x y j})
          (inS (ua-gluePt (μ-eq y) i (μ e z x)))
          j

  TotalSpaceHopfPush→≃Hopf : (x : TotalSpaceHopfPush) → typ A ≃ Hopf (induced x)
  TotalSpaceHopfPush→≃Hopf (inl x) = μ-eq x
  TotalSpaceHopfPush→≃Hopf (inr x) = μ-eq x
  TotalSpaceHopfPush→≃Hopf (push (x , y) i₁) = pp x y i₁
    where
    pp : (x y : _) → PathP (λ i → typ A ≃ ua (μ-eq y) i) (μ-eq x) (μ-eq (μ e x y))
    pp x y = ΣPathP (P , help)
      where
      P : PathP (λ z → typ A → ua (μ-eq y) z) (fst (μ-eq x))
                (fst (μ-eq (μ e x y)))
      P i z = ua-lem x y z i i1

      abstract
        help : PathP (λ i₂ → isEquiv (P i₂)) (snd (μ-eq x))
                     (snd (μ-eq (μ e x y)))
        help = toPathP (isPropIsEquiv _ _ _)

  Push→TotalSpaceHopf : (a : typ A) (x : TotalSpaceHopfPush)
    → Σ[ x ∈ Susp (typ A) ] Hopf x
  Push→TotalSpaceHopf a x = (induced x) , fst (TotalSpaceHopfPush→≃Hopf x) a

  Push→TotalSpaceHopf-equiv : (a : typ A) → isEquiv (Push→TotalSpaceHopf a)
  Push→TotalSpaceHopf-equiv a = pRec (isPropIsEquiv _)
                    (J (λ a _ → isEquiv (Push→TotalSpaceHopf a))
                      (subst isEquiv (sym main)
                        isEquivTotalSpaceHopfPush→TotalSpace))
                    (conA (pt A) a)
    where
    lem₁ : (x : _) → fst ((Push→TotalSpaceHopf (pt A)) x)
                    ≡ fst (TotalSpaceHopfPush→TotalSpace x)
    lem₁ (inl x) = refl
    lem₁ (inr x) = refl
    lem₁ (push a i) = refl

    lem₂ : (x : _)
      → PathP (λ i → Hopf (lem₁ x i))
               (snd ((Push→TotalSpaceHopf (pt A)) x))
               (snd (TotalSpaceHopfPush→TotalSpace x))
    lem₂ (inl x) = μₗ e x
    lem₂ (inr x) = μₗ e x
    lem₂ (push (x , y) i) j =
      hcomp (λ k → λ {(i = i0) → μₗ e x j
                     ; (i = i1) → μ-assoc-filler e-ass x y j k
                     ; (j = i0) → ua-lem x y (pt A) i k
                     ; (j = i1) → ua-gluePt (μ-eq y) i x})
            (ua-gluePt (μ-eq y) i (μₗ e x j))

    main : Push→TotalSpaceHopf (pt A) ≡ TotalSpaceHopfPush→TotalSpace
    main i x = (lem₁ x i) , (lem₂ x i)

  TotalSpaceHopfPush² : Type _
  TotalSpaceHopfPush² = Pushout {A = TotalSpaceHopfPush} (λ _ → tt) induced

  P : TotalSpaceHopfPush² → Type _
  P (inl x) = typ A
  P (inr x) = Hopf x
  P (push a i) = ua (TotalSpaceHopfPush→≃Hopf a) i

  TotalSpacePush² : Type _
  TotalSpacePush² = Σ[ x ∈ TotalSpaceHopfPush² ] P x

  TotalSpacePush²' : Type _
  TotalSpacePush²' =
    Pushout {A = typ A × TotalSpaceHopfPush}
            {C = Σ[ x ∈ Susp (typ A) ] Hopf x}
            fst
            λ x → Push→TotalSpaceHopf (fst x) (snd x)

  IsoTotalSpacePush²TotalSpacePush²' : Iso TotalSpacePush² TotalSpacePush²'
  IsoTotalSpacePush²TotalSpacePush²' =
    compIso iso₂ (compIso (equivToIso fl.flatten) iso₁)
    where
    module fl =
      FlatteningLemma (λ _ → tt) induced (λ x → typ A)
                      Hopf TotalSpaceHopfPush→≃Hopf

    iso₁ : Iso (Pushout fl.Σf fl.Σg) TotalSpacePush²'
    fun iso₁ (inl x) = inl (snd x)
    fun iso₁ (inr x) = inr x
    fun iso₁ (push a i) = push ((snd a) , (fst a)) i
    inv iso₁ (inl x) = inl (tt , x)
    inv iso₁ (inr x) = inr x
    inv iso₁ (push a i) = push (snd a , fst a) i
    rightInv iso₁ (inl x) = refl
    rightInv iso₁ (inr x) = refl
    rightInv iso₁ (push a i) = refl
    leftInv iso₁ (inl x) = refl
    leftInv iso₁ (inr x) = refl
    leftInv iso₁ (push a i) = refl

    iso₂ : Iso TotalSpacePush² (Σ (Pushout (λ _ → tt) induced) fl.E)
    fun iso₂ (inl x , y) = inl x , y
    fun iso₂ (inr x , y) = inr x , y
    fun iso₂ (push a i , y) = push a i , y
    inv iso₂ (inl x , y) = inl x , y
    inv iso₂ (inr x , y) = inr x , y
    inv iso₂ (push a i , y) = push a i , y
    rightInv iso₂ (inl x , snd₁) = refl
    rightInv iso₂ (inr x , snd₁) = refl
    rightInv iso₂ (push a i , snd₁) = refl
    leftInv iso₂ (inl x , snd₁) = refl
    leftInv iso₂ (inr x , snd₁) = refl
    leftInv iso₂ (push a i , snd₁) = refl

  F : TotalSpacePush²'
     → (Pushout {A = typ A × Σ (Susp (typ A)) Hopf} fst snd)
  F (inl x) = inl x
  F (inr x) = inr x
  F (push (x , y) i) = push (x , Push→TotalSpaceHopf x y) i

  G : (Pushout {A = typ A × Σ (Susp (typ A)) Hopf} fst snd)
    → TotalSpacePush²'
  G (inl x) = inl x
  G (inr x) = inr x
  G (push (x , y) i) =
    hcomp (λ k → λ { (i = i0) → inl x
                    ; (i = i1)
                     → inr (secEq (_ , Push→TotalSpaceHopf-equiv x) y k)})
      (push (x , invEq (_ , Push→TotalSpaceHopf-equiv x) y) i)

  IsoTotalSpacePush²'ΣPush : Iso TotalSpacePush²'
           (Pushout {A = typ A × Σ (Susp (typ A)) Hopf} fst snd)
  fun IsoTotalSpacePush²'ΣPush = F
  inv IsoTotalSpacePush²'ΣPush = G
  rightInv IsoTotalSpacePush²'ΣPush (inl x) = refl
  rightInv IsoTotalSpacePush²'ΣPush (inr x) = refl
  rightInv IsoTotalSpacePush²'ΣPush (push (x , y) i) j =
    hcomp (λ k → λ { (i = i0) → inl x
                    ; (i = i1)
                     → inr (secEq (_ , Push→TotalSpaceHopf-equiv x) y k)
                    ; (j = i0) → F (
                         hfill (λ k →
                           λ { (i = i0) → inl x
                             ; (i = i1)
                              → inr (secEq (_
                                    , Push→TotalSpaceHopf-equiv x) y k)})
                          (inS (push (x
                                    , invEq (_
                                     , Push→TotalSpaceHopf-equiv x) y) i)) k)
                    ; (j = i1)
                     → push (x
                           , (secEq (_
                            , Push→TotalSpaceHopf-equiv x) y k)) i})
          (push (x , (secEq (_ , Push→TotalSpaceHopf-equiv x) y i0)) i)
  leftInv IsoTotalSpacePush²'ΣPush (inl x) = refl
  leftInv IsoTotalSpacePush²'ΣPush (inr x) = refl
  leftInv IsoTotalSpacePush²'ΣPush (push (x , y) i) j =
    hcomp (λ k → λ { (i = i0) → inl x
                    ; (i = i1) → inr (secEq (Push→TotalSpaceHopf x
                                           , Push→TotalSpaceHopf-equiv x)
                                        (Push→TotalSpaceHopf x y) (j ∨ k))
                    ; (j = i1) → push (x , y) i})
          (hcomp (λ k → λ { (i = i0) → inl x
                           ; (i = i1) → inr (retEq≡secEq
                                              (Push→TotalSpaceHopf x
                                             , Push→TotalSpaceHopf-equiv x)
                                               y (~ k) j)
                           ; (j = i1) → push (x , y) i
                           ; (j = i0) → push (x , invEq
                                               (Push→TotalSpaceHopf x
                                              , Push→TotalSpaceHopf-equiv x)
                                               (Push→TotalSpaceHopf x y)) i})
            (push (x , retEq (Push→TotalSpaceHopf x
                            , Push→TotalSpaceHopf-equiv x) y j) i))

  joinIso₂ : Iso TotalSpacePush² (join (typ A) (join (typ A) (typ A)))
  joinIso₂ =
    compIso IsoTotalSpacePush²TotalSpacePush²'
              (compIso IsoTotalSpacePush²'ΣPush
                (compIso (equivToIso (joinPushout≃join _ _))
                  (pathToIso (cong (join (typ A))
                             (isoToPath IsoTotalSpaceJoin)))))
