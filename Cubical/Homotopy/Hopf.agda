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
open import Cubical.Data.Int hiding (_·_)

open import Cubical.HITs.Pushout.Flattening
open import Cubical.HITs.Pushout
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.S1
open import Cubical.HITs.S2
open import Cubical.HITs.S3
open import Cubical.HITs.PropositionalTruncation
  renaming (rec to pRec ; elim to pElim)
open import Cubical.HITs.Join
open import Cubical.HITs.Interval
  renaming ( zero to I0 ; one to I1 )

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
  joinIso₁ = theIso
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

    theIso : Iso TotalSpaceHopfPush (join (typ A) (typ A))
    fun theIso = F
    inv theIso = G
    rightInv theIso = s
    leftInv theIso = r

  isEquivTotalSpaceHopfPush→TotalSpace :
    isEquiv TotalSpaceHopfPush→TotalSpace
  isEquivTotalSpaceHopfPush→TotalSpace =
    isoToIsEquiv theIso
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

    theIso : Iso TotalSpaceHopfPush (Σ (Susp (typ A)) Hopf)
    fun theIso = TotalSpaceHopfPush→TotalSpace
    inv theIso = inv'
    rightInv theIso = sect
    leftInv theIso = retr

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


-- Direct construction of Hopf fibration for S¹
module S¹Hopf where
  Border : (x : S¹) → (j : I) → Partial (j ∨ ~ j) (Σ Type₀ (λ T → T ≃ S¹))
  Border x j (j = i0) = S¹ , (x ·_) , rotIsEquiv x
  Border x j (j = i1) = S¹ , idEquiv S¹

  -- Hopf fibration using SuspS¹
  HopfSuspS¹ : SuspS¹ → Type₀
  HopfSuspS¹ north = S¹
  HopfSuspS¹ south = S¹
  HopfSuspS¹ (merid x j) = Glue S¹ (Border x j)

  -- Hopf fibration using S²
  -- TODO : prove that it is equivalent to HopfSuspS¹
  HopfS² : S² → Type₀
  HopfS² base = S¹
  HopfS² (surf i j) = Glue S¹ (λ { (i = i0) → _ , idEquiv S¹
                                 ; (i = i1) → _ , idEquiv S¹
                                 ; (j = i0) → _ , idEquiv S¹
                                 ; (j = i1) → _ , _ , rotIsEquiv (loop i) } )

  -- Hopf fibration using more direct definition of the rot equivalence
  -- TODO : prove that it is equivalent to HopfSuspS¹
  HopfS²' : S² → Type₀
  HopfS²' base = S¹
  HopfS²' (surf i j) = Glue S¹ (λ { (i = i0) → _ , rotLoopEquiv i0
                                  ; (i = i1) → _ , rotLoopEquiv i0
                                  ; (j = i0) → _ , rotLoopEquiv i0
                                  ; (j = i1) → _ , rotLoopEquiv i } )

  -- Total space of the fibration
  TotalHopf : Type₀
  TotalHopf = Σ SuspS¹ HopfSuspS¹

  -- Forward direction
  filler-1 : I → (j : I) → (y : S¹) → Glue S¹ (Border y j) → join S¹ S¹
  filler-1 i j y x = hfill (λ t → λ { (j = i0) → inl (rotInv-1 x y t)
                                    ; (j = i1) → inr x })
                           (inS (push ((unglue (j ∨ ~ j) x) · invLooper y) (unglue (j ∨ ~ j) x) j)) i

  TotalHopf→JoinS¹S¹ : TotalHopf → join S¹ S¹
  TotalHopf→JoinS¹S¹ (north , x) = inl x
  TotalHopf→JoinS¹S¹ (south , x) = inr x
  TotalHopf→JoinS¹S¹ (merid y j , x) = filler-1 i1 j y x

  -- Backward direction
  JoinS¹S¹→TotalHopf : join S¹ S¹ → TotalHopf
  JoinS¹S¹→TotalHopf (inl x) = (north , x)
  JoinS¹S¹→TotalHopf (inr x) = (south , x)
  JoinS¹S¹→TotalHopf (push y x j) =
    (merid (invLooper y · x) j
    , glue (λ { (j = i0) → y ; (j = i1) → x }) (rotInv-2 x y j))

  -- Now for the homotopies, we will need to fill squares indexed by x y : S¹ with value in S¹
  -- Some will be extremeley tough, but happen to be easy when x = y = base
  -- therefore, we fill them for x = y = base and then use the connectedness of S¹ × S¹ and
  -- the discreteness of ΩS¹ to get general fillers.

  -- To proceed with that strategy, we first need a lemma :
  -- the sections of the trivial fibration λ (_ : S¹) (_ : S¹) → Int are constant

  -- this should be generalized to a constant fibration over a connected space with
  -- discrete fiber
  fibℤ : S¹ → S¹ → Type₀
  fibℤ _ _ = ℤ

  S¹→HSet : (A : Type₀) (p : isSet A) (F : S¹ → A) (x : S¹) → F base ≡ F x
  S¹→HSet A p F base = refl {x = F base}
  S¹→HSet A p F (loop i) = f' i
    where
    f : PathP (λ i → F base ≡ F (loop i)) refl (cong F loop)
    f i = λ j → F (loop (i ∧ j))
    L : cong F loop ≡ refl
    L = p (F base) (F base) (f i1) refl
    f' : PathP (λ i → F base ≡ F (loop i)) (refl {x = F base}) (refl {x = F base})
    f' = transport (λ i → PathP (λ j → F base ≡ F (loop j)) refl (L i)) f

  constant-loop : (F : S¹ → S¹ → ℤ) → (x y : S¹) → F base base ≡ F x y
  constant-loop F x y = L0 ∙ L1
    where
    p : isSet (S¹ → ℤ)
    p = isSetΠ (λ _ → isSetℤ)
    L : F base ≡ F x
    L = S¹→HSet (S¹ → ℤ) p F x
    L0 : F base base ≡ F x base
    L0 i = L i base
    L1 : F x base ≡ F x y
    L1 = S¹→HSet ℤ isSetℤ (F x) y

  discretefib : (F : S¹ → S¹ → Type₀) → Type₀
  discretefib F = (a : (x y : S¹) → F x y) →
          (b : (x y : S¹) → F x y) →
          (a base base ≡ b base base) →
          (x y : S¹) → a x y ≡ b x y

  discretefib-fibℤ : discretefib fibℤ
  discretefib-fibℤ a b h x y i =
    hcomp (λ t → λ { (i = i0) → constant-loop a x y t
                   ; (i = i1) → constant-loop b x y t })
          (h i)

  -- first homotopy

  assocFiller-3-aux : I → I → I → I → S¹
  assocFiller-3-aux x y j i =
    hfill (λ t → λ { (i = i0) → rotInv-1 (loop y) (loop (~ y) · loop x) t
                   ; (i = i1) → rotInv-3 (loop y) (loop x) t
                   ; (x = i0) (y = i0) → base
                   ; (x = i0) (y = i1) → base
                   ; (x = i1) (y = i0) → base
                   ; (x = i1) (y = i1) → base })
          (inS ((rotInv-2 (loop x) (loop y) i) · (invLooper (loop (~ y) · loop x)))) j

  -- assocFiller-3-endpoint is used only in the type of the next function, to specify the
  -- second endpoint.
  -- However, I only need the first endpoint, but I cannot specify only one of them as is.
  -- TODO : use cubical extension types when available to remove assocFiller-3-endpoint
  assocFiller-3-endpoint : (x : S¹) → (y : S¹) → y ≡ y
  assocFiller-3-endpoint base base i = base
  assocFiller-3-endpoint (loop x) base i = assocFiller-3-aux x i0 i1 i
  assocFiller-3-endpoint base (loop y) i = assocFiller-3-aux i0 y i1 i
  assocFiller-3-endpoint (loop x) (loop y) i = assocFiller-3-aux x y i1 i

  assocFiller-3 : (x : S¹) → (y : S¹) →
                  PathP (λ j → rotInv-1 y (invLooper y · x) j ≡ rotInv-3 y x j)
                        (λ i → ((rotInv-2 x y i) · (invLooper (invLooper y · x))))
                        (assocFiller-3-endpoint x y)
  assocFiller-3 base base j i = base
  assocFiller-3 (loop x) base j i = assocFiller-3-aux x i0 j i
  assocFiller-3 base (loop y) j i = assocFiller-3-aux i0 y j i
  assocFiller-3 (loop x) (loop y) j i = assocFiller-3-aux x y j i

  assoc-3 : (_ y : S¹) → basedΩS¹ y
  assoc-3 x y i = assocFiller-3 x y i1 i

  fibℤ≡fibAssoc-3 : fibℤ ≡ (λ _ y → basedΩS¹ y)
  fibℤ≡fibAssoc-3 i = λ x y → basedΩS¹≡ℤ y (~ i)

  discretefib-fibAssoc-3 : discretefib (λ _ y → basedΩS¹ y)
  discretefib-fibAssoc-3 =
    transp (λ i → discretefib (fibℤ≡fibAssoc-3 i)) i0 discretefib-fibℤ

  assocConst-3 : (x y : S¹) → assoc-3 x y ≡ refl
  assocConst-3 x y = discretefib-fibAssoc-3 assoc-3 (λ _ _ → refl) refl x y

  assocSquare-3 : I → I → S¹ → S¹ → S¹
  assocSquare-3 i j x y = hcomp (λ t → λ { (i = i0) → assocFiller-3 x y j i0
                                         ; (i = i1) → assocFiller-3 x y j i1
                                         ; (j = i0) → assocFiller-3 x y i0 i
                                         ; (j = i1) → assocConst-3 x y t i })
                              (assocFiller-3 x y j i)

  filler-3 : I → I → S¹ → S¹ → join S¹ S¹
  filler-3 i j y x =
    hcomp (λ t → λ { (i = i0) → filler-1 t j (invLooper y · x)
                                             (glue (λ { (j = i0) → y ; (j = i1) → x })
                                                   (rotInv-2 x y j))
                   ; (i = i1) → push (rotInv-3 y x t) x j
                   ; (j = i0) → inl (assocSquare-3 i t x y)
                   ; (j = i1) → inr x })
          (push ((rotInv-2 x y (i ∨ j)) · (invLooper (invLooper y · x))) (rotInv-2 x y (i ∨ j)) j)

  JoinS¹S¹→TotalHopf→JoinS¹S¹ : ∀ x → TotalHopf→JoinS¹S¹ (JoinS¹S¹→TotalHopf x) ≡ x
  JoinS¹S¹→TotalHopf→JoinS¹S¹ (inl x) i = inl x
  JoinS¹S¹→TotalHopf→JoinS¹S¹ (inr x) i = inr x
  JoinS¹S¹→TotalHopf→JoinS¹S¹ (push y x j) i = filler-3 i j y x

  -- Second homotopy

  -- This HIT is the total space of the Hopf fibration but the ends of SuspS¹ have not been
  -- glued together yet — which makes it into a cylinder.
  -- This allows to write compositions that do not properly match at the endpoints. However,
  -- I suspect it is unnecessary. TODO : do without PseudoHopf

  PseudoHopf : Type₀
  PseudoHopf = (S¹ × Interval) × S¹

  PseudoHopf-π1 : PseudoHopf → S¹
  PseudoHopf-π1 ((y , _) , _) = y

  PseudoHopf-π2 : PseudoHopf → S¹
  PseudoHopf-π2 (_ , x) = x

  assocFiller-4-aux : I → I → I → I → S¹
  assocFiller-4-aux x y j i =
    hfill (λ t → λ { (i = i0) → ((invLooper (loop y · loop x · loop (~ y))) · (loop y · loop x))
                                · (rotInv-1 (loop x) (loop y) t)
                   ; (i = i1) → (rotInv-4 (loop y) (loop y · loop x) (~ t)) · loop x
                   ; (x = i0) (y = i0) → base
                   ; (x = i0) (y = i1) → base
                   ; (x = i1) (y = i0) → base
                   ; (x = i1) (y = i1) → base })
          (inS (rotInv-2 (loop y · loop x) (loop y · loop x · loop (~ y)) i)) j

  -- See assocFiller-3-endpoint
  -- TODO : use cubical extension types when available to remove assocFiller-4-endpoint
  assocFiller-4-endpoint : (x y : S¹) → basedΩS¹ (((invLooper (y · x · invLooper y)) · (y · x)) · x)
  assocFiller-4-endpoint base base i = base
  assocFiller-4-endpoint (loop x) base i = assocFiller-4-aux x i0 i1 i
  assocFiller-4-endpoint base (loop y) i = assocFiller-4-aux i0 y i1 i
  assocFiller-4-endpoint (loop x) (loop y) i = assocFiller-4-aux x y i1 i

  assocFiller-4 : (x y : S¹) →
                  PathP (λ j → ((invLooper (y · x · invLooper y)) · (y · x)) · (rotInv-1 x y j) ≡ (rotInv-4 y (y · x) (~ j)) · x)
                        (λ i → (rotInv-2 (y · x) (y · x · invLooper y) i))
                        (assocFiller-4-endpoint x y)
  assocFiller-4 base base j i = base
  assocFiller-4 (loop x) base j i = assocFiller-4-aux x i0 j i
  assocFiller-4 base (loop y) j i = assocFiller-4-aux i0 y j i
  assocFiller-4 (loop x) (loop y) j i = assocFiller-4-aux x y j i

  assoc-4 : (x y : S¹) → basedΩS¹ (((invLooper (y · x · invLooper y)) · (y · x)) · x)
  assoc-4 x y i = assocFiller-4 x y i1 i

  fibℤ≡fibAssoc-4 : fibℤ ≡ (λ x y → basedΩS¹ (((invLooper (y · x · invLooper y)) · (y · x)) · x))
  fibℤ≡fibAssoc-4 i = λ x y → basedΩS¹≡ℤ (((invLooper (y · x · invLooper y)) · (y · x)) · x) (~ i)

  discretefib-fibAssoc-4 : discretefib (λ x y → basedΩS¹ (((invLooper (y · x · invLooper y)) · (y · x)) · x))
  discretefib-fibAssoc-4 =
    transp (λ i → discretefib (fibℤ≡fibAssoc-4 i)) i0 discretefib-fibℤ

  assocConst-4 : (x y : S¹) → assoc-4 x y ≡ refl
  assocConst-4 x y = discretefib-fibAssoc-4 assoc-4 (λ _ _ → refl) refl x y

  assocSquare-4 : I → I → S¹ → S¹ → S¹
  assocSquare-4 i j x y =
    hcomp (λ t → λ { (i = i0) → assocFiller-4 x y j i0
                   ; (i = i1) → assocFiller-4 x y j i1
                   ; (j = i0) → assocFiller-4 x y i0 i
                   ; (j = i1) → assocConst-4 x y t i })
          (assocFiller-4 x y j i)

  filler-4-0 : (_ j : I) → (y : S¹) → Glue S¹ (Border y j) → PseudoHopf
  filler-4-0 i j y x =
    let x' = unglue (j ∨ ~ j) x in
    hfill (λ t → λ { (j = i0) → ((invLooper (y · x · invLooper y) · (y · x) , I0)
                                , invLooper (y · x · invLooper y) · (y · x) · (rotInv-1 x y t))
                   ; (j = i1) → ((invLooper (x · invLooper y) · x , I1) , x) })
          (inS ((invLooper (x' · invLooper y) · x' , seg j) , rotInv-2 x' (x' · invLooper y) j)) i

  filler-4-1 : (_ j : I) → (y : S¹) → Glue S¹ (Border y j) → PseudoHopf
  filler-4-1 i j y x =
    let x' = unglue (j ∨ ~ j) x in
    hfill (λ t → λ { (j = i0) → ((invLooper (y · x · invLooper y) · (y · x) , I0)
                                , (rotInv-4 y (y · x) (~ t)) · x)
                   ; (j = i1) → ((invLooper (x · invLooper y) · x , I1) , x) })
          (inS ((invLooper (x' · invLooper y) · x' , seg j) , unglue (j ∨ ~ j) x)) i

  filler-4-2 : (_ j : I) → (y : S¹) → Glue S¹ (Border y j) → TotalHopf
  filler-4-2 i j y x =
    let x' = unglue (j ∨ ~ j) x in
    hcomp (λ t → λ { (i = i0) → JoinS¹S¹→TotalHopf (filler-1 t j y x)
                   ; (i = i1) → (merid (PseudoHopf-π1 (filler-4-0 t j y x)) j
                                , glue (λ { (j = i0) → rotInv-1 x y t ; (j = i1) → x })
                                       (PseudoHopf-π2 (filler-4-0 t j y x)))
                   ; (j = i0) → (north , rotInv-1 x y t)
                   ; (j = i1) → (south , x) })
          (merid (invLooper (x' · invLooper y) · x') j
          , glue (λ { (j = i0) → y · x · invLooper y ; (j = i1) → x }) (rotInv-2 x' (x' · invLooper y) j))

  filler-4-3 : (_ j : I) → (y : S¹) → Glue S¹ (Border y j) → PseudoHopf
  filler-4-3 i j y x =
    let x' = unglue (j ∨ ~ j) x in
    hcomp (λ t → λ { (i = i0) → filler-4-0 t j y x
                   ; (i = i1) → filler-4-1 t j y x
                   ; (j = i0) → ((invLooper (y · x · invLooper y) · (y · x) , I0) , assocSquare-4 i t x y)
                   ; (j = i1) → ((invLooper (x · invLooper y) · x , I1) , x) })
          ((invLooper (x' · invLooper y) · x' , seg j) , rotInv-2 x' (x' · invLooper y) (i ∨ j))

  filler-4-4 : (_ j : I) → (y : S¹) → Glue S¹ (Border y j) → PseudoHopf
  filler-4-4 i j y x =
    let x' = unglue (j ∨ ~ j) x in
    hcomp (λ t → λ { (i = i0) → filler-4-1 t j y x
                   ; (i = i1) → ((y , seg j) , unglue (j ∨ ~ j) x)
                   ; (j = i0) → ((rotInv-4 y (y · x) i , I0)
                                , (rotInv-4 y (y · x) (i ∨ ~ t)) · x)
                   ; (j = i1) → ((rotInv-4 y x i , I1) , x) })
          ((rotInv-4 y x' i , seg j) , x')

  filler-4-5 : (_ j : I) → (y : S¹) → Glue S¹ (Border y j) → TotalHopf
  filler-4-5 i j y x =
    hcomp (λ t → λ { (i = i0) → filler-4-2 (~ t) j y x
                   ; (i = i1) → (merid (PseudoHopf-π1 (filler-4-4 t j y x)) j
                                , glue (λ { (j = i0) → x ; (j = i1) → x })
                                       (PseudoHopf-π2 (filler-4-4 t j y x)))
                   ; (j = i0) → (north , x)
                   ; (j = i1) → (south , x) })
          (merid (PseudoHopf-π1 (filler-4-3 i j y x)) j
          , glue (λ { (j = i0) → x ; (j = i1) → x }) (PseudoHopf-π2 (filler-4-3 i j y x)))

  TotalHopf→JoinS¹S¹→TotalHopf : ∀ x → JoinS¹S¹→TotalHopf (TotalHopf→JoinS¹S¹ x) ≡ x
  TotalHopf→JoinS¹S¹→TotalHopf (north , x) i = (north , x)
  TotalHopf→JoinS¹S¹→TotalHopf (south , x) i = (south , x)
  TotalHopf→JoinS¹S¹→TotalHopf (merid y j , x) i = filler-4-5 i j y x


  JoinS¹S¹≡TotalHopf : join S¹ S¹ ≡ TotalHopf
  JoinS¹S¹≡TotalHopf = isoToPath (iso JoinS¹S¹→TotalHopf
                                      TotalHopf→JoinS¹S¹
                                      TotalHopf→JoinS¹S¹→TotalHopf
                                      JoinS¹S¹→TotalHopf→JoinS¹S¹)

  S³≡TotalHopf : S³ ≡ TotalHopf
  S³≡TotalHopf = S³≡joinS¹S¹ ∙ JoinS¹S¹≡TotalHopf

  open Iso
  IsoS³TotalHopf : Iso (S₊ 3) TotalHopf
  fun IsoS³TotalHopf x = JoinS¹S¹→TotalHopf (S³→joinS¹S¹ (inv IsoS³S3 x))
  inv IsoS³TotalHopf x = fun IsoS³S3 (joinS¹S¹→S³ (TotalHopf→JoinS¹S¹ x))
  rightInv IsoS³TotalHopf x =
       cong (JoinS¹S¹→TotalHopf ∘ S³→joinS¹S¹)
            (leftInv IsoS³S3 (joinS¹S¹→S³ (TotalHopf→JoinS¹S¹ x)))
    ∙∙ cong JoinS¹S¹→TotalHopf
            (joinS¹S¹→S³→joinS¹S¹ (TotalHopf→JoinS¹S¹ x))
    ∙∙ TotalHopf→JoinS¹S¹→TotalHopf x
  leftInv IsoS³TotalHopf x =
       cong (fun IsoS³S3 ∘ joinS¹S¹→S³)
            (JoinS¹S¹→TotalHopf→JoinS¹S¹ (S³→joinS¹S¹ (inv IsoS³S3 x)))
    ∙∙ cong (fun IsoS³S3) (S³→joinS¹S¹→S³ (inv IsoS³S3 x))
    ∙∙ Iso.rightInv IsoS³S3 x
