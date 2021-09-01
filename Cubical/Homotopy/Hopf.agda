{-# OPTIONS --safe #-}
module Cubical.Homotopy.Hopf where

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Groups.Connected
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.MayerVietorisUnreduced
open import Cubical.ZCohomology.Groups.Unit
open import Cubical.ZCohomology.Groups.Sn
open import Cubical.ZCohomology.RingStructure.CupProduct
open import Cubical.ZCohomology.RingStructure.RingLaws
open import Cubical.ZCohomology.RingStructure.GradedCommutativity

open import Cubical.Functions.Embedding

open import Cubical.Data.Fin

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Pointed.Homogeneous

open import Cubical.Foundations.Univalence

open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Sigma
open import Cubical.Data.Int hiding (_+'_)
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Algebra.Group
  renaming (ℤ to ℤGroup ; Unit to UnitGroup) hiding (Bool)

open import Cubical.HITs.Pushout.Flattening
open import Cubical.Homotopy.Connected
open import Cubical.HITs.Pushout
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.S1 renaming (_·_ to _*_)
open import Cubical.HITs.Truncation
  renaming (rec to trRec ; elim to trElim ; elim2 to trElim2)
open import Cubical.HITs.SetTruncation
  renaming (rec to sRec ; elim to sElim ; elim2 to sElim2 ; map to sMap)
open import Cubical.HITs.PropositionalTruncation
  renaming (rec to pRec ; elim to pElim)

open import Cubical.Algebra.AbGroup

open import Cubical.Homotopy.Loopspace

open import Cubical.HITs.Join


retEq≡secEq : ∀ {ℓ} {A B : Type ℓ} (e : A ≃ B)
                → (x : _) → secEq e (e .fst x) ≡ cong (e .fst) (retEq e x)
retEq≡secEq {A = A} =
  EquivJ (λ B e → (x : _) → secEq e (e .fst x) ≡ cong (e .fst) (retEq e x) )
         λ _ → refl

record HSpace {ℓ : Level} (A : Pointed ℓ) : Type ℓ where
  constructor HSp
  field
    μ : typ A → typ A → typ A
    μₗ : (x : typ A) → μ (pt A) x ≡ x
    μᵣ : (x : typ A) → μ x (pt A) ≡ x
    μₗᵣ : μₗ (pt A) ≡ μᵣ (pt A)

record assocHSpace {ℓ : Level} {A : Pointed ℓ} (e : HSpace A) : Type ℓ where
  constructor assocHSp
  field
    μ-assoc : (x y z : _) → HSpace.μ e (HSpace.μ e x y) z
                           ≡ HSpace.μ e x (HSpace.μ e y z)

    μ-assoc-filler : (y z : typ A)
      → PathP (λ i → HSpace.μ e (HSpace.μₗ e y i) z ≡ HSpace.μₗ e (HSpace.μ e y z) i)
               (μ-assoc (pt A) y z) refl

S1-HSpace : HSpace (S₊∙ 1)
HSpace.μ S1-HSpace = _*_
HSpace.μₗ S1-HSpace x = refl
HSpace.μᵣ S1-HSpace base = refl
HSpace.μᵣ S1-HSpace (loop i) = refl
HSpace.μₗᵣ S1-HSpace x = refl

S1-AssocHSpace : assocHSpace S1-HSpace
assocHSpace.μ-assoc S1-AssocHSpace base _ _ = refl
assocHSpace.μ-assoc S1-AssocHSpace (loop i) x y j = h x y j i
  where
  h : (x y : S₊ 1) → cong (_* y) (rotLoop x) ≡ rotLoop (x * y)
  h = wedgeconFun _ _ (λ _ _ → isOfHLevelPath 2 (isGroupoidS¹ _ _) _ _)
        (λ x → refl)
        (λ { base → refl ; (loop i) → refl})
        refl
assocHSpace.μ-assoc-filler S1-AssocHSpace _ _ = refl

module hopfBase {ℓ : Level} {A : Pointed ℓ} {e : HSpace A} (e-ass : assocHSpace e) (conA : ((x y : typ A) → ∥ x ≡ y ∥)) where
  isEquiv-μ : (x : typ A) → isEquiv (λ z → (HSpace.μ e z x))
  isEquiv-μ x = pRec (isPropIsEquiv _)
                     (J (λ x _ → isEquiv (λ z → HSpace.μ e z x))
                       (subst isEquiv (funExt (λ z → sym (HSpace.μᵣ e z))) (idIsEquiv (typ A))))
                     (conA (pt A) x)

  μ-eq : (x : typ A) → typ A ≃ typ A
  μ-eq x = (λ z → HSpace.μ e z x) , (isEquiv-μ x)

  isEquiv-μ' : (x : typ A) → isEquiv (HSpace.μ e x)
  isEquiv-μ' x =
    pRec (isPropIsEquiv _)
          (J (λ x _ → isEquiv (HSpace.μ e x))
            (subst isEquiv (funExt (λ x → sym (HSpace.μₗ e x))) (idIsEquiv (typ A))))
          (conA (pt A) x)

  μ-eq' : (x : typ A) → typ A ≃ typ A
  μ-eq' x = HSpace.μ e x , isEquiv-μ' x

  Hopf : Susp (typ A) → Type ℓ
  Hopf north = typ A
  Hopf south = typ A
  Hopf (merid a i₁) = ua (μ-eq a) i₁

  TotalSpaceHopf' : Type _
  TotalSpaceHopf' = Pushout {A = typ A × typ A} fst λ x → HSpace.μ e (fst x) (snd x)

  TotalSpaceHopf'→TotalSpace : TotalSpaceHopf' → Σ[ x ∈ Susp (typ A) ] Hopf x
  TotalSpaceHopf'→TotalSpace (inl x) = north , x
  TotalSpaceHopf'→TotalSpace (inr x) = south , x
  TotalSpaceHopf'→TotalSpace (push (x , y) i₁) = merid y i₁ , ua-gluePt (μ-eq y) i₁ x

  joinIso₁ : Iso (TotalSpaceHopf') (join (typ A) (typ A))
  joinIso₁ = iso F G s r
    where
    F : TotalSpaceHopf' → join (typ A) (typ A)
    F (inl x) = inl x
    F (inr x) = inr x
    F (push (a , x) i) = push a (HSpace.μ e a x) i

    G : join (typ A) (typ A) → TotalSpaceHopf'
    G (inl x) = inl x
    G (inr x) = inr x
    G (push a b i) = (push (a , invEq (μ-eq' a) b) ∙ cong inr (secEq (μ-eq' a) b)) i

    s : section F G
    s (inl x) = refl
    s (inr x) = refl
    s (push a b i) j =
      hcomp (λ k → λ { (i = i0) → inl a
                      ; (i = i1) → inr (secEq (μ-eq' a) b (j ∨ k))
                      ; (j = i0) → F (compPath-filler (push (a , invEq (μ-eq' a) b)) (cong inr (secEq (μ-eq' a) b)) k i)
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
                      ; (i = i1) → inr (HSpace.μ e x y)
                      ; (j = i0) → (push (x , invEq (μ-eq' x) (HSpace.μ e x y))
                                 ∙ (λ i₁ → inr (retEq≡secEq (μ-eq' x) y (~ k) i₁))) i
                      ; (j = i1) → push (x , y) i})
         (hcomp (λ k → λ { (i = i0) → inl x
                      ; (i = i1) → inr (HSpace.μ e x (retEq (μ-eq' x) y k))
                      ; (j = i1) → push (x , retEq (μ-eq' x) y k) i})
                ((push (x , invEq (μ-eq' x) (HSpace.μ e x y))) i))

  isEquivTotalSpaceHopf'→TotalSpace : isEquiv TotalSpaceHopf'→TotalSpace
  isEquivTotalSpaceHopf'→TotalSpace =
    isoToIsEquiv (iso _ inv inv* retr)
    where
    inv : _ → _
    inv (north , y) = inl y
    inv (south , y) = inr y
    inv (merid a i , y) =
      hcomp (λ k → λ { (i = i0) → push (y , a) (~ k)
                      ; (i = i1) → inr y})
            (inr (ua-unglue (μ-eq a) i y))
      where
      
      pp : PathP (λ i → ua (μ-eq a) i → TotalSpaceHopf') inl inr
      pp = ua→ {e = μ-eq a} {B = λ _ → TotalSpaceHopf'} λ b → push (b , a)

    inv* : (x : _) → TotalSpaceHopf'→TotalSpace (inv x) ≡ x
    inv* (north , x) = refl
    inv* (south , x) = refl
    inv* (merid a i , y) j =
      hcomp (λ k → λ { (i = i0) → merid a (~ k ∧ ~ j) , ua-gluePt (μ-eq a) (~ k ∧ ~ j) y
                      ; (i = i1) → south , y
                      ; (j = i0) → TotalSpaceHopf'→TotalSpace
                                      (hfill (λ k → λ { (i = i0) → push (y , a) (~ k)
                                                       ; (i = i1) → inr y})
                                             (inS (inr (ua-unglue (μ-eq a) i y)))
                                             k)
                      ; (j = i1) → merid a i , y})
            ((merid a (i ∨ ~ j)) , s (μ-eq a) i j y)
      where
      s : ∀ {ℓ} {A B : Type ℓ} (e : A ≃ B) →
                PathP (λ i → PathP (λ j → (y : ua e i) → ua e (i ∨ ~ j))
                 (λ y → ua-unglue e i y)
                 λ y → y)
                 (λ j y → ua-gluePt e (~ j) y)
                 refl
      s {A = A} {B = B} = EquivJ (λ B e → PathP (λ i → PathP (λ j → (y : ua e i) → ua e (i ∨ ~ j))
                 (λ y → ua-unglue e i y)
                 λ y → y)
                 (λ j y → ua-gluePt e (~ j) y)
                 refl)
                 h
        where
        h : _
        h i j a = ua-gluePt (idEquiv B) (i ∨ ~ j) (ua-unglue (idEquiv B) i a)


    retr : retract TotalSpaceHopf'→TotalSpace inv
    retr (inl x) = refl
    retr (inr x) = refl
    retr (push (x , y) i) j =
      hcomp (λ k → λ { (i = i0) → push (x , y) (~ k)
                      ; (i = i1) → inr (HSpace.μ e x y)
                      ; (j = i1) → push (x , y) (i ∨ ~ k)})
            (inr (HSpace.μ e x y))

  IsoTotalSpaceJoin : Iso (Σ[ x ∈ Susp (typ A) ] Hopf x) (join (typ A) (typ A))
  IsoTotalSpaceJoin =
    compIso (equivToIso (invEquiv (_ , isEquivTotalSpaceHopf'→TotalSpace)))
            joinIso₁

  induced : TotalSpaceHopf' → Susp (typ A)
  induced = fst ∘ TotalSpaceHopf'→TotalSpace

  lem : (x y z : typ A) → (i j : I) → ua (μ-eq y) i
  lem x y z i j =
    fill (λ k → ua (μ-eq y) i)
         (λ j → λ { (i = i0) → HSpace.μ e z x
                  ; (i = i1) → assocHSpace.μ-assoc e-ass z x y j})
          (inS (ua-gluePt (μ-eq y) i (HSpace.μ e z x)))
          j

  v : (x : TotalSpaceHopf') → typ A ≃ Hopf (induced x)
  v (inl x) = μ-eq x
  v (inr x) = μ-eq x
  v (push (x , y) i₁) = pp x y i₁
    where
    pp : (x y : _) → PathP (λ i → typ A ≃ ua (μ-eq y) i) (μ-eq x) (μ-eq (HSpace.μ e x y))
    pp x y = ΣPathP (P , help)
      where
      P : PathP (λ z → typ A → ua (μ-eq y) z) (fst (μ-eq x))
                (fst (μ-eq (HSpace.μ e x y)))
      P i z = lem x y z i i1

      abstract
        help : PathP (λ i₂ → isEquiv (P i₂)) (snd (μ-eq x))
                     (snd (μ-eq (HSpace.μ e x y)))
        help = toPathP (isPropIsEquiv _ _ _)

  v' : (a : typ A) (x : TotalSpaceHopf') → Σ[ x ∈ Susp (typ A) ] Hopf x
  v' a x = (induced x) , fst (v x) a

  v'-equiv : (a : typ A) → isEquiv (v' a)
  v'-equiv a = pRec (isPropIsEquiv _)
                    (J (λ a _ → isEquiv (v' a))
                      (subst isEquiv (sym main)
                        isEquivTotalSpaceHopf'→TotalSpace))
                    (conA (pt A) a)
    where
    help1 : (x : _) → fst ((v' (pt A)) x) ≡ fst (TotalSpaceHopf'→TotalSpace x)
    help1 (inl x) = refl
    help1 (inr x) = refl
    help1 (push a i) = refl

    help2 : (x : _)
      → PathP (λ i → Hopf (help1 x i))
               (snd ((v' (pt A)) x))
               (snd (TotalSpaceHopf'→TotalSpace x))
    help2 (inl x) = HSpace.μₗ e x
    help2 (inr x) = HSpace.μₗ e x
    help2 (push (x , y) i) j =
      hcomp (λ k → λ {(i = i0) → HSpace.μₗ e x j
                     ; (i = i1) → assocHSpace.μ-assoc-filler e-ass x y j k
                     ; (j = i0) → lem x y (pt A) i k
                     ; (j = i1) → ua-gluePt (μ-eq y) i x})
            (ua-gluePt (μ-eq y) i (HSpace.μₗ e x j))

    main : v' (pt A) ≡ TotalSpaceHopf'→TotalSpace 
    main i x = (help1 x i) , (help2 x i)

  megaPush : Type _
  megaPush = Pushout {A = TotalSpaceHopf'} (λ _ → tt) induced

  P : megaPush → Type _
  P (inl x) = typ A
  P (inr x) = Hopf x
  P (push a i) = ua (v a) i

  totalSpaceMegaPush : Type _
  totalSpaceMegaPush = Σ[ x ∈ megaPush ] P x

  totalSpaceMegaPush' : Type _
  totalSpaceMegaPush' =
    Pushout {A = typ A × TotalSpaceHopf'}
            {C = Σ[ x ∈ Susp (typ A) ] Hopf x}
            fst
            λ x → v' (fst x) (snd x)

  z : Iso totalSpaceMegaPush totalSpaceMegaPush'
  z = compIso whe2 (compIso (equivToIso fl.flatten) whe)
    where
    module fl = FlatteningLemma ((λ _ → tt)) induced (λ x → typ A) Hopf v
    
    whe : Iso (Pushout fl.Σf fl.Σg) totalSpaceMegaPush'
    Iso.fun whe (inl x) = inl (snd x)
    Iso.fun whe (inr x) = inr x
    Iso.fun whe (push a i) = push ((snd a) , (fst a)) i
    Iso.inv whe (inl x) = inl (tt , x)
    Iso.inv whe (inr x) = inr x
    Iso.inv whe (push a i) = push (snd a , fst a) i
    Iso.rightInv whe (inl x) = refl
    Iso.rightInv whe (inr x) = refl
    Iso.rightInv whe (push a i) = refl
    Iso.leftInv whe (inl x) = refl
    Iso.leftInv whe (inr x) = refl
    Iso.leftInv whe (push a i) = refl

    whe2 : Iso totalSpaceMegaPush (Σ (Pushout (λ _ → tt) induced) fl.E)
    Iso.fun whe2 (inl x , y) = inl x , y
    Iso.fun whe2 (inr x , y) = inr x , y
    Iso.fun whe2 (push a i , y) = push a i , y
    Iso.inv whe2 (inl x , y) = inl x , y
    Iso.inv whe2 (inr x , y) = inr x , y
    Iso.inv whe2 (push a i , y) = push a i , y
    Iso.rightInv whe2 (inl x , snd₁) = refl
    Iso.rightInv whe2 (inr x , snd₁) = refl
    Iso.rightInv whe2 (push a i , snd₁) = refl
    Iso.leftInv whe2 (inl x , snd₁) = refl
    Iso.leftInv whe2 (inr x , snd₁) = refl
    Iso.leftInv whe2 (push a i , snd₁) = refl

  F : totalSpaceMegaPush'
       →    (Pushout {A = typ A × Σ (Susp (typ A)) Hopf}
                    fst
                    snd)
  F (inl x) = inl x
  F (inr x) = inr x
  F (push (x , y) i) = push (x , v' x y) i

  G : (Pushout {A = typ A × Σ (Susp (typ A)) Hopf}
                    fst
                    snd)
                    → totalSpaceMegaPush'
  G (inl x) = inl x
  G (inr x) = inr x
  G (push (x , y) i) =
    hcomp (λ k → λ { (i = i0) → inl x
                    ; (i = i1) → inr (secEq (_ , v'-equiv x) y k)})
      (push (x , invEq (_ , v'-equiv x) y) i)

  zz : Iso totalSpaceMegaPush'
           (Pushout {A = typ A × Σ (Susp (typ A)) Hopf}
                    fst
                    snd)
  Iso.fun zz = F
  Iso.inv zz = G
  Iso.rightInv zz (inl x) = refl
  Iso.rightInv zz (inr x) = refl
  Iso.rightInv zz (push (x , y) i) j =
    hcomp (λ k → λ { (i = i0) → inl x
                    ; (i = i1) → inr (secEq (_ , v'-equiv x) y k)
                    ; (j = i0) → F (
                         hfill (λ k → λ { (i = i0) → inl x
                                         ; (i = i1) → inr (secEq (_ , v'-equiv x) y k)})
                            (inS (push (x , invEq (_ , v'-equiv x) y) i)) k)
                    ; (j = i1) → push (x , (secEq (_ , v'-equiv x) y k)) i})
          (push (x , (secEq (_ , v'-equiv x) y i0)) i)
  Iso.leftInv zz (inl x) = refl
  Iso.leftInv zz (inr x) = refl
  Iso.leftInv zz (push (x , y) i) j =
    hcomp (λ k → λ { (i = i0) → inl x
                    ; (i = i1) → inr (secEq (v' x , v'-equiv x) (v' x y) (j ∨ k))
                    ; (j = i1) → push (x , y) i})
          (hcomp (λ k → λ { (i = i0) → inl x
                           ; (i = i1) → inr (retEq≡secEq (v' x , v'-equiv x) y (~ k) j)
                           ; (j = i1) → push (x , y) i
                           ; (j = i0) → push (x , invEq (v' x , v'-equiv x) (v' x y)) i})
            (push (x , retEq (v' x , v'-equiv x) y j) i))

  IsoJoin₁ : Iso totalSpaceMegaPush (join (typ A) (join (typ A) (typ A)))
  IsoJoin₁ =
    compIso z (compIso zz (compIso (equivToIso (joinPushout≃join _ _))
              (pathToIso (cong (join (typ A)) (isoToPath IsoTotalSpaceJoin)))))
