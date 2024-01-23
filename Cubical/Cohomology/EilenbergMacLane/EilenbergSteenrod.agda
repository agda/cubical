{-# OPTIONS --safe --lossy-unification #-}

module Cubical.Cohomology.EilenbergMacLane.EilenbergSteenrod where

open import Cubical.Homotopy.EilenbergMacLane.GroupStructure
open import Cubical.Homotopy.EilenbergMacLane.Base
open import Cubical.Homotopy.EilenbergMacLane.Properties
open import Cubical.Homotopy.EilenbergSteenrod

open import Cubical.Cohomology.EilenbergMacLane.Base

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.Unit
open import Cubical.Algebra.Group.Instances.Unit
open import Cubical.Algebra.AbGroup.Instances.Pi

open import Cubical.HITs.Wedge
open import Cubical.HITs.Pushout
open import Cubical.HITs.Susp
open import Cubical.HITs.Truncation as T
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Int
open import Cubical.Data.Unit

open import Cubical.Axiom.Choice

open Iso
module _ where
  open coHomTheory

  -- This module verifies the (reduced) Eilenberg-Steenrod axioms for
  -- the following ℤ-indexed cohomology theory

  coHomRedℤ : ∀ {ℓ ℓ'} → AbGroup ℓ' → ℤ → Pointed ℓ → AbGroup (ℓ-max ℓ ℓ')
  coHomRedℤ G (pos n) A = coHomRedGr n G A
  coHomRedℤ G (negsuc n) A = UnitAbGroup

  module coHomRedℤ {ℓ ℓ'} {G : AbGroup ℓ} where
    Hmap∙ : (n : ℤ) {A B : Pointed ℓ'}
       → A →∙ B
       → AbGroupHom (coHomRedℤ G n B) (coHomRedℤ G n A)
    Hmap∙ (pos n) = coHomHom∙ n
    Hmap∙ (negsuc n) f = idGroupHom

    compAx : (n : ℤ) {A B C : Pointed ℓ'}
           (g : B →∙ C) (f : A →∙ B) →
          compGroupHom (Hmap∙ n g) (Hmap∙ n f)
        ≡ Hmap∙ n (g ∘∙ f)
    compAx (pos n) g f = Σ≡Prop (λ _ → isPropIsGroupHom _ _)
      (funExt (ST.elim (λ _ → isSetPathImplicit)
        λ a → cong ∣_∣₂ (→∙Homogeneous≡ (isHomogeneousEM n) refl)))
    compAx (negsuc n) g f = Σ≡Prop (λ _ → isPropIsGroupHom _ _) refl

    idAx : (n : ℤ) {A : Pointed ℓ'} →
          Hmap∙ n (idfun∙ A) ≡ idGroupHom
    idAx (pos n) = Σ≡Prop (λ _ → isPropIsGroupHom _ _)
      (funExt (ST.elim (λ _ → isSetPathImplicit)
        λ f → cong ∣_∣₂ (ΣPathP (refl , sym (lUnit (snd f))))))
    idAx (negsuc n) = refl

    suspMap : (n : ℤ) {A : Pointed ℓ'} →
        AbGroupHom (coHomRedℤ G (sucℤ n) (Susp (typ A) , north))
        (coHomRedℤ G n A)
    fst (suspMap (pos n) {A = A}) =
      ST.map λ f → (λ x → ΩEM+1→EM n
                            (sym (snd f)
                          ∙∙ cong (fst f) (merid x ∙ sym (merid (pt A)))
                          ∙∙ snd f))
        , cong (ΩEM+1→EM n)
               (cong (sym (snd f) ∙∙_∙∙ snd f)
                 (cong (cong (fst f))
                 (rCancel (merid (pt A))))
             ∙ ∙∙lCancel (snd f))
        ∙ ΩEM+1→EM-refl n
    snd (suspMap (pos n) {A = A}) =
      makeIsGroupHom
       (ST.elim2 (λ _ _ → isSetPathImplicit)
        (λ f g → cong ∣_∣₂ (→∙Homogeneous≡ (isHomogeneousEM n)
          (funExt λ x → main n _ (sym (snd f)) _ (sym (snd g))
                        (cong (fst f) (merid x ∙ sym (merid (pt A))))
                        (cong (fst g) (merid x ∙ sym (merid (pt A))))))))
      where
      main : (n : ℕ) (x : EM G (suc n)) (f0 : 0ₖ (suc n) ≡ x)
             (y : EM G (suc n)) (g0 : 0ₖ (suc n) ≡ y)
             (f1 : x ≡ x) (g1 : y ≡ y)
             → ΩEM+1→EM n (sym (cong₂ _+ₖ_ (sym f0) (sym g0)
                          ∙ rUnitₖ (suc n) (0ₖ (suc n)))
                          ∙∙ cong₂ _+ₖ_ f1 g1
                          ∙∙ (cong₂ _+ₖ_ (sym f0) (sym g0)
                          ∙ rUnitₖ (suc n) (0ₖ (suc n))))
              ≡ ΩEM+1→EM n (f0 ∙∙ f1 ∙∙ sym f0)
        +[ n ]ₖ ΩEM+1→EM n (g0 ∙∙ g1 ∙∙ sym g0)
      main zero = J> (J> λ f g →
           cong (ΩEM+1→EM {G = G} zero)
             (cong (λ x → sym x ∙∙ cong₂ _+ₖ_ f g ∙∙ x)
             (sym (rUnit refl))
            ∙∙ sym (rUnit _)
            ∙∙ cong₂+₁ f g)
           ∙∙ ΩEM+1→EM-hom zero f g
           ∙∙ cong₂ _+ₖ_ (cong (ΩEM+1→EM zero) (rUnit f))
                         (cong (ΩEM+1→EM zero) (rUnit g)))
      main (suc n) =
        J> (J> λ f g →
           cong (ΩEM+1→EM {G = G} (suc n))
             (cong (λ x → sym x ∙∙ cong₂ _+ₖ_ f g ∙∙ x)
             (sym (rUnit refl))
            ∙∙ sym (rUnit _)
            ∙∙ cong₂+₂ n f g)
           ∙∙ ΩEM+1→EM-hom (suc n) f g
           ∙∙ cong₂ _+ₖ_ (cong (ΩEM+1→EM (suc n)) (rUnit f))
                         (cong (ΩEM+1→EM (suc n)) (rUnit g)))
    fst (suspMap (negsuc n)) _ = tt*
    snd (suspMap (negsuc n)) = makeIsGroupHom λ _ _ → refl

    toSusp-coHomRed : (n : ℕ) {A : Pointed ℓ'}
      → A →∙ EM∙ G n → (Susp (typ A) , north) →∙ EM∙ G (suc n)
    fst (toSusp-coHomRed n f) north = 0ₖ (suc n)
    fst (toSusp-coHomRed n f) south = 0ₖ (suc n)
    fst (toSusp-coHomRed n f) (merid a i) = EM→ΩEM+1 n (fst f a) i
    snd (toSusp-coHomRed n f) = refl

    suspMapIso : (n : ℤ) {A : Pointed ℓ'} →
        AbGroupIso (coHomRedℤ G (sucℤ n) (Susp (typ A) , north))
                   (coHomRedℤ G n A)
    fun (fst (suspMapIso n)) = suspMap n .fst
    inv (fst (suspMapIso (pos n))) = ST.map (toSusp-coHomRed n)
    inv (fst (suspMapIso (negsuc zero))) _ = 0ₕ∙ zero
    inv (fst (suspMapIso (negsuc (suc n)))) _ = tt*
    rightInv (fst (suspMapIso (pos n) {A = A})) =
      ST.elim (λ _ → isSetPathImplicit)
        λ f → cong ∣_∣₂ (→∙Homogeneous≡ (isHomogeneousEM n)
          (funExt λ x → cong (ΩEM+1→EM n)
                     (sym (rUnit _)
                     ∙∙ cong-∙ (toSusp-coHomRed n f .fst)
                         (merid x) (sym (merid (pt A)))
                     ∙∙ cong (EM→ΩEM+1 n (fst f x) ∙_)
                             (cong sym (cong (EM→ΩEM+1 n) (snd f)
                                      ∙ EM→ΩEM+1-0ₖ n))
                      ∙ sym (rUnit _))
                     ∙ Iso.leftInv (Iso-EM-ΩEM+1 n) (fst f x)))
    rightInv (fst (suspMapIso (negsuc zero))) tt* = refl
    rightInv (fst (suspMapIso (negsuc (suc n)))) tt* = refl
    leftInv (fst (suspMapIso (pos n) {A = A})) =
      ST.elim (λ _ → isSetPathImplicit)
              λ f → cong ∣_∣₂ (→∙Homogeneous≡ (isHomogeneousEM (suc n))
                (funExt λ { north → sym (snd f)
                          ; south → sym (snd f) ∙ cong (fst f) (merid (pt A))
                          ; (merid a i) j → lem a f j i}))
      where
      lem : (a : typ A) (f : Susp∙ (typ A) →∙ EM∙ G (suc n))
        → PathP (λ i → snd f (~ i) ≡ (sym (snd f) ∙ cong (fst f) (merid (pt A))) i)
                 (EM→ΩEM+1 n (ΩEM+1→EM n (sym (snd f)
                                        ∙∙ cong (fst f) (toSusp A a)
                                        ∙∙ snd f)))
                 (cong (fst f) (merid a))
      lem a f = Iso.rightInv (Iso-EM-ΩEM+1 n) _
              ◁ λ i j → hcomp (λ k
                → λ { (i = i1) → fst f (merid a j)
                     ; (j = i0) → snd f (~ i ∧ k)
                     ; (j = i1) → compPath-filler'
                                 (sym (snd f)) (cong (fst f) (merid (pt A))) k i})
                   (fst f (compPath-filler (merid a)
                           (sym (merid (pt A))) (~ i) j))
    leftInv (fst (suspMapIso (negsuc zero) {A = A})) =
      ST.elim (λ _ → isSetPathImplicit)
              λ f → cong ∣_∣₂ (Σ≡Prop (λ _ → hLevelEM G 0 _ _)
                              (funExt (suspToPropElim (pt A)
                                (λ _ → hLevelEM G 0 _ _)
                                (sym (snd f)))))
    leftInv (fst (suspMapIso (negsuc (suc n)))) tt* = refl
    snd (suspMapIso n) = suspMap n .snd

  satisfies-ES : ∀ {ℓ ℓ'} (G : AbGroup ℓ) → coHomTheory {ℓ'} (coHomRedℤ G)
  Hmap (satisfies-ES G) = coHomRedℤ.Hmap∙
  HMapComp (satisfies-ES G) = coHomRedℤ.compAx
  HMapId (satisfies-ES G) = coHomRedℤ.idAx
  fst (Suspension (satisfies-ES G)) n = GroupIso→GroupEquiv (coHomRedℤ.suspMapIso n)
  snd (Suspension (satisfies-ES G)) f (pos n) =
    funExt (ST.elim (λ _ → isSetPathImplicit) λ f
      → cong ∣_∣₂ (→∙Homogeneous≡ (isHomogeneousEM (suc n))
                  (funExt λ { north → refl
                            ; south → refl
                            ; (merid a i) → refl})))
  snd (Suspension (satisfies-ES G)) f (negsuc zero) =
    funExt λ {tt* → cong ∣_∣₂ (Σ≡Prop (λ _ → hLevelEM G 0 _ _) refl)}
  snd (Suspension (satisfies-ES G)) f (negsuc (suc n)) = refl
  Exactness (satisfies-ES G) {A = A} {B = B} f (pos n) = isoToPath help
    where
    To : (x : coHomRed n G B)
      → isInKer (coHomHom∙ n f) x
      → isInIm (coHomHom∙ n (cfcod (fst f) , refl)) x
    To = ST.elim (λ _ → isSetΠ λ _ → isProp→isSet (isPropIsInIm _ _))
      λ g p → PT.map (λ id → ∣ (λ { (inl x) → 0ₖ n
                                   ; (inr x) → fst g x
                                   ; (push a i) → id (~ i) .fst a})
                              , snd g ∣₂
                    , cong ∣_∣₂ (→∙Homogeneous≡ (isHomogeneousEM n)
                              refl))
               (Iso.fun ST.PathIdTrunc₀Iso p)

    From : (x : coHomRed n G B)
      → isInIm (coHomHom∙ n (cfcod (fst f) , refl)) x
      → isInKer (coHomHom∙ n f) x
    From =
      ST.elim (λ _ → isSetΠ λ _ → isProp→isSet (isPropIsInKer _ _))
        λ g → PT.rec (isPropIsInKer _ _)
          (uncurry (ST.elim (λ _ → isSetΠ λ _ → isProp→isSet (isPropIsInKer _ _))
            λ h p → PT.rec (squash₂ _ _)
              (λ id → cong ∣_∣₂ (→∙Homogeneous≡ (isHomogeneousEM n)
                (funExt λ x → sym (funExt⁻ (cong fst id) (fst f x))
                                  ∙ cong (fst h) (sym (push x)
                                                ∙ push (pt A)
                                                ∙ λ i → inr (snd f i))
                                  ∙ snd h)))
              (Iso.fun ST.PathIdTrunc₀Iso p)))

    help : Iso (Ker (coHomHom∙ n f))
               (Im (coHomHom∙ n (cfcod (fst f) , refl)))
    fun help (x , p) = x , To x p
    inv help (x , p) = x , From x p
    rightInv help (x , p) = Σ≡Prop (λ _ → isPropIsInIm _ _) refl
    leftInv help (x , p) = Σ≡Prop (λ _ → isPropIsInKer _ _) refl
  Exactness (satisfies-ES {ℓ} {ℓ'} G) {A = A} {B = B} f (negsuc n) =
    isoToPath help
    where
    help : Iso (Ker (coHomRedℤ.Hmap∙ {G = G} (negsuc n) f))
               (Im (coHomRedℤ.Hmap∙ {G = G} (negsuc n) {A = B}
                (cfcod (fst f) , refl)))
    fun help (tt* , p) = tt* , ∣ tt* , refl ∣₁
    inv help (tt* , p) = tt* , refl
    rightInv help (tt* , p) = Σ≡Prop (λ _ → isPropIsInIm _ _) refl
    leftInv help (tt* , p) = Σ≡Prop (λ _ → isPropIsInKer _ _) refl
  Dimension (satisfies-ES G) (pos zero) p = ⊥.rec (p refl)
  fst (Dimension (satisfies-ES G) (pos (suc n)) _) = 0ₕ∙ (suc n)
  snd (Dimension (satisfies-ES G) (pos (suc n)) _) =
      ST.elim (λ _ → isSetPathImplicit)
        λ f → T.rec (isProp→isOfHLevelSuc n (squash₂ _ _))
          (λ p → cong ∣_∣₂ (→∙Homogeneous≡ (isHomogeneousEM (suc n))
            (funExt λ { (lift false) → sym p
                      ; (lift true) → sym (snd f)})))
          (Iso.fun (PathIdTruncIso (suc n))
           (isContr→isProp (isConnectedEM {G' = G} (suc n))
             ∣ fst f (lift false) ∣ ∣ 0ₖ (suc n) ∣))
  Dimension (satisfies-ES G) (negsuc n) _ = isContrUnit*
  BinaryWedge (satisfies-ES G) (pos n) {A = A} {B = B} =
    GroupIso→GroupEquiv main
    where
    main : GroupIso _ _
    fun (fst main) =
      ST.rec (isSet× squash₂ squash₂)
        λ f → ∣ f ∘∙ (inl , refl) ∣₂ , ∣ f ∘∙ (inr , sym (push tt)) ∣₂
    inv (fst main) =
      uncurry (ST.rec2 squash₂
        λ f g → ∣ (λ { (inl x) → fst f x
                     ; (inr x) → fst g x
                     ; (push a i) → (snd f ∙ sym (snd g)) i})
                , snd f ∣₂)
    rightInv (fst main) =
      uncurry
        (ST.elim2 (λ _ _ → isOfHLevelPath 2 (isSet× squash₂ squash₂) _ _)
        λ f g → ΣPathP
          ((cong ∣_∣₂ (→∙Homogeneous≡ (isHomogeneousEM n) refl))
         , cong ∣_∣₂ (→∙Homogeneous≡ (isHomogeneousEM n) refl)))
    leftInv (fst main) =
      ST.elim (λ _ → isSetPathImplicit)
       λ f → cong ∣_∣₂ (→∙Homogeneous≡ (isHomogeneousEM n)
         (funExt λ { (inl x) → refl
                   ; (inr x) → refl
                   ; (push a i) j → lem (snd f) (cong (fst f) (push tt)) j i}))
      where
      lem : ∀ {ℓ} {A : Type ℓ} {x y z : A}
        → (p : x ≡ y) (q : x ≡ z)
        → (refl ∙ p) ∙ sym (sym q ∙ p) ≡ q
      lem p q = cong₂ _∙_ (sym (lUnit p)) (symDistr (sym q) p)
              ∙ assoc p (sym p) q
              ∙ cong (_∙ q) (rCancel p)
              ∙ sym (lUnit q)
    snd main =
      makeIsGroupHom
       (ST.elim2 (λ _ _ → isOfHLevelPath 2 (isSet× squash₂ squash₂) _ _)
       λ f g → ΣPathP
         (cong ∣_∣₂ (→∙Homogeneous≡ (isHomogeneousEM n) refl)
        , (cong ∣_∣₂ (→∙Homogeneous≡ (isHomogeneousEM n) refl))))
  BinaryWedge (satisfies-ES G) (negsuc n) {A = A} {B = B} =
    invGroupEquiv (GroupIso→GroupEquiv lUnitGroupIso^)

open coHomTheoryGen
satisfies-ES-gen : ∀ {ℓ ℓ'} (G : AbGroup ℓ) → coHomTheoryGen {ℓ'} (coHomRedℤ G)
Hmap (satisfies-ES-gen G) = coHomTheory.Hmap (satisfies-ES G)
HMapComp (satisfies-ES-gen G) = coHomTheory.HMapComp (satisfies-ES G)
HMapId (satisfies-ES-gen G) = coHomTheory.HMapId (satisfies-ES G)
Suspension (satisfies-ES-gen G) = coHomTheory.Suspension (satisfies-ES G)
Exactness (satisfies-ES-gen G) = coHomTheory.Exactness (satisfies-ES G)
Dimension (satisfies-ES-gen G) = coHomTheory.Dimension (satisfies-ES G)
Wedge (satisfies-ES-gen G) (pos n) {I = I} satAC {A = A} =
  subst isEquiv altEquiv≡ (snd altEquiv)
  where
  eq : _ ≃ _
  fst eq = _
  snd eq = satAC _

  mainIso : Iso _ _
  fun mainIso = ST.map λ f i
    → (λ x → f .fst (inr (i , x))) , cong (fst f) (sym (push i)) ∙ snd f
  inv mainIso = ST.map λ f → (λ { (inl x) → 0ₖ n
                                 ; (inr x) → f (fst x) .fst (snd x)
                                 ; (push a i) → f a .snd (~ i)})
                     , refl
  rightInv mainIso = ST.elim (λ _ → isSetPathImplicit)
    λ f → cong ∣_∣₂ (funExt (λ i → ΣPathP (refl , (sym (rUnit (snd (f i)))))))
  leftInv mainIso = ST.elim (λ _ → isSetPathImplicit)
    λ f → cong ∣_∣₂ (ΣPathP ((funExt
      (λ { (inl x) → sym (snd f)
         ; (inr x) → refl
         ; (push a i) j
           → compPath-filler (cong (fst f) (sym (push a))) (snd f) (~ j) (~ i)}))
    , λ i j → snd f (~ i ∨ j)))

  altEquiv :  (coHomRedℤ G (pos n) (⋁gen∙ I A) .fst)
        ≃ (ΠAbGroup (λ i → coHomRedℤ G (pos n) (A i)) .fst)
  altEquiv = isoToEquiv
    (compIso
    (compIso (compIso mainIso setTruncTrunc2Iso)
             (equivToIso eq))
    (codomainIsoDep λ i → invIso setTruncTrunc2Iso))

  altEquiv≡ : fst altEquiv ≡ _
  altEquiv≡ = funExt (ST.elim (λ _ → isOfHLevelPath 2 (isSetΠ (λ _ → squash₂)) _ _)
    λ _ → refl)
Wedge (satisfies-ES-gen G) (negsuc n) {I = I} satAC {A = A} =
  isoToIsEquiv (iso _ (λ _ → tt*) (λ _ → refl) λ _ → refl)
