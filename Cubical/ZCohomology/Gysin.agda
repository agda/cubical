{-# OPTIONS --safe --experimental-lossy-unification #-}
module Cubical.ZCohomology.Gysin where

open import Cubical.Foundations.Path
open import Cubical.Foundations.Equiv.HalfAdjoint
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

open import Cubical.Functions.Embedding

open import Cubical.Relation.Nullary

open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Int hiding (_+'_)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Fin

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.ZAction
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Int

open import Cubical.HITs.Truncation as T
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.Pushout.Flattening
open import Cubical.HITs.Pushout
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.S1 renaming (_·_ to _*_)
open import Cubical.HITs.Join

open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Hopf
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Group.Base

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Groups.Connected
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.MayerVietorisUnreduced
open import Cubical.ZCohomology.Groups.Unit
open import Cubical.ZCohomology.Groups.Wedge
open import Cubical.ZCohomology.Groups.Sn
open import Cubical.ZCohomology.RingStructure.CupProduct
open import Cubical.ZCohomology.RingStructure.RingLaws
open import Cubical.ZCohomology.RingStructure.GradedCommutativity

open PlusBis

-- There seems to be some problems with the termination checker.
-- Spelling out integer induction with 3 base cases like this
-- solves the issue.
private
  Int-ind : ∀ {ℓ} (P : ℤ → Type ℓ)
          → P (pos zero) → P (pos 1)
          → P (negsuc zero)
          → ((x y : ℤ) → P x → P y → P (x + y)) → (x : ℤ) → P x
  Int-ind P z one min ind (pos zero) = z
  Int-ind P z one min ind (pos (suc zero)) = one
  Int-ind P z one min ind (pos (suc (suc n))) =
    ind (pos (suc n)) 1  (Int-ind P z one min ind (pos (suc n))) one
  Int-ind P z one min ind (negsuc zero) = min
  Int-ind P z one min ind (negsuc (suc n)) =
    ind (negsuc n) (negsuc zero) (Int-ind P z one min ind (negsuc n)) min

-- The untruncated version (coHomRed n (S₊ n)), i.e.
-- (S₊∙ n →∙ coHomK-ptd n) is in fact equal to
-- (coHomRed n (S₊ n)). Its useful to formulate
-- (S₊∙ n →∙ coHomK-ptd n) as a group in its own right
-- and prove it equivalent to (coHomRed n (S₊ n)).

-- We start with the addition
private
  _++_ : ∀ {ℓ} {A : Pointed ℓ} {n : ℕ} →
        (A →∙ coHomK-ptd n) → (A →∙ coHomK-ptd n) → (A →∙ coHomK-ptd n)
  fst (f ++ g) x = fst f x +ₖ fst g x
  snd (f ++ g) = cong₂ _+ₖ_ (snd f) (snd g) ∙ rUnitₖ _ (0ₖ _)

-- If we truncate the addition, we get back our usual
-- addition on (coHomRed n (S₊ n))
addAgree : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ) (x y : A →∙ coHomK-ptd n)
         → Path (fst (coHomRedGrDir n A))
                 ∣ x ++ y ∣₂
                 (∣ x ∣₂ +ₕ∙ ∣ y ∣₂)
addAgree {A = A} zero f g =
  cong ∣_∣₂ (→∙Homogeneous≡ (isHomogeneousKn _) refl)
addAgree {A = A} (suc zero) f g =
  cong ∣_∣₂ (→∙Homogeneous≡ (isHomogeneousKn _) refl)
addAgree {A = A} (suc (suc n)) f g =
  cong ∣_∣₂ (→∙Homogeneous≡ (isHomogeneousKn _) refl)

-- We formulate (S₊∙ n →∙ coHomK-ptd n) as a group, πS.
module _ where
  open import Cubical.Algebra.Monoid
  open import Cubical.Algebra.Semigroup
  open GroupStr
  open IsGroup
  open IsMonoid
  open IsSemigroup
  πS : (n : ℕ) → Group ℓ-zero
  fst (πS n) = S₊∙ n →∙ coHomK-ptd n
  1g (snd (πS n)) = (λ _ → 0ₖ n) , refl
  GroupStr._·_ (snd (πS n)) f g = (λ x → fst f x +ₖ fst g x)
                                  , cong₂ _+ₖ_ (snd f) (snd g) ∙ rUnitₖ n (0ₖ n)
  inv (snd (πS n)) f = (λ x → -ₖ fst f x) , cong -ₖ_ (snd f) ∙ -0ₖ {n = n}
  isGroup (snd (πS n)) = makeIsGroup
                         (helper n)
                         (λ x y z → →∙Homogeneous≡
                                     (isHomogeneousKn n)
                                     (funExt λ w → assocₖ n (fst x w) (fst y w) (fst z w)))
                         (λ { (f , p) → →∙Homogeneous≡ (isHomogeneousKn n) (funExt λ x → rUnitₖ n (f x)) })
                         (λ { (f , p) → →∙Homogeneous≡ (isHomogeneousKn n) (funExt λ x → lUnitₖ n (f x)) })
                         (λ { (f , p) → →∙Homogeneous≡ (isHomogeneousKn n) (funExt λ x → rCancelₖ n (f x)) })
                         (λ { (f , p) → →∙Homogeneous≡ (isHomogeneousKn n) (funExt λ x → lCancelₖ n (f x)) })
          where
          helper : (n : ℕ) → isSet (S₊∙ n →∙ coHomK-ptd n)
          helper zero = isOfHLevelΣ 2 (isSetΠ (λ _ → isSetℤ))  λ _ → isOfHLevelPath 2 isSetℤ _ _
          helper (suc n) = isOfHLevel↑∙' 0 n


  isSetπS : (n : ℕ) → isSet (S₊∙ n →∙ coHomK-ptd n)
  isSetπS = λ n → is-set (snd (πS n))

-- πS is equivalent to (coHomRed n (S₊∙ n))
K : (n : ℕ) → GroupIso (coHomRedGrDir n (S₊∙ n)) (πS n)
fst (K n) = setTruncIdempotentIso (isSetπS n)
snd (K zero) =
  makeIsGroupHom
    (ST.elim2 (λ _ _ → isOfHLevelPath 2 (isSetπS 0) _ _)
      λ f g → →∙Homogeneous≡ (isHomogeneousKn 0) refl)
snd (K (suc zero)) =
    makeIsGroupHom
    (ST.elim2 (λ _ _ → isOfHLevelPath 2 (isSetπS 1) _ _)
      λ f g → →∙Homogeneous≡ (isHomogeneousKn 1) refl)
snd (K (suc (suc n))) =
    makeIsGroupHom
    (ST.elim2 (λ _ _ → isOfHLevelPath 2 (isSetπS _) _ _)
      λ f g → →∙Homogeneous≡ (isHomogeneousKn _) refl)

-- πS has the following generator
genFunSpace : (n : ℕ) → S₊∙ n →∙ coHomK-ptd n
fst (genFunSpace zero) false = 1
fst (genFunSpace zero) true = 0
snd (genFunSpace zero) = refl
fst (genFunSpace (suc n)) = ∣_∣
snd (genFunSpace (suc zero)) = refl
snd (genFunSpace (suc (suc n))) = refl

πS≅ℤ : (n : ℕ) → GroupIso (πS n) ℤGroup
fst (πS≅ℤ zero) = IsoBool→∙
snd (πS≅ℤ zero) = makeIsGroupHom λ _ _ → refl
πS≅ℤ (suc n) =
  compGroupIso
    (invGroupIso (K (suc n)))
    (compGroupIso
      (GroupEquiv→GroupIso (coHomGr≅coHomRedGr n (S₊∙ (suc n))))
      (Hⁿ-Sⁿ≅ℤ n))

Iso-πS-ℤ : (n : ℕ) → Iso (S₊∙ (suc n) →∙ coHomK-ptd (suc n)) ℤ
Iso-πS-ℤ n = compIso (invIso (setTruncIdempotentIso (isOfHLevel↑∙' 0 n)))
               (compIso (equivToIso (fst (coHomGr≅coHomRedGr n (S₊∙ (suc n)))))
               (fst (Hⁿ-Sⁿ≅ℤ n)))

Iso-πS-ℤ' : (n : ℕ) → Iso (S₊∙ n →∙ coHomK-ptd n) ℤ
Iso-πS-ℤ' n = fst (πS≅ℤ n)

Iso-πS-ℤPres1 : (n : ℕ) → Iso.fun (fst (πS≅ℤ (suc n))) (∣_∣ , refl) ≡ pos 1
Iso-πS-ℤPres1 zero = refl
Iso-πS-ℤPres1 (suc n) =
  cong (Iso.fun (fst (Hⁿ-Sⁿ≅ℤ n))) (lem n) ∙ Iso-πS-ℤPres1 n
  where
  lem : (n : ℕ) → Iso.fun (fst (suspensionAx-Sn n n)) ∣ ∣_∣ ∣₂ ≡ ∣ ∣_∣ ∣₂
  lem zero =
    cong ∣_∣₂ (funExt λ x → transportRefl (∣ x ∣ +ₖ (0ₖ 1)) ∙ rUnitₖ 1 ∣ x ∣)
  lem (suc n) = cong ∣_∣₂
    (funExt λ x → (λ i → transportRefl ((ΩKn+1→Kn (suc (suc n))
       (transp (λ j → 0ₖ (suc (suc (suc n))) ≡ ∣ merid north (~ j ∧ ~ i) ∣) i
        (λ z → ∣ compPath-filler
                  (merid (transportRefl (transportRefl x i) i))
                  (sym (merid north)) i z
           ∣)))) i)
    ∙ Iso.leftInv (Iso-Kn-ΩKn+1 (suc (suc n))) ∣ x ∣)

-- The first step of the Gysin sequence is to formulate
-- an equivalence g : Kᵢ ≃ (Sⁿ →∙ Kᵢ₊ₙ)
module g-base where
  g : (n : ℕ) (i : ℕ) → coHomK i → (S₊∙ n →∙ coHomK-ptd (i +' n))
  fst (g n i x) y = x ⌣ₖ (genFunSpace n) .fst y
  snd (g n i x) = cong (x ⌣ₖ_) ((genFunSpace n) .snd) ∙ ⌣ₖ-0ₖ i n x

  -- We give another version of g which will be easier to work with now
  G : (n : ℕ) (i : ℕ) → coHomK i → (S₊∙ n →∙ coHomK-ptd (n +' i))
  fst (G n i x) y = (genFunSpace n) .fst y ⌣ₖ x
  snd (G n i x) = cong (_⌣ₖ x) ((genFunSpace n) .snd) ∙ 0ₖ-⌣ₖ n i x

  -ₖ'^-Iso : (n : ℕ) (i : ℕ)
    → (S₊∙ n →∙ coHomK-ptd (i +' n)) ≃ (S₊∙ n →∙ coHomK-ptd (i +' n))
  -ₖ'^-Iso n i = isoToEquiv (iso F F FF FF)
    where
    lem : (i n : ℕ) → (-ₖ'^ i · n) (snd (coHomK-ptd (i +' n))) ≡ 0ₖ _
    lem zero zero = refl
    lem zero (suc zero) = refl
    lem zero (suc (suc n)) = refl
    lem (suc zero) zero = refl
    lem (suc (suc i)) zero = refl
    lem (suc i) (suc n) = refl

    F : S₊∙ n →∙ coHomK-ptd (i +' n) → S₊∙ n →∙ coHomK-ptd (i +' n)
    fst (F f) x = (-ₖ'^ i · n) (fst f x)
    snd (F f) = cong (-ₖ'^ i · n) (snd f) ∙ lem i n

    FF : (x : _) → F (F x) ≡ x
    FF x =
      →∙Homogeneous≡ (isHomogeneousKn _)
        (funExt λ y → -ₖ'-gen² i n _ _ (fst x y))

  transpPres0ₖ : ∀ {k m : ℕ} (p : k ≡ m) → subst coHomK p (0ₖ k) ≡ 0ₖ m
  transpPres0ₖ {k = k} =
    J (λ m p → subst coHomK p (0ₖ k) ≡ 0ₖ m) (transportRefl _)

  -- There will be some index swapping going on. We state this explicitly, since we will
  -- need to trace the maps later
  indexSwap : (n : ℕ) (i : ℕ)
    → (S₊∙ n →∙ coHomK-ptd (n +' i))
     ≃ (S₊∙ n →∙ coHomK-ptd (i +' n))
  indexSwap n i =
    isoToEquiv (iso (λ f → (λ x → subst coHomK (+'-comm n i) (fst f x)) ,
      cong (subst coHomK (+'-comm n i)) (snd f) ∙ transpPres0ₖ (+'-comm n i))
      (λ f → (λ x → subst coHomK (sym (+'-comm n i)) (fst f x))
            , (cong (subst coHomK (sym (+'-comm n i))) (snd f)
                    ∙ transpPres0ₖ (sym (+'-comm n i))))
      (λ f → →∙Homogeneous≡ (isHomogeneousKn _)
                (funExt λ x → transportTransport⁻ _ (f .fst x)))
      λ f → →∙Homogeneous≡ (isHomogeneousKn _)
                (funExt λ x → transportTransport⁻ _ (f .fst x)))

  -- g is a composition of G and our two previous equivs.
  g≡ : (n : ℕ) (i : ℕ) → g n i ≡ λ x
    → fst (compEquiv (indexSwap n i) (-ₖ'^-Iso n i)) ((G n i) x)
  g≡ n i = funExt (λ f → →∙Homogeneous≡ (isHomogeneousKn _)
             (funExt λ y → gradedComm'-⌣ₖ _ _ f (genFunSpace n .fst y)))

  -- We need a third Iso.

  suspKn-Iso-fun : (n m : ℕ) →
    (S₊∙ (suc n) →∙ coHomK-ptd (suc m))
        → (S₊ n → coHomK m)
  suspKn-Iso-fun zero m (f , p) false = ΩKn+1→Kn _ (sym p ∙∙ cong f loop ∙∙ p)
  suspKn-Iso-fun zero m (f , p) true = 0ₖ _
  suspKn-Iso-fun (suc n) m (f , p) x =
    ΩKn+1→Kn _ (sym p ∙∙ cong f (merid x ∙ sym (merid (ptSn _))) ∙∙ p)

  suspKn-Iso-fun∙ : (n m : ℕ) → (f : _) → suspKn-Iso-fun n m f (ptSn _) ≡ 0ₖ m
  suspKn-Iso-fun∙ zero m = λ _ → refl
  suspKn-Iso-fun∙ (suc n) m (f , p) =
    cong (ΩKn+1→Kn m)
      (cong (sym p ∙∙_∙∙ p) (cong (cong f) (rCancel (merid (ptSn _)))))
     ∙∙ cong (ΩKn+1→Kn m) (∙∙lCancel p)
     ∙∙ ΩKn+1→Kn-refl m

  suspKn-Iso-inv : (n m : ℕ) → (S₊∙ n →∙ coHomK-ptd m)
    → (S₊∙ (suc n) →∙ coHomK-ptd (suc m))
  fst (suspKn-Iso-inv zero m (f , p)) base = 0ₖ _
  fst (suspKn-Iso-inv zero m (f , p)) (loop i) = Kn→ΩKn+1 m (f false) i
  snd (suspKn-Iso-inv zero m (f , p)) = refl
  fst (suspKn-Iso-inv (suc n) m (f , p)) north = 0ₖ _
  fst (suspKn-Iso-inv (suc n) m (f , p)) south = 0ₖ _
  fst (suspKn-Iso-inv (suc n) m (f , p)) (merid a i) = Kn→ΩKn+1 m (f a) i
  snd (suspKn-Iso-inv (suc n) m (f , p)) = refl

  suspKn-Iso : (n m : ℕ) →
    Iso (S₊∙ (suc n) →∙ coHomK-ptd (suc m))
        (S₊∙ n →∙ coHomK-ptd m)
  Iso.fun (suspKn-Iso n m) f = (suspKn-Iso-fun n m f)
                             , (suspKn-Iso-fun∙ n m f)
  Iso.inv (suspKn-Iso n m) = suspKn-Iso-inv n m
  Iso.rightInv (suspKn-Iso zero m) (f , p) =
    →∙Homogeneous≡ (isHomogeneousKn _)
      (funExt λ { false → cong (ΩKn+1→Kn m) (sym (rUnit _))
                         ∙ Iso.leftInv (Iso-Kn-ΩKn+1 _) (f false)
                ; true → sym p})
  Iso.rightInv (suspKn-Iso (suc n) m) (f , p) =
    →∙Homogeneous≡ (isHomogeneousKn _)
      (funExt λ x →
         (λ i → ΩKn+1→Kn m
           (sym (rUnit
             (cong-∙
               (suspKn-Iso-inv (suc n) m (f , p) .fst)
                 (merid x) (sym (merid (ptSn _))) i)) i))
      ∙∙ cong (ΩKn+1→Kn m)
          (cong (Kn→ΩKn+1 m (f x) ∙_)
            (cong sym (cong (Kn→ΩKn+1 m) p ∙ Kn→ΩKn+10ₖ m))
             ∙ sym (rUnit _))
      ∙∙ Iso.leftInv (Iso-Kn-ΩKn+1 _)  (f x))
  Iso.leftInv (suspKn-Iso zero m) (f , p) = →∙Homogeneous≡ (isHomogeneousKn _)
    (funExt λ { base → sym p
              ; (loop i) j → lem j i})
    where
    lem : PathP (λ i → p (~ i) ≡ p (~ i))
               (Kn→ΩKn+1 m (ΩKn+1→Kn m (sym p ∙∙ cong f loop ∙∙ p)))
               (cong f loop)
    lem = Iso.rightInv (Iso-Kn-ΩKn+1 _) _
      ◁ λ i → doubleCompPath-filler (sym p) (cong f loop) p (~ i)
  Iso.leftInv (suspKn-Iso (suc n) m) (f , p) =
    →∙Homogeneous≡ (isHomogeneousKn _)
     (funExt λ { north → sym p
               ; south → sym p ∙ cong f (merid (ptSn _))
               ; (merid a i) j → lem a j i})
    where
    lem : (a : S₊ (suc n))
      → PathP (λ i → p (~ i) ≡ (sym p ∙ cong f (merid (ptSn (suc n)))) i)
               (Kn→ΩKn+1 m
                 (ΩKn+1→Kn m
                   (sym p ∙∙ cong f (merid a ∙ sym (merid (ptSn _))) ∙∙ p)))
               (cong f (merid a))
    lem a = Iso.rightInv (Iso-Kn-ΩKn+1 _) _
        ◁ λ i j → hcomp (λ k →
             λ { (i = i1) → (f (merid a j))
               ; (j = i0) → p (k ∧ ~ i)
               ; (j = i1) → compPath-filler'
                              (sym p) (cong f (merid (ptSn _))) k i })
               (f (compPath-filler (merid a) (sym (merid (ptSn _))) (~ i) j))

  glIsoInvHom : (n m : ℕ) (x y : coHomK n) (z : S₊ (suc m))
    → Iso.inv (suspKn-Iso _ _) (G m n (x +ₖ y)) .fst z
    ≡ Iso.inv (suspKn-Iso _ _) (G m n x) .fst z
    +ₖ Iso.inv (suspKn-Iso _ _) (G m n y) .fst z
  glIsoInvHom zero zero x y base = refl
  glIsoInvHom (suc n) zero x y base = refl
  glIsoInvHom zero zero x y (loop i) j = lem j i
    where
    lem : (cong (Iso.inv (suspKn-Iso _ _) (G zero zero (x + y)) .fst) loop)
        ≡ cong₂ _+ₖ_ (cong (Iso.inv (suspKn-Iso _ _) (G zero zero x) .fst) loop)
                     (cong (Iso.inv (suspKn-Iso _ _) (G zero zero y) .fst) loop)
    lem = Kn→ΩKn+1-hom 0 x y
     ∙ ∙≡+₁ (cong (Iso.inv (suspKn-Iso _ _) (G zero zero x) .fst) loop)
            (cong (Iso.inv (suspKn-Iso _ _) (G zero zero y) .fst) loop)
  glIsoInvHom (suc n) zero x y (loop i) j = lem j i
    where
    lem : Kn→ΩKn+1 (suc n) ((pos (suc zero)) ·₀ (x +ₖ y))
      ≡ cong₂ _+ₖ_ (cong (Iso.inv (suspKn-Iso zero (zero +' suc n))
                         (G zero (suc n) x) .fst) loop)
                   (cong (Iso.inv (suspKn-Iso zero (zero +' suc n))
                         (G zero (suc n) y) .fst) loop)
    lem = cong (Kn→ΩKn+1 (suc n)) (lUnit⌣ₖ _ (x +ₖ y))
     ∙∙ Kn→ΩKn+1-hom (suc n) x y
     ∙∙ (λ i → ∙≡+₂ n (Kn→ΩKn+1 (suc n) (lUnit⌣ₖ _ x (~ i)))
                       (Kn→ΩKn+1 (suc n) (lUnit⌣ₖ _ y (~ i))) i)
  glIsoInvHom zero (suc m) x y north = refl
  glIsoInvHom zero (suc m) x y south = refl
  glIsoInvHom zero (suc m) x y (merid a i) j = lem j i
    where
    lem : Kn→ΩKn+1 (suc m) (_⌣ₖ_ {n = suc m} {m = zero} ∣ a ∣ (x + y))
      ≡ cong₂ _+ₖ_ (Kn→ΩKn+1 (suc m) (_⌣ₖ_ {n = suc m} {m = zero} ∣ a ∣ x))
                   (Kn→ΩKn+1 (suc m) (_⌣ₖ_ {n = suc m} {m = zero} ∣ a ∣ y))
    lem = cong (Kn→ΩKn+1 (suc m)) (leftDistr-⌣ₖ (suc m) 0 ∣ a ∣ x y)
     ∙∙ Kn→ΩKn+1-hom (suc m) _ _
     ∙∙ ∙≡+₂ _ _ _
  glIsoInvHom (suc n) (suc m) x y north = refl
  glIsoInvHom (suc n) (suc m) x y south = refl
  glIsoInvHom (suc n) (suc m) x y (merid a i) j = lem j i
    where
    lem : Kn→ΩKn+1 (suc (suc (m +ℕ n)))
                   (_⌣ₖ_ {n = suc m} {m = suc n} ∣ a ∣ (x +ₖ y))
      ≡ cong₂ _+ₖ_ (Kn→ΩKn+1 (suc (suc (m +ℕ n)))
                     (_⌣ₖ_ {n = suc m} {m = suc n} ∣ a ∣ x))
                   (Kn→ΩKn+1 (suc (suc (m +ℕ n)))
                     (_⌣ₖ_ {n = suc m} {m = suc n} ∣ a ∣ y))
    lem = cong (Kn→ΩKn+1 (suc (suc (m +ℕ n))))
             (leftDistr-⌣ₖ (suc m) (suc n) ∣ a ∣ x y)
     ∙∙ Kn→ΩKn+1-hom _ _ _
     ∙∙ ∙≡+₂ _ _ _

  private
    +'-suc' : (n m : ℕ) → suc n +' m ≡ suc (n +' m)
    +'-suc' zero zero = refl
    +'-suc' (suc n) zero = refl
    +'-suc' zero (suc m) = refl
    +'-suc' (suc n) (suc m) = refl

  decomposeG : (i n : ℕ) (x : coHomK i)
    → G (suc n) i x
     ≡ subst (λ x → S₊∙ (suc n) →∙ coHomK-ptd x)
              (sym (+'-suc' n i))
              (Iso.inv (suspKn-Iso n _) (G n i x))
  decomposeG zero zero x =
    →∙Homogeneous≡ (isHomogeneousKn _)
      (funExt λ z → (λ i → x ·₀ ∣ z ∣) ∙ h3 x z ∙ sym (transportRefl _))
      where
      h3 : (x : ℤ) (z : S¹)
        → _·₀_ {n = 1} x ∣ z ∣
          ≡ fst (Iso.inv (suspKn-Iso 0 zero) (G zero zero x)) z
      h3 =
        Int-ind _
          (λ { base → refl ; (loop i) j → Kn→ΩKn+10ₖ zero (~ j) i})
          (λ { base → refl ; (loop i) j → rUnit (cong ∣_∣ₕ (lUnit loop j)) j i})
          (λ { base → refl ; (loop i) j → rUnit (cong ∣_∣ₕ (sym loop)) j i})
          λ x y inx iny z
            → rightDistr-⌣ₖ 0 1 x y ∣ z ∣
            ∙∙ cong₂ _+ₖ_ (inx z) (iny z)
            ∙∙ sym (glIsoInvHom zero zero x y z)
  decomposeG (suc i) zero x =
    →∙Homogeneous≡ (isHomogeneousKn _)
      (funExt λ z → lem z
            ∙ sym (transportRefl
               ((Iso.inv (suspKn-Iso zero (suc i)) (G zero (suc i) x)) .fst z)))
    where
    lem : (z : S₊ 1)
      → _ ≡ Iso.inv (suspKn-Iso zero (suc i)) (G zero (suc i) x) .fst z
    lem base = refl
    lem (loop k) j = Kn→ΩKn+1 (suc i) (lUnit⌣ₖ _ x (~ j)) k
  decomposeG zero (suc n) x =
    →∙Homogeneous≡ (isHomogeneousKn _)
      (funExt λ z → main x z
        ∙ λ i → transportRefl
                  (Iso.inv (suspKn-Iso (suc n) (suc n))
                           (G (suc n) zero x)) (~ i) .fst z)
      where
      +merid : rUnitₖ (suc (suc n)) ∣ south ∣ ≡ cong ∣_∣ₕ (merid (ptSn _))
      +merid = sym (lUnit _)
             ∙ cong (cong ∣_∣ₕ)
             λ j i → transp (λ _ → S₊ (suc (suc n))) (i ∨ j)
                             (merid (ptSn (suc n)) i)

      lem : (a : S₊ (suc n))
        → PathP (λ i → ∣ merid a i ∣ₕ
                       ≡ Kn→ΩKn+1 (suc n) (∣ a ∣ +ₖ (0ₖ _)) i)
                 refl (sym (rUnitₖ (suc (suc n)) ∣ south ∣))
      lem a =
        flipSquare ((λ i j → ∣ compPath-filler (merid a)
                                 (sym (merid (ptSn _))) i j ∣ₕ)
              ▷ cong (Kn→ΩKn+1 (suc n)) (sym (rUnitₖ (suc n) ∣ a ∣ₕ)))
            ▷ sym (cong sym +merid)

      lem₂ : (a : S₊ (suc n)) → (λ i → -ₖ ∣ merid a i ∣)
                               ≡ Kn→ΩKn+1 (suc n) (-ₖ ∣ a ∣)
      lem₂ a =
        cong (cong ∣_∣ₕ) (sym (symDistr (merid a)
                       (sym (merid (ptSn (suc n))))))
            ∙ sym (Kn→ΩKn+1-ₖ (suc n) ∣ a ∣)

      main : (x : ℤ) (z : S₊ (suc (suc n)))
       → _⌣ₖ_ {n = suc (suc n)} {m = 0} ∣ z ∣ x
        ≡ Iso.inv (suspKn-Iso (suc n) (suc n)) (G (suc n) zero x) .fst z
      main = Int-ind _
            (λ { north → refl ; south → refl
              ; (merid a i) j → Kn→ΩKn+10ₖ (suc n) (~ j) i})
            (λ { north → refl ; south → refl
               ; (merid a i) j →
                 hcomp (λ k →
                    λ { (i = i0) → ∣ north ∣
                      ; (i = i1) → rUnitₖ (suc (suc n)) ∣ south ∣ (~ k)
                      ; (j = i0) → rUnitₖ (suc (suc n)) ∣ merid a i ∣ (~ k)
                      ; (j = i1) → lem a i k})
                      ∣ merid a i ∣ₕ})
            (λ { north → refl
               ; south → refl
               ; (merid a i) j → lem₂ a j i})
            λ x y indx indy z → leftDistr-⌣ₖ _ _ ∣ z ∣ x y
                               ∙ cong₂ _+ₖ_ (indx z) (indy z)
                               ∙ sym (glIsoInvHom _ _ _ _ _)
  decomposeG (suc i) (suc n) x =
    →∙Homogeneous≡ (isHomogeneousKn _)
      (funExt λ z → lem z
         ∙ λ j →
           transportRefl ((Iso.inv (suspKn-Iso (suc n) (suc (suc (n +ℕ i))))
                     (G (suc n) (suc i) x))) (~ j) .fst z)
    where
    lem : (z : S₊ (suc (suc n))) → _
    lem north = refl
    lem south = refl
    lem (merid a i) = refl

  isEquivGzero : (i : ℕ) → isEquiv (G zero i)
  isEquivGzero i =
    isoToIsEquiv
      (iso _ (λ f → fst f false)
        (λ {(f , p) → →∙Homogeneous≡ (isHomogeneousKn _)
              (funExt λ { false → rUnitₖ _ (f false) ; true → sym p})})
        (lUnit⌣ₖ _))

  isEquivG : (n i : ℕ) → isEquiv (G n i)
  isEquivG zero i =
    isoToIsEquiv
      (iso _ (λ f → fst f false)
        (λ {(f , p) → →∙Homogeneous≡ (isHomogeneousKn _)
              (funExt λ { false → rUnitₖ _ (f false) ; true → sym p})})
        (lUnit⌣ₖ _))
  isEquivG (suc n) i =
    subst isEquiv (sym (funExt (decomposeG i n)))
      (compEquiv (compEquiv (G n i , isEquivG n i)
        (isoToEquiv (invIso (suspKn-Iso n (n +' i)))))
        (pathToEquiv (λ j → S₊∙ (suc n) →∙ coHomK-ptd (+'-suc' n i (~ j)))) .snd)

  isEquiv-g : (n i : ℕ) → isEquiv (g n i)
  isEquiv-g n i =
    subst isEquiv (sym (g≡ n i))
      (compEquiv (G n i , isEquivG n i)
        (compEquiv (indexSwap n i) (-ₖ'^-Iso n i)) .snd)

-- We now generealise the equivalence g to also apply to arbitrary fibrations (Q : B → Type)
-- satisfying (Q * ≃∙ Sⁿ)
module _ {ℓ} (B : Pointed ℓ) (Q : typ B → Pointed ℓ-zero)
         (conB : (x y : typ B) → ∥ x ≡ y ∥₁)
         (n : ℕ) (Q-is : Iso (typ (Q (pt B))) (S₊ n))
         (Q-is-ptd : Iso.fun Q-is (pt (Q (pt B))) ≡ snd (S₊∙ n))
         (c : (b : typ B) → (Q b →∙ coHomK-ptd n))
         (c-pt : c (pt B) .fst ≡ ((λ x → genFunSpace n .fst (Iso.fun Q-is x))))
         where

  g : (b : typ B) (i : ℕ) → coHomK i → (Q b →∙ coHomK-ptd (i +' n))
  fst (g b i x) y = x ⌣ₖ c b .fst y
  snd (g b i x) = cong (x ⌣ₖ_) (c b .snd) ∙ ⌣ₖ-0ₖ i n x

  g-hom : (b : typ B) (i : ℕ) → (x y : coHomK i)
        → g b i (x +ₖ y) ≡ ((g b i x) ++ (g b i y))
  g-hom b i x y =
    →∙Homogeneous≡ (isHomogeneousKn _)
      (funExt λ z → rightDistr-⌣ₖ i n x y (c b .fst z))

  gPathP' : (i : ℕ)
    → PathP (λ j → coHomK i →
                 (isoToPath Q-is j , ua-gluePath (isoToEquiv Q-is) (Q-is-ptd) j)
              →∙ coHomK-ptd (i +' n))
       (g (pt B) i) (g-base.g n i)
  gPathP' i =
    toPathP
      (funExt
      λ x → →∙Homogeneous≡ (isHomogeneousKn _)
          (funExt λ y
         → (λ i → transportRefl (transportRefl x i ⌣ₖ c (pt B) .fst
                                     (Iso.inv Q-is (transportRefl y i))) i)
                  ∙ cong (x ⌣ₖ_)
                         (funExt⁻ c-pt (Iso.inv Q-is y)
                            ∙ cong (genFunSpace n .fst) (Iso.rightInv Q-is y))))

  g-base : (i : ℕ) → isEquiv (g (pt B) i)
  g-base i = transport (λ j → isEquiv (gPathP' i (~ j))) (g-base.isEquiv-g n i)

  g-equiv : (b : typ B) (i : ℕ) → isEquiv (g b i)
  g-equiv b i =
    PT.rec (isPropIsEquiv _)
         (J (λ b _ → isEquiv (g b i))
           (g-base i))
         (conB (pt B) b)

module _ {ℓ} (B : Pointed ℓ) (Q : typ B → Pointed ℓ-zero)
         (conB : (x y : typ B) → ∥ x ≡ y ∥₂)
         (n : ℕ) (Q-is : Iso (typ (Q (pt B))) (S₊ n))
         (Q-is-ptd : Iso.fun Q-is (pt (Q (pt B))) ≡ snd (S₊∙ n)) where

  is-setQ→K : (b : typ B) → isSet (Q b →∙ coHomK-ptd n)
  is-setQ→K b =
    ST.rec (isProp→isOfHLevelSuc 1 isPropIsSet)
          (J (λ b _ → isSet (Q b →∙ coHomK-ptd n))
            (subst isSet (cong (_→∙ coHomK-ptd n)
              (ua∙ (isoToEquiv (invIso Q-is))
                   (cong (Iso.inv Q-is) (sym Q-is-ptd) ∙ Iso.leftInv Q-is _)))
              (isOfHLevelRetractFromIso 2 (fst (πS≅ℤ n)) isSetℤ)))
          (conB (pt B) b)


  isConnB : isConnected 3 (typ B)
  fst isConnB = ∣ pt B ∣
  snd isConnB =
    T.elim (λ _ → isOfHLevelPath 3 (isOfHLevelTrunc 3) _ _)
           λ a → ST.rec (isOfHLevelTrunc 3 _ _) (cong ∣_∣ₕ) (conB (pt B) a)

  isPropPath : isProp (∥ pt B ≡ pt B ∥₂)
  isPropPath =
    isOfHLevelRetractFromIso 1 setTruncTrunc2Iso
      (isContr→isProp (isConnectedPath _ isConnB (pt B) (pt B)))

  -- We construct a term in c* : (b : B) → (Q b →∙ Kₙ)
  -- Which is equal to the generator of (Sⁿ →∙ Kₙ) over the base point.
  c* : Σ[ c ∈ ((b : typ B) → (Q b →∙ coHomK-ptd n)) ]
         (c (pt B) .fst ≡ ((λ x → genFunSpace n .fst (Iso.fun Q-is x))))
  fst c* b =
    ST.rec (is-setQ→K b)
          (J (λ b _ → Q b →∙ coHomK-ptd n)
            ((λ x → genFunSpace n .fst (Iso.fun Q-is x))
           , cong (genFunSpace n .fst) Q-is-ptd ∙ genFunSpace n .snd))
         (conB (pt B) b)
  snd c* =
    funExt λ x → (λ i → ST.rec (is-setQ→K (pt B))
                  (J (λ b _ → Q b →∙ coHomK-ptd n)
                   ((λ x₁ → genFunSpace n .fst (Iso.fun Q-is x₁)) ,
                    (λ i → genFunSpace n .fst (Q-is-ptd i))
                          ∙ genFunSpace n .snd))
                  (isPropPath (conB (pt B) (pt B)) ∣ refl ∣₂ i) .fst x)
      ∙ (λ i → transportRefl (genFunSpace n .fst
                               (Iso.fun Q-is (transportRefl x i))) i)

  p-help : {b : fst B} (p : pt B ≡ b)
        → (subst (fst ∘ Q) (sym p) (snd (Q b))) ≡ (snd (Q (pt B)))
  p-help {b = b} =
    J (λ b p → subst (fst ∘ Q) (sym p) (snd (Q b)) ≡ snd (Q (pt B)))
      (transportRefl _)

  -- This form of c* will make things somewhat easier to work with later on.
  c≡ : (b : fst B) (p : ∥ pt B ≡ b ∥₂)
    → (c* .fst b)
      ≡ ST.rec (is-setQ→K b)
             (λ pp → (λ qb →
               genFunSpace n .fst (Iso.fun Q-is (subst (fst ∘ Q) (sym pp) qb)))
             , cong (genFunSpace n .fst ∘ Iso.fun Q-is) (p-help pp)
             ∙ ((λ i → genFunSpace n .fst (Q-is-ptd i)) ∙ genFunSpace n .snd)) p
  c≡ b =
    ST.elim (λ _ → isOfHLevelPath 2 (is-setQ→K b) _ _)
          (J (λ b a → c* .fst b ≡
      ST.rec (is-setQ→K b) (λ pp →
         (λ qb →
            genFunSpace n .fst (Iso.fun Q-is (subst (fst ∘ Q) (sym pp) qb)))
         ,
         cong (genFunSpace n .fst ∘ Iso.fun Q-is) (p-help pp) ∙
         (λ i → genFunSpace n .fst (Q-is-ptd i)) ∙ genFunSpace n .snd) ∣ a ∣₂)
      ((λ i → ST.rec (is-setQ→K (pt B))
      (J (λ b₁ _ → Q b₁ →∙ coHomK-ptd n)
       ((λ x → genFunSpace n .fst (Iso.fun Q-is x)) ,
        (λ i → genFunSpace n .fst (Q-is-ptd i)) ∙ genFunSpace n .snd))
          (isPropPath (conB (pt B) (pt B)) ∣ refl ∣₂ i))
          ∙ →∙Homogeneous≡ (isHomogeneousKn n)
            (transportRefl ((λ x → genFunSpace n .fst (Iso.fun Q-is x)))
            ∙ funExt λ x → cong (genFunSpace n .fst ∘ Iso.fun Q-is)
                     (sym (transportRefl x)))))

-- We are now almost ready to define the Thom isomorphism.
-- The following module contains the types and functions occuring in it.
module preThom {ℓ ℓ'} (B : Pointed ℓ) (P : typ B → Type ℓ') where
  E : Type _
  E = Σ (typ B) P

  Ẽ : Type _
  Ẽ = Pushout {A = E} (λ _ → tt) fst

  i : (n : ℕ) → (P-base : Iso (P (pt B)) (S₊ n)) → S₊ (suc n) → Ẽ
  i zero P-base base = inr (pt B)
  i zero P-base (loop j) = (sym (push (pt B , Iso.inv P-base false))
                               ∙ push ((pt B) , Iso.inv P-base true)) j
  i (suc n) P-base north = inl tt
  i (suc n) P-base south = inr (pt B)
  i (suc n) P-base (merid a i₁) = push (pt B , Iso.inv P-base a) i₁

  Q : typ B → Pointed ℓ'
  Q x = Susp (P x) , north

  F : Type _
  F = Σ (typ B) λ x → Q x .fst

  F̃ : Type _
  F̃ = Pushout {A = typ B} {C = F} (λ _ → tt) λ b → b , north

  invFE : Ẽ → F̃
  invFE (inl x) = inl tt
  invFE (inr x) = inr (x , south)
  invFE (push (x , a) i₁) = ((push x) ∙ λ i → inr (x , merid a i)) i₁

  funFE : F̃ → Ẽ
  funFE (inl x) = inl tt
  funFE (inr (x , north)) = inl tt
  funFE (inr (x , south)) = inr x
  funFE (inr (x , merid a i₁)) = push (x , a) i₁
  funFE (push a i₁) = inl tt

  IsoFE : Iso F̃ Ẽ
  Iso.fun IsoFE = funFE
  Iso.inv IsoFE = invFE
  Iso.rightInv IsoFE (inl x) = refl
  Iso.rightInv IsoFE (inr x) = refl
  Iso.rightInv IsoFE (push (x , a) i₁) k = lem k i₁
    where
    lem : cong funFE (((push x) ∙ λ i → inr (x , merid a i)))
        ≡ push (x , a)
    lem = congFunct funFE (push x) (λ i → inr (x , merid a i))
     ∙ sym (lUnit (push (x , a)))
  Iso.leftInv IsoFE (inl x) = refl
  Iso.leftInv IsoFE (inr (x , north)) = push x
  Iso.leftInv IsoFE (inr (x , south)) = refl
  Iso.leftInv IsoFE (inr (x , merid a i)) j =
    compPath-filler' (push x) (λ i₁ → inr (x , merid a i₁)) (~ j) i
  Iso.leftInv IsoFE (push a i₁) k =  push a (i₁ ∧ k)


  F̃→Q : ∀ {ℓ} {A : Pointed ℓ} → (F̃ , inl tt) →∙ A → (b : typ B) → Q b →∙ A
  fst (F̃→Q {A = A , a} (f , p) b) north = f (inr (b , north))
  fst (F̃→Q {A = A , a} (f , p) b) south = f (inr (b , south))
  fst (F̃→Q {A = A , a} (f , p) b) (merid a₁ i₁) = f (inr (b , merid a₁ i₁))
  snd (F̃→Q {A = A , a} (f , p) b) = sym (cong f (push b)) ∙ p

  Q→F̃ : ∀ {ℓ} {A : Pointed ℓ} → ((b : typ B) → Q b →∙ A) → (F̃ , inl tt) →∙ A
  fst (Q→F̃ {A = A , a} f) (inl x) = a
  fst (Q→F̃ {A = A , a} f) (inr (x , north)) = f x .fst north
  fst (Q→F̃ {A = A , a} f) (inr (x , south)) = f x .fst south
  fst (Q→F̃ {A = A , a} f) (inr (x , merid a₁ i₁)) = f x .fst (merid a₁ i₁)
  fst (Q→F̃ {A = A , a} f) (push a₁ i₁) = snd (f a₁) (~ i₁)
  snd (Q→F̃ {A = A , a} f) = refl

  Q→F̃-hom : (n : ℕ) → (f g : ((b : typ B) → Q b →∙ coHomK-ptd n))
             → Q→F̃ (λ b → f b ++ g b) ≡ (Q→F̃ f ++ Q→F̃ g)
  Q→F̃-hom n f g =
    →∙Homogeneous≡ (isHomogeneousKn _)
      (funExt λ { (inl x) → sym (rUnitₖ _ (0ₖ _))
                ; (inr (x , north)) → refl
                ; (inr (x , south)) → refl
                ; (inr (x , merid a i₁)) → refl
                ; (push a j) i →
                  compPath-filler (cong₂ _+ₖ_ (snd (f a)) (snd (g a)))
                                  (rUnitₖ n (0ₖ n)) (~ i) (~ j)})

  Q→F̃→Q : ∀ {ℓ} {A : Pointed ℓ}
    → (x : (b : typ B) → Q b →∙ A) (b : typ B) (q : Q b .fst)
    → F̃→Q (Q→F̃ x) b .fst q ≡ x b .fst q
  Q→F̃→Q f b north = refl
  Q→F̃→Q f b south = refl
  Q→F̃→Q f b (merid a i₁) = refl

  F̃→Q→F̃ : ∀ {ℓ} {A : Pointed ℓ} (f : F̃ → typ A) (p : _)
    → (x : F̃) → fst (Q→F̃ {A = A} (F̃→Q (f , p))) x ≡ f x
  F̃→Q→F̃ f p (inl x) = sym p
  F̃→Q→F̃ f p (inr (x , north)) = refl
  F̃→Q→F̃ f p (inr (x , south)) = refl
  F̃→Q→F̃ f p (inr (x , merid a i₁)) = refl
  F̃→Q→F̃ f p (push a i₁) j =
    compPath-filler (sym (cong f (push a))) p (~ j) (~ i₁)

  IsoF̃Q : ∀ {ℓ} {A : Pointed ℓ}
    → Iso ((F̃ , inl tt) →∙ A)
          ((b : typ B) → Q b →∙ A)
  Iso.fun (IsoF̃Q {A = A , a}) = F̃→Q
  Iso.inv (IsoF̃Q {A = A , a}) = Q→F̃
  Iso.rightInv (IsoF̃Q {A = A , a}) f =
    funExt λ b → ΣPathP (funExt (Q→F̃→Q f b)
               , sym (rUnit (snd (f b))))
  Iso.leftInv (IsoF̃Q {A = A , a}) (f , p) =
    ΣPathP ((funExt (F̃→Q→F̃ f p))
         , λ i j → p (~ i ∨ j))

  -- The main result
  ι : (k : ℕ) → Iso ((b : typ B) → Q b →∙ coHomK-ptd k)
                      ((Ẽ , inl tt) →∙ coHomK-ptd k)
  ι k = compIso (invIso IsoF̃Q) IsoFE-extend
    where

    IsoFE-extend : Iso ((F̃ , inl tt) →∙ coHomK-ptd k)
             ((Ẽ , inl tt) →∙ coHomK-ptd k)
    Iso.fun IsoFE-extend G = (λ x → G .fst (Iso.inv IsoFE x))
                , (snd G)
    Iso.inv IsoFE-extend G = (λ x → G .fst (Iso.fun IsoFE x))
                , (snd G)
    Iso.rightInv IsoFE-extend G =
      →∙Homogeneous≡ (isHomogeneousKn _)
        (funExt λ x → cong (G .fst) (Iso.rightInv IsoFE x))
    Iso.leftInv IsoFE-extend G =
      →∙Homogeneous≡ (isHomogeneousKn _)
        (funExt λ x → cong (G .fst) (Iso.leftInv IsoFE x))

  ι-hom : (k : ℕ) → (f g : ((b : typ B) → Q b →∙ coHomK-ptd k))
                   → Iso.fun (ι k) (λ b → f b ++ g b)
                   ≡ (Iso.fun (ι k) f ++ Iso.fun (ι k) g)
  ι-hom k f g =
    →∙Homogeneous≡ (isHomogeneousKn _)
        (funExt λ x → funExt⁻ (cong fst (Q→F̃-hom _ f g)) (invFE x))

-- Packing everything up gives us the Thom Isomorphism between
-- the nᵗʰ cohomology of B and the (n+i)ᵗʰ reduced cohomology of Ẽ,
-- as defined above
module Thom {ℓ} (B : Pointed ℓ) (P : typ B → Type ℓ-zero)
         (conB : (x y : typ B) → ∥ x ≡ y ∥₁)
         (n : ℕ) (Q-is : Iso (typ (preThom.Q B P (pt B))) (S₊ n))
         (Q-is-ptd : Iso.fun Q-is (pt (preThom.Q B P (pt B))) ≡ snd (S₊∙ n))
         (c : (b : typ B) → (preThom.Q B P b →∙ coHomK-ptd n))
         (c-pt : c (pt B) .fst ≡ ((λ x → genFunSpace n .fst (Iso.fun Q-is x))))
         where

  ϕ : (i : ℕ)
    → GroupEquiv (coHomGr i (typ B))
                  (coHomRedGrDir (i +' n) (preThom.Ẽ B P , inl tt))
  fst (ϕ i) =
    isoToEquiv
      (setTruncIso
        (compIso
          (codomainIsoDep
            λ b →
              equivToIso ((g B (preThom.Q B P) conB n Q-is Q-is-ptd c c-pt b i)
                 , g-equiv B (preThom.Q B P) conB n Q-is Q-is-ptd c c-pt b i))
            (preThom.ι B P (i +' n))))
  snd (ϕ i) =
    makeIsGroupHom
    (ST.elim2 (λ _ _ → isOfHLevelPath 2 squash₂ _ _)
      λ F G →
        cong ∣_∣₂ (cong (Iso.fun (preThom.ι B P (i +' n)))
                       (funExt (λ a →
                         g-hom B (preThom.Q B P)
                               conB n Q-is Q-is-ptd c c-pt a i (F a) (G a)))
                     ∙ preThom.ι-hom B P (i +' n) _ _)
           ∙ addAgree (i +' n) _ _)

-- We finally get the Gysin sequence
module Gysin {ℓ} (B : Pointed ℓ) (P : typ B → Type ℓ-zero)
         (conB : (x y : typ B) → ∥ x ≡ y ∥₂)
         (n : ℕ) (Q-is : Iso (typ (preThom.Q B P (pt B))) (S₊ n))
         (Q-is-ptd : Iso.fun Q-is (pt (preThom.Q B P (pt B))) ≡ snd (S₊∙ n))
         where

  0-connB : (x y : typ B) → ∥ x ≡ y ∥₁
  0-connB x y = ST.rec (isProp→isSet squash₁) (∥_∥₁.∣_∣₁) (conB x y)

  c = (c* B (preThom.Q B P) conB n Q-is Q-is-ptd .fst)
  c-ptd = (c* B (preThom.Q B P) conB n Q-is Q-is-ptd .snd)
  cEq = c≡ B (preThom.Q B P) conB n Q-is Q-is-ptd

  module w = Thom B P 0-connB n Q-is Q-is-ptd c c-ptd

  ϕ = w.ϕ

  E' = preThom.E B P

  E'̃ = preThom.Ẽ B P

  -- The generator of coHom n (typ B)
  e : coHom n (typ B)
  e = ∣ (λ b → c b .fst south) ∣₂

  -- The maps of interest are ⌣, p, E-susp and j*. In reality, we are interested
  -- in the composition of ϕ and j* (which is just the cup product),
  -- but it's easier to first give an exact sequence involving p, E-susp and j*
  ⌣-hom : (i : ℕ) → GroupHom (coHomGr i (typ B)) (coHomGr (i +' n) (typ B))
  fst (⌣-hom i) x = x ⌣ e
  snd (⌣-hom i) =
    makeIsGroupHom λ f g → rightDistr-⌣ _ _ f g e

  p : E' → typ B
  p = fst

  p-hom : (i : ℕ) → GroupHom (coHomGr i (typ B)) (coHomGr i E')
  p-hom i = coHomMorph _ p

  E-susp : (i : ℕ) →
    GroupHom (coHomGr i E') (coHomRedGrDir (suc i) (E'̃ , inl tt))
  fst (E-susp i) =
    ST.map λ f → (λ { (inl x) → 0ₖ _
                   ; (inr x) → 0ₖ _
                   ; (push a j) → Kn→ΩKn+1 _ (f a) j}) , refl
  snd (E-susp zero) =
    makeIsGroupHom (ST.elim2 (λ _ _ → isOfHLevelPath 2 squash₂ _ _)
      λ f g →
        cong ∣_∣₂ (→∙Homogeneous≡ (isHomogeneousKn 1)
          (funExt λ { (inl x) → refl
                    ; (inr x) → refl
                    ; (push a j) k →
                      (Kn→ΩKn+1-hom zero (f a) (g a)
                     ∙ ∙≡+₁ (Kn→ΩKn+1 _ (f a)) (Kn→ΩKn+1 _ (g a))) k j})))
  snd (E-susp (suc i)) =
    makeIsGroupHom (ST.elim2 (λ _ _ → isOfHLevelPath 2 squash₂ _ _)
      λ f g →
        cong ∣_∣₂ (→∙Homogeneous≡ (isHomogeneousKn _)
          (funExt λ { (inl x) → refl
                    ; (inr x) → refl
                    ; (push a j) k → (Kn→ΩKn+1-hom _ (f a) (g a)
                                   ∙ ∙≡+₂ _ (Kn→ΩKn+1 _ (f a))
                                            (Kn→ΩKn+1 _ (g a))) k j})))

  module cofibSeq where
    j* : (i : ℕ) →
      GroupHom (coHomRedGrDir i (E'̃ , (inl tt))) (coHomGr i (typ B))
    fst (j* i) = ST.map λ f → λ x → fst f (inr x)
    snd (j* zero) =
      makeIsGroupHom
        (ST.elim2 (λ _ _ → isOfHLevelPath 2 squash₂ _ _) λ _ _ → refl)
    snd (j* (suc zero)) =
      makeIsGroupHom
        (ST.elim2 (λ _ _ → isOfHLevelPath 2 squash₂ _ _) λ _ _ → refl)
    snd (j* (suc (suc i₁))) =
      makeIsGroupHom
        (ST.elim2 (λ _ _ → isOfHLevelPath 2 squash₂ _ _) λ _ _ → refl)

    Im-j⊂Ker-p : (i : ℕ) (x : _) → isInIm (j* i) x → isInKer (p-hom i) x
    Im-j⊂Ker-p i =
      ST.elim (λ _ → isSetΠ (λ _ → isOfHLevelPath 2 squash₂ _ _))
        λ f → PT.rec (squash₂ _ _)
          (uncurry (ST.elim (λ _ → isSetΠ (λ _ → isOfHLevelPath 2 squash₂ _ _))
            λ g P → subst (isInKer (p-hom i)) P
              (cong ∣_∣₂ (funExt λ x →
                cong (g .fst) (sym (push x)) ∙ g .snd))))

    Ker-p⊂Im-j : (i : ℕ) (x : _) → isInKer (p-hom i) x → isInIm (j* i) x
    Ker-p⊂Im-j i =
      ST.elim (λ _ → isSetΠ (λ _ → isProp→isSet squash₁))
        λ f ker → PT.rec squash₁
          (λ id → ∣ ∣ (λ { (inl x) → 0ₖ _
                         ; (inr x) → f x
                         ; (push a i₁) → funExt⁻ id a (~ i₁)}) , refl ∣₂
                         , refl ∣₁)
                   (Iso.fun PathIdTrunc₀Iso ker)

  Im-p⊂Ker-Susp : (i : ℕ) (x : _)
                → isInIm (p-hom i) x → isInKer (E-susp i) x
  Im-p⊂Ker-Susp i =
    ST.elim (λ _ → isSetΠ (λ _ → isOfHLevelPath 2 squash₂ _ _))
      λ f → PT.rec (squash₂ _ _)
        (uncurry (ST.elim (λ _ → isSetΠ (λ _ → isOfHLevelPath 2 squash₂ _ _))
          λ g y → subst (isInKer (E-susp i)) y
            (cong ∣_∣₂ (→∙Homogeneous≡ (isHomogeneousKn _)
              (funExt λ { (inl x) → refl
                        ; (inr x) → sym (Kn→ΩKn+1 _ (g x))
                        ; (push a j) k → Kn→ΩKn+1 i (g (fst a)) (~ k ∧ j)})))))

  Ker-Susp⊂Im-p : (i : ℕ) (x : _)
                → isInKer (E-susp i) x → isInIm (p-hom i) x
  Ker-Susp⊂Im-p i =
    ST.elim (λ _ → isSetΠ (λ _ → isProp→isSet squash₁))
      λ f ker → PT.rec squash₁
        (λ id → ∣ ∣ (λ x → ΩKn+1→Kn i (sym (funExt⁻ (cong fst id) (inr x)))) ∣₂
                  , cong ∣_∣₂ (funExt (λ { (a , b) →
                         cong (ΩKn+1→Kn i)
                           (lUnit _
                          ∙ cong (_∙ sym (funExt⁻ (λ i₁ → fst (id i₁)) (inr a)))
                           (sym (flipSquare (cong snd id))
                       ∙∙ (PathP→compPathR
                            (cong (funExt⁻ (cong fst id)) (push (a , b))))
                       ∙∙ assoc _ _ _
                        ∙ sym (rUnit _))
                        ∙ (sym (assoc _ _ _)
                        ∙∙ cong (Kn→ΩKn+1 i (f (a , b)) ∙_) (rCancel _)
                        ∙∙ sym (rUnit _)))
                        ∙ Iso.leftInv (Iso-Kn-ΩKn+1 _) (f (a , b))})) ∣₁)
        (Iso.fun PathIdTrunc₀Iso ker)

  Im-Susp⊂Ker-j : (i : ℕ) (x : _)
               → isInIm (E-susp i) x → isInKer (cofibSeq.j* (suc i)) x
  Im-Susp⊂Ker-j i =
    ST.elim (λ _ → isSetΠ (λ _ → isOfHLevelPath 2 squash₂ _ _))
      λ g → PT.rec (squash₂ _ _)
        (uncurry (ST.elim (λ _ → isSetΠ (λ _ → isOfHLevelPath 2 squash₂ _ _))
          λ f id → PT.rec (squash₂ _ _)
            (λ P → subst (isInKer (cofibSeq.j* (suc i))) (cong ∣_∣₂ P)
              (cong ∣_∣₂ refl))
            (Iso.fun PathIdTrunc₀Iso id)))

  Ker-j⊂Im-Susp : (i : ℕ) (x : _)
                → isInKer (cofibSeq.j* (suc i)) x → isInIm (E-susp i) x
  Ker-j⊂Im-Susp i =
    ST.elim (λ _ → isSetΠ (λ _ → isProp→isSet squash₁))
      λ f ker
       → PT.rec squash₁
          (λ p → ∣ ∣ (λ x → ΩKn+1→Kn _ (sym (snd f)
                                     ∙∙ cong (fst f) (push x)
                                     ∙∙ funExt⁻ p (fst x))) ∣₂
                  , cong ∣_∣₂ (→∙Homogeneous≡ (isHomogeneousKn _)
                    (funExt (λ { (inl x) → sym (snd f)
                               ; (inr x) → sym (funExt⁻ p x)
                               ; (push a j) k → h3 f p a k j}))) ∣₁)
          (Iso.fun PathIdTrunc₀Iso ker)
          where
          h3 : (f : (E'̃ , inl tt) →∙ coHomK-ptd (suc i))
           → (p : (fst f ∘ inr) ≡ (λ _ → 0ₖ (suc i)))
           → (a : preThom.E B P)
           → PathP (λ i → snd f (~ i) ≡ p (~ i) (fst a))
                   (Kn→ΩKn+1 i (ΩKn+1→Kn i (sym (snd f)
                                          ∙∙ cong (fst f) (push a)
                                          ∙∙ funExt⁻ p (fst a))))
                   (cong (fst f) (push a))
          h3 f p a =
            Iso.rightInv (Iso-Kn-ΩKn+1 i) _
              ◁ λ i j →
                 doubleCompPath-filler (sym (snd f)) (cong (fst f) (push a))
                 (funExt⁻ p (fst a)) (~ i) j

  -- We compose ϕ and j*. The above exact sequence will induce another one for
  -- this composition. In fact, this group hom is definitionally equal to
  -- (λ x → x ⌣ e) modulo truncation elimination and snd fields.
  ϕ∘j : (i : ℕ) → GroupHom (coHomGr i (typ B)) (coHomGr (i +' n) (typ B))
  ϕ∘j i = compGroupHom (fst (fst (ϕ i)) , snd (ϕ i)) (cofibSeq.j* (i +' n))

  private
    +'-suc' : (i n : ℕ) → (suc i +' n) ≡ suc (i +' n)
    +'-suc' zero zero = refl
    +'-suc' (suc i₁) zero = refl
    +'-suc' zero (suc n) = refl
    +'-suc' (suc i₁) (suc n) = refl

    Path→GroupPath : ∀ {ℓ ℓ'} {n m : ℕ} (G : ℕ → Group ℓ) (H : Group ℓ')
         (p : n ≡ m)
      → GroupEquiv (G n) H
      → GroupEquiv (G m) H
    Path→GroupPath {n = n} G H =
      J (λ m _ → GroupEquiv (G n) H → GroupEquiv (G m) H)
        λ p → p

    h-ret : ∀ {ℓ ℓ'} {n m : ℕ} (G : ℕ → Group ℓ) (H : Group ℓ')
      → (e : GroupEquiv (G n) H)
      → (p : n ≡ m)
      → (x : G m .fst)
      → invEq (fst e) (fst (fst (Path→GroupPath G H p e)) x)
       ≡ subst (λ x → G x .fst) (sym p) x
    h-ret G H e =
      J (λ m p → ((x : G m .fst)
               → invEq (fst e) (fst (fst (Path→GroupPath G H p e)) x)
                ≡ subst (λ x → G x .fst) (sym p) x))
        λ x → cong (invEq (fst e) )
              (λ i → transportRefl (transportRefl (fst (fst e)
                     (transportRefl (transportRefl x i) i)) i) i)
           ∙∙ retEq (fst e) x
           ∙∙ sym (transportRefl _)

  thomIso' : (i : ℕ) → GroupEquiv (coHomRedGrDir (suc (i +' n)) (E'̃ , inl tt))
                            (coHomGr (suc i) (typ B))
  thomIso' i = (Path→GroupPath
                (λ n → coHomRedGrDir n (E'̃ , inl tt)) _ (+'-suc' i n)
                  (invGroupEquiv (ϕ (suc i))))

  ϕ' : (i : ℕ) → GroupHom (coHomRedGrDir (suc (i +' n)) (E'̃ , inl tt))
                            (coHomGr (suc i) (typ B))
  ϕ' i = fst (fst (thomIso' i)) , snd (thomIso' i)

  susp∘ϕ : (i : ℕ) → GroupHom (coHomGr (i +' n) E') (coHomGr (suc i) (typ B))
  susp∘ϕ i = compGroupHom (E-susp (i +' n)) (ϕ' i)

  Im-ϕ∘j⊂Ker-p : (i : ℕ) (x : _) → isInIm (ϕ∘j i) x → isInKer (p-hom _) x
  Im-ϕ∘j⊂Ker-p i x p =
    cofibSeq.Im-j⊂Ker-p _ x
      (PT.rec squash₁ (uncurry (λ f p → ∣ fst (fst (ϕ _)) f , p ∣₁)) p)

  Ker-p⊂Im-ϕ∘j : (i : ℕ) (x : _) → isInKer (p-hom _) x → isInIm (ϕ∘j i) x
  Ker-p⊂Im-ϕ∘j i x p =
    PT.rec squash₁
      (uncurry (λ f p →
          ∣ (invEq (fst (ϕ _)) f)
         , (cong (fst (cofibSeq.j* _)) (secEq (fst (ϕ _)) f) ∙ p) ∣₁))
        (cofibSeq.Ker-p⊂Im-j _ x p)

  Im-p⊂KerSusp∘ϕ : (i : ℕ) (x : _)
                 → isInIm (p-hom _) x → isInKer (susp∘ϕ i) x
  Im-p⊂KerSusp∘ϕ i x p =
    cong (fst (ϕ' _)) (Im-p⊂Ker-Susp _ x p) ∙ IsGroupHom.pres1 (snd (ϕ' _))

  KerSusp∘ϕ⊂Im-p : (i : ℕ) (x : _)
    → isInKer (susp∘ϕ i) x → isInIm (p-hom _) x
  KerSusp∘ϕ⊂Im-p i x p =
    Ker-Susp⊂Im-p _ x (sym (retEq (fst (thomIso' _)) _)
                    ∙ (cong (invEq (fst (thomIso' _))) p
                    ∙ IsGroupHom.pres1 (snd (invGroupEquiv (thomIso' _)))))

  Im-Susp∘ϕ⊂Ker-ϕ∘j : (i : ℕ) → (x : _)
                    → isInIm (susp∘ϕ i) x → isInKer (ϕ∘j (suc i)) x
  Im-Susp∘ϕ⊂Ker-ϕ∘j i x =
    PT.rec (squash₂ _ _)
      (uncurry λ f → J (λ x p → isInKer (ϕ∘j (suc i)) x)
        ((λ i → fst (cofibSeq.j* _) (fst (fst (ϕ _)) (fst (ϕ' _) (fst (E-susp _) f))))
             ∙∙ cong (fst (cofibSeq.j* _))
                     ((h-ret (λ n → coHomRedGrDir n (E'̃ , inl tt)) _
                             (invGroupEquiv (ϕ (suc i))) (+'-suc' i n)) (fst (E-susp _) f))
             ∙∙ (natTranspLem _ (λ n → fst (cofibSeq.j* n)) (sym (+'-suc' i n))
             ∙ cong (subst (λ z → coHomGr z (typ B) .fst) (sym (+'-suc' i n)))
                    (Im-Susp⊂Ker-j _ (fst (E-susp (i +' n)) f) ∣ f , refl ∣₁)
              ∙ tLem i n)))
    where
    tLem : (i n : ℕ) → subst (λ z → coHomGr z (typ B) .fst) (sym (+'-suc' i n))
                               (0ₕ _) ≡ 0ₕ _
    tLem zero zero = refl
    tLem zero (suc n) = refl
    tLem (suc i₁) zero = refl
    tLem (suc i₁) (suc n) = refl

  Ker-ϕ∘j⊂Im-Susp∘ϕ : (i : ℕ) (x : _)
    → isInKer (ϕ∘j (suc i)) x → isInIm (susp∘ϕ i) x
  Ker-ϕ∘j⊂Im-Susp∘ϕ i x p =
    PT.rec squash₁
      (uncurry (λ f p → ∣ f , cong (fst (fst (thomIso' i))) p
                        ∙ secEq (fst (thomIso' _)) x ∣₁))
      (Ker-j⊂Im-Susp _ (invEq (fst (thomIso' _)) x)
        ((cong (cofibSeq.j* (suc (i +' n)) .fst ) lem₁
        ∙ natTranspLem _ (λ n → cofibSeq.j* n .fst) (+'-suc' i n))
        ∙∙ cong (transport (λ j → (coHomGr (+'-suc' i n j) (typ B) .fst))) p
        ∙∙ lem₂ i n))
    where
    lem₁ : invEq (fst (thomIso' i)) x
         ≡ transport (λ j → coHomRed (+'-suc' i n j)
                     (E'̃ , inl tt)) (fst (fst (ϕ _)) x)
    lem₁ = cong (transport (λ j → coHomRed (+'-suc' i n j) (E'̃ , inl tt)))
                (transportRefl _ ∙ cong (fst (fst (ϕ _)))
                  λ i → transportRefl (transportRefl x i) i)

    lem₂ : (i n : ℕ)
         → transport (λ j → coHomGr (+'-suc' i n j) (typ B) .fst)
                      (GroupStr.1g (coHomGr (suc i +' n) (typ B) .snd)) ≡ 0ₕ _
    lem₂ zero zero = refl
    lem₂ zero (suc n) = refl
    lem₂ (suc i₁) zero = refl
    lem₂ (suc i₁) (suc n) = refl

  -- Finally, we have that ϕ∘j is just the cup product, and we have arrived
  -- at an exact sequence involving it.
  ϕ∘j≡ : (i : ℕ) → ϕ∘j i ≡ ⌣-hom i
  ϕ∘j≡ i =
    Σ≡Prop (λ _ → isPropIsGroupHom _ _)
           (funExt (ST.elim (λ _ → isOfHLevelPath 2 squash₂ _ _)
           λ _ → refl))

  -- We can now restate the previous resluts for (λ x → x ⌣ e)
  Im-⌣e⊂Ker-p : (i : ℕ) (x : _)
              → isInIm (⌣-hom i) x → isInKer (p-hom _) x
  Im-⌣e⊂Ker-p i x p =
    Im-ϕ∘j⊂Ker-p i x (subst (λ p → isInIm p x) (sym (ϕ∘j≡ i)) p)

  Ker-p⊂Im-⌣e : (i : ℕ) (x : _)
              → isInKer (p-hom _) x → isInIm (⌣-hom i) x
  Ker-p⊂Im-⌣e i x p =
    subst (λ p → isInIm p x) (ϕ∘j≡ i) (Ker-p⊂Im-ϕ∘j i x p)

  Im-Susp∘ϕ⊂Ker-⌣e : (i : ℕ) (x : _)
                   → isInIm (susp∘ϕ i) x → isInKer (⌣-hom (suc i)) x
  Im-Susp∘ϕ⊂Ker-⌣e i x p =
    subst (λ p → isInKer p x) (ϕ∘j≡ (suc i)) (Im-Susp∘ϕ⊂Ker-ϕ∘j i x p)

  Ker-⌣e⊂Im-Susp∘ϕ : (i : ℕ) (x : _)
                   → isInKer (⌣-hom (suc i)) x → isInIm (susp∘ϕ i) x
  Ker-⌣e⊂Im-Susp∘ϕ i x p =
    Ker-ϕ∘j⊂Im-Susp∘ϕ i x (subst (λ p → isInKer p x) (sym (ϕ∘j≡ (suc i))) p)
