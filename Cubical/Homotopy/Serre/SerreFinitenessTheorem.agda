{-# OPTIONS --lossy-unification --safe #-}
module Cubical.Homotopy.Serre.SerreFinitenessTheorem where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma

open import Cubical.Homotopy.Connected
open import Cubical.HITs.Sn hiding (S)

open import Cubical.Homotopy.Serre.SAF
open import Cubical.Homotopy.Serre.FPAbGroup
open import Cubical.Homotopy.Serre.HomotopyGroups
open import Cubical.Homotopy.Serre.ConnectedCovers.Base
open import Cubical.Homotopy.Serre.ConnectedCovers.EMIsFiber
open import Cubical.Homotopy.Serre.CorollariesToHurewicz
open import Cubical.Homotopy.Serre.CorollariesToGanea

private
  variable
    ℓ ℓ' : Level

isFPId : (X : Pointed ℓ) (n : ℕ) → isFP (πAb n (X < (suc n) >)) ≡ isFP (πAb n X)
isFPId X n = λ i → isFP (πConnCovEq X n n ≤-refl i)

mutual
  saf→isFPπ : (X : Pointed ℓ) (safX : saf X) (scX : isConnected 3 (typ X)) (n : ℕ)
    → isFP (πAb n X)
  saf→isFPπ X safX scX zero = saf→isFPBottomπ X safX 0 scX
  saf→isFPπ X safX scX (suc n) =
    transport (isFPId X (suc n)) (saf→isFPBottomπ (X < (2 + n) >) (saf→saf<-> X safX scX (suc n)) (suc n) (ConnCovIsConn X (2 + n)))

  saf→saf<-> : (X : Pointed ℓ) (safX : saf X) (scX : isConnected 3 (typ X)) (n : ℕ)
    → saf (X < (suc n) >)
  saf→saf<-> X safX scX 0 = transport (λ i → saf (1ConnCovEq X scX i)) safX
  saf→saf<-> X safX scX (suc n) =
    safTotal (<->EMFibSeq X n) (Conn→ConnConnCov X 3 (suc n) scX)
      (saf→saf<-> X safX scX n) (isFP→safEM' (πAb n X) (saf→isFPπ X safX scX n) n)

-- Universe polymorphic for demonstration purposes,
-- but should get specialized back to spheres in ℓ-zero
isFPπAbSn : {ℓ : Level} (n m : ℕ) → isFP (πAb n (S {ℓ = ℓ} (2 + m)))
isFPπAbSn n m = saf→isFPπ (S (2 + m)) (saf-Sn (2 + m)) rem2 n
  where
  rem1 : isConnected 3 (S₊ (2 + m))
  rem1 = isConnectedSubtr' m 3 (sphereConnected (suc (suc m)))

  rem2 : isConnected 3 (S (2 + m) .fst)
  rem2 = isConnectedRetractFromIso 3 rUnit*×Iso rem1

open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.HITs.S1
open import Cubical.HITs.Susp
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Homotopy.Group.Base
open import Cubical.Homotopy.Group.PinSn
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Int
open import Cubical.Algebra.AbGroup.Instances.Int
open import Cubical.Algebra.AbGroup.Instances.IntMod
open import Cubical.Algebra.Group.Instances.IntMod
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group
open import Cubical.Algebra.AbGroup.FinitePresentation

open import Cubical.Data.Nat renaming (isEven to isEvenℕ ; _+_ to _+ℕ_)
open import Cubical.Data.Nat.IsEven
open import Cubical.Data.Bool hiding (_≤_)
open import Cubical.Data.Unit
open import Cubical.Data.Nat.Order
open import Cubical.Data.Int as ℤData renaming (_+_ to _+ℤ_)
open import Cubical.HITs.SetQuotients as SQ
open import Cubical.Data.Nat.Order.Inductive
open import Cubical.Algebra.Group.QuotientGroup
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup
open import Cubical.Algebra.Group.Instances.Unit
open import Cubical.HITs.SetTruncation as ST
open import Cubical.Algebra.Group.Instances.Bool
open import Cubical.HITs.Truncation as TR

open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Group.Base
open import Cubical.Data.Empty as ⊥

open import Cubical.Algebra.Group.ZAction

-- TODO: upstream and add for Group as well
AbGroupIso→AbGroupEquiv : {G : AbGroup ℓ} {H : AbGroup ℓ'} → AbGroupIso G H → AbGroupEquiv G H
AbGroupIso→AbGroupEquiv (e , h) = isoToEquiv e , h

-- How is this not in the library yet??
isOfHLevel+ : ∀ {ℓ} {A : Type ℓ} (n m : ℕ) → isOfHLevel n A → isOfHLevel (m + n) A
isOfHLevel+ n zero h = h
isOfHLevel+ n (suc m) h = isOfHLevelSuc (m + n) (isOfHLevel+ n m h)

πLowHLevel : ∀ {ℓ} {A : Pointed ℓ} → (n : ℕ) → isOfHLevel (suc n) (typ A) → isContr (π n A)
πLowHLevel {A = A} zero p =
  isContr→isContrSetTrunc (pt A , p _)
πLowHLevel (suc n) p =
  subst isContr (isoToPath (Iso-πΩ-π n)) (πLowHLevel n (p _ _))

πVanish : ∀ {ℓ} {A : Pointed ℓ} (n m : ℕ) (le : n ≤ suc m) (hA : isOfHLevel n (fst A)) → isContr (π m A)
πVanish zero m le HA = πLowHLevel m (isProp→isOfHLevelSuc m (isContr→isProp HA))
πVanish {A = A} (suc zero) zero le HA =
  πLowHLevel zero (isProp→isOfHLevelSuc zero HA)
πVanish {A = A} (suc (suc n)) zero le HA =
  ⊥.rec (snotz (cong predℕ (+-comm (suc (suc n)) (le .fst) ∙ snd le)))
πVanish {A = A} (suc n) (suc m) le HA =
  subst isContr
    (isoToPath (Iso-πΩ-π m))
    (πVanish {A = Ω A} n m (pred-≤-pred le) (isOfHLevelPath' n HA _ _))

π'Vanish : ∀ {ℓ} {A : Pointed ℓ} (n m : ℕ) (le : n ≤ suc m) (hA : isOfHLevel n (fst A))
  → isContr (π' m A)
π'Vanish n m le hA = isOfHLevelRetractFromIso 0 (setTruncIso (IsoSphereMapΩ m)) (πVanish n m le hA)

open FinitePresentation
open AbGroupStr

-- This could probably be done nicer?
finPresTrivialAbGroup : FinitePresentation {ℓ = ℓ} trivialAbGroup
finPresTrivialAbGroup .nGens = 0
finPresTrivialAbGroup .nRels = 0
finPresTrivialAbGroup .rels = (λ x y → pos 0) , record { pres· = λ x y i x₁ → pos 0 ; pres1 = λ i x → pos 0 ; presinv = λ x i x₁ → pos 0 }
finPresTrivialAbGroup .fpiso .fst .Iso.fun = λ x → [ (λ x₁ → pos 0) ]
finPresTrivialAbGroup .fpiso .fst .Iso.inv = λ x → lift tt
finPresTrivialAbGroup .fpiso .fst .Iso.sec = elimProp (λ x → is-set (snd (ℤ[Fin 0 ] /Im _) ) _ _) λ a → cong [_] (funExt (λ { () }))
finPresTrivialAbGroup .fpiso .fst .Iso.ret (lift tt) = refl
finPresTrivialAbGroup .fpiso .snd = record { pres· = λ x y i →  [ (λ x₁ → pos 0) ] ; pres1 = λ i → [ (λ x → pos 0) ] ; presinv = λ x i → [ (λ x₁ → pos 0) ] }

isFPTrivialAbGroup : isFP {ℓ = ℓ} trivialAbGroup
isFPTrivialAbGroup = ∣ finPresTrivialAbGroup ∣₁

finPresℤ : FinitePresentation {ℓ = ℓ-zero} ℤAbGroup
finPresℤ .nGens = 1
finPresℤ .nRels = 0
finPresℤ .rels = (λ x y → 0) , record { pres· = λ x y i x₁ → 0 ; pres1 = λ i x → 0 ; presinv = λ x i x₁ → 0 }
finPresℤ .fpiso .fst .Iso.fun = λ x → [ (λ x₁ → x) ]
finPresℤ .fpiso .fst .Iso.inv = SQ.rec isSetℤ (λ x → x (0 , tt)) λ a b
  → PT.elim (λ _ → isSetℤ _ _)
     (λ {(_ , p) → (cong (a (0 , tt) +ℤ_) (sym (+InvL (snd ℤAbGroup) (b (0 , tt))))
                  ∙ ℤData.+Assoc (a (0 , tt)) (ℤData.- b (0 , tt)) (b (0 , tt)))
                  ∙ sym (cong (_+ℤ b (0 , tt)) (funExt⁻ p (0 , tt)))
                  ∙ ℤData.+Comm 0 (b (0 , tt))})
finPresℤ .fpiso .fst .Iso.sec = SQ.elimProp (λ _ → squash/ _ _)
  λ a → cong [_] (funExt λ { (zero , tt) i → a (0 , tt)})
finPresℤ .fpiso .fst .Iso.ret _ = refl
finPresℤ .fpiso .snd = makeIsGroupHom λ _ _ → refl

isFPℤ : isFP {ℓ = ℓ-zero} ℤAbGroup
isFPℤ = ∣ finPresℤ ∣₁

sigh : GroupIso {ℓ' = ℓ} UnitGroup₀ UnitGroup
sigh = invGroupIso (contrGroupIsoUnit (tt* , (λ { tt* → refl })))

-- π_{n+2}(S⁰) = 0
lemma0 : (n : ℕ) → πAb n (S₊∙ 0) ≡ trivialAbGroup
lemma0 n = AbGroupPath _ _ .fst (AbGroupIso→AbGroupEquiv suff)
  where
  boo : isContr (π (suc (suc n)) (S₊∙ 0))
  boo = πVanish 2 (suc (suc n)) ((suc n)
                 , cong suc (+-comm n 2)) isSetBool

  suff : GroupIso (πGr (suc n) (S₊∙ 0)) UnitGroup
  suff = compGroupIso (contrGroupIsoUnit boo) sigh

-- π_{n+2}(S¹) = 0
lemma1 : (n : ℕ) → πAb n (S₊∙ 1) ≡ trivialAbGroup
lemma1 n = AbGroupPath _ _ .fst (AbGroupIso→AbGroupEquiv suff)
  where
  boo : isContr (π (suc (suc n)) (S₊∙ 1))
  boo = πVanish 3 (suc (suc n)) (n , +-comm n 3) isGroupoidS¹

  suff : GroupIso (πGr (suc n) (S₊∙ 1)) UnitGroup
  suff = compGroupIso (contrGroupIsoUnit boo) sigh

isFPπAbS₊ : (n m : ℕ) → isFP (πAb n (S₊∙ m))
isFPπAbS₊ n 0 = subst isFP (sym (lemma0 n)) isFPTrivialAbGroup
isFPπAbS₊ n 1 = subst isFP (sym (lemma1 n)) isFPTrivialAbGroup
isFPπAbS₊ n (suc (suc m)) = subst (λ A → isFP (πAb n A)) (sym rem) (isFPπAbSn n m)
  where
  rem : S₊∙ (suc (suc m)) ≡ S (suc (suc m))
  rem = ΣPathP ((isoToPath (iso (λ x → (x , tt*)) fst (λ { (x , tt*) → refl }) λ _ → refl))
               , toPathP (λ i → north , tt*))

BoolAbGroupStr : AbGroupStr Bool
BoolAbGroupStr = Group→AbGroup BoolGroup (λ { false false → refl ; false true → refl ; true false → refl ; true true → refl }) .snd

_·𝐁_ : Bool → Bool → Bool
_·𝐁_ =  GroupStr._·_ (snd BoolGroup)

BoolGroupComm : (x y : Bool) → (x ·𝐁 y) ≡ (y ·𝐁 x)
BoolGroupComm false false = refl
BoolGroupComm false true = refl
BoolGroupComm true false = refl
BoolGroupComm true true = refl

BoolPresHom : AbGroupHom ℤ[Fin 1 ] ℤ[Fin 1 ]
BoolPresHom .fst a s = a s +ℤ a s
BoolPresHom .snd = makeIsGroupHom λ f g
  → funExt λ {(zero , tt)
  → AbGroupTheory.comm-4 ℤAbGroup (f (zero , tt)) (g (zero , tt)) (f (zero , tt)) (g (zero , tt))}

doubleHomℤ : GroupHom ℤGroup ℤGroup
doubleHomℤ .fst a = a +ℤ a
doubleHomℤ .snd = makeIsGroupHom λ a b → AbGroupTheory.comm-4 ℤAbGroup a b a b

ℤ[Fin1]≅ℤ : GroupIso ℤGroup (AbGroup→Group ℤ[Fin 1 ])
ℤ[Fin1]≅ℤ .fst .Iso.fun f _ = f
ℤ[Fin1]≅ℤ .fst .Iso.inv f = f (0 , tt)
ℤ[Fin1]≅ℤ .fst .Iso.sec f = funExt λ {(0 , tt) → refl}
ℤ[Fin1]≅ℤ .fst .Iso.ret f = refl
ℤ[Fin1]≅ℤ .snd = makeIsGroupHom λ _ _ → refl

finPresBoolAbGroup' : FinitePresentation {ℓ = ℓ-zero}
  (Group→AbGroup BoolGroup BoolGroupComm)
finPresBoolAbGroup' .nGens = 1
finPresBoolAbGroup' .nRels = 1
finPresBoolAbGroup' .rels = BoolPresHom
finPresBoolAbGroup' .fpiso =
  compGroupIso
    (compGroupIso (invGroupIso ℤGroup/2≅Bool)
      (invGroupIso (ℤ/imIso doubleHomℤ)))
        (Hom/ImIso _ _ ℤ[Fin1]≅ℤ ℤ[Fin1]≅ℤ λ _ → refl)


isFPBool : isFP (Group→AbGroup BoolGroup BoolGroupComm) -- ( , ?)
isFPBool = ∣ finPresBoolAbGroup' ∣₁


π₀S¹⁺ : (n : ℕ) → π 0 (S₊∙ (suc n)) ≡ Unit*
π₀S¹⁺ n = ua (isContr→Equiv (∣ ptSn (suc n) ∣₂
  , (ST.elim (λ _ → isSetPathImplicit)
             (sphereElim n (λ _ → isProp→isOfHLevelSuc n (squash₂ _ _)) refl)))
    isContrUnit*)

π₁S⁰ : π 1 (S₊∙ 0) ≡ Unit*
π₁S⁰ = ua (isContr→Equiv
            (isContr→isContrSetTrunc (refl , (λ p → isSetBool _ _ _ _)))
            isContrUnit*)

π₁S²⁺ : (n : ℕ) → π 1 (S₊∙ (suc (suc n))) ≡ Unit*
π₁S²⁺ n = ua (isContr→Equiv (∣ refl ∣₂
  , (ST.elim (λ _ → isSetPathImplicit)
             λ p → TR.rec (isProp→isOfHLevelSuc n (squash₂ _ _))
                           (cong ∣_∣₂)
                           (isConnectedPath (suc n)
                            (isConnectedPathSⁿ (suc n) _ _) refl p .fst)))
    isContrUnit*)

-- π_n(S^m)
πSphere : (n m : ℕ) → AbGroup₀
πSphere 0 0 = (π 0 (S₊∙ 0)) , rem
  where
  rem : AbGroupStr ∥ Bool ∥₂
  rem = subst AbGroupStr (sym (setTruncIdempotent isSetBool)) BoolAbGroupStr
πSphere 0 (suc m) =
  (π 0 (S₊∙ (suc m))) ,
  subst AbGroupStr (sym (π₀S¹⁺ m)) (trivialAbGroup .snd)
πSphere 1 0 =
  (π 1 (S₊∙ 0)) ,
  subst AbGroupStr (sym π₁S⁰) (trivialAbGroup .snd)
πSphere 1 1 =
  Group→AbGroup (πGr 0 (S₊∙ 1))
                (ST.elim2 (λ _ _ → isSetPathImplicit) λ p q → cong ∣_∣₂ (comm-ΩS¹ p q))
πSphere 1 (suc (suc m)) =
  π 1 (S₊∙ (suc (suc m))) ,
  subst AbGroupStr (sym (π₁S²⁺ m)) (trivialAbGroup .snd)
πSphere (suc (suc n)) m = πAb n (S₊∙ m)

isFPπSphere : (n m : ℕ) → isFP (πSphere n m)
isFPπSphere 0 0 = subst isFP (fst (AbGroupPath _ _)
  ((invEquiv (setTruncIdempotent≃ isSetBool))
  , makeIsGroupHom λ _ _ → refl)) isFPBool
isFPπSphere 0 (suc m) = subst isFP
  (sym (fst (AbGroupPath _ _)
  (pathToEquiv (π₀S¹⁺ m) , (makeIsGroupHom λ _ _ → refl))))
  isFPTrivialAbGroup
isFPπSphere 1 0 = subst isFP (sym (fst (AbGroupPath _ _)
  (pathToEquiv π₁S⁰ , (makeIsGroupHom λ _ _ → refl)))) isFPTrivialAbGroup
isFPπSphere 1 1 =
  subst isFP (fst (AbGroupPath _ _)
                  (AbGroupIso→AbGroupEquiv (invGroupIso (πₙSⁿ≅ℤ 0))))
        isFPℤ
isFPπSphere 1 (suc (suc m)) =
  subst isFP (sym (fst (AbGroupPath _ _)
                       (pathToEquiv (π₁S²⁺ m) , (makeIsGroupHom λ _ _ → refl))))
        isFPTrivialAbGroup
isFPπSphere (suc (suc n)) m = isFPπAbS₊ n m
