{-# OPTIONS --cubical --no-import-sorts --safe --experimental-lossy-unification #-}
module Cubical.ZCohomology.Groups.Wedge where

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.MayerVietorisUnreduced
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.HITs.Wedge
open import Cubical.HITs.SetTruncation renaming (rec to sRec ; rec2 to pRec2 ; elim to sElim ; elim2 to sElim2 ; map to sMap)
open import Cubical.HITs.PropositionalTruncation renaming (rec to pRec ; ∣_∣ to ∣_∣₁)
open import Cubical.HITs.Truncation renaming (elim to trElim ; rec to trRec ; elim2 to trElim2)
open import Cubical.Data.Nat
open import Cubical.Algebra.Group

open import Cubical.ZCohomology.Groups.Unit
open import Cubical.ZCohomology.Groups.Sn

open import Cubical.HITs.Pushout
open import Cubical.Data.Sigma

open import Cubical.Foundations.Isomorphism
open import Cubical.Homotopy.Connected
open import Cubical.HITs.Susp
open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.Foundations.Equiv

open GroupIso renaming (map to map')
open GroupHom

{-
This module proves that Hⁿ(A ⋁ B) ≅ Hⁿ(A) × Hⁿ(B) for n ≥ 1 directly (rather than by means of Mayer-Vietoris).

Proof sketch:

Any ∣ f ∣₂ ∈ Hⁿ(A ⋁ B) is uniquely characterised by a pair of functions
  f₁ : A → Kₙ
  f₂ : B → Kₙ
together with a path
  p : f₁ (pt A) ≡ f₂ (pt B)

The map F : Hⁿ(A ⋁ B) → Hⁿ(A) × Hⁿ(B) simply forgets about p, i.e.:
  F(∣ f ∣₂) := (∣ f₁ ∣₂ , ∣ f₂ ∣₂)

The construction of its inverse is defined by
  F⁻(∣ f₁ ∣₂ , ∣ f₂ ∣₂) := ∣ f₁∨f₂ ∣₂
  where
  f₁∨f₂ : A ⋁ B → Kₙ is defined inductively by
  f₁∨f₂ (inl x) := f₁ x + f₂ (pt B)
  f₁∨f₂ (inr x) := f₂ x + f₁ (pt B)
  cong f₁∨f₂ (push tt) := "f₁ (pt A) + f₂ (pt B) =(commutativity) f₂ (pt B) + f₁ (pt A)"
  (this is the map wedgeFun⁻ below)

The fact that F and F⁻ cancel out is a proposition and we may thus assume for any
  ∣ f ∣₂ ∈ Hⁿ(A ⋁ B) and its corresponding f₁ that
  f₁ (pt A) = f₂ (pt B) = 0                (*)
  and
  f (inl (pt A)) = 0                       (**)

The fact that F(F⁻(∣ f₁ ∣₂ , ∣ f₂ ∣₂)) = ∣ f₁ ∣₂ , ∣ f₂ ∣₂) follows immediately from (*)

The other way is slightly trickier. We need to construct paths
  Pₗ : f (inl (x)) + f (inr (pt B)) ---> f (inl (x))
  Pᵣ  : f (inr (x)) + f (inl (pt A)) ---> f (inr (x))

Together with a filler of the following square

     cong f (push tt)
    ----------------->
   ^                  ^
   |                  |
   |                  |
Pₗ |                  | Pᵣ
   |                  |
   |                  |
   |                  |
    ----------------->
            Q
where Q is commutativity proof f (inl (pt A)) + f (inr (pt B)) = f (inr (pt B)) + f (inl (pt A))

The square is filled by first constructing Pₗ by
  f (inl (x)) + f (inr (pt B))    ---[cong f (push tt)⁻¹]--->
  f (inl (x)) + f (inl (pt A))    ---[(**)]--->
  f (inl (x)) + 0                 ---[right-unit]--->
  f (inl (x))

and then Pᵣ by
  f (inr (x)) + f (inl (pt A))    ---[(**)]--->
  f (inr (x)) + 0                 ---[right-unit]--->
  f (inr (x))

and finally by using the fact that the groupoid laws for Kₙ are refl at its base point.
-}

module _ {ℓ ℓ'} (A : Pointed ℓ) (B : Pointed ℓ') where

  private
    wedgeFun⁻ : ∀ n → (f : typ A → coHomK (suc n)) (g : typ B → coHomK (suc n))
            → ((A ⋁ B) → coHomK (suc n))
    wedgeFun⁻ n f g (inl x) = f x +ₖ g (pt B)
    wedgeFun⁻ n f g (inr x) = g x +ₖ f (pt A)
    wedgeFun⁻ n f g (push a i) = commₖ (suc n) (f (pt A)) (g (pt B)) i

  Hⁿ-⋁ : (n : ℕ) → GroupIso (coHomGr (suc n) (A ⋁ B)) (×coHomGr (suc n) (typ A) (typ B))
  fun (map' (Hⁿ-⋁ zero)) =
    sElim (λ _ → isSet× setTruncIsSet setTruncIsSet)
           λ f → ∣ (λ x → f (inl x)) ∣₂ , ∣ (λ x → f (inr x)) ∣₂
  isHom (map' (Hⁿ-⋁ zero)) =
    sElim2 (λ _ _ → isOfHLevelPath 2 (isSet× setTruncIsSet setTruncIsSet) _ _)
            λ _ _ → refl
  inv (Hⁿ-⋁ zero) = uncurry (sElim2 (λ _ _ → setTruncIsSet)
                             λ f g → ∣ wedgeFun⁻ 0 f g ∣₂)
  rightInv (Hⁿ-⋁ zero) =
    uncurry
    (coHomPointedElim _ (pt A) (λ _ → isPropΠ λ _ → isSet× setTruncIsSet setTruncIsSet _ _)
      λ f fId → coHomPointedElim _ (pt B) (λ _ → isSet× setTruncIsSet setTruncIsSet _ _)
        λ g gId → ΣPathP (cong ∣_∣₂ (funExt (λ x → cong (f x +ₖ_) gId ∙ rUnitₖ 1 (f x))) ,
                           cong ∣_∣₂ (funExt (λ x → cong (g x +ₖ_) fId ∙ rUnitₖ 1 (g x)))))
  leftInv (Hⁿ-⋁ zero) =
    sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
      (λ f → pRec (setTruncIsSet _ _)
                   (λ fId → cong ∣_∣₂ (sym fId))
                   (helper f _ refl))
    where
    helper : (f : A ⋁ B → coHomK 1) (x : coHomK 1)
          → f (inl (pt A)) ≡ x
          → ∥ f ≡ wedgeFun⁻ 0 (λ x → f (inl x)) (λ x → f (inr x)) ∥
    helper f =
      trElim (λ _ → isProp→isOfHLevelSuc 2 (isPropΠ λ _ → propTruncIsProp))
        (sphereElim 0 (λ _ → isPropΠ λ _ → propTruncIsProp)
          λ inlId → (∣ funExt (λ { (inl x) → sym (rUnitₖ 1 (f (inl x)))
                                           ∙∙ cong ((f (inl x)) +ₖ_) (sym inlId)
                                           ∙∙ cong ((f (inl x)) +ₖ_) (cong f (push tt))
                                 ; (inr x) → sym (rUnitₖ 1 (f (inr x)))
                                            ∙ cong ((f (inr x)) +ₖ_) (sym inlId)
                                 ; (push tt i) j → cheating (f (inl (pt A))) (sym (inlId))
                                                             (f (inr (pt B)))
                                                             (cong f (push tt)) j i}) ∣₁))
      where
      cheating : (x : coHomK 1) (r : ∣ base ∣ ≡ x) (y : coHomK 1) (p : x ≡ y)
             → PathP (λ j → ((sym (rUnitₖ 1 x) ∙∙ cong (x +ₖ_) r ∙∙ cong (x +ₖ_) p)) j
                             ≡ (sym (rUnitₖ 1 y) ∙ cong (y +ₖ_) r) j)
                       p (commₖ 1 x y)
      cheating x = J (λ x r → (y : coHomK 1) (p : x ≡ y)
                            → PathP (λ j → ((sym (rUnitₖ 1 x) ∙∙ cong (x +ₖ_) r ∙∙ cong (x +ₖ_) p)) j
                                            ≡ (sym (rUnitₖ 1 y) ∙ cong (y +ₖ_) r) j)
                                     p (commₖ 1 x y))
                     λ y → J (λ y p → PathP (λ j → ((sym (rUnitₖ 1 ∣ base ∣) ∙∙ refl ∙∙ cong (∣ base ∣ +ₖ_) p)) j
                                                     ≡ (sym (rUnitₖ 1 y) ∙ refl) j)
                                              p (commₖ 1 ∣ base ∣ y))
                             λ i j → comp (λ _ → hLevelTrunc 3 S¹)
                                           (λ k → λ {(i = i0) → ∣ base ∣
                                                    ; (i = i1) → ∣ base ∣
                                                    ; (j = i0) → (rUnit (λ _ → ∣ base ∣) k) i
                                                    ; (j = i1) → (rUnit (λ _ → ∣ base ∣) k) i})
                                           ∣ base ∣
  fun (map' (Hⁿ-⋁ (suc n))) =
    sElim (λ _ → isSet× setTruncIsSet setTruncIsSet)
           λ f → ∣ (λ x → f (inl x)) ∣₂ , ∣ (λ x → f (inr x)) ∣₂
  isHom (map' (Hⁿ-⋁ (suc n))) =
    sElim2 (λ _ _ → isOfHLevelPath 2 (isSet× setTruncIsSet setTruncIsSet) _ _)
            λ _ _ → refl
  inv (Hⁿ-⋁ (suc n)) =
    uncurry (sElim2 (λ _ _ → setTruncIsSet)
                     λ f g → ∣ wedgeFun⁻ (suc n) f g ∣₂)
  rightInv (Hⁿ-⋁ (suc n)) =
   uncurry
    (coHomPointedElim _ (pt A) (λ _ → isPropΠ λ _ → isSet× setTruncIsSet setTruncIsSet _ _)
      λ f fId → coHomPointedElim _ (pt B) (λ _ → isSet× setTruncIsSet setTruncIsSet _ _)
        λ g gId → ΣPathP (cong ∣_∣₂ (funExt (λ x → cong (f x +ₖ_) gId ∙ rUnitₖ (2 + n) (f x))) ,
                           cong ∣_∣₂ (funExt (λ x → cong (g x +ₖ_) fId ∙ rUnitₖ (2 + n) (g x)))))
  leftInv (Hⁿ-⋁ (suc n)) =
    sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
      (λ f → pRec (setTruncIsSet _ _)
                   (λ fId → cong ∣_∣₂ (sym fId))
                   (helper f _ refl))
    where
    helper : (f : A ⋁ B → coHomK (2 + n)) (x : coHomK (2 + n))
          → f (inl (pt A)) ≡ x
          → ∥ f ≡ wedgeFun⁻ (suc n) (λ x → f (inl x)) (λ x → f (inr x)) ∥
    helper f =
      trElim (λ _ → isProp→isOfHLevelSuc (3 + n) (isPropΠ λ _ → propTruncIsProp))
        (sphereToPropElim (suc n) (λ _ → isPropΠ λ _ → propTruncIsProp)
          λ inlId → (∣ funExt (λ { (inl x) → sym (rUnitₖ (2 + n) (f (inl x)))
                                           ∙∙ cong ((f (inl x)) +ₖ_) (sym inlId)
                                           ∙∙ cong ((f (inl x)) +ₖ_) (cong f (push tt))
                                 ; (inr x) → sym (rUnitₖ (2 + n) (f (inr x)))
                                            ∙ cong ((f (inr x)) +ₖ_) (sym inlId)
                                 ; (push tt i) j → cheating (f (inl (pt A))) (sym (inlId))
                                                             (f (inr (pt B))) (cong f (push tt)) j i}) ∣₁))
      where
      cheating : (x : coHomK (2 + n)) (r : ∣ north ∣ ≡ x) (y : coHomK (2 + n)) (p : x ≡ y)
             → PathP (λ j → ((sym (rUnitₖ (2 + n) x) ∙∙ cong (x +ₖ_) r ∙∙ cong (x +ₖ_) p)) j
                             ≡ (sym (rUnitₖ (2 + n) y) ∙ cong (y +ₖ_) r) j)
                       p (commₖ (2 + n) x y)
      cheating x =
         J (λ x r → (y : coHomK (2 + n)) (p : x ≡ y)
                            → PathP (λ j → ((sym (rUnitₖ (2 + n) x) ∙∙ cong (x +ₖ_) r ∙∙ cong (x +ₖ_) p)) j
                                            ≡ (sym (rUnitₖ (2 + n) y) ∙ cong (y +ₖ_) r) j)
                                     p (commₖ (2 + n) x y))
                     doubleCheating
        where
        doubleCheating : (y : coHomK (2 + n)) → (p : ∣ north ∣ ≡ y)
                      → PathP (λ j → ((refl ∙∙ refl ∙∙ cong (∣ north ∣ +ₖ_) p)) j
                                      ≡ (sym (rUnitₖ (2 + n) y) ∙ refl) j)
                               p
                               (commₖ (2 + n) ∣ north ∣ y)
        doubleCheating y =
          J (λ y p → PathP (λ j → ((refl ∙∙ refl ∙∙ cong (∣ north ∣ +ₖ_) p)) j
                                      ≡ (sym (rUnitₖ (2 + n) y) ∙ refl) j)
                               p
                               (commₖ (2 + n) ∣ north ∣ y))
            λ i j → comp (λ _ → coHomK (2 + n))
                          (λ k → λ {(i = i0) → ∣ north ∣
                                   ; (i = i1) → commₖ-base (2 + n) (~ k) j
                                   ; (j = i0) → rUnit (λ _ → ∣ north ∣) k i
                                   ; (j = i1) → rUnit (λ _ → ∣ north ∣) k i})
                          ∣ north ∣

  wedgeConnected : ((x : typ A) → ∥ pt A ≡ x ∥) → ((x : typ B) → ∥ pt B ≡ x ∥) → (x : A ⋁ B) → ∥ inl (pt A) ≡ x ∥
  wedgeConnected conA conB =
    PushoutToProp (λ _ → propTruncIsProp)
                  (λ a → pRec propTruncIsProp (λ p → ∣ cong inl p ∣₁) (conA a))
                   λ b → pRec propTruncIsProp (λ p → ∣ push tt ∙ cong inr p ∣₁) (conB b)


open import Cubical.HITs.KleinBottle
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Equiv.HalfAdjoint
funSpaceKleinIso : ∀ {ℓ} {A : Type ℓ} → Iso (KleinBottle → A)
           (Σ[ x ∈ A ] Σ[ p ∈ x ≡ x ] Σ[ q ∈ x ≡ x ]
             PathP (λ i → p (~ i) ≡ p i) q q)
Iso.fun funSpaceKleinIso f = f point , (cong f line1) , ((cong f line2) , (λ i j → f (square i j)))
Iso.inv funSpaceKleinIso (x , p , q , sq) point = x
Iso.inv funSpaceKleinIso (x , p , q , sq) (line1 i) = p i
Iso.inv funSpaceKleinIso (x , p , q , sq) (line2 i) = q i
Iso.inv funSpaceKleinIso (x , p , q , sq) (square i j) = sq i j
Iso.rightInv funSpaceKleinIso (x , p , q , sq) = refl
Iso.leftInv funSpaceKleinIso f = funExt λ {point → refl ; (line1 i) → refl ; (line2 i) → refl ; (square i j) → refl}

module _ (x : coHomK 2) (p q : x ≡ x) where
  test : Iso (PathP (λ i → p (~ i) ≡ p i) q q) (p ∙ p ∙ q ≡ q)
  test  = pathToIso (PathP≡doubleCompPathˡ _ _ _ _
                  ∙∙ cong (_≡ q) (doubleCompPath-elim' _ _ _)
                  ∙∙ cong (λ x → p ∙ x ≡ q) (isCommΩK-based 2 x q p))

  compPathIso : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p q : x ≡ y) (r : y ≡ z) → Iso (x ≡ y) (x ≡ z) 
  Iso.fun (compPathIso p q r) = _∙ r
  Iso.inv (compPathIso p q r) = _∙ sym r
  Iso.rightInv (compPathIso p q r) P = sym (assoc _ _ _) ∙∙ cong (P ∙_) (lCancel r) ∙∙ sym (rUnit P)
  Iso.leftInv (compPathIso p q r) P = sym (assoc _ _ _) ∙∙ cong (P ∙_) (rCancel r) ∙∙ sym (rUnit P)

  PathP→idempIso : Iso (PathP (λ i → p (~ i) ≡ p i) q q) (p ∙ p ≡ refl)
  PathP→idempIso =
    compIso test (compIso (congIso (compPathIso (p ∙ p ∙ q) q (sym q)))
            (pathToIso (cong₂ _≡_ ((λ j → (p ∙ p ∙ λ i → q (i ∧ ~ j)) ∙ (λ i → q (~ i ∧ ~ j)))
                               ∙∙ sym (rUnit _)
                               ∙∙ cong (p ∙_) (sym (rUnit _)))
                       (rCancel q))))

funSpaceKleinIso' : Iso (coHom 2 KleinBottle) ∥ (Σ[ x ∈ coHomK 2 ] Σ[ p ∈ x ≡ x ] Σ[ q ∈ x ≡ x ] p ∙ p ≡ refl ) ∥₂
funSpaceKleinIso' = setTruncIso (compIso funSpaceKleinIso (Σ-cong-iso-snd λ x → Σ-cong-iso-snd λ p → Σ-cong-iso-snd λ q → PathP→idempIso x p q))

tihi : Iso ∥ (Σ[ x ∈ coHomK 2 ] Σ[ p ∈ x ≡ x ] Σ[ q ∈ x ≡ x ] p ∙ p ≡ refl ) ∥₂
          ∥ Σ[ p ∈ Path (coHomK 2) (0ₖ _) (0ₖ _) ] p ∙ p ≡ refl ∥₂
Iso.fun tihi = sRec setTruncIsSet (uncurry (trElim (λ _ → isOfHLevelΠ 4 λ _ → isOfHLevelPlus 2 setTruncIsSet)
                    (sphereElim _ (λ _ → isSetΠ λ _ → setTruncIsSet)
                    λ {(p , _  , idem) → ∣ p , idem ∣₂})))
Iso.inv tihi = sMap λ {(p , idem) → (0ₖ _) , (p , (refl , idem))}
Iso.rightInv tihi = sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
                           λ _ → refl
Iso.leftInv tihi =
  sElim (λ _ → isOfHLevelPath 2 setTruncIsSet _ _)
        (uncurry
          (trElim (λ _ → isOfHLevelΠ 4 λ _ → isOfHLevelPlus 3 (setTruncIsSet _ _))
                  (sphereToPropElim 1 (λ _ → isPropΠ (λ _ → setTruncIsSet _ _))
                    λ {(p , q , idem) → trRec (setTruncIsSet _ _)
                                               (λ qId → cong ∣_∣₂ (ΣPathP (refl , ΣPathP (refl , (ΣPathP ((sym qId) , refl))))))
                                               (Iso.fun (PathIdTruncIso 1)
                                                        (isContr→isProp (isConnectedPathKn 1 _ _) ∣ q ∣ ∣ refl ∣ ))})))

open import Cubical.Data.Sum


tes : (x : coHomK 1) →  x +ₖ x ≡ 0ₖ _ → x ≡ 0ₖ _ 
tes = trElim {!j : I
p : ∣
    hcomp
    (λ {
       ; k (i = i0) → ∣ base ∣
       ; k (i = i1) → loop k
       })
    (loop i)
    ∣
    ≡ 0ₖ 1
!} λ {base p → refl ; (loop i) → {!!}}
  where
  helper2 : PathP (λ i → ∣ loop i ∣ +ₖ ∣ loop i ∣ ≡ ∣ base ∣ → ∣ loop i ∣ ≡ 0ₖ 1) (λ p → p) λ p → p
  helper2 = toPathP (funExt λ x → (λ i → transport (λ i → Path (coHomK 1) ∣ loop i ∣ ∣ base ∣)
     (transp
      (λ j →
         Path (coHomK 1) ∣
         (sym loop ∙∙ sym loop ∙∙ refl) (i ∨ j)
         ∣
         ∣ base ∣) i (sym (compPath-filler (sym x) (cong ∣_∣ (sym loop ∙∙ sym loop ∙∙ refl)) i)))) ∙∙ {!!} ∙∙ {! ∙∙ {!!}!})

testi : cong (λ x → ∣ x ∣ +ₖ ∣ x ∣) loop ≡ cong ∣_∣ loop ∙ cong ∣_∣ loop 
testi = (λ j → (λ i →
         ∣
         hcomp
         (λ { k (i = i0) → base
            ; k (i = i1) → loop k
            })
         (rUnit loop j i)
         ∣)) ∙∙ ((λ j → (λ i →
         ∣
         hcomp
         (λ { k (i = i0) → base
            ; k (i = i1) → loop (k ∨ j)
            })
         ((loop ∙ λ z → loop (z ∧ j)) i)
         ∣)))
         ∙∙ ((λ j → (λ i →
         ∣
         hfill
         (λ { k (i = i0) → base
            ; k (i = i1) → base
            })
         (inS ((loop ∙ loop) i))
         (~ j)
         ∣)) ∙ congFunct ∣_∣ loop loop)

stupid : {!!}
stupid = {!!}

test3 : Path ∥ Σ[ x ∈ coHomK 1 ] x +ₖ x ≡ 0ₖ _  ∥₂ ∣ (0ₖ _) , cong ∣_∣ loop ∣₂ ∣ 0ₖ _ , sym (cong ∣_∣ loop) ∣₂
test3 = cong ∣_∣₂ (ΣPathP ((cong ∣_∣ loop) , toPathP ((λ j → transport (λ i → testi j i ≡ 0ₖ 1) (lUnit (cong ∣_∣ loop) j)) ∙∙ (λ j → transp (λ i → (cong ∣_∣ loop ∙ cong ∣_∣ loop) (i ∨ j) ≡ 0ₖ 1) j (((λ i → (cong ∣_∣ loop ∙ cong ∣_∣ loop) (~ i ∧ j)) ∙ cong ∣_∣ loop))) ∙∙ (cong (_∙ cong ∣_∣ loop) (symDistr (cong ∣_∣ loop) (cong ∣_∣ loop))  ∙∙ (λ i → (sym (cong ∣_∣ loop) ∙ λ j → ∣ loop (~ j ∨ i) ∣) ∙ λ j → ∣ loop (j ∨ i) ∣) ∙∙ λ i → rUnit (rUnit (sym (cong ∣_∣ loop)) (~ i)) (~ i)))))

test2 : Σ[ x ∈ coHomK 1 ] x +ₖ x ≡ 0ₖ _ → Type₀
test2  = uncurry
          (trElim {!!}
            λ {base → {!!}
            ; (loop i) → {!!}})
