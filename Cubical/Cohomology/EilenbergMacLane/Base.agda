{-# OPTIONS --safe --lossy-unification #-}

module Cubical.Cohomology.EilenbergMacLane.Base where

open import Cubical.Homotopy.EilenbergMacLane.GroupStructure
open import Cubical.Homotopy.EilenbergMacLane.Base
open import Cubical.Homotopy.EilenbergMacLane.Properties
open import Cubical.Homotopy.EilenbergMacLane.Order2

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous

open import Cubical.Foundations.Isomorphism
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Data.Nat
open import Cubical.Data.Sigma

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Group.Instances.IntMod

open import Cubical.HITs.SetTruncation as ST
  hiding (rec ; map ; elim ; elim2 ; elim3)

private
  variable
    ℓ ℓ' : Level

open IsAbGroup
open IsGroup
open IsSemigroup

open IsMonoid
open AbGroupStr

-- cohomology groups
coHom : (n : ℕ) (G : AbGroup ℓ) (A : Type ℓ') → Type _
coHom n G A = ∥ (A → EM G n) ∥₂

module _ {n : ℕ} {G : AbGroup ℓ} {A : Type ℓ'} where
  _+ₕ_ : coHom n G A → coHom n G A → coHom n G A
  _+ₕ_ = ST.rec2 squash₂ λ f g → ∣ (λ x → f x +ₖ g x) ∣₂

  -ₕ_ : coHom n G A → coHom n G A
  -ₕ_ = ST.map λ f x → -ₖ f x

  _-ₕ_ : coHom n G A → coHom n G A → coHom n G A
  _-ₕ_ = ST.rec2 squash₂ λ f g → ∣ (λ x → f x -ₖ g x) ∣₂

module _ (n : ℕ) {G : AbGroup ℓ} {A : Type ℓ'} where
  +ₕ-syntax : coHom n G A → coHom n G A → coHom n G A
  +ₕ-syntax = _+ₕ_

  -ₕ-syntax : coHom n G A → coHom n G A
  -ₕ-syntax = -ₕ_

  -'ₕ-syntax : coHom n G A → coHom n G A → coHom n G A
  -'ₕ-syntax = _-ₕ_

  syntax +ₕ-syntax n x y = x +[ n ]ₕ y
  syntax -ₕ-syntax n x = -[ n ]ₕ x
  syntax -'ₕ-syntax n x y = x -[ n ]ₕ y

module _ (n : ℕ) {G : AbGroup ℓ} {A : Type ℓ'} where
  0ₕ : coHom n G A
  0ₕ = ∣ (λ _ → 0ₖ n) ∣₂

  rUnitₕ : (x : coHom n G A) → x +ₕ 0ₕ ≡ x
  rUnitₕ = ST.elim (λ _ → isSetPathImplicit)
           λ f → cong ∣_∣₂ (funExt λ x → rUnitₖ n (f x))

  lUnitₕ : (x : coHom n G A) → 0ₕ +[ n ]ₕ x ≡ x
  lUnitₕ = ST.elim (λ _ → isSetPathImplicit)
           λ f → cong ∣_∣₂ (funExt λ x → lUnitₖ n (f x))

  commₕ : (x y : coHom n G A) → x +ₕ y ≡ y +ₕ x
  commₕ = ST.elim2 (λ _ _ → isSetPathImplicit)
           λ f g → cong ∣_∣₂ (funExt λ x → commₖ n (f x) (g x))

  assocₕ : (x y z : coHom n G A) → x +ₕ (y +ₕ z) ≡ (x +ₕ y) +ₕ z
  assocₕ = ST.elim3 (λ _ _ _ → isSetPathImplicit)
           λ f g h → cong ∣_∣₂ (funExt λ x → assocₖ n (f x) (g x) (h x))

  rCancelₕ : (x : coHom n G A) → x +ₕ (-ₕ x) ≡ 0ₕ
  rCancelₕ = ST.elim (λ _ → isSetPathImplicit)
           λ f → cong ∣_∣₂ (funExt λ x → rCancelₖ n (f x))

  lCancelₕ : (x : coHom n G A) → (-ₕ x) +ₕ x ≡ 0ₕ
  lCancelₕ = ST.elim (λ _ → isSetPathImplicit)
           λ f → cong ∣_∣₂ (funExt λ x → lCancelₖ n (f x))

coHomGr : (n : ℕ) (G : AbGroup ℓ) (A : Type ℓ') → AbGroup (ℓ-max ℓ ℓ')
fst (coHomGr n G A) = coHom n G A
0g (snd (coHomGr n G A)) = 0ₕ n
AbGroupStr._+_ (snd (coHomGr n G A)) = _+ₕ_
- snd (coHomGr n G A) = -ₕ_
is-set (isSemigroup (isMonoid (isGroup (isAbGroup (snd (coHomGr n G A)))))) = squash₂
·Assoc (isSemigroup (isMonoid (isGroup (isAbGroup (snd (coHomGr n G A)))))) = assocₕ n
·IdR (isMonoid (isGroup (isAbGroup (snd (coHomGr n G A))))) = rUnitₕ n
·IdL (isMonoid (isGroup (isAbGroup (snd (coHomGr n G A))))) = lUnitₕ n
·InvR (isGroup (isAbGroup (snd (coHomGr n G A)))) = rCancelₕ n
·InvL (isGroup (isAbGroup (snd (coHomGr n G A)))) = lCancelₕ n
+Comm (isAbGroup (snd (coHomGr n G A))) = commₕ n

-- reduced cohomology groups
coHomRed : (n : ℕ) (G : AbGroup ℓ) (A : Pointed ℓ') → Type _
coHomRed n G A = ∥ (A →∙ EM∙ G n) ∥₂

0ₕ∙ : (n : ℕ) {G : AbGroup ℓ} {A : Pointed ℓ'} → coHomRed n G A
0ₕ∙ n = ∣ (λ _ → 0ₖ n) , refl ∣₂

-- operations
module _ {n : ℕ} {G : AbGroup ℓ} {A : Pointed ℓ'} where
  _+ₕ∙_ : coHomRed n G A → coHomRed n G A → coHomRed n G A
  _+ₕ∙_ = ST.rec2 squash₂
    λ f g → ∣ (λ x → fst f x +ₖ fst g x)
            , cong₂ _+ₖ_ (snd f) (snd g) ∙ rUnitₖ n (0ₖ n) ∣₂

  -ₕ∙_ : coHomRed n G A → coHomRed n G A
  -ₕ∙_ = ST.map λ f → (λ x → -ₖ (fst f x))
                    , cong -ₖ_ (snd f)
                    ∙ -0ₖ n

-- group laws
-- Note that→∙Homogeneous≡ (in Foundations.Pointed.Homogeneous) is
-- purposely avoided to minimise the size of the proof terms
module coHomRedAxioms (n : ℕ) {G : AbGroup ℓ} {A : Pointed ℓ'} where
  commₕ∙ : (x y : coHomRed n G A) → x +ₕ∙ y ≡ y +ₕ∙ x
  commₕ∙ =
    ST.elim2 (λ _ _ → isSetPathImplicit)
      λ f g → cong ∣_∣₂ (ΣPathP (funExt (λ x → commₖ n (fst f x) (fst g x))
                              , help n _ (sym (snd f)) _ (sym (snd g))))
    where
    help : (n : ℕ) (f0 : EM G n) (f1 : 0ₖ n ≡ f0)
                    (g0 : EM G n) (g1 : 0ₖ n ≡ g0)
        → PathP (λ i → commₖ n f0 g0 i ≡ 0ₖ n)
                 (sym (cong₂ _+ₖ_ f1 g1) ∙ rUnitₖ n (0ₖ n))
                 (sym (cong₂ _+ₖ_ g1 f1) ∙ rUnitₖ n (0ₖ n))
    help zero _ _ _ _ =
      isOfHLevelPathP' 0 (is-set (snd G) _ _) _ _ .fst
    help (suc zero) = J> (J> refl)
    help (suc (suc n)) = J> (J> refl)

  rCancelₕ∙ : (x : coHomRed n G A) → (x +ₕ∙ (-ₕ∙ x)) ≡ 0ₕ∙ n
  rCancelₕ∙ =
    ST.elim (λ _ → isSetPathImplicit)
      λ f → cong ∣_∣₂ (ΣPathP ((funExt (λ x → rCancelₖ n (fst f x)))
                    , help n _ (sym (snd f))))
    where
    help : (n : ℕ) (f0 : EM G n) (f1 : 0ₖ n ≡ f0)
      → PathP (λ i → rCancelₖ n f0 i ≡ 0ₖ n)
               (cong₂ _+ₖ_ (sym f1) (cong -ₖ_ (sym f1) ∙ -0ₖ n)
                                  ∙ rUnitₖ n (0ₖ n))
               refl
    help zero _ _ = isOfHLevelPathP' 0 (is-set (snd G) _ _) _ _ .fst
    help (suc zero) = J> (sym (rUnit _) ∙ sym (rUnit _))
    help (suc (suc n)) = J> (sym (rUnit _) ∙ sym (rUnit _))

  lCancelₕ∙ : (x : coHomRed n G A) → ((-ₕ∙ x) +ₕ∙ x) ≡ 0ₕ∙ n
  lCancelₕ∙ x = commₕ∙ (-ₕ∙ x) x ∙ rCancelₕ∙ x

  rUnitₕ∙ : (x : coHomRed n G A) → (x +ₕ∙ 0ₕ∙ n) ≡ x
  rUnitₕ∙ = ST.elim (λ _ → isSetPathImplicit)
     λ f → cong ∣_∣₂ (ΣPathP ((funExt λ x → rUnitₖ n (fst f x))
                   , help n _ (sym (snd f))))
    where
    help : (n : ℕ) (f0 : EM G n) (f1 : 0ₖ n ≡ f0)
      → PathP (λ i → rUnitₖ n f0 i ≡ 0ₖ n)
               (cong (_+ₖ 0ₖ n) (sym f1) ∙ rUnitₖ n (0ₖ n))
               (sym f1)
    help zero _ _ = isOfHLevelPathP' 0 (is-set (snd G) _ _) _ _ .fst
    help (suc zero) = J> sym (rUnit refl)
    help (suc (suc n)) = J> sym (rUnit refl)

  lUnitₕ∙ : (x : coHomRed n G A) → (0ₕ∙ n +ₕ∙ x) ≡ x
  lUnitₕ∙ = ST.elim (λ _ → isSetPathImplicit)
    λ f → cong ∣_∣₂ (ΣPathP ((funExt (λ x → lUnitₖ n (fst f x)))
                  , help n _ (sym (snd f))))
    where
    help : (n : ℕ) (f0 : EM G n) (f1 : 0ₖ n ≡ f0)
      → PathP (λ i → lUnitₖ n f0 i ≡ 0ₖ n)
               (cong (0ₖ n +ₖ_) (sym f1) ∙ rUnitₖ n (0ₖ n))
               (sym f1)
    help zero _ _ = isOfHLevelPathP' 0 (is-set (snd G) _ _) _ _ .fst
    help (suc zero) = J> sym (rUnit refl)
    help (suc (suc n)) = J> sym (rUnit refl)

  assocₕ∙ : (x y z : coHomRed n G A) → x +ₕ∙ (y +ₕ∙ z) ≡ (x +ₕ∙ y) +ₕ∙ z
  assocₕ∙ =
    ST.elim3 (λ _ _ _ → isSetPathImplicit)
     λ f g h → cong ∣_∣₂
       (ΣPathP ((funExt (λ x → assocₖ n (fst f x) (fst g x) (fst h x)))
      , help n _ (sym (snd f)) _ (sym (snd g)) _ (sym (snd h))))
    where
    help : (n : ℕ) (f0 : EM G n) (f1 : 0ₖ n ≡ f0)
                    (g0 : EM G n) (g1 : 0ₖ n ≡ g0)
                    (h0 : EM G n) (h1 : 0ₖ n ≡ h0)
        → PathP (λ i → assocₖ n f0 g0 h0 i ≡ 0ₖ n)
                 (cong₂ _+ₖ_ (sym f1)
                  (cong₂ _+ₖ_ (sym g1) (sym h1) ∙ rUnitₖ n (0ₖ n))
                    ∙ rUnitₖ n (0ₖ n))
                 (cong₂ _+ₖ_ (cong₂ _+ₖ_ (sym f1) (sym g1)
                   ∙ rUnitₖ n (0ₖ n)) (sym h1) ∙ rUnitₖ n (0ₖ n))
    help zero _ _ _ _ _ _ = isOfHLevelPathP' 0 (is-set (snd G) _ _) _ _ .fst
    help (suc zero) =
      J> (J> (J> cong (_∙ refl)
        (cong (cong₂ _+ₖ_ refl) (sym (rUnit refl))
        ∙ (cong (λ z → cong₂ (+ₖ-syntax {G = G} 1) z (refl {x = 0ₖ {G = G} 1}))
          (rUnit refl)))))
    help (suc (suc n)) =
      J> (J> (J> flipSquare ((sym (rUnit refl))
        ◁ flipSquare (cong (_∙ refl)
        (cong (cong₂ _+ₖ_ refl) (sym (rUnit refl))
        ∙ (cong (λ z → cong₂ (+ₖ-syntax {G = G} (suc (suc n))) z
                              (refl {x = 0ₖ {G = G} (suc (suc n))}))
          (rUnit refl)))))))

coHomRedGr : (n : ℕ) (G : AbGroup ℓ) (A : Pointed ℓ') → AbGroup _
fst (coHomRedGr n G A) = coHomRed n G A
0g (snd (coHomRedGr n G A)) = 0ₕ∙ n
AbGroupStr._+_ (snd (coHomRedGr n G A)) = _+ₕ∙_
- snd (coHomRedGr n G A) = -ₕ∙_
is-set (isSemigroup (isMonoid (isGroup (isAbGroup (snd (coHomRedGr n G A)))))) = squash₂
·Assoc (isSemigroup (isMonoid (isGroup (isAbGroup (snd (coHomRedGr n G A)))))) = coHomRedAxioms.assocₕ∙ n
·IdR (isMonoid (isGroup (isAbGroup (snd (coHomRedGr n G A))))) = coHomRedAxioms.rUnitₕ∙ n
·IdL (isMonoid (isGroup (isAbGroup (snd (coHomRedGr n G A))))) = coHomRedAxioms.lUnitₕ∙ n
·InvR (isGroup (isAbGroup (snd (coHomRedGr n G A)))) = coHomRedAxioms.rCancelₕ∙ n
·InvL (isGroup (isAbGroup (snd (coHomRedGr n G A)))) = coHomRedAxioms.lCancelₕ∙ n
+Comm (isAbGroup (snd (coHomRedGr n G A))) = coHomRedAxioms.commₕ∙ n

coHom≅coHomRed : (n : ℕ) (G : AbGroup ℓ) (A : Pointed ℓ')
  → AbGroupEquiv (coHomGr (suc n) G (fst A)) (coHomRedGr (suc n) G A)
coHom≅coHomRed n G A =
  GroupIso→GroupEquiv (invGroupIso main)
  where
  con-lem : (n : ℕ) (x : EM G (suc n)) → ∥ x ≡ 0ₖ (suc n) ∥₁
  con-lem n =
    EM-raw'-elim G (suc n)
     (λ _ → isProp→isOfHLevelSuc (suc n) squash₁)
       (EM-raw'-trivElim G n (λ _ → isProp→isOfHLevelSuc n squash₁)
         ∣ EM-raw'→EM∙ G (suc n) ∣₁)

  main : GroupIso _ _
  Iso.fun (fst main) = ST.map fst
  Iso.inv (fst main) = ST.map λ f → (λ x → f x -ₖ f (pt A))
                            , rCancelₖ (suc n) (f (pt A))
  Iso.rightInv (fst main) =
    ST.elim (λ _ → isSetPathImplicit)
      λ f → PT.rec (squash₂ _ _)
        (λ p → cong ∣_∣₂
          (funExt λ x → cong (λ z → f x +ₖ z)
            (cong -ₖ_ p ∙ -0ₖ (suc n)) ∙ rUnitₖ (suc n) (f x)))
        (con-lem n (f (pt A)))
  Iso.leftInv (fst main) =
    ST.elim (λ _ → isSetPathImplicit)
      λ f → cong ∣_∣₂ (→∙Homogeneous≡ (isHomogeneousEM (suc n))
             (funExt λ x → cong (fst f x +ₖ_) (cong -ₖ_ (snd f) ∙ -0ₖ (suc n))
                          ∙ rUnitₖ (suc n) (fst f x)))
  snd main =
    makeIsGroupHom (ST.elim2 (λ _ _ → isSetPathImplicit)
      λ _ _ → refl)

-- ℤ/2 lemmas
+ₕ≡id-ℤ/2 : ∀ {ℓ}  {A : Type ℓ} (n : ℕ) (x : coHom n ℤ/2 A) → x +ₕ x ≡ 0ₕ n
+ₕ≡id-ℤ/2 n =
  ST.elim (λ _ → isSetPathImplicit)
    λ f → cong ∣_∣₂ (funExt λ x → +ₖ≡id-ℤ/2 n (f x))

-ₕConst-ℤ/2 : (n : ℕ) {A : Type ℓ} (x : coHom n ℤ/2 A) → -ₕ x ≡ x
-ₕConst-ℤ/2 zero =
  ST.elim (λ _ → isSetPathImplicit)
    λ f → cong ∣_∣₂ (funExt λ x → -Const-ℤ/2 (f x))
-ₕConst-ℤ/2 (suc n) =
  ST.elim (λ _ → isSetPathImplicit)
    λ f → cong ∣_∣₂ (funExt λ x → -ₖConst-ℤ/2 n (f x))

coHomFun : ∀ {ℓ''} {A : Type ℓ} {B : Type ℓ'} {G : AbGroup ℓ''}
            (n : ℕ) (f : A → B)
         → coHom n G B → coHom n G A
coHomFun n f = ST.map λ g x → g (f x)

coHomHom : ∀ {ℓ''} {A : Type ℓ} {B : Type ℓ'} {G : AbGroup ℓ''}
            (n : ℕ) (f : A → B)
         → AbGroupHom (coHomGr n G B) (coHomGr n G A)
fst (coHomHom n f) = coHomFun n f
snd (coHomHom n f) =
  makeIsGroupHom (ST.elim2 (λ _ _ → isOfHLevelPath 2 squash₂ _ _)
   λ f g → refl)

coHomFun∙ : ∀ {ℓ''} {A : Pointed ℓ} {B : Pointed ℓ'} {G : AbGroup ℓ''}
            (n : ℕ) (f : A →∙ B)
         → coHomRed n G B → coHomRed n G A
coHomFun∙ n f = ST.map λ g → g ∘∙ f

coHomHom∙ : ∀ {ℓ''} {A : Pointed ℓ} {B : Pointed ℓ'} {G : AbGroup ℓ''}
            (n : ℕ) (f : A →∙ B)
         → AbGroupHom (coHomRedGr n G B) (coHomRedGr n G A)
fst (coHomHom∙ n f) = coHomFun∙ n f
snd (coHomHom∙ n f) =
  makeIsGroupHom (ST.elim2 (λ _ _ → isSetPathImplicit)
    λ g h → cong ∣_∣₂ (→∙Homogeneous≡ (isHomogeneousEM n) refl))
