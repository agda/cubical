{-# OPTIONS --safe #-}
module Cubical.HITs.Sn.Properties where

open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Path
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Univalence
open import Cubical.HITs.S1 renaming (_·_ to _*_)
open import Cubical.HITs.S2
open import Cubical.HITs.S3
open import Cubical.Data.Nat hiding (elim)
open import Cubical.Data.Sigma
open import Cubical.HITs.Sn.Base
open import Cubical.HITs.Susp renaming (toSusp to σ)
open import Cubical.HITs.Truncation
open import Cubical.Homotopy.Connected
open import Cubical.HITs.Join renaming (joinS¹S¹→S³ to joinS¹S¹→S3)
open import Cubical.Data.Bool


private
  variable
    ℓ : Level

open Iso

IsoSucSphereSusp : (n : ℕ) → Iso (S₊ (suc n)) (Susp (S₊ n))
IsoSucSphereSusp zero = S¹IsoSuspBool
IsoSucSphereSusp (suc n) = idIso

IsoSucSphereSusp∙ : (n : ℕ)
  → Iso.inv (IsoSucSphereSusp n) north ≡ ptSn (suc n)
IsoSucSphereSusp∙ zero = refl
IsoSucSphereSusp∙ (suc n) = refl

-- Elimination principles for spheres
sphereElim : (n : ℕ) {A : (S₊ (suc n)) → Type ℓ} → ((x : S₊ (suc n)) → isOfHLevel (suc n) (A x))
          → A (ptSn (suc n))
          → (x : S₊ (suc n)) → A x
sphereElim zero hlev pt = toPropElim hlev pt
sphereElim (suc n) hlev pt north = pt
sphereElim (suc n) {A = A} hlev pt south = subst A (merid (ptSn (suc n))) pt
sphereElim (suc n) {A = A} hlev pt (merid a i) =
  sphereElim n {A = λ a → PathP (λ i → A (merid a i)) pt (subst A (merid (ptSn (suc n))) pt)}
               (λ a → isOfHLevelPathP' (suc n) (hlev south) _ _)
               (λ i → transp (λ j → A (merid (ptSn (suc n)) (i ∧ j))) (~ i) pt)
               a i

sphereElim2 : ∀ {ℓ} (n : ℕ) {A : (S₊ (suc n)) → (S₊ (suc n)) → Type ℓ}
          → ((x y : S₊ (suc n)) → isOfHLevel (suc n) (A x y))
          → A (ptSn (suc n)) (ptSn (suc n))
          → (x y : S₊ (suc n)) → A x y
sphereElim2 n hlev pt = sphereElim n (λ _ → isOfHLevelΠ (suc n) λ _ → hlev _ _)
                                     (sphereElim n (hlev _ ) pt)

private
  compPath-lem : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : z ≡ y)
              → PathP (λ i → (p ∙ sym q) i ≡ y) p q
  compPath-lem {y = y} p q i j =
    hcomp (λ k → λ { (i = i0) → p j
                    ; (i = i1) → q (~ k ∨ j)
                    ; (j = i1) → y })
          (p (j ∨ i))

sphereToPropElim : (n : ℕ) {A : (S₊ (suc n)) → Type ℓ} → ((x : S₊ (suc n)) → isProp (A x))
          → A (ptSn (suc n))
          → (x : S₊ (suc n)) → A x
sphereToPropElim zero = toPropElim
sphereToPropElim (suc n) hlev pt north = pt
sphereToPropElim (suc n) {A = A} hlev pt south = subst A (merid (ptSn (suc n))) pt
sphereToPropElim (suc n) {A = A} hlev pt (merid a i) =
  isProp→PathP {B = λ i → A (merid a i)} (λ _ → hlev _) pt (subst A (merid (ptSn (suc n))) pt) i

-- Elimination rule for fibrations (x : Sⁿ) → (y : Sᵐ) → A x y of h-Level (n + m).
-- The following principle is just the special case of the "Wedge Connectivity Lemma"
-- for spheres (See Cubical.Homotopy.WedgeConnectivity or chapter 8.6 in the HoTT book).
-- We prove it directly here for three reasons:
-- (i) it should perform better
-- (ii) we get a slightly stronger statement for spheres: one of the homotopies will, by design, be refl
-- (iii) the fact that the two homotopies only differ by (composition with) the homotopy leftFunction(base) ≡ rightFunction(base)
-- is close to trivial

wedgeconFun : (n m : ℕ) {A : (S₊ (suc n)) → (S₊ (suc m)) → Type ℓ}
          → ((x : S₊ (suc n)) (y : S₊ (suc m)) → isOfHLevel ((suc n) + (suc m)) (A x y))
          → (f : (x : _) → A (ptSn (suc n)) x)
          → (g : (x : _) → A x (ptSn (suc m)))
          → (g (ptSn (suc n)) ≡ f (ptSn (suc m)))
          → (x : S₊ (suc n)) (y : S₊ (suc m)) → A x y
wedgeconLeft : (n m : ℕ) {A : (S₊ (suc n)) → (S₊ (suc m)) → Type ℓ}
             → (hLev : ((x : S₊ (suc n)) (y : S₊ (suc m)) → isOfHLevel ((suc n) + (suc m)) (A x y)))
             → (f : (x : _) → A (ptSn (suc n)) x)
             → (g : (x : _) → A x (ptSn (suc m)))
             → (hom : g (ptSn (suc n)) ≡ f (ptSn (suc m)))
             → (x : _) → wedgeconFun n m hLev f g hom (ptSn (suc n)) x ≡ f x
wedgeconRight : (n m : ℕ) {A : (S₊ (suc n)) → (S₊ (suc m)) → Type ℓ}
             → (hLev : ((x : S₊ (suc n)) (y : S₊ (suc m)) → isOfHLevel ((suc n) + (suc m)) (A x y)))
             → (f : (x : _) → A (ptSn (suc n)) x)
             → (g : (x : _) → A x (ptSn (suc m)))
             → (hom : g (ptSn (suc n)) ≡ f (ptSn (suc m)))
             → (x : _) → wedgeconFun n m hLev f g hom x (ptSn (suc m)) ≡ g x
wedgeconFun zero zero {A = A} hlev f g hom = F
  where
  helper : SquareP (λ i j → A (loop i) (loop j)) (cong f loop) (cong f loop)
                        (λ i → hcomp (λ k → λ { (i = i0) → hom k
                                                ; (i = i1) → hom k })
                                      (g (loop i)))
                         λ i → hcomp (λ k → λ { (i = i0) → hom k
                                                ; (i = i1) → hom k })
                                       (g (loop i))
  helper = toPathP (isOfHLevelPathP' 1 (hlev _ _) _ _ _ _)

  F : (x y : S¹) → A x y
  F base y = f y
  F (loop i) base = hcomp (λ k → λ { (i = i0) → hom k
                                    ; (i = i1) → hom k })
                          (g (loop i))
  F (loop i) (loop j) = helper i j

wedgeconFun zero (suc m) {A = A} hlev f g hom = F₀
  module _ where
  transpLemma₀ : (x : S₊ (suc m)) → transport (λ i₁ → A base (merid x i₁)) (g base) ≡ f south
  transpLemma₀ x = cong (transport (λ i₁ → A base (merid x i₁)))
                                  hom
              ∙ (λ i → transp (λ j → A base (merid x (i ∨ j))) i
                               (f (merid x i)))

  pathOverMerid₀ : (x : S₊ (suc m)) → PathP (λ i₁ → A base (merid x i₁))
                                            (g base)
                                            (transport (λ i₁ → A base (merid (ptSn (suc m)) i₁))
                                                       (g base))
  pathOverMerid₀ x i = hcomp (λ k → λ { (i = i0) → g base
                                      ; (i = i1) → (transpLemma₀ x ∙ sym (transpLemma₀ (ptSn (suc m)))) k})
                            (transp (λ i₁ → A base (merid x (i₁ ∧ i))) (~ i)
                                    (g base))

  pathOverMeridId₀ : pathOverMerid₀ (ptSn (suc m)) ≡ λ i → transp (λ i₁ → A base (merid (ptSn (suc m)) (i₁ ∧ i))) (~ i)
                                                                 (g base)
  pathOverMeridId₀  =
       (λ j i → hcomp (λ k → λ {(i = i0) → g base
                               ; (i = i1) → rCancel (transpLemma₀ (ptSn (suc m))) j k})
                      (transp (λ i₁ → A base (merid (ptSn (suc m)) (i₁ ∧ i))) (~ i)
                              (g base)))
     ∙ λ j i → hfill (λ k → λ { (i = i0) → g base
                                ; (i = i1) → transport (λ i₁ → A base (merid (ptSn (suc m)) i₁))
                                                        (g base)})
                      (inS (transp (λ i₁ → A base (merid (ptSn (suc m)) (i₁ ∧ i))) (~ i)
                                   (g base))) (~ j)

  indStep₀ : (x : _) (a : _) → PathP (λ i → A x (merid a i))
                                             (g x)
                                             (subst (λ y → A x y) (merid (ptSn (suc m)))
                                                    (g x))
  indStep₀ = wedgeconFun zero m (λ _ _ → isOfHLevelPathP' (2 + m) (hlev _ _) _ _)
                              pathOverMerid₀
                              (λ a i → transp (λ i₁ → A a (merid (ptSn (suc m)) (i₁ ∧ i))) (~ i)
                                               (g a))
                              (sym pathOverMeridId₀)

  F₀ : (x : S¹) (y : Susp (S₊ (suc m))) → A x y
  F₀ x north = g x
  F₀ x south = subst (λ y → A x y) (merid (ptSn (suc m))) (g x)
  F₀ x (merid a i) = indStep₀ x a i
wedgeconFun (suc n) m {A = A} hlev f g hom = F₁
  module _ where
  transpLemma₁ : (x : S₊ (suc n)) → transport (λ i₁ → A (merid x i₁) (ptSn (suc m))) (f (ptSn (suc m))) ≡ g south
  transpLemma₁ x = cong (transport (λ i₁ → A (merid x i₁) (ptSn (suc m))))
                       (sym hom)
                ∙ (λ i → transp (λ j → A (merid x (i ∨ j)) (ptSn (suc m))) i
                                 (g (merid x i)))

  pathOverMerid₁ : (x : S₊ (suc n)) → PathP (λ i₁ → A (merid x i₁) (ptSn (suc m)))
                                            (f (ptSn (suc m)))
                                            (transport (λ i₁ → A (merid (ptSn (suc n)) i₁) (ptSn (suc m)))
                                                       (f (ptSn (suc m))))
  pathOverMerid₁ x i = hcomp (λ k → λ { (i = i0) → f (ptSn (suc m))
                                      ; (i = i1) → (transpLemma₁ x ∙ sym (transpLemma₁ (ptSn (suc n)))) k })
                            (transp (λ i₁ → A (merid x (i₁ ∧ i)) (ptSn (suc m))) (~ i)
                                    (f (ptSn (suc m))))

  pathOverMeridId₁ : pathOverMerid₁ (ptSn (suc n)) ≡ λ i → transp (λ i₁ → A (merid (ptSn (suc n)) (i₁ ∧ i)) (ptSn (suc m))) (~ i)
                                                                 (f (ptSn (suc m)))
  pathOverMeridId₁ =
        (λ j i → hcomp (λ k → λ { (i = i0) → f (ptSn (suc m))
                                  ; (i = i1) → rCancel (transpLemma₁ (ptSn (suc n))) j k })
                        (transp (λ i₁ → A (merid (ptSn (suc n)) (i₁ ∧ i)) (ptSn (suc m))) (~ i)
                                (f (ptSn (suc m)))))
       ∙ λ j i → hfill (λ k → λ { (i = i0) → f (ptSn (suc m))
                                  ; (i = i1) → transport (λ i₁ → A (merid (ptSn (suc n)) i₁) (ptSn (suc m)))
                                                          (f (ptSn (suc m))) })
                        (inS (transp (λ i₁ → A (merid (ptSn (suc n)) (i₁ ∧ i)) (ptSn (suc m))) (~ i)
                                     (f (ptSn (suc m))))) (~ j)

  indStep₁ : (a : _) (y : _) → PathP (λ i → A (merid a i) y)
                                             (f y)
                                             (subst (λ x → A x y) (merid (ptSn (suc n)))
                                                    (f y))
  indStep₁ = wedgeconFun n m (λ _ _ → isOfHLevelPathP' (suc (n + suc m)) (hlev _ _) _ _)
                           (λ a i → transp (λ i₁ → A (merid (ptSn (suc n)) (i₁ ∧ i)) a) (~ i)
                                            (f a))
                           pathOverMerid₁
                           pathOverMeridId₁

  F₁ : (x : Susp (S₊ (suc n))) (y : S₊ (suc m))  → A x y
  F₁ north y = f y
  F₁ south y = subst (λ x → A x y) (merid (ptSn (suc n))) (f y)
  F₁ (merid a i) y = indStep₁ a y i
wedgeconRight zero zero {A = A} hlev f g hom = right
  where
  right : (x : S¹) → _
  right base = sym hom
  right (loop i) j = hcomp (λ k → λ { (i = i0) → hom (~ j ∧ k)
                                     ; (i = i1) → hom (~ j ∧ k)
                                     ; (j = i1) → g (loop i) })
                           (g (loop i))
wedgeconRight zero (suc m) {A = A} hlev f g hom x = refl
wedgeconRight (suc n) m {A = A} hlev f g hom = right
  where
  lem : (x : _) → indStep₁ n m hlev f g hom x (ptSn (suc m)) ≡ _
  lem = wedgeconRight n m (λ _ _ → isOfHLevelPathP' (suc (n + suc m)) (hlev _ _) _ _)
                           (λ a i → transp (λ i₁ → A (merid (ptSn (suc n)) (i₁ ∧ i)) a) (~ i)
                                            (f a))
                           (pathOverMerid₁ n m hlev f g hom)
                           (pathOverMeridId₁ n m hlev f g hom)

  right : (x : Susp (S₊ (suc n))) → _ ≡ g x
  right north = sym hom
  right south = cong (subst (λ x → A x (ptSn (suc m)))
                            (merid (ptSn (suc n))))
                            (sym hom)
              ∙ λ i → transp (λ j → A (merid (ptSn (suc n)) (i ∨ j)) (ptSn (suc m))) i
                              (g (merid (ptSn (suc n)) i))
  right (merid a i) j =
    hcomp (λ k → λ { (i = i0) → hom (~ j)
                    ; (i = i1) → transpLemma₁ n m hlev f g hom (ptSn (suc n)) j
                    ; (j = i0) → lem a (~ k) i
                    ; (j = i1) → g (merid a i)})
          (hcomp (λ k →  λ { (i = i0) → hom (~ j)
                            ; (i = i1) → compPath-lem (transpLemma₁ n m hlev f g hom a) (transpLemma₁ n m hlev f g hom (ptSn (suc n))) k j
                            ; (j = i1) → g (merid a i)})
                 (hcomp (λ k → λ { (i = i0) → hom (~ j)
                                  ; (j = i0) → transp (λ i₂ → A (merid a (i₂ ∧ i)) (ptSn (suc m))) (~ i)
                                                       (f (ptSn (suc m)))
                                  ; (j = i1) → transp (λ j → A (merid a (i ∧ (j ∨ k))) (ptSn (suc m))) (k ∨ ~ i)
                                                       (g (merid a (i ∧ k))) })
                        (transp (λ i₂ → A (merid a (i₂ ∧ i)) (ptSn (suc m))) (~ i)
                                (hom (~ j)))))
wedgeconLeft zero zero {A = A} hlev f g hom x = refl
wedgeconLeft zero (suc m) {A = A} hlev f g hom = help
  where
  left₁ : (x : _) → indStep₀ m hlev f g hom base x ≡ _
  left₁ = wedgeconLeft zero m (λ _ _ → isOfHLevelPathP' (2 + m) (hlev _ _) _ _)
                              (pathOverMerid₀ m hlev f g hom)
                              (λ a i → transp (λ i₁ → A a (merid (ptSn (suc m)) (i₁ ∧ i))) (~ i)
                                               (g a))
                              (sym (pathOverMeridId₀ m hlev f g hom))

  help : (x : S₊ (suc (suc m))) → _
  help north = hom
  help south = cong (subst (A base) (merid (ptSn (suc m)))) hom
             ∙ λ i → transp (λ j → A base (merid (ptSn (suc m)) (i ∨ j))) i
                             (f (merid (ptSn (suc m)) i))
  help (merid a i) j =
    hcomp (λ k → λ { (i = i0) → hom j
                    ; (i = i1) → transpLemma₀ m hlev f g hom (ptSn (suc m)) j
                    ; (j = i0) → left₁ a (~ k) i
                    ; (j = i1) → f (merid a i)})
          (hcomp (λ k →  λ { (i = i0) → hom j
                            ; (i = i1) → compPath-lem (transpLemma₀ m hlev f g hom a)
                                                       (transpLemma₀ m hlev f g hom (ptSn (suc m))) k j
                            ; (j = i1) → f (merid a i)})
                 (hcomp (λ k → λ { (i = i0) → hom j
                                  ; (j = i0) → transp (λ i₂ → A base (merid a (i₂ ∧ i))) (~ i)
                                                       (g base)
                                  ; (j = i1) → transp (λ j → A base (merid a (i ∧ (j ∨ k)))) (k ∨ ~ i)
                                                       (f (merid a (i ∧ k)))})
                        (transp (λ i₂ → A base (merid a (i₂ ∧ i))) (~ i)
                                (hom j))))
wedgeconLeft (suc n) m {A = A} hlev f g hom _ = refl

---------- Connectedness -----------

sphereConnected : (n : HLevel) → isConnected (suc n) (S₊ n)
sphereConnected n = ∣ ptSn n ∣ , elim (λ _ → isOfHLevelPath (suc n) (isOfHLevelTrunc (suc n)) _ _)
                                     (λ a → sym (spoke ∣_∣ (ptSn n)) ∙ spoke ∣_∣ a)

-- The fact that path spaces of Sn are connected can be proved directly for Sⁿ.
-- (Unfortunately, this does not work for higher paths)
pathIdTruncSⁿ : (n : ℕ) (x y : S₊ (suc n))
             → Path (hLevelTrunc (2 + n) (S₊ (suc n))) ∣ x ∣ ∣ y ∣
             → hLevelTrunc (suc n) (x ≡ y)
pathIdTruncSⁿ n = sphereElim n (λ _ → isOfHLevelΠ (suc n) λ _ → isOfHLevelΠ (suc n)  λ _ → isOfHLevelTrunc (suc n))
                     (sphereElim n (λ _ → isOfHLevelΠ (suc n)  λ _ → isOfHLevelTrunc (suc n))
                       λ _ → ∣ refl ∣)

pathIdTruncSⁿ⁻ : (n : ℕ) (x y : S₊ (suc n))
             → hLevelTrunc (suc n) (x ≡ y)
             → Path (hLevelTrunc (2 + n) (S₊ (suc n))) ∣ x ∣ ∣ y ∣
pathIdTruncSⁿ⁻ n x y = rec (isOfHLevelTrunc (2 + n) _ _)
                           (J (λ y _ → Path (hLevelTrunc (2 + n) (S₊ (suc n))) ∣ x ∣ ∣ y ∣) refl)

pathIdTruncSⁿretract : (n : ℕ) (x y : S₊ (suc n)) → (p : hLevelTrunc (suc n) (x ≡ y)) → pathIdTruncSⁿ n x y (pathIdTruncSⁿ⁻ n x y p) ≡ p
pathIdTruncSⁿretract n =
  sphereElim n (λ _ → isOfHLevelΠ (suc n) λ _ → isOfHLevelΠ (suc n) λ _ → isOfHLevelPath (suc n) (isOfHLevelTrunc (suc n)) _ _)
    λ y → elim (λ _ → isOfHLevelPath (suc n) (isOfHLevelTrunc (suc n)) _ _)
      (J (λ y p → pathIdTruncSⁿ n (ptSn (suc n)) y (pathIdTruncSⁿ⁻ n (ptSn (suc n)) y ∣ p ∣) ≡ ∣ p ∣)
         (cong (pathIdTruncSⁿ n (ptSn (suc n)) (ptSn (suc n))) (transportRefl refl) ∙ pm-help n))
  where
  pm-help : (n : ℕ) → pathIdTruncSⁿ n (ptSn (suc n)) (ptSn (suc n)) refl  ≡ ∣ refl ∣
  pm-help zero = refl
  pm-help (suc n) = refl

isConnectedPathSⁿ : (n : ℕ) (x y : S₊ (suc n)) → isConnected (suc n) (x ≡ y)
isConnectedPathSⁿ n x y =
  isContrRetract
   (pathIdTruncSⁿ⁻ n x y)
   (pathIdTruncSⁿ n x y)
   (pathIdTruncSⁿretract n x y)
     ((isContr→isProp (sphereConnected (suc n)) ∣ x ∣ ∣ y ∣)
      , isProp→isSet (isContr→isProp (sphereConnected (suc n))) _ _ _)

-- Some lemmas on the H space structure on S¹
rUnitS¹ : (x : S¹) → x * base ≡ x
rUnitS¹ base = refl
rUnitS¹ (loop i₁) = refl

commS¹ : (a x : S¹) → a * x ≡ x * a
commS¹ = wedgeconFun _ _ (λ _ _ → isGroupoidS¹ _ _)
         (sym ∘ rUnitS¹)
         rUnitS¹
         refl

assocS¹ : (x y z : S¹) → x * (y * z) ≡ (x * y) * z
assocS¹ = wedgeconFun _ _ (λ _ _ → isSetΠ λ _ → isGroupoidS¹ _ _)
          (λ _ _ → refl)
          (λ x z i → (rUnitS¹ x (~ i)) * z)
          refl

invLooperDistr : (x y : S¹) → invLooper (x * y) ≡ invLooper x * invLooper y
invLooperDistr =
  wedgeconFun 0 0 (λ _ _ → isGroupoidS¹ _ _) (λ _ → refl)
    (λ x → cong invLooper (rUnitS¹ x) ∙ sym (rUnitS¹ (invLooper x)))
    (sym (rUnit refl))

SuspS¹-hom : (a x : S¹)
  → Path (Path (hLevelTrunc 4 (S₊ 2)) _ _)
          (cong ∣_∣ₕ (σ (S₊∙ 1) (a * x)))
          (cong ∣_∣ₕ (σ (S₊∙ 1) a)
        ∙ (cong ∣_∣ₕ (σ (S₊∙ 1) x)))
SuspS¹-hom = wedgeconFun _ _ (λ _ _ → isOfHLevelTrunc 4 _ _ _ _)
           (λ x → lUnit _
                 ∙ cong (_∙ cong ∣_∣ₕ (σ (S₊∙ 1) x))
                        (cong (cong ∣_∣ₕ) (sym (rCancel (merid base)))))
           (λ x → (λ i → cong ∣_∣ₕ (σ (S₊∙ 1) (rUnitS¹ x i)))
               ∙∙ rUnit _
               ∙∙ cong (cong ∣_∣ₕ (σ (S₊∙ 1) x) ∙_)
                       (cong (cong ∣_∣ₕ) (sym (rCancel (merid base)))))
           (sym (l (cong ∣_∣ₕ (σ (S₊∙ 1) base))
                (cong (cong ∣_∣ₕ) (sym (rCancel (merid base))))))
  where
  l : ∀ {ℓ} {A : Type ℓ} {x : A} (p : x ≡ x) (P : refl ≡ p)
    → lUnit p ∙ cong (_∙ p) P ≡ rUnit p ∙ cong (p ∙_) P
  l p = J (λ p P → lUnit p ∙ cong (_∙ p) P ≡ rUnit p ∙ cong (p ∙_) P) refl

rCancelS¹ : (x : S¹) → ptSn 1 ≡ x * (invLooper x)
rCancelS¹ base = refl
rCancelS¹ (loop i) j =
  hcomp (λ r → λ {(i = i0) → base ; (i = i1) → base ; (j = i0) → base})
        base

SuspS¹-inv : (x : S¹) → Path (Path (hLevelTrunc 4 (S₊ 2)) _ _)
                         (cong ∣_∣ₕ (σ (S₊∙ 1) (invLooper x)))
                         (cong ∣_∣ₕ (sym (σ (S₊∙ 1) x)))
SuspS¹-inv x = (lUnit _
       ∙∙ cong (_∙ cong ∣_∣ₕ (σ (S₊∙ 1) (invLooper x)))
               (sym (lCancel (cong ∣_∣ₕ (σ (S₊∙ 1) x))))
                  ∙∙ sym (assoc _ _ _))
       ∙∙ cong (sym (cong ∣_∣ₕ (σ (S₊∙ 1) x)) ∙_) lem
       ∙∙ (assoc _ _ _
       ∙∙ cong (_∙ (cong ∣_∣ₕ (sym (σ (S₊∙ 1) x))))
               (lCancel (cong ∣_∣ₕ (σ (S₊∙ 1) x)))
       ∙∙ sym (lUnit _))
  where
  lem : cong ∣_∣ₕ (σ (S₊∙ 1) x)
      ∙ cong ∣_∣ₕ (σ (S₊∙ 1) (invLooper x))
     ≡ cong ∣_∣ₕ (σ (S₊∙ 1) x)
     ∙ cong ∣_∣ₕ (sym (σ (S₊∙ 1) x))
  lem = sym (SuspS¹-hom x (invLooper x))
     ∙ ((λ i → cong ∣_∣ₕ (σ (S₊∙ 1) (rCancelS¹ x (~ i))))
     ∙ cong (cong ∣_∣ₕ) (rCancel (merid base))) ∙ sym (rCancel _)

-------------------- join Sⁿ Sᵐ ≃ Sⁿ⁺¹⁺ᵐ -------------------------
{-
This section contains a proof that join Sⁿ Sᵐ ≃ Sⁿ⁺ᵐ⁺¹. This is easy using
various properties proved in HITs.Join. However, we would like the map
join Sⁿ Sᵐ → Sⁿ⁺ᵐ⁺¹
to be nice, in particular when n = m = 1. Therefore, we put in some extra work into
the equivalence.
-}


{- We begin with join S¹ S¹ ≃ S³. The iso is induced by: -}
S¹×S¹→S² : S¹ → S¹ → S₊ 2
S¹×S¹→S² base y = north
S¹×S¹→S² (loop i) base = north
S¹×S¹→S² (loop i) (loop j) =
  (sym (rCancel (merid base))
  ∙∙ (λ i → merid (loop i) ∙ sym (merid base))
  ∙∙ rCancel (merid base)) i j

joinS¹S¹→S³ : join S¹ S¹ → S₊ 3
joinS¹S¹→S³ (inl x) = north
joinS¹S¹→S³ (inr x) = south
joinS¹S¹→S³ (push a b i) = merid (S¹×S¹→S² a b) i

{- Proving that this is an equivalence directly is painful,
  so we simply prove that it is equal to the old definition of
  the equivalence join S¹ S¹ ≃ S³ ≃ S₊ 3
  To this end, we start by rephrasing the map -}
private
  3cell : (r i j k : I) → S₊ 3
  3cell r i j k =
    hfill (λ r → λ {(i = i0) → merid (merid base j) (k ∧ ~ r)
                   ; (i = i1) → merid (merid base j) (k ∧ ~ r)
                   ; (j = i0) → merid north (k ∧ ~ r)
                   ; (j = i1) → merid south (k ∧ ~ r)
                   ; (k = i0) → north
                   ; (k = i1) → merid (merid base j) (~ r)})
          (inS (merid (merid (loop i) j) k))
          r

joinS¹S¹→S³' : join S¹ S¹ → S₊ 3
joinS¹S¹→S³' (inl x) = north
joinS¹S¹→S³' (inr x) = north
joinS¹S¹→S³' (push base b i) = north
joinS¹S¹→S³' (push (loop i₁) base i) = north
joinS¹S¹→S³' (push (loop i₁) (loop i₂) i) = 3cell i1 i₁ i₂ i

{- These two maps are equal -}
joinS¹S¹→S³'≡joinS¹S¹→S³' : (x : _) → joinS¹S¹→S³ x ≡ joinS¹S¹→S³' x
joinS¹S¹→S³'≡joinS¹S¹→S³' (inl base) = refl
joinS¹S¹→S³'≡joinS¹S¹→S³' (inl (loop i)) = refl
joinS¹S¹→S³'≡joinS¹S¹→S³' (inr base) = sym (merid north)
joinS¹S¹→S³'≡joinS¹S¹→S³' (inr (loop i)) = sym (merid north)
joinS¹S¹→S³'≡joinS¹S¹→S³' (push base base i) k = merid north (~ k ∧ i)
joinS¹S¹→S³'≡joinS¹S¹→S³' (push base (loop i₁) i) k  = merid north (~ k ∧ i)
joinS¹S¹→S³'≡joinS¹S¹→S³' (push (loop i₁) base i) k =  (merid north) (~ k ∧ i)
joinS¹S¹→S³'≡joinS¹S¹→S³' (push (loop i) (loop j) k) l =
  hcomp (λ r → λ { (i = i0) → merid (sym (rCancel (merid base)) (~ r) j)
                                      (~ l ∧ k)
                  ; (i = i1) → merid (sym (rCancel (merid base)) (~ r) j)
                                      (~ l ∧ k)
                  ; (j = i0) → merid north (~ l ∧ k)
                  ; (j = i1) → merid north (~ l ∧ k)
                  ; (k = i0) → north
                  ; (k = i1) → merid (sym (rCancel (merid base)) (~ r) j) (~ l)
                  ; (l = i0) → merid (doubleCompPath-filler
                                      (sym (rCancel (merid base)))
                                      (cong (σ (S₊∙ 1)) loop)
                                      (rCancel (merid base)) r i j) k
                  ; (l = i1) → 3cell i1 i j k})
    (hcomp (λ r → λ {(i = i0) → merid (cp-fill base r j) (k ∧ ~ l)
                   ; (i = i1) → merid (cp-fill base r j) (k ∧ ~ l)
                   ; (j = i0) → merid north (~ l ∧ k)
                   ; (j = i1) → merid (merid base (~ r)) (~ l ∧ k)
                   ; (k = i0) → north
                   ; (k = i1) → merid (cp-fill base r j) (~ l)
                   ; (l = i0) → merid (cp-fill (loop i) r j) k
                   ; (l = i1) → 3cell i1 i j k})
       (hcomp (λ r → λ {(i = i0) → merid (merid base j) (k ∧ (~ r ∨ ~ l))
                   ; (i = i1) → merid (merid base j) (k ∧ (~ r ∨ ~ l))
                   ; (j = i0) → merid north (k ∧ (~ l ∨ ~ r))
                   ; (j = i1) → merid south (k ∧ (~ l ∨ ~ r))
                   ; (k = i0) → north
                   ; (k = i1) → merid (merid base j) (~ r ∨ ~ l)
                   ; (l = i0) → merid (merid (loop i) j) k
                   ; (l = i1) → 3cell r i j k})
              (merid (merid (loop i) j) k)))
  where
  cp-fill : (a : S¹) → _
  cp-fill a = compPath-filler (merid a) (sym (merid base))

{- joinS¹S¹→S³' is equal to the original
  equivalence (modulo a flipping of interval variables) -}
joinS¹S¹→S³'Id : (x : join S¹ S¹)
  → joinS¹S¹→S³' x ≡ (Iso.fun IsoS³S3 ∘ flip₀₂S³ ∘ joinS¹S¹→S3) x
joinS¹S¹→S³'Id (inl x) = refl
joinS¹S¹→S³'Id (inr x) = refl
joinS¹S¹→S³'Id (push base base i) = refl
joinS¹S¹→S³'Id (push base (loop i₁) i) = refl
joinS¹S¹→S³'Id (push (loop i₁) base i) = refl
joinS¹S¹→S³'Id (push (loop i) (loop j) k) l =
  hcomp (λ r → λ {(i = i0) → merid (merid base (j ∧ ~ l)) (~ r ∧ k)
                 ; (i = i1) → merid (merid base (j ∧ ~ l)) (~ r ∧ k)
                 ; (j = i0) → merid north (k ∧ ~ r)
                 ; (j = i1) → merid (merid base (~ l)) (~ r ∧ k)
                 ; (k = i0) → north
                 ; (k = i1) → merid (merid base (j ∧ ~ l)) (~ r)
                 ; (l = i0) → 3cell r i j k
                 ; (l = i1) → Iso.fun (IsoType→IsoSusp S²IsoSuspS¹)
                                       (meridian-contraction-2 k j i r)})
        (merid (S²Cube i j l) k)
  where
  S²Cube : Cube {A = S₊ 2} (λ j l → merid base (j ∧ ~ l))
                             (λ j l → merid base (j ∧ ~ l))
                             (λ i l → north)
                             (λ i l → merid base (~ l))
                             (λ i j → merid (loop i) j)
                             λ i j → fun S²IsoSuspS¹ (surf j i)
  S²Cube i j l =
    hcomp (λ r → λ {(i = i0) → merid base (j ∧ (~ l ∨ ~ r))
                 ; (i = i1) → merid base (j ∧ (~ l ∨ ~ r))
                 ; (j = i0) → north
                 ; (j = i1) → merid base (~ l ∨ ~ r)
                 ; (l = i0) → merid (loop i) j
                 ; (l = i1) → meridian-contraction j i r})
           (merid (loop i) j)

{-So, finally our map joinS¹S¹→S³ is an iso. We state its inverse explicitly. -}
Iso-joinS¹S¹-S³ : Iso (join S¹ S¹) (S₊ 3)
fun Iso-joinS¹S¹-S³ = joinS¹S¹→S³
inv Iso-joinS¹S¹-S³ = S³→joinS¹S¹ ∘ flip₀₂S³ ∘ Iso.inv IsoS³S3
rightInv Iso-joinS¹S¹-S³ x =
     joinS¹S¹→S³'≡joinS¹S¹→S³'
       ((S³→joinS¹S¹ ∘ flip₀₂S³ ∘ Iso.inv IsoS³S3) x)
  ∙∙ joinS¹S¹→S³'Id ((S³→joinS¹S¹ ∘ flip₀₂S³ ∘ Iso.inv IsoS³S3) x)
  ∙∙ Iso.leftInv (compIso (invIso IsoS³S3)
                  (compIso flip₀₂S³Iso (S³IsojoinS¹S¹))) x
leftInv Iso-joinS¹S¹-S³ x =
     cong (S³→joinS¹S¹ ∘ flip₀₂S³ ∘ inv IsoS³S3)
          (joinS¹S¹→S³'≡joinS¹S¹→S³' x ∙ joinS¹S¹→S³'Id x)
   ∙ Iso.rightInv (compIso (invIso IsoS³S3) (compIso flip₀₂S³Iso (S³IsojoinS¹S¹))) x

{- We now get the full iso Sⁿ * Sᵐ ≃ Sⁿ⁺ᵐ⁺¹ -}
IsoSphereJoin : (n m : ℕ)
  → Iso (join (S₊ n) (S₊ m)) (S₊ (suc (n + m)))
IsoSphereJoin zero zero = compIso (invIso Susp-iso-joinBool) (invIso S¹IsoSuspBool)
IsoSphereJoin zero (suc m) = compIso join-comm (invIso Susp-iso-joinBool)
IsoSphereJoin (suc zero) zero = (invIso Susp-iso-joinBool)
IsoSphereJoin (suc zero) (suc zero) = Iso-joinS¹S¹-S³
IsoSphereJoin (suc zero) (suc (suc m)) =
  compIso join-comm
    (compIso (compIso (Iso-joinSusp-suspJoin {A = S₊∙ (suc m)} {B = S₊∙ (suc zero)})
      (congSuspIso join-comm))
      (congSuspIso (IsoSphereJoin (suc zero) (suc m))))
IsoSphereJoin (suc (suc n)) m =
  compIso (Iso-joinSusp-suspJoin {A = S₊∙ (suc n)} {B = S₊∙ m}) (congSuspIso (IsoSphereJoin (suc n) m))

{- Pointedness holds by refl.
  This is due to the explicit definition of Iso-joinSusp-suspJoin  -}
IsoSphereJoinPres∙ : (n m : ℕ)
  → Iso.fun (IsoSphereJoin n m) (inl (ptSn n)) ≡ ptSn (suc (n + m))
IsoSphereJoinPres∙ zero zero = refl
IsoSphereJoinPres∙ zero (suc m) = refl
IsoSphereJoinPres∙ (suc zero) zero = refl
IsoSphereJoinPres∙ (suc zero) (suc zero) = refl
IsoSphereJoinPres∙ (suc zero) (suc (suc m)) = refl
IsoSphereJoinPres∙ (suc (suc n)) m = refl

IsoSphereJoin⁻Pres∙ : (n m : ℕ)
  → Iso.inv (IsoSphereJoin n m) (ptSn (suc (n + m))) ≡ inl (ptSn n)
IsoSphereJoin⁻Pres∙ n m =
     cong (Iso.inv (IsoSphereJoin n m)) (sym (IsoSphereJoinPres∙ n m))
   ∙ Iso.leftInv (IsoSphereJoin n m) (inl (ptSn n))

-- Inversion on spheres
invSphere : {n : ℕ} → S₊ n → S₊ n
invSphere {n = zero} = not
invSphere {n = (suc zero)} = invLooper
invSphere {n = (suc (suc n))} = invSusp

invSphere² : (n : ℕ) (x : S₊ n) → invSphere (invSphere x) ≡ x
invSphere² zero = notnot
invSphere² (suc zero) base = refl
invSphere² (suc zero) (loop i) = refl
invSphere² (suc (suc n)) = invSusp²

-- Interaction between σ and invSphere
σ-invSphere : (n : ℕ) (x : S₊ (suc n))
                 → σ (S₊∙ (suc n)) (invSphere x)
                 ≡ sym (σ (S₊∙ (suc n)) x)
σ-invSphere zero base =
  rCancel (merid base) ∙∙ refl ∙∙ cong sym (sym (rCancel (merid base)))
σ-invSphere zero (loop i) j =
  hcomp (λ k → λ { (j = i0) → doubleCompPath-filler
                                 (sym (rCancel (merid base)))
                                 (λ i → (σ (S₊∙ 1) (loop (~ i))))
                                 (rCancel (merid base)) (~ k) i
                  ; (j = i1) → doubleCompPath-filler
                                  (sym (cong sym (rCancel (merid base))))
                                  (λ i → sym (σ (S₊∙ 1) (loop i)))
                                  (cong sym (rCancel (merid base))) (~ k) i})
        (sym≡cong-sym  (sym (rCancel (merid base))
                    ∙∙ (λ i → (σ (S₊∙ 1) (loop i)))
                    ∙∙ (rCancel (merid base))) j i)
σ-invSphere (suc n) x = toSusp-invSusp (S₊∙ (suc n)) x


-- Some facts about the map S¹×S¹→S²
-- Todo: generalise to Sⁿ×Sᵐ→Sⁿ⁺ᵐ
S¹×S¹→S²rUnit : (a : S¹) → S¹×S¹→S² a base ≡ north
S¹×S¹→S²rUnit base = refl
S¹×S¹→S²rUnit (loop i) = refl

S¹×S¹→S²x+x : (x : S¹) → S¹×S¹→S² x x ≡ north
S¹×S¹→S²x+x base = refl
S¹×S¹→S²x+x (loop i) k = lem k i
  where
  lem : cong₂ S¹×S¹→S² loop loop ≡ refl
  lem = cong₂Funct S¹×S¹→S² loop loop
    ∙ (λ i → rUnit (cong (λ x → S¹×S¹→S²rUnit x i) loop) (~ i))

S¹×S¹→S²-antiComm : (a b : S¹) → S¹×S¹→S² a b ≡ S¹×S¹→S² b (invLooper a)
S¹×S¹→S²-antiComm base base = refl
S¹×S¹→S²-antiComm base (loop i) = refl
S¹×S¹→S²-antiComm (loop i) base = refl
S¹×S¹→S²-antiComm (loop i) (loop j) k =
  sym≡flipSquare (λ j i → S¹×S¹→S² (loop i) (loop j)) (~ k) i j

private
  S¹×S¹→S²-Distr-filler : (i : I)
    → cong₂ (λ b c → S¹×S¹→S² ((loop i) * b) c) loop loop
    ≡ cong (S¹×S¹→S² (loop i)) loop
  S¹×S¹→S²-Distr-filler i =
    cong₂Funct (λ b c → S¹×S¹→S² ((loop i) * b) c) loop loop
     ∙∙ (λ j → cong (λ x → S¹×S¹→S²rUnit (rotLoop x i) j) loop ∙
                cong (λ c → S¹×S¹→S² (loop i) c) loop)
     ∙∙ sym (lUnit _)

S¹×S¹→S²-Distr : (a b : S¹) → S¹×S¹→S² (a * b) b ≡ S¹×S¹→S² a b
S¹×S¹→S²-Distr a base j = S¹×S¹→S² (rUnitS¹ a j) base
S¹×S¹→S²-Distr base (loop i) k = S¹×S¹→S²-Distr-filler i0 k i
S¹×S¹→S²-Distr (loop i₁) (loop i) k = S¹×S¹→S²-Distr-filler i₁ k i

invSusp∘S¹×S¹→S² : (a b : S¹)
  → S¹×S¹→S² a (invLooper b) ≡ invSusp (S¹×S¹→S² a b)
invSusp∘S¹×S¹→S² base b = merid base
invSusp∘S¹×S¹→S² (loop i) base = merid base
invSusp∘S¹×S¹→S² (loop i) (loop j) k =
  hcomp (λ r → λ {(i = i0) → i-Boundary₂ r j k
                 ; (i = i1) → i-Boundary₂ r j k
                 ; (j = i0) → m-b k
                 ; (j = i1) → m-b k
                 ; (k = i0) → doubleCompPath-filler
                                rCancel-mb⁻¹ (cong σ₁ loop) rCancel-mb r i (~ j)
                 ; (k = i1)
                    → invSusp (doubleCompPath-filler
                                 rCancel-mb⁻¹ (cong σ₁ loop) rCancel-mb r i j)})
   (hcomp (λ r → λ {(i = i0) → i-Boundary r (~ j) k
                   ; (i = i1) → i-Boundary r (~ j) k
                   ; (j = i0) → merid base (~ r ∨ k)
                   ; (j = i1) → merid base (r ∧ k)
                   ; (k = i0) → cp-filler (loop i) r (~ j)
                   ; (k = i1) → invSusp (cp-filler (loop i) r j)})
           (merid (loop i) (~ j)))
  where
  σ₁ = σ (S₊∙ 1)
  m-b = merid base
  rCancel-mb = rCancel m-b
  rCancel-mb⁻¹ = sym (rCancel m-b)

  cp-filler : (a : S¹) (i j : I) → S₊ 2
  cp-filler a i j = compPath-filler (merid a) (sym (merid base)) i j

  i-Boundary : I → I → I → S₊ 2
  i-Boundary r j k =
    hfill (λ r → λ{(j = i0) → m-b (k ∧ r)
                  ; (j = i1) → m-b (~ r ∨ k)
                  ; (k = i0) → cp-filler base r j
                  ; (k = i1) → invSusp (cp-filler base r (~ j))})
          (inS (m-b j))
          r

  i-Boundary₂ : I → I → I → S₊ 2
  i-Boundary₂ r j k =
    hcomp (λ i → λ {(r = i0) → i-Boundary i (~ j) k
                 ; (r = i1) → m-b k
                 ; (j = i0) → m-b (k ∨ (~ i ∧ ~ r))
                 ; (j = i1) → m-b (k ∧ (i ∨ r))
                 ; (k = i0) → rCancel-filler m-b i r (~ j)
                 ; (k = i1) → invSusp (rCancel-filler m-b i r j) })
     (hcomp (λ i → λ {(r = i0) → m-b (~ j ∨ (~ i ∧ k))
                 ; (r = i1) → m-b (k ∨ (~ i ∧ ~ j))
                 ; (j = i0) → m-b (k ∨ (~ r ∨ ~ i))
                 ; (j = i1) → m-b (k ∧ (~ i ∨ r))
                 ; (k = i0) → m-b (~ j ∧ (~ r ∨ ~ i))
                 ; (k = i1) → m-b ((~ j ∨ ~ i) ∨ r) })
            (m-b (~ j ∨ k)))
