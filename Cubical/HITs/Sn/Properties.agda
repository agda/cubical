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
open import Cubical.HITs.S1 renaming (_·_ to _*_) hiding (rec ; elim)
open import Cubical.HITs.S2 renaming (S¹×S¹→S² to S¹×S¹→S²')
open import Cubical.HITs.S3
open import Cubical.Data.Nat hiding (elim)
open import Cubical.Data.Sigma
open import Cubical.HITs.Sn.Base
open import Cubical.HITs.Susp
open import Cubical.HITs.Truncation
open import Cubical.HITs.PropositionalTruncation as PT hiding (rec ; elim)
open import Cubical.HITs.SmashProduct.Base
open import Cubical.HITs.Pushout.Base
open import Cubical.Homotopy.Connected
open import Cubical.HITs.Join renaming (joinS¹S¹→S³ to joinS¹S¹→S3)
open import Cubical.Data.Bool hiding (elim)

private
  variable
    ℓ : Level

open Iso

σSn : (n : ℕ) → S₊ n → Path (S₊ (suc n)) (ptSn (suc n)) (ptSn (suc n))
σSn zero = cong SuspBool→S¹ ∘ merid
σSn (suc n) x = toSusp (S₊∙ (suc n)) x

σS : {n : ℕ} → S₊ n → Path (S₊ (suc n)) (ptSn _) (ptSn _)
σS {n = n} = σSn n

σS∙ : {n : ℕ} → σS (ptSn n) ≡ refl
σS∙ {n = zero} = refl
σS∙ {n = suc n} = rCancel (merid (ptSn (suc n)))

IsoSucSphereSusp : (n : ℕ) → Iso (S₊ (suc n)) (Susp (S₊ n))
IsoSucSphereSusp zero = S¹IsoSuspBool
IsoSucSphereSusp (suc n) = idIso

IsoSphereSusp : (n : ℕ) → Iso (S₊ n) (Susp (S⁻ n))
IsoSphereSusp zero = BoolIsoSusp⊥
IsoSphereSusp (suc n) = IsoSucSphereSusp n

EquivSphereSusp : (n : ℕ) → Susp (S⁻ n) ≃ S₊ n
EquivSphereSusp n = isoToEquiv (invIso (IsoSphereSusp n))

IsoSucSphereSusp∙ : (n : ℕ)
  → Iso.inv (IsoSucSphereSusp n) north ≡ ptSn (suc n)
IsoSucSphereSusp∙ zero = refl
IsoSucSphereSusp∙ (suc n) = refl

IsoSucSphereSusp∙' : (n : ℕ)
  → Iso.fun (IsoSucSphereSusp n) (ptSn (suc n)) ≡ north
IsoSucSphereSusp∙' zero = refl
IsoSucSphereSusp∙' (suc n) = refl

suspFunS∙ : {n : ℕ} → (S₊ n → S₊ n) → S₊∙ (suc n) →∙ S₊∙ (suc n)
suspFunS∙ {n = zero} f =
  (λ x → Iso.inv S¹IsoSuspBool (suspFun f (Iso.fun S¹IsoSuspBool x))) , refl
suspFunS∙ {n = suc n} f = suspFun f , refl

suspFunS∙Id : {n : ℕ} → suspFunS∙ (idfun (S₊ n)) ≡ idfun∙ _
suspFunS∙Id {n = zero} = ΣPathP ((funExt (λ { base → refl
  ; (loop i) j → help j i})) , refl)
  where
  help : cong (fst (suspFunS∙ (idfun (S₊ zero)))) loop ≡ loop
  help = (λ j → cong (λ x → SuspBool→S¹ (suspFunIdFun {A = Bool} j
                               (S¹→SuspBool x))) loop)
       ∙ λ i j → S¹→SuspBool→S¹ (loop j) i
suspFunS∙Id {n = suc n} = ΣPathP (suspFunIdFun , refl)

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

sphereElim' : (n : ℕ) {A : S₊ n → Type ℓ} →
      ((x : S₊ n) → isOfHLevel n (A x)) →
      A (ptSn n) → (x : S₊ n) → A x
sphereElim' zero st _ x = st x .fst
sphereElim' (suc n) = sphereElim n

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

sphereToTrunc : (n : ℕ) {A : S⁻ n → Type ℓ}
  → ((x : S⁻ n) → hLevelTrunc n (A x))
  → ∥ ((x : _) → A x) ∥₁
sphereToTrunc zero _ = ∣ (λ{()}) ∣₁
sphereToTrunc (suc zero) {A = A} indr =
  rec squash₁ (λ p → rec squash₁
    (λ q → ∣ (λ { false → q ; true → p}) ∣₁)
         (indr false)) (indr true)
sphereToTrunc (suc (suc zero)) {A = A} indr =
  lem (indr base) (cong indr loop)
  where
  lem : (x : hLevelTrunc 2 (A base))
      → PathP (λ i → hLevelTrunc 2 (A (loop i))) x x
      → ∥ ((x : S¹) → A x) ∥₁
  lem = elim (λ _ → isSetΠ λ _ → isProp→isSet squash₁) λ a p
    → rec squash₁ (λ q → ∣ (λ { base → a
      ; (loop i) → toPathP {A = λ i → A (loop i)} q i}) ∣₁)
        (PathIdTruncIso 1 .Iso.fun
          (fromPathP p))
sphereToTrunc (suc (suc (suc n))) {A = A} indr =
  lem (sphereToTrunc (suc (suc n))) (indr north) (indr south)
    λ a → cong indr (merid a)
  where
  lem : ({A : S₊ (suc n) → Type _} →
      ((i : S₊ (suc n)) → hLevelTrunc (suc (suc n)) (A i)) →
      ∥ ((x : S₊ (suc n)) → A x) ∥₁)
      → (x : hLevelTrunc (3 + n) (A north))
        (y : hLevelTrunc (3 + n) (A south))
      → ((a : _) → PathP (λ i → hLevelTrunc (3 + n) (A (merid a i))) x y)
      → ∥ ((x : S₊ (2 + n)) → A x) ∥₁
  lem indr =
    elim (λ _ → isOfHLevelΠ2 (3 + n)
              λ _ _ → isProp→isOfHLevelSuc (2 + n) squash₁)
      λ a → elim (λ _ → isOfHLevelΠ (3 + n)
              λ _ → isProp→isOfHLevelSuc (2 + n) squash₁)
              λ b → λ f →
          PT.map (λ ma → λ { north → a
                            ; south → b
                            ; (merid a i) → ma a i})
            (indr {A = λ x → PathP (λ i → A (merid x i)) a b}
              λ x → rec (isOfHLevelTrunc (2 + n))
                (λ p → ∣ toPathP p ∣)
                (Iso.fun (PathIdTruncIso _) (fromPathP (f x))))

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
          (cong ∣_∣ₕ (σSn 1 (a * x)))
          (cong ∣_∣ₕ (σSn 1 a)
        ∙ (cong ∣_∣ₕ (σSn 1 x)))
SuspS¹-hom = wedgeconFun _ _ (λ _ _ → isOfHLevelTrunc 4 _ _ _ _)
           (λ x → lUnit _
                 ∙ cong (_∙ cong ∣_∣ₕ (σSn 1 x))
                        (cong (cong ∣_∣ₕ) (sym (rCancel (merid base)))))
           (λ x → (λ i → cong ∣_∣ₕ (σSn 1 (rUnitS¹ x i)))
               ∙∙ rUnit _
               ∙∙ cong (cong ∣_∣ₕ (σSn 1 x) ∙_)
                       (cong (cong ∣_∣ₕ) (sym (rCancel (merid base)))))
           (sym (l (cong ∣_∣ₕ (σSn 1 base))
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
                         (cong ∣_∣ₕ (σSn 1 (invLooper x)))
                         (cong ∣_∣ₕ (sym (σSn 1 x)))
SuspS¹-inv x = (lUnit _
       ∙∙ cong (_∙ cong ∣_∣ₕ (σSn 1 (invLooper x)))
               (sym (lCancel (cong ∣_∣ₕ (σSn 1 x))))
                  ∙∙ sym (assoc _ _ _))
       ∙∙ cong (sym (cong ∣_∣ₕ (σSn 1 x)) ∙_) lem
       ∙∙ (assoc _ _ _
       ∙∙ cong (_∙ (cong ∣_∣ₕ (sym (σSn 1 x))))
               (lCancel (cong ∣_∣ₕ (σSn 1 x)))
       ∙∙ sym (lUnit _))
  where
  lem : cong ∣_∣ₕ (σSn 1 x)
      ∙ cong ∣_∣ₕ (σSn 1 (invLooper x))
     ≡ cong ∣_∣ₕ (σSn 1 x)
     ∙ cong ∣_∣ₕ (sym (σSn 1 x))
  lem = sym (SuspS¹-hom x (invLooper x))
     ∙ ((λ i → cong ∣_∣ₕ (σSn 1 (rCancelS¹ x (~ i))))
     ∙ cong (cong ∣_∣ₕ) (rCancel (merid base))) ∙ sym (rCancel _)

-- Inversion on spheres
invSphere : {n : ℕ} → S₊ n → S₊ n
invSphere {n = zero} = not
invSphere {n = (suc zero)} = invLooper
invSphere {n = (suc (suc n))} = invSusp

-- sometimes also this version is useful
invSphere' : {n : ℕ} → S₊ n → S₊ n
invSphere' {n = zero} = not
invSphere' {n = (suc zero)} = invLooper
invSphere' {n = suc (suc n)} north = north
invSphere' {n = suc (suc n)} south = north
invSphere' {n = suc (suc n)} (merid a i) = σSn (suc n) a (~ i)

invSphere'≡ : {n : ℕ} → (x : S₊ n) → invSphere' x ≡ invSphere x
invSphere'≡ {n = zero} x = refl
invSphere'≡ {n = suc zero} x = refl
invSphere'≡ {n = suc (suc n)} north = merid (ptSn _)
invSphere'≡ {n = suc (suc n)} south = refl
invSphere'≡ {n = suc (suc n)} (merid a i) j =
  compPath-filler (merid a) (sym (merid (ptSn _))) (~ j) (~ i)

invSphere² : (n : ℕ) (x : S₊ n) → invSphere (invSphere x) ≡ x
invSphere² zero = notnot
invSphere² (suc zero) base = refl
invSphere² (suc zero) (loop i) = refl
invSphere² (suc (suc n)) = invSusp²

-- Interaction between σ and invSphere
σ-invSphere : (n : ℕ) (x : S₊ (suc n))
                 → σSn (suc n) (invSphere x)
                 ≡ sym (σSn (suc n) x)
σ-invSphere zero base =
  rCancel (merid base) ∙∙ refl ∙∙ cong sym (sym (rCancel (merid base)))
σ-invSphere zero (loop i) j =
  hcomp (λ k → λ { (j = i0) → doubleCompPath-filler
                                 (sym (rCancel (merid base)))
                                 (λ i → (σSn 1 (loop (~ i))))
                                 (rCancel (merid base)) (~ k) i
                  ; (j = i1) → doubleCompPath-filler
                                  (sym (cong sym (rCancel (merid base))))
                                  (λ i → sym (σSn 1 (loop i)))
                                  (cong sym (rCancel (merid base))) (~ k) i})
        (sym≡cong-sym  (sym (rCancel (merid base))
                    ∙∙ (λ i → (σSn 1 (loop i)))
                    ∙∙ (rCancel (merid base))) j i)
σ-invSphere (suc n) x = toSusp-invSusp (S₊∙ (suc n)) x
