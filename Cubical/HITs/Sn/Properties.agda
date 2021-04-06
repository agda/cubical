{-# OPTIONS --cubical --no-import-sorts --safe  #-}
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
open import Cubical.HITs.S1 hiding (_·_)
open import Cubical.Data.Nat hiding (elim)
open import Cubical.Data.Sigma
open import Cubical.HITs.Sn.Base
open import Cubical.HITs.Susp
open import Cubical.HITs.Truncation
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Connected

private
  variable
    ℓ : Level

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

wedgeConSn : ∀ {ℓ} (n m : ℕ) {A : (S₊ (suc n)) → (S₊ (suc m)) → Type ℓ}
          → ((x : S₊ (suc n)) (y : S₊ (suc m)) → isOfHLevel ((suc n) + (suc m)) (A x y))
          → (f : (x : _) → A (ptSn (suc n)) x)
          → (g : (x : _) → A x (ptSn (suc m)))
          → (g (ptSn (suc n)) ≡ f (ptSn (suc m)))
          → Σ[ F ∈ ((x : S₊ (suc n)) (y : S₊ (suc m)) → A x y) ]
              ((x : S₊ (suc m)) → F (ptSn (suc n)) x ≡ f x) × ((x : S₊ (suc n)) → F x (ptSn (suc m)) ≡ g x)
wedgeConSn zero zero {A = A} hlev f g hom = F , (λ _ → refl) , right
  where
  helper : SquareP (λ i j → A (loop i) (loop j)) (cong f loop) (cong f loop)
                        (λ i → hcomp (λ k → λ { (i = i0) → hom k
                                                ; (i = i1) → hom k })
                                      (g (loop i)))
                         λ i → hcomp (λ k → λ { (i = i0) → hom k
                                                ; (i = i1) → hom k })
                                       (g (loop i))
  helper = transport (sym (PathP≡Path _ _ _))
                     (isOfHLevelPathP' 1 (hlev base base) _ _ _ _)

  F : (x y : S¹) → A x y
  F base y = f y
  F (loop i) base = hcomp (λ k → λ { (i = i0) → hom k
                                    ; (i = i1) → hom k })
                          (g (loop i))
  F (loop i) (loop j) = helper i j

  right : (x : S¹) → F x base ≡ g x
  right base = sym hom
  right (loop i) j = hcomp (λ k → λ { (i = i0) → hom (~ j ∧ k)
                                     ; (i = i1) → hom (~ j ∧ k)
                                     ; (j = i1) → g (loop i) })
                           (g (loop i))
wedgeConSn zero (suc m) {A = A} hlev f g hom = F , left , (λ _ → refl)
  where
  transpLemma : (x : S₊ (suc m)) → transport (λ i₁ → A base (merid x i₁)) (g base) ≡ f south
  transpLemma x = cong (transport (λ i₁ → A base (merid x i₁)))
                                  hom
              ∙ (λ i → transp (λ j → A base (merid x (i ∨ j))) i
                               (f (merid x i)))

  pathOverMerid : (x : S₊ (suc m)) → PathP (λ i₁ → A base (merid x i₁))
                                            (g base)
                                            (transport (λ i₁ → A base (merid (ptSn (suc m)) i₁))
                                                       (g base))
  pathOverMerid x i = hcomp (λ k → λ { (i = i0) → g base
                                      ; (i = i1) → (transpLemma x ∙ sym (transpLemma (ptSn (suc m)))) k})
                            (transp (λ i₁ → A base (merid x (i₁ ∧ i))) (~ i)
                                    (g base))

  pathOverMeridId : pathOverMerid (ptSn (suc m)) ≡ λ i → transp (λ i₁ → A base (merid (ptSn (suc m)) (i₁ ∧ i))) (~ i)
                                                                 (g base)
  pathOverMeridId  =
       (λ j i → hcomp (λ k → λ {(i = i0) → g base
                               ; (i = i1) → rCancel (transpLemma (ptSn (suc m))) j k})
                      (transp (λ i₁ → A base (merid (ptSn (suc m)) (i₁ ∧ i))) (~ i)
                              (g base)))
     ∙ λ j i → hfill (λ k → λ { (i = i0) → g base
                                ; (i = i1) → transport (λ i₁ → A base (merid (ptSn (suc m)) i₁))
                                                        (g base)})
                      (inS (transp (λ i₁ → A base (merid (ptSn (suc m)) (i₁ ∧ i))) (~ i)
                                   (g base))) (~ j)

  indStep : Σ[ F ∈ ((x : _) (a : _) → PathP (λ i → A x (merid a i))
                                             (g x)
                                             (subst (λ y → A x y) (merid (ptSn (suc m)))
                                                    (g x))) ] _
  indStep = wedgeConSn zero m (λ _ _ → isOfHLevelPathP' (2 + m) (hlev _ _) _ _)
                              pathOverMerid
                              (λ a i → transp (λ i₁ → A a (merid (ptSn (suc m)) (i₁ ∧ i))) (~ i)
                                               (g a))
                              (sym pathOverMeridId)

  F : (x : S¹) (y : Susp (S₊ (suc m))) → A x y
  F x north = g x
  F x south = subst (λ y → A x y) (merid (ptSn (suc m))) (g x)
  F x (merid a i) = indStep .fst x a i

  left : (x : Susp (S₊ (suc m))) → F base x ≡ f x
  left north = hom
  left south = cong (subst (A base) (merid (ptSn (suc m)))) hom
             ∙ λ i → transp (λ j → A base (merid (ptSn (suc m)) (i ∨ j))) i
                             (f (merid (ptSn (suc m)) i))
  left (merid a i) j =
    hcomp (λ k → λ { (i = i0) → hom j
                    ; (i = i1) → transpLemma (ptSn (suc m)) j
                    ; (j = i0) → indStep .snd .fst a (~ k) i
                    ; (j = i1) → f (merid a i)})
          (hcomp (λ k →  λ { (i = i0) → hom j
                            ; (i = i1) → compPath-lem (transpLemma a) (transpLemma (ptSn (suc m))) k j
                            ; (j = i1) → f (merid a i)})
                 (hcomp (λ k → λ { (i = i0) → hom j
                                  ; (j = i0) → transp (λ i₂ → A base (merid a (i₂ ∧ i))) (~ i)
                                                       (g base)
                                  ; (j = i1) → transp (λ j → A base (merid a (i ∧ (j ∨ k)))) (k ∨ ~ i)
                                                       (f (merid a (i ∧ k)))})
                        (transp (λ i₂ → A base (merid a (i₂ ∧ i))) (~ i)
                                (hom j))))

wedgeConSn (suc n) m {A = A} hlev f g hom = F , ((λ _ → refl) , right)
  where
  transpLemma : (x : S₊ (suc n)) → transport (λ i₁ → A (merid x i₁) (ptSn (suc m))) (f (ptSn (suc m))) ≡ g south
  transpLemma x = cong (transport (λ i₁ → A (merid x i₁) (ptSn (suc m))))
                       (sym hom)
                ∙ (λ i → transp (λ j → A (merid x (i ∨ j)) (ptSn (suc m))) i
                                 (g (merid x i)))

  pathOverMerid : (x : S₊ (suc n)) → PathP (λ i₁ → A (merid x i₁) (ptSn (suc m)))
                                            (f (ptSn (suc m)))
                                            (transport (λ i₁ → A (merid (ptSn (suc n)) i₁) (ptSn (suc m)))
                                                       (f (ptSn (suc m))))
  pathOverMerid x i = hcomp (λ k → λ { (i = i0) → f (ptSn (suc m))
                                      ; (i = i1) → (transpLemma x ∙ sym (transpLemma (ptSn (suc n)))) k })
                            (transp (λ i₁ → A (merid x (i₁ ∧ i)) (ptSn (suc m))) (~ i)
                                    (f (ptSn (suc m))))

  pathOverMeridId : pathOverMerid (ptSn (suc n)) ≡ λ i → transp (λ i₁ → A (merid (ptSn (suc n)) (i₁ ∧ i)) (ptSn (suc m))) (~ i)
                                                                 (f (ptSn (suc m)))
  pathOverMeridId =
        (λ j i → hcomp (λ k → λ { (i = i0) → f (ptSn (suc m))
                                  ; (i = i1) → rCancel (transpLemma (ptSn (suc n))) j k })
                        (transp (λ i₁ → A (merid (ptSn (suc n)) (i₁ ∧ i)) (ptSn (suc m))) (~ i)
                                (f (ptSn (suc m)))))
       ∙ λ j i → hfill (λ k → λ { (i = i0) → f (ptSn (suc m))
                                  ; (i = i1) → transport (λ i₁ → A (merid (ptSn (suc n)) i₁) (ptSn (suc m)))
                                                          (f (ptSn (suc m))) })
                        (inS (transp (λ i₁ → A (merid (ptSn (suc n)) (i₁ ∧ i)) (ptSn (suc m))) (~ i)
                                     (f (ptSn (suc m))))) (~ j)

  indStep : Σ[ F ∈ ((a : _) (y : _) → PathP (λ i → A (merid a i) y)
                                             (f y)
                                             (subst (λ x → A x y) (merid (ptSn (suc n)))
                                                    (f y))) ] _
  indStep = wedgeConSn n m (λ _ _ → isOfHLevelPathP' (suc (n + suc m)) (hlev _ _) _ _)
                           (λ a i → transp (λ i₁ → A (merid (ptSn (suc n)) (i₁ ∧ i)) a) (~ i)
                                            (f a))
                           pathOverMerid
                           pathOverMeridId

  F : (x : Susp (S₊ (suc n))) (y : S₊ (suc m))  → A x y
  right : (x : Susp (S₊ (suc n))) → F x (ptSn (suc m)) ≡ g x
  F north y = f y
  F south y = subst (λ x → A x y) (merid (ptSn (suc n))) (f y)
  F (merid a i) y = indStep .fst a y i
  right north = sym hom
  right south = cong (subst (λ x → A x (ptSn (suc m)))
                            (merid (ptSn (suc n))))
                            (sym hom)
              ∙ λ i → transp (λ j → A (merid (ptSn (suc n)) (i ∨ j)) (ptSn (suc m))) i
                              (g (merid (ptSn (suc n)) i))
  right (merid a i) j =
    hcomp (λ k → λ { (i = i0) → hom (~ j)
                    ; (i = i1) → transpLemma (ptSn (suc n)) j
                    ; (j = i0) → indStep .snd .snd a (~ k) i
                    ; (j = i1) → g (merid a i)})
          (hcomp (λ k →  λ { (i = i0) → hom (~ j)
                            ; (i = i1) → compPath-lem (transpLemma a) (transpLemma (ptSn (suc n))) k j
                            ; (j = i1) → g (merid a i)})
                 (hcomp (λ k → λ { (i = i0) → hom (~ j)
                                  ; (j = i0) → transp (λ i₂ → A (merid a (i₂ ∧ i)) (ptSn (suc m))) (~ i)
                                                       (f (ptSn (suc m)))
                                  ; (j = i1) → transp (λ j → A (merid a (i ∧ (j ∨ k))) (ptSn (suc m))) (k ∨ ~ i)
                                                       (g (merid a (i ∧ k))) })
                        (transp (λ i₂ → A (merid a (i₂ ∧ i)) (ptSn (suc m))) (~ i)
                                (hom (~ j)))))

{-
test : {!!}
test = {!!}

tok : {n m : ℕ} {x y : S₊ (suc m)} (z : hLevelTrunc (suc n) (S₊ (suc m)))
  → Path (hLevelTrunc (suc n) (S₊ (suc m))) ∣ x ∣ z → (l : ∣ y ∣ ≡ z) → hLevelTrunc n (x ≡ y) 
tok {n = n} {m = m} {x = x} {y = y} z =
  J (λ z p → (l : ∣ y ∣ ≡ z) → hLevelTrunc n (x ≡ y) ) {!!}




pathIdTruncFunSn : {n m : ℕ} {x y : S₊ (suc m)} → Path (hLevelTrunc (suc n) (S₊ (suc m))) ∣ x ∣ ∣ y ∣ → hLevelTrunc n (x ≡ y)
pathIdTruncFunSn {n = zero} {x = x} {y = y} p = tt*
pathIdTruncFunSn {n = suc n} {m = zero} {x = base} {y = base} p = ∣ refl ∣
pathIdTruncFunSn {n = suc zero} {m = zero} {x = base} {y = loop i} p =
  hcomp (λ k → λ {(i = i0) → ∣ refl ∣ ; (i = i1) → ∣ {!!} ∣})
        (rec {!!} (λ {base → ∣ ((λ k → loop (i ∧ k))) ∣
                    ; (loop j) → ∣ (λ k → loop (i ∧ k)) ∣}) (p i))

pathIdTruncFunSn {n = suc (suc n)} {m = zero} {x = base} {y = loop i} p = {!!}
pathIdTruncFunSn {n = suc n} {m = zero} {x = loop i} {y = y} p = {!!}
pathIdTruncFunSn {n = suc n} {m = suc m} {x = x} {y = y} p = {!!}
-}
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

testFib : (n m : ℕ) (x : S₊ (suc n)) (y : hLevelTrunc (2 + m) (S₊ (suc n))) → hLevelTrunc (2 + m) Type₀
testFib n m x = rec (isOfHLevelTrunc (2 + m)) λ y → ∣ hLevelTrunc (suc m) (x ≡ y) ∣
{-
open import Cubical.Data.Int hiding (_·_ ; +-comm ; +-assoc) renaming (_+_ to _+Z_)
open import Cubical.HITs.Pushout
S¹-mod→ : (n : ℕ) → S¹ → S¹
S¹-mod→ n base = base
S¹-mod→ n (loop i) = intLoop (pos n) i

data S1-mod (n : ℕ) : Type₀ where
  [_] : S¹ → S1-mod n
  coher : cong [_] (intLoop (pos n)) ≡ refl
  isGr : isGroupoid (S1-mod n)

S1-mod-elim : ∀ {ℓ} {n : ℕ} {A : S1-mod n → Type ℓ}
           → ((x : _) → isGroupoid (A x))
           → (f : (m : S¹) → A [ m ])
           → SquareP (λ i j → A (coher i j))
                     (cong f (intLoop (pos n))) (λ i → f base)
                     (λ i → f base)            (λ i → f base)
           → (x : _) → A x
S1-mod-elim gr f p [ x ] = f x
S1-mod-elim gr f p (coher i j) = p i j
S1-mod-elim {A = A} gr f p (isGr x y a b c d i j k) = helper i j k
  where
  helper : PathP (λ i → PathP (λ j → PathP (λ k → A (isGr x y a b c d i j k))
                                             (S1-mod-elim gr f p x) (S1-mod-elim gr f p y))
                               (λ k → S1-mod-elim gr f p (a k)) λ k → S1-mod-elim gr f p (b k))
                 (λ j k → S1-mod-elim gr f p (c j k)) λ j k → S1-mod-elim gr f p (d j k)
  helper = toPathP (isOfHLevelPathP' 1 (isOfHLevelPathP' 2 (gr _) _ _) _ _ _ _)


-- finInt n = ℤ/(n-1)
open import Cubical.Data.Empty renaming (rec to ⊥-rec)
data finInt (n : ℕ) : Type₀ where
  [_] : ℕ → finInt n
  LUnit : (m : ℕ) → [ n + m ] ≡ [ m ]
  is-set : isSet (finInt n)





ℤ/_ : (n : ℕ) → Type₀
ℤ/ zero = ⊥
ℤ/ suc n = finInt n

open import Cubical.Data.Fin

finInt-rec : ∀ {ℓ} {n : ℕ} {A : Type ℓ}
           → isSet A
           → (f : ℕ → A)
           → ((x : ℕ) → (f (n + x)) ≡ (f x))
           → finInt n → A
finInt-rec {A = A} isset f _ [ x ] = f x
finInt-rec {A = A} isset f s (LUnit x i) = s x i
finInt-rec {A = A} isset f s (is-set x x₁ x₂ y i i₁) = helper i i₁ 
  where
  helper : Square (λ i₁ → finInt-rec isset f s (x₂ i₁))
                   (λ i₁ → finInt-rec isset f s (y i₁))
                   (λ i → finInt-rec isset f s x)
                   λ i → finInt-rec isset f s x₁
  helper = isSet→isSet' isset _ _ _ _


open import Cubical.Data.Nat.Order
open import Cubical.Data.Sum renaming (rec to ⊎-rec)
open import Cubical.Relation.Nullary

suc[] : {n : ℕ} → finInt n → finInt n
suc[] {n = n} [ x ] = [ suc x ]
suc[] {n = n} (LUnit m i) = ((λ i → [ +-suc n m (~ i) ]) ∙ LUnit (suc m)) i
suc[] {n = n} (is-set x x₁ x₂ y i i₁) =
  is-set (suc[] x) (suc[] x₁) (cong suc[] x₂) (cong suc[] y) i i₁

congSuc[] : (n x y : ℕ) → Path (finInt n) [ x ] [ y ] → Path (finInt n) [ suc x ] [ suc y ] 
congSuc[] n x y p = {!<-suc!}

<-suc : {x y : ℕ} → x < y → suc x < suc y
<-suc {x = x} le = (fst le) , (+-suc (fst le) (suc x) ∙ cong suc (snd le))


module _ (n : ℕ) where
  help2 : (n y : ℕ) → y < (suc n) → ¬ (y ≡ n) → suc y < suc n
  help2 zero zero le false = ⊥-rec (false refl)
  help2 (suc n) zero le false = n , +-comm n 2
  help2 zero (suc y) (zero , p) false = ⊥-rec (snotz (cong predℕ p))
  help2 zero (suc y) (suc k , p) false = ⊥-rec (snotz (sym (+-suc k (suc y)) ∙ cong predℕ p))
  help2 (suc n) (suc y) le false = <-suc (help2 n y ((fst le) , (cong predℕ (sym (+-suc (fst le) (suc y)) ∙ snd le))) λ p → false (cong suc p))

  help : (x : ℕ) →  (p : Σ[ y ∈ ℕ ] (Path (finInt (suc n)) [ x ] [ y ] × (y < suc n))) → Dec (fst p ≡ n)
                   → Σ[ y ∈ ℕ ] (Path (finInt (suc n)) [ (suc x) ] [ y ] × (y < suc n))
  help x (y , l , k) (yes p) = 0 , (cong suc[] l ∙∙ (λ i → [ suc (p i) ]) ∙ (λ i → [ +-comm 0 (suc n) i ]) ∙∙ LUnit 0) , n , (+-comm n 1)
  help x (y , l , k) (no ¬p) = (suc y) , (cong suc[] l) , help2 n y k ¬p

helpfun : (n x : ℕ) → (p : Σ[ y ∈ ℕ ] ((Σ[ k ∈ ℕ ] (x ≡ y + k · (suc n))) × (y < (suc n))))
      → ((fst p < n) ⊎ (fst p ≡ n))
      →  Σ[ y ∈ ℕ ] ((Σ[ k ∈ ℕ ] (suc x ≡ y + k · (suc n))) × (y < (suc n)))
helpfun n x (y , (k , i) , le) (inr z) = 0 , (k + 1  , (cong suc i ∙∙ (λ i → suc (z i) + k · suc n) ∙∙  cong (_· suc n) (+-comm 1 k))) , n , +-comm n 1
helpfun n x (y , (k , i) , le) (inl z) = suc y , (k , cong suc i) , <-suc z

isProp⊎< : (x y : ℕ) → isProp ((x < y) ⊎ (x ≡ y))
isProp⊎< x y (inl x₁) (inl x₂) i = inl (m<n-isProp x₁ x₂ i)
isProp⊎< x y (inl x₁) (inr x₂) = ⊥-rec (¬m<m (subst (λ x → x < y) x₂ x₁))
isProp⊎< x y (inr x₁) (inl x₂) = ⊥-rec (¬m<m (subst (λ x → x < y) x₁ x₂))
isProp⊎< x y (inr x₁) (inr x₂) i = inr (isSetℕ x y x₁ x₂ i)

helpfunId : (n x : ℕ) → (p : Σ[ y ∈ ℕ ] ((Σ[ k ∈ ℕ ] (x ≡ y + k · (suc n))) × (y < (suc n))))
      → (z w : (fst p < n) ⊎ (fst p ≡ n)) → helpfun n x p z ≡ helpfun n x p w
helpfunId n x p z w i = helpfun n x p (isProp⊎< _ _ z w i)

leastElem : (n x : ℕ) → Σ[ y ∈ ℕ ] ((Σ[ k ∈ ℕ ] (x ≡ y + k · (suc n))) × (y < (suc n)))
leastElem n zero = 0 , (0 , refl) , (n , +-comm n 1)
leastElem n (suc x) = helpfun n x (leastElem n x) (<-split (snd (snd (leastElem n x))))


isPropLeast : (n x y : ℕ) → ((Σ[ k ∈ ℕ ] (x ≡ y + k · (suc n))) × (y < (suc n)))
isPropLeast n x = {!!}


open import Cubical.Foundations.Function
{-
leastElem-lem-n : (n : ℕ) → Dec (fst (leastElem (suc n) n) ≡ suc n) → fst (leastElem (suc n) (suc n)) ≡ 0
leastElem-lem-n n (yes p) i = (fst (help (suc n) n (leastElem (suc n) n)
                                      (isPropDec (isSetℕ (fst (leastElem (suc n) n)) (suc n))
                                                    (discreteℕ (fst (leastElem (suc n) n)) (suc n))
                                                    (yes p) i)))
leastElem-lem-n n (no ¬p) = (λ i → (fst (help (suc n) n (leastElem (suc n) n)
                                      (isPropDec (isSetℕ (fst (leastElem (suc n) n)) (suc n))
                                                    (discreteℕ (fst (leastElem (suc n) n)) (suc n))
                                                    (no ¬p) i)))) ∙ {!suc (fst (leastElem (suc n) n))!} ∙ {!¬p!}
{- (fst (help (suc n) n (leastElem (suc n) n)
                                      (isPropDec (isSetℕ (fst (leastElem (suc n) n)) (suc n))
                                                    (discreteℕ (fst (leastElem (suc n) n)) (suc n))
                                                    (yes {!discreteℕ (fst (leastElem (suc n) n)) (suc n)!}) i))) -}
  where
  c = (leastElem (suc n) n)

  help3 : fst c ≡ suc n
  help3 = {!fst c !}
-}


{-
_+fin_ : {n : ℕ} → finInt n → finInt n → finInt n
_+fin_ {n = zero} x y = [ 0 ]
_+fin_ {n = suc n} =
  elimfinInt (λ _ → isSetΠ λ _ → is-set)
    (λ x → elimfinInt (λ _ → is-set)
               (λ y → [ x + y ])
               ((λ i → [ +-comm x (suc n) i ]) ∙∙ LUnit _ ∙∙ λ i → [ +-comm x 0 (~ i) ])
               λ y → (λ i → [ (+-comm x (suc (n + y)) ∙ sym (+-assoc (suc n) y x)) i ]) ∙∙ LUnit _ ∙∙ λ i → [ +-comm y x i ])
    (funExt (elimfinInt (λ _ → isOfHLevelPath 2 is-set _ _) LUnit (isProp→PathP (λ _ → is-set _ _) _ _) λ _ → isProp→PathP (λ _ → is-set _ _) _ _ ))
    λ x → funExt (elimfinInt (λ _ → isOfHLevelPath 2 is-set _ _) (λ y → (λ i → [ +-assoc (suc n) x y (~ i) ]) ∙ LUnit (x + y)) (isProp→PathP (λ _ → is-set _ _ ) _ _) λ _ → isProp→PathP (λ _ → is-set _ _) _ _)

test : (n : ℕ) → finInt n → finInt n
test zero x = [ 0 ]
test (suc n) = elimfinInt (λ _ → is-set) (λ m → [ m + 1 ]) (LUnit 1) λ x → (λ i → [ +-assoc (suc n) x 1 (~ i) ]) ∙ LUnit (x + 1)

isEqt : (n : ℕ) → Iso (finInt (suc n)) (finInt (suc n)) -- isEquiv (test (suc n))
Iso.fun (isEqt n) = test (suc n)
Iso.inv (isEqt n) =
  elimfinInt (λ _ → is-set) (λ m → [ m + n ]) (LUnit n) λ x → (λ i → [ +-assoc (suc n) x n (~ i) ]) ∙ LUnit (x + n)
Iso.rightInv (isEqt n) =
  elimfinInt (λ _ → isOfHLevelPath 2 is-set _ _)
             (λ m → (λ i → [ (sym (+-assoc m n 1) ∙ +-comm m (n + 1) ∙ (λ j → +-comm n 1 j + m)) i ]) ∙ LUnit m)
             (toPathP (is-set _ _ _ _))
             λ _ → toPathP (is-set _ _ _ _)
Iso.leftInv (isEqt n) =
  elimfinInt (λ _ → isOfHLevelPath 2 is-set _ _)
             (λ m → (λ i → [ (sym (+-assoc m 1 n) ∙ +-comm m (1 + n)) i ]) ∙ LUnit m)
             (toPathP (is-set _ _ _ _))
             λ _ → toPathP (is-set _ _ _ _)


module _ where
  path : (n : ℕ) → Path (TypeOfHLevel ℓ-zero 2) (finInt (suc n) , is-set) (finInt (suc n) , is-set)
  path n = Σ≡Prop (λ _ → isPropIsSet) (ua (isoToEquiv (isEqt n)))

  path_^ : (n m : ℕ) → finInt (suc n) ≡ (finInt (suc n))
  path n ^ zero = refl
  path n ^ (suc zero) = cong fst (path n)
  path n ^ (suc (suc m)) = path n ^ (suc m) ∙ cong fst (path n)

  F : (n : ℕ) → (m : S¹) → TypeOfHLevel ℓ-zero 2
  F n base = finInt (suc n) , is-set
  F n (loop i) = path n i

  tsa : (n : ℕ) (m : ℕ) → cong fst (cong (F n) (intLoop (pos (suc m)))) ≡ path n ^ (suc m)
  tsa n zero i = cong fst (cong (F n) (lUnit loop (~ i)))
  tsa n (suc m) i = tsa n m i ∙ path n ^ 1

  tsa' : (n : ℕ) (m : ℕ) → cong fst (cong (F n) (intLoop (pos m))) ≡ path n ^ m
  tsa' n zero = refl
  tsa' n (suc m) = tsa n m

  

  isEqt_^ : (n m : ℕ) → finInt (suc n) ≃ finInt (suc n)
  isEqt n ^ zero = idEquiv _
  isEqt n ^ (suc zero) = isoToEquiv (isEqt n)
  isEqt n ^ (suc (suc m)) = compEquiv (isEqt n ^ (suc m)) (isoToEquiv (isEqt n))


  isEqt-lem : (n m : ℕ) (x : _) → fst (isEqt n ^ m) [ x ] ≡ [ x + m ]
  isEqt-lem n zero x i = [ +-comm 0 x i ]
  isEqt-lem n (suc zero) x = refl
  isEqt-lem n (suc (suc m)) x =
      cong (fst (isoToEquiv (isEqt n))) (isEqt-lem n (suc m) x)
    ∙∙ (λ i → [ +-assoc x (suc m) 1 (~ i) ])
    ∙∙ λ i → [ x + suc (+-comm m 1 i) ]

  isEqt-lem2 : (n : ℕ) → isEqt n ^ (suc n) ≡ idEquiv _
  isEqt-lem2 n = Σ≡Prop (λ _ → isPropIsEquiv _)
                        (funExt (elimfinInt (λ _ → isOfHLevelPath 2 is-set _ _)
                                (λ m → isEqt-lem n (suc n) m ∙∙ (λ i → [ +-comm m (suc n) i ]) ∙∙ LUnit _)
                                (isProp→PathP (λ _ → is-set _ _) _ _)
                                λ _ → isProp→PathP (λ _ → is-set _ _) _ _))


  tsb : (n m : ℕ) → path n ^ (suc m) ≡ ua (isEqt n ^ (suc m))
  tsb n zero = refl
  tsb n (suc m) = (λ i → tsb n m i ∙ (λ i → fst (path n i))) ∙ sym (uaCompEquiv _ _)

  path-lem : (n : ℕ) → path n ^ (suc n) ≡ refl
  path-lem n = tsb n n ∙∙ (λ i → ua (isEqt-lem2 n i)) ∙∙ uaIdEquiv

  eqProp : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} → ((x : A) → isProp (B x)) → {x y : Σ A B} {p q : x ≡ y} → cong fst p ≡ cong fst q → p ≡ q 
  fst (eqProp isProp {x = x} {y = y} {p = p} {q = q} fstp i j) = fstp i j
  snd (eqProp {B = B} isProp {x = x} {y = y} {p = p} {q = q} fstp i j) =
    hcomp (λ k → λ { (i = i0) → isProp (fst (p j)) (snd (p j)) (snd (p j)) k
                   ; (i = i1) → isProp (fst (q j)) (transport (λ r → B (fstp r j)) (snd (p j))) (snd (q j)) k
                   ; (j = i0) → isProp (fst x) (transp (λ r → B (fst x)) (~ i) (snd x)) (snd x) k 
                   ; (j = i1) → isProp (fst y) (transp (λ r → B (fst y)) (~ i) (snd y)) (snd y) k })
          (transp (λ r → B (fstp (i ∧ r) j)) (~ i) (snd (p j)) )

  hm : (n : ℕ) → cong (F n) (intLoop (pos (suc n))) ≡ refl
  hm n = eqProp (λ _ → isPropIsSet) (tsa n n ∙ path-lem n)

CODE : (n : ℕ) → S1-mod (suc n) → Type₀
CODE n x = fst (helper x)
  where


  helper : S1-mod (suc n) → TypeOfHLevel ℓ-zero 2
  helper =
    S1-mod-elim (λ _ → isOfHLevelTypeOfHLevel 2)
                (F n)
                λ i j → hm n i j

decode' : (n : ℕ) (x : S1-mod (suc n)) → CODE n x → [ base ] ≡ x
decode' n = S1-mod-elim (λ _ → isGroupoidΠ λ _ → isOfHLevelPath 3 isGr _ _) tehe (toPathP (isOfHLevelPath' 1 (isSetΠ (λ _ → isGr _ _)) _ _ _ _))
  where

  intLem : (a b : ℕ) → (pos a) +Z (pos b) ≡ pos (a + b)
  intLem a zero = cong pos (sym (+-comm a 0))
  intLem a (suc b) = cong sucInt (intLem a b) ∙ cong pos (cong suc (+-comm a b) ∙ sym (+-comm a (suc b)))

  F' : CODE n [ base ] → [ base ] ≡ [ base ]
  F' = elimfinInt (λ _ → isGr _ _) (λ m i → [ intLoop (pos m) i ])
                 coher
                 λ x → (λ j i → [ intLoop (intLem (suc n) x (~ j)) i ])
                    ∙∙ (λ j i → [ intLoop-hom (pos (suc n)) (pos x) (~ j) i ])
                    ∙∙ congFunct [_] (intLoop (pos (suc n))) (intLoop (pos x))
                    ∙∙ (λ i → coher i ∙ λ j → [ intLoop (pos x) j ])
                    ∙∙ sym (lUnit _)

  tehe : _
  tehe base = F'
  tehe (loop i) = toPathP (funExt help) i
    where
    help : (x : _) → transport (λ i → CODE n [ loop i ] → Path (S1-mod (suc n)) [ base ] [ loop i ]) F' x ≡ F' x
    help =
      elimfinInt (λ _ → isOfHLevelPath 2 (isGr _ _) _ _)
                 (λ m → (λ i → transport (λ i → Path (S1-mod (suc n)) [ base ] [ loop i ]) (F' (transportRefl [ m + n ] i)))
                       ∙∙ (λ j → transp (λ i → Path (S1-mod (suc n)) [ base ] [ loop (i ∨ j) ]) j (compPath-filler (λ j → [ intLoop (pos (m + n)) j ]) (λ z → [ loop (z ∧ j) ]) j))
                       ∙∙ (λ i → (λ j → [ intLoop (intLem m n (~ i)) j ]) ∙ (λ j → [ loop j ])) -- sym (congFunct [_] (intLoop (pos (m + n))) loop)
                       ∙∙ (λ i → (λ j → [ intLoop-hom (pos m) (pos n) (~ i) j ]) ∙ (λ j → [ loop j ])) -- (λ i j → [ intLoop (pos (suc (m + n))) j ] )
                       ∙∙ (λ i → congFunct [_] (intLoop (pos m)) (intLoop (pos n)) i ∙ (λ j → [ loop j ]))
                       ∙∙ sym (assoc _ _ _)
                       ∙∙ (λ i → (λ j → [ intLoop (pos m) j ]) ∙ congFunct [_] (intLoop (pos n)) (lUnit loop i) (~ i))
                       ∙∙ (λ i → (λ j → [ intLoop (pos m) j ]) ∙ λ j → [ intLoop-hom (pos n) 1 i j ])
                       ∙∙ (λ i → (λ j → [ intLoop (pos m) j ]) ∙ λ j → [ intLoop (intLem n 1 i) j ])
                       ∙∙ (λ i → (λ j → [ intLoop (pos m) j ]) ∙ λ j → [ intLoop (pos (+-comm n 1 i)) j ])
                       ∙∙ (λ i → (λ j → [ intLoop (pos m) j ]) ∙ coher i)
                        ∙ sym (rUnit (λ j → [ intLoop (pos m) j ])))
                 (toPathP (isOfHLevelPath' 1 (isGr _ _) _ _ _ _))
                 λ _ → toPathP (isOfHLevelPath' 1 (isGr _ _) _ _ _ _)
    

encode' : (n : ℕ) (x : S1-mod (suc n)) → [ base ] ≡ x → CODE n x
encode' n x p = subst (CODE n) p [ 0 ]

encode-decode : (n : ℕ) (x : S1-mod (suc n)) (p : [ base ] ≡ x) → decode' n x (encode' n x p) ≡ p
encode-decode n x = J (λ x p → decode' n x (encode' n x p) ≡ p) refl

tr-help : (n m : ℕ) → transport (path n ^ m) [ 0 ] ≡ [ m ]
tr-help n zero = refl
tr-help n (suc zero) = refl
tr-help n (suc (suc m)) =
     substComposite (λ x → x) (path n ^ (suc m)) (path n ^ 1) [ 0 ]
  ∙∙ cong (subst (λ x → x) (λ i → fst (path n i))) (tr-help n (suc m))
  ∙∙ λ i → [ suc (+-comm m 1 i) ]

decode-encode : (n : ℕ) (a : CODE n [ base ]) → encode' n [ base ] (decode' n [ base ] a) ≡ a
decode-encode n =
  elimfinInt (λ _ → isOfHLevelPath 2 is-set _ _)
             (λ m → (λ i → transport (tsa' n m i) [ 0 ])
                   ∙ tr-help n m)
             (isProp→PathP (λ _ → is-set _ _) _ _)
             λ _ → isProp→PathP (λ _ → is-set _ _) _ _

finalIso : (n : ℕ) → Iso (Path (S1-mod (suc n)) [ base ] [ base ]) (finInt (suc n))
Iso.fun (finalIso n) = encode' n [ base ]
Iso.inv (finalIso n) = decode' n [ base ]
Iso.rightInv (finalIso n) = decode-encode n
Iso.leftInv (finalIso n) = encode-decode n [ base ]
-}
-}
