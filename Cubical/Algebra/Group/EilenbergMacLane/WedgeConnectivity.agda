{-# OPTIONS --cubical --no-import-sorts --safe --experimental-lossy-unification #-}

module Cubical.Algebra.Group.EilenbergMacLane.WedgeConnectivity where

open import Cubical.Algebra.Group.EilenbergMacLane.Base
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.GroupoidLaws renaming (assoc to ∙assoc)
open import Cubical.Foundations.Path
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Transport

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties
open import Cubical.Homotopy.Connected
open import Cubical.HITs.Truncation as Trunc renaming (rec to trRec; elim to trElim)
open import Cubical.HITs.EilenbergMacLane1
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Data.Empty
  renaming (rec to ⊥-rec)
open import Cubical.HITs.Truncation
  renaming (elim to trElim ; rec to trRec ; rec2 to trRec2)
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.HITs.Susp
open import Cubical.Functions.Morphism
open import Cubical.Foundations.Path

private
  variable ℓ ℓ' ℓ'' : Level

  wedgeConFun' : (G : AbGroup ℓ) (H : AbGroup ℓ') (n : ℕ)
              → {A : EM-raw G (suc n) → EM-raw H (suc zero) → Type ℓ''}
              → ((x : _) (y : _) → isOfHLevel (suc n + suc zero) (A x y))
              → (f : (x : _) → A ptS x)
              → (g : (x : _) → A x ptS)
              → f ptS ≡ g ptS
              → (x : _) (y : _) → A x y
  wedgeConFun'ᵣ : (G : AbGroup ℓ) (H : AbGroup ℓ') (n : ℕ)
              → {A : EM-raw G (suc n) → EM-raw H (suc zero) → Type ℓ''}
              → (hLev : ((x : _) (y : _) → isOfHLevel (suc n + suc zero) (A x y)))
              → (f : (x : _) → A ptS x)
              → (g : (x : _) → A x ptS)
              → (p : f ptS ≡ g ptS)
              → (x : _) → wedgeConFun' G H n hLev f g p x ptS ≡ g x
  wedgeConFun' G H zero {A = A} hlev f g p =
    elimSet _ (λ _ → isSetΠ λ _ → hlev _ _) f k
    where
    I→A : (x : fst G) → (i : I) → A (emloop x i) embase
    I→A x i =
      hcomp (λ k → λ {(i = i0) → p (~ k) ; (i = i1) → p (~ k)})
            (g (emloop x i))

    SquareP2 : (x : _) (z : _)
      → SquareP (λ i j → A (emloop x i) (emloop z j))
          (cong f (emloop z)) (cong f (emloop z))
          (λ i → I→A x i) λ i → I→A x i
    SquareP2 x z =
      toPathP (isOfHLevelPathP' 1 (λ _ _ → hlev _ _ _ _) _ _ _ _)

    CubeP2 : (x : _) (g h : _)
      → PathP (λ k → PathP (λ j → PathP (λ i → A (emloop x i) (emcomp g h j k))
              (f (emcomp g h j k)) (f (emcomp g h j k)))
              (λ i → SquareP2 x g i k) λ i → SquareP2 x ((snd (AbGroup→Group H) GroupStr.· g) h) i k)
              (λ _ i → I→A x i) λ j i → SquareP2 x h i j
    CubeP2 x g h = toPathP (isOfHLevelPathP' 1 (isOfHLevelPathP 2 (hlev _ _) _ _) _ _ _ _)

    k : (x : _) → PathP (λ i → (y : EM₁ (AbGroup→Group H)) → A (emloop x i) y)  f f
    k x i embase = I→A x i
    k x i (emloop z j) = SquareP2 x z i j
    k x i (emcomp g h j k) = CubeP2 x g h k j i
    k x i (emsquash y z p q r s j k' l) = mega i j k' l
      where
      mega :
        PathP (λ i →
          PathP (λ j →
            PathP (λ k' →
              PathP (λ l → A (emloop x i) (emsquash y z p q r s j k' l))
                    (k x i y)
                    (k x i z))
                   (λ l → k x i (p l))
                   λ l → k x i (q l))
                 (λ k' l → k x i (r k' l))
                 λ k' l → k x i (s k' l))
               (λ j k l → f (emsquash y z p q r s j k l))
               λ j k l → f (emsquash y z p q r s j k l)
      mega =
        toPathP (isOfHLevelPathP' 1
          (isOfHLevelPathP 2 (isOfHLevelPathP 2 (hlev _ _) _ _) _ _) _ _ _ _)
  wedgeConFun' G H (suc n) {A = A} hLev f g p north y = f y
  wedgeConFun' G H (suc n) {A = A} hLev f g p south y = subst (λ x → A x y) (merid ptS) (f y)
  wedgeConFun' G H (suc n) {A = A} hLev f g p (merid a i) y = mainₗ a y i
    module _ where
    llem₁ : g south ≡ subst (λ x₁ → A x₁ ptS) (merid ptS) (f ptS)
    llem₁ = (λ i → transp (λ j → A (merid ptS (j ∨ ~ i)) ptS) (~ i) (g (merid ptS (~ i))))
          ∙ cong (subst (λ x₁ → A x₁ ptS) (merid ptS)) (sym p)

    llem₂' :
      Square
       (λ i → transp (λ j → A (merid ptS (i ∨ j)) ptS) i (g (merid ptS i))) refl
       (cong (subst (λ x → A x ptS) (merid ptS)) (sym p)) llem₁
    llem₂' i j =
      hcomp (λ k → λ { (i = i0) → transp (λ z → A (merid ptS (j ∨ z)) ptS) j
                                            (g (merid ptS j))
                      ; (i = i1) → subst (λ x₁ → A x₁ ptS) (merid ptS) (p (~ k))
                      ; (j = i0) → (subst (λ x → A x ptS) (merid ptS)) (p (~ k ∨ ~ i))})
            (transp (λ k → A (merid ptS (k ∨ ~ i ∧ j)) ptS) (~ i ∧ j) (g (merid ptS (~ i ∧ j))))

    llem₂ : (λ i₁ → transp (λ j → A (merid ptS (i₁ ∧ j)) ptS) (~ i₁) (f ptS))
        ≡ (λ i₁ →  hcomp (λ k → λ { (i₁ = i0) → p (~ k) ; (i₁ = i1) → llem₁ k })
                          (g (merid ptS i₁)))
    llem₂ i j =
      hcomp (λ k → λ { (i = i0) → transp (λ j₁ → A (merid ptS (j ∧ j₁)) ptS) (~ j) (p (~ k))
                      ; (j = i0) → p (~ k)
                      ; (j = i1) → llem₂' k i})
        (transp (λ k → A (merid ptS ((i ∨ k) ∧ j)) ptS) (i ∨ ~ j) (g (merid ptS (i ∧ j))))

    mainₗ : (a : _) (y : _)
      → PathP (λ i → A (merid a i) y) (f y) (subst (λ x → A x y) (merid ptS) (f y))
    mainₗ =
      wedgeConFun' G H n
        (λ _ _ → isOfHLevelPathP' (suc (n + 1)) (hLev _ _) _ _)
        (λ x i → transp (λ j → A (merid ptS (i ∧ j)) x) (~ i) (f x))
        (λ x i → hcomp (λ k → λ { (i = i0) → p (~ k)
                                 ; (i = i1) → llem₁ k})
                        (g (merid x i)))
        llem₂

    mainP : (y : _)
      → mainₗ y ptS
      ≡ λ i → hcomp (λ k → λ { (i = i0) → p (~ k)
                               ; (i = i1) → llem₁ k})
                      (g (merid y i))
    mainP y = 
      wedgeConFun'ᵣ G H n
        (λ _ _ → isOfHLevelPathP' (suc (n + 1)) (hLev _ _) _ _)
        (λ x i → transp (λ j → A (merid ptS (i ∧ j)) x) (~ i) (f x))
        (λ x i → hcomp (λ k → λ { (i = i0) → p (~ k)
                                 ; (i = i1) → llem₁ k})
                        (g (merid x i)))
        llem₂ y
  wedgeConFun'ᵣ G H zero {A = A} hLev f g p =
    elimProp _ (λ _ → hLev _ _ _ _) p
  wedgeConFun'ᵣ G H (suc n) {A = A} hLev f g p north = p
  wedgeConFun'ᵣ G H (suc n) {A = A} hLev f g p south = sym (llem₁ G H n hLev f g p ptS i0 ptS)
  wedgeConFun'ᵣ G H (suc n) {A = A} hLev f g p (merid a i) k = P k i
    where
    lem : _
    lem i j =
      hcomp (λ k → λ { (i = i1) → g (merid a j)
                      ; (j = i0) → p (i ∨ ~ k)
                      ; (j = i1) → llem₁ G H n hLev f g p ptS i0 ptS (~ i ∧ k)})
        (g (merid a j))

    P : PathP (λ k → PathP (λ i → A (merid a i) ptS)
              (p k) (llem₁ G H n hLev f g p ptS i0 ptS (~ k)))
              (λ i → mainₗ G H n hLev f g p a i ptS a ptS i) λ i → g (merid a i)
    P = mainP G H n hLev f g p a i0 ptS a ◁ lem

private
  wedgeConFun : (G : AbGroup ℓ) (H : AbGroup ℓ')
                 (k n m : ℕ) → (n + m ≡ k) → {A : EM-raw G (suc n) → EM-raw H (suc m) → Type ℓ''}
              → ((x : _) (y : _) → isOfHLevel (suc n + suc m) (A x y))
              → (f : (x : _) → A ptS x)
              → (g : (x : _) → A x ptS)
              → f ptS ≡ g ptS
              → (x : _) (y : _) → A x y
  wedgeconLeft : (G : AbGroup ℓ) (H : AbGroup ℓ') (k n m : ℕ) (P : n + m ≡ k)
                 {A : EM-raw G (suc n) → EM-raw H (suc m) → Type ℓ''}
              → (hLev : ((x : _) (y : _) → isOfHLevel (suc n + suc m) (A x y)))
              → (f : (x : _) → A ptS x)
              → (g : (x : _) → A x ptS)
              → (p : f ptS ≡ g ptS)
               → (x : _) → wedgeConFun G H k n m P hLev f g p ptS x ≡ f x
  wedgeconRight : (G : AbGroup ℓ) (H : AbGroup ℓ') (k n m : ℕ) (P : n + m ≡ k) {A : EM-raw G (suc n) → EM-raw H (suc m) → Type ℓ''}
              → (hLev : ((x : _) (y : _) → isOfHLevel (suc n + suc m) (A x y)))
              → (f : (x : _) → A ptS x)
              → (g : (x : _) → A x ptS)
              → (p : f ptS ≡ g ptS)
               → (x : _) → wedgeConFun G H k n m P hLev f g p x ptS ≡ g x
  wedgeConFun G H k n zero P {A = A} hLev f g p = wedgeConFun' G H n hLev f g p
  wedgeConFun G H k zero (suc m) P {A = A} hLev f g p x y =
    wedgeConFun' H G (suc m) {A = λ x y → A y x}
      (λ x y → subst (λ n → isOfHLevel (2 + n) (A y x)) (+-comm 1 m) (hLev y x))
      g f (sym p) y x
  wedgeConFun G H l (suc n) (suc m) P {A = A} hlev f g p north y = f y
  wedgeConFun G H l (suc n) (suc m) P {A = A} hlev f g p south y = subst (λ x → A x y) (merid ptS) (f y)
  wedgeConFun G H zero (suc n) (suc m) P {A = A} hlev f g p (merid a i) y = main** i
    module _ where
    main** : PathP (λ i → A (merid a i) y) (f y) (subst (λ x → A x y) (merid ptS) (f y))
    main** = ⊥-rec (snotz P)
  wedgeConFun G H (suc l) (suc n) (suc m) P {A = A} hlev f g p (merid a i) y = main* a y i
    module _ where
    lem₁* : g south ≡ (subst (λ x → A x ptS) (merid ptS) (f ptS))
    lem₁* = ((λ i → transp (λ j → A (merid ptS (~ i ∨ j)) ptS) (~ i) (g (merid ptS (~ i)))))
          ∙ cong (subst (λ x → A x ptS) (merid ptS)) (sym p)

    lem₁'* :
      Square
        (λ i → transp (λ j → A (merid ptS (~ i ∨ j)) ptS) (~ i) (g (merid ptS (~ i))))
        (refl {x = subst (λ x → A x ptS) (merid ptS) (f ptS)})
        lem₁*
        ((cong (transport (λ z → A (merid ptS z) ptS)) (sym p)))
    lem₁'* i j =
      hcomp (λ k → λ { (i = i0) → transp (λ j₁ → A (merid ptS (~ j ∨ j₁)) ptS) (~ j) (g (merid ptS (~ j)))
                      ; (i = i1) → subst (λ x → A x ptS) (merid ptS) (p (~ k))
                      ; (j = i1) → cong (transport (λ z → A (merid ptS z) ptS)) (sym p) (i ∧ k)})
             (transp (λ j₁ → A (merid ptS ((~ j ∧ ~ i) ∨ j₁)) ptS) (~ j ∧ ~ i) (g (merid ptS (~ j ∧ ~ i))))


    lem₂* : (λ i₁ → transp (λ j → A (merid ptS (j ∧ i₁)) ptS) (~ i₁) (f ptS))
        ≡ (λ i₁ → hcomp (λ k → λ { (i₁ = i0) → p (~ k) ; (i₁ = i1) → lem₁* k })
           (g (merid ptS i₁)))
    lem₂* i j =
      hcomp (λ k → λ { (i = i0) → transp (λ z → A (merid ptS (z ∧ j)) ptS) (~ j) (p (~ k))
                      ; (j = i0) → p (~ k)
                      ; (j = i1) → lem₁'* k (~ i)})
            (transp (λ z → A (merid ptS ((i ∨ z) ∧ j)) ptS) (i ∨ ~ j) (g (merid ptS (i ∧ j))))

    main* : (a : _) (y : _) → PathP (λ i → A (merid a i) y) (f y) (subst (λ x → A x y) (merid ptS) (f y))
    main* =
      wedgeConFun G H l n (suc m) (cong predℕ P)
        (λ _ _ → isOfHLevelPathP' (suc (n + (suc (suc m)))) (hlev _ _) _ _)
        (λ x i → transp (λ j → A (merid ptS (j ∧ i)) x) (~ i) (f x))
        (λ y i → hcomp (λ k → λ { (i = i0) → p (~ k)
                                  ; (i = i1) → lem₁* k})
                       (g (merid y i)))
        lem₂*

    mainR : (x : _) → main* x ptS
                    ≡ λ i → hcomp (λ k → λ { (i = i0) → p (~ k)
                                             ; (i = i1) → lem₁* k})
                                               (g (merid x i))
    mainR x =
      wedgeconRight G H l n (suc m) (cong predℕ P)
        (λ _ _ → isOfHLevelPathP' (suc (n + (suc (suc m)))) (hlev _ _) _ _)
        (λ x i → transp (λ j → A (merid ptS (j ∧ i)) x) (~ i) (f x))
        (λ y i → hcomp (λ k → λ { (i = i0) → p (~ k)
                                  ; (i = i1) → lem₁* k})
                       (g (merid y i)))
        lem₂* x
  wedgeconLeft G H k zero zero P {A = A} hLev f g p _ = refl
  wedgeconLeft G H k (suc n) zero P {A = A} hLev f g p _ = refl
  wedgeconLeft G H k zero (suc m) P {A = A} hLev f g p x =
    wedgeConFun'ᵣ H G (suc m)
        (λ x₁ y →
           subst (λ n → (x₂ y₁ : A y x₁) → isOfHLevel (suc n) (x₂ ≡ y₁))
           (+-comm 1 m) (hLev y x₁))
        g f (λ i → p (~ i)) x
  wedgeconLeft G H k (suc n) (suc m) P {A = A} hLev f g p _ = refl
  wedgeconRight G H k n zero P {A = A} hLev f g p = wedgeConFun'ᵣ G H n hLev f g p
  wedgeconRight G H k zero (suc m) P {A = A} hLev f g p _ = refl
  wedgeconRight G H zero (suc n) (suc m) P {A = A} hLev f g p x = ⊥-rec (snotz P)
  wedgeconRight G H l (suc n) (suc m) P {A = A} hLev f g p north = p
  wedgeconRight G H l (suc n) (suc m) P {A = A} hLev f g p south =
    sym (lem₁* G H _ n m refl hLev f g p ptS i0 ptS)
  wedgeconRight G H (suc l) (suc n) (suc m) P {A = A} hLev f g p (merid a i) k =
    help k i
    where
    lem : _
    lem i j =
      hcomp (λ k → λ { (i = i1) → g (merid a j)
                      ; (j = i0) → p (i ∨ ~ k)
                      ; (j = i1) → lem₁* G H l n m P hLev f g p ptS i0 ptS (~ i ∧ k)})
            (g (merid a j))

    help : PathP (λ k → PathP (λ i → A (merid a i) ptS)
                 (p k) (lem₁* G H l n m P hLev f g p ptS i0 ptS (~ k)))
                 (λ i → main* G H l n m P hLev f g p a i north a north i) (cong g (merid a))
    help = mainR G H l n m P hLev f g p a i0 ptS a ◁ lem

module wedgeConEM (G : AbGroup ℓ) (H : AbGroup ℓ') (n m : ℕ) {A : EM-raw G (suc n) → EM-raw H (suc m) → Type ℓ''}
                  (hLev : ((x : _) (y : _) → isOfHLevel (suc n + suc m) (A x y)))
                  (f : (x : _) → A ptS x)
                  (g : (x : _) → A x ptS)
                  (p : f ptS ≡ g ptS) where
  fun : (x : EM-raw G (suc n)) (y : EM-raw H (suc m)) → A x y
  fun = wedgeConFun G H (n + m) n m refl hLev f g p

  left : (x : EM-raw H (suc m)) → fun ptS x ≡ f x
  left = wedgeconLeft G H (n + m) n m refl hLev f g p

  right : (x : EM-raw G (suc n)) → fun x ptS ≡ g x
  right = wedgeconRight G H (n + m) n m refl hLev f g p
