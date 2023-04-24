{-# OPTIONS --safe --lossy-unification #-}

module Cubical.Homotopy.EilenbergMacLane.WedgeConnectivity where

open import Cubical.Homotopy.EilenbergMacLane.Base
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Algebra.Group.Base
open import Cubical.HITs.Truncation as Trunc renaming (rec to trRec; elim to trElim)
open import Cubical.HITs.EilenbergMacLane1
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Data.Empty
  renaming (rec to ⊥-rec)
open import Cubical.Data.Nat
open import Cubical.HITs.Susp

{-
This file contains a direct construction of the wedge connectivity lemma for EM
spaces. This direct construction gives nicer reductions and computes better than
the more general theorem. The main results are in the module "wedgeConEM" at the
end of this file.
-}

private
  variable ℓ ℓ' ℓ'' : Level

-- One of the base cases, stated separately to avoid termination issues
  wedgeConFun' : (G : AbGroup ℓ) (H : AbGroup ℓ') (n : ℕ)
              → {A : EM-raw G (suc n) → EM-raw H (suc zero) → Type ℓ''}
              → ((x : _) (y : _) → isOfHLevel (suc n + suc zero) (A x y))
              → (f : (x : _) → A ptEM-raw x)
              → (g : (x : _) → A x ptEM-raw)
              → f ptEM-raw ≡ g ptEM-raw
              → (x : _) (y : _) → A x y
  wedgeConFun'ᵣ : (G : AbGroup ℓ) (H : AbGroup ℓ') (n : ℕ)
              → {A : EM-raw G (suc n) → EM-raw H (suc zero) → Type ℓ''}
              → (hLev : ((x : _) (y : _) → isOfHLevel (suc n + suc zero) (A x y)))
              → (f : (x : _) → A ptEM-raw x)
              → (g : (x : _) → A x ptEM-raw)
              → (p : f ptEM-raw ≡ g ptEM-raw)
              → (x : _) → wedgeConFun' G H n hLev f g p x ptEM-raw ≡ g x
  wedgeConFun' G H zero {A = A} hlev f g p =
    elimSet _ (λ _ → isSetΠ λ _ → hlev _ _) f mainpath
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

    mainpath : (x : _) → PathP (λ i → (y : EM₁ (AbGroup→Group H)) → A (emloop x i) y) f f
    mainpath x i embase = I→A x i
    mainpath x i (emloop z j) = SquareP2 x z i j
    mainpath x i (emcomp g h j k) = CubeP2 x g h k j i
    mainpath x i (emsquash y z p q r s j k' l) = mega i j k' l
      where
      mega :
        PathP (λ i → PathP (λ j → PathP (λ k →
          PathP (λ l → A (emloop x i) (emsquash y z p q r s j k l))
                    (mainpath x i y)
                    (mainpath x i z))
                    (λ l → mainpath x i (p l))
                     λ l → mainpath x i (q l))
                    (λ k l → mainpath x i (r k l))
                     λ k l → mainpath x i (s k l))
                    (λ j mainpath l → f (emsquash y z p q r s j mainpath l))
                     λ j mainpath l → f (emsquash y z p q r s j mainpath l)
      mega =
        toPathP (isOfHLevelPathP' 1
          (isOfHLevelPathP 2 (isOfHLevelPathP 2 (hlev _ _) _ _) _ _) _ _ _ _)
  wedgeConFun' G H (suc n) {A = A} hLev f g p north y = f y
  wedgeConFun' G H (suc n) {A = A} hLev f g p south y = subst (λ x → A x y) (merid ptEM-raw) (f y)
  wedgeConFun' G H (suc n) {A = A} hLev f g p (merid a i) y = mainₗ a y i
    module _ where
    llem₁ : g south ≡ subst (λ x₁ → A x₁ ptEM-raw) (merid ptEM-raw) (f ptEM-raw)
    llem₁ = (λ i → transp (λ j → A (merid ptEM-raw (j ∨ ~ i)) ptEM-raw) (~ i) (g (merid ptEM-raw (~ i))))
          ∙ cong (subst (λ x₁ → A x₁ ptEM-raw) (merid ptEM-raw)) (sym p)

    llem₁' :
      Square
       (λ i → transp (λ j → A (merid ptEM-raw (i ∨ j)) ptEM-raw) i (g (merid ptEM-raw i))) refl
       (cong (subst (λ x → A x ptEM-raw) (merid ptEM-raw)) (sym p)) llem₁
    llem₁' i j =
      hcomp (λ k → λ { (i = i0) → transp (λ z → A (merid ptEM-raw (j ∨ z)) ptEM-raw) j
                                            (g (merid ptEM-raw j))
                      ; (i = i1) → subst (λ x₁ → A x₁ ptEM-raw) (merid ptEM-raw) (p (~ k))
                      ; (j = i0) → (subst (λ x → A x ptEM-raw) (merid ptEM-raw)) (p (~ k ∨ ~ i))})
            (transp (λ k → A (merid ptEM-raw (k ∨ ~ i ∧ j)) ptEM-raw) (~ i ∧ j) (g (merid ptEM-raw (~ i ∧ j))))

    llem₂ : (λ i₁ → transp (λ j → A (merid ptEM-raw (i₁ ∧ j)) ptEM-raw) (~ i₁) (f ptEM-raw))
        ≡ (λ i₁ →  hcomp (λ k → λ { (i₁ = i0) → p (~ k) ; (i₁ = i1) → llem₁ k })
                          (g (merid ptEM-raw i₁)))
    llem₂ i j =
      hcomp (λ k → λ { (i = i0) → transp (λ j₁ → A (merid ptEM-raw (j ∧ j₁)) ptEM-raw) (~ j) (p (~ k))
                      ; (j = i0) → p (~ k)
                      ; (j = i1) → llem₁' k i})
        (transp (λ k → A (merid ptEM-raw ((i ∨ k) ∧ j)) ptEM-raw) (i ∨ ~ j) (g (merid ptEM-raw (i ∧ j))))

    mainₗ : (a : _) (y : _)
      → PathP (λ i → A (merid a i) y) (f y) (subst (λ x → A x y) (merid ptEM-raw) (f y))
    mainₗ =
      wedgeConFun' G H n
        (λ _ _ → isOfHLevelPathP' (suc (n + 1)) (hLev _ _) _ _)
        (λ x i → transp (λ j → A (merid ptEM-raw (i ∧ j)) x) (~ i) (f x))
        (λ x i → hcomp (λ k → λ { (i = i0) → p (~ k)
                                 ; (i = i1) → llem₁ k})
                        (g (merid x i)))
        llem₂

    mainP : (y : _)
      → mainₗ y ptEM-raw
      ≡ λ i → hcomp (λ k → λ { (i = i0) → p (~ k)
                               ; (i = i1) → llem₁ k})
                      (g (merid y i))
    mainP y =
      wedgeConFun'ᵣ G H n
        (λ _ _ → isOfHLevelPathP' (suc (n + 1)) (hLev _ _) _ _)
        (λ x i → transp (λ j → A (merid ptEM-raw (i ∧ j)) x) (~ i) (f x))
        (λ x i → hcomp (λ k → λ { (i = i0) → p (~ k)
                                 ; (i = i1) → llem₁ k})
                        (g (merid x i)))
        llem₂ y
  wedgeConFun'ᵣ G H zero {A = A} hLev f g p =
    elimProp _ (λ _ → hLev _ _ _ _) p
  wedgeConFun'ᵣ G H (suc n) {A = A} hLev f g p north = p
  wedgeConFun'ᵣ G H (suc n) {A = A} hLev f g p south = sym (llem₁ G H n hLev f g p ptEM-raw i0 ptEM-raw)
  wedgeConFun'ᵣ G H (suc n) {A = A} hLev f g p (merid a i) k = P k i
    where
    llem : _
    llem i j =
      hcomp (λ k → λ { (i = i1) → g (merid a j)
                      ; (j = i0) → p (i ∨ ~ k)
                      ; (j = i1) → llem₁ G H n hLev f g p ptEM-raw i0 ptEM-raw (~ i ∧ k)})
        (g (merid a j))

    P : PathP (λ k → PathP (λ i → A (merid a i) ptEM-raw)
              (p k) (llem₁ G H n hLev f g p ptEM-raw i0 ptEM-raw (~ k)))
              (λ i → mainₗ G H n hLev f g p a i ptEM-raw a ptEM-raw i) λ i → g (merid a i)
    P = mainP G H n hLev f g p a i0 ptEM-raw a ◁ llem

-- Here, the actual stuff gets proved. However an additional natural number is stuck into the context
-- to convince the termination checker
private
  wedgeConFun : (G : AbGroup ℓ) (H : AbGroup ℓ')
                 (k n m : ℕ) → (n + m ≡ k) → {A : EM-raw G (suc n) → EM-raw H (suc m) → Type ℓ''}
              → ((x : _) (y : _) → isOfHLevel (suc n + suc m) (A x y))
              → (f : (x : _) → A ptEM-raw x)
              → (g : (x : _) → A x ptEM-raw)
              → f ptEM-raw ≡ g ptEM-raw
              → (x : _) (y : _) → A x y
  wedgeconLeft : (G : AbGroup ℓ) (H : AbGroup ℓ') (k n m : ℕ) (P : n + m ≡ k)
                 {A : EM-raw G (suc n) → EM-raw H (suc m) → Type ℓ''}
              → (hLev : ((x : _) (y : _) → isOfHLevel (suc n + suc m) (A x y)))
              → (f : (x : _) → A ptEM-raw x)
              → (g : (x : _) → A x ptEM-raw)
              → (p : f ptEM-raw ≡ g ptEM-raw)
               → (x : _) → wedgeConFun G H k n m P hLev f g p ptEM-raw x ≡ f x
  wedgeconRight : (G : AbGroup ℓ) (H : AbGroup ℓ')
                 (k n m : ℕ) (P : n + m ≡ k) {A : EM-raw G (suc n) → EM-raw H (suc m) → Type ℓ''}
              → (hLev : ((x : _) (y : _) → isOfHLevel (suc n + suc m) (A x y)))
              → (f : (x : _) → A ptEM-raw x)
              → (g : (x : _) → A x ptEM-raw)
              → (p : f ptEM-raw ≡ g ptEM-raw)
               → (x : _) → wedgeConFun G H k n m P hLev f g p x ptEM-raw ≡ g x
  wedgeConFun G H k n zero P {A = A} hLev f g p = wedgeConFun' G H n hLev f g p
  wedgeConFun G H k zero (suc m) P {A = A} hLev f g p x y =
    wedgeConFun' H G (suc m) {A = λ x y → A y x}
      (λ x y → subst (λ n → isOfHLevel (2 + n) (A y x)) (+-comm 1 m) (hLev y x))
      g f (sym p) y x
  wedgeConFun G H l (suc n) (suc m) P {A = A} hlev f g p north y = f y
  wedgeConFun G H l (suc n) (suc m) P {A = A} hlev f g p south y = subst (λ x → A x y) (merid ptEM-raw) (f y)
  wedgeConFun G H zero (suc n) (suc m) P {A = A} hlev f g p (merid a i) y = ⊥-path i
    where
    ⊥-path : PathP (λ i → A (merid a i) y) (f y) (subst (λ x → A x y) (merid ptEM-raw) (f y))
    ⊥-path = ⊥-rec (snotz P)
  wedgeConFun G H (suc l) (suc n) (suc m) P {A = A} hlev f g p (merid a i) y = mmain a y i
    module _ where
    llem₃ : g south ≡ (subst (λ x → A x ptEM-raw) (merid ptEM-raw) (f ptEM-raw))
    llem₃ = ((λ i → transp (λ j → A (merid ptEM-raw (~ i ∨ j)) ptEM-raw) (~ i) (g (merid ptEM-raw (~ i)))))
          ∙ cong (subst (λ x → A x ptEM-raw) (merid ptEM-raw)) (sym p)

    llem₃' :
      Square
        (λ i → transp (λ j → A (merid ptEM-raw (~ i ∨ j)) ptEM-raw) (~ i) (g (merid ptEM-raw (~ i))))
        (refl {x = subst (λ x → A x ptEM-raw) (merid ptEM-raw) (f ptEM-raw)})
        llem₃
        ((cong (transport (λ z → A (merid ptEM-raw z) ptEM-raw)) (sym p)))
    llem₃' i j =
      hcomp (λ k → λ { (i = i0) → transp (λ j₁ → A (merid ptEM-raw (~ j ∨ j₁)) ptEM-raw) (~ j) (g (merid ptEM-raw (~ j)))
                      ; (i = i1) → subst (λ x → A x ptEM-raw) (merid ptEM-raw) (p (~ k))
                      ; (j = i1) → cong (transport (λ z → A (merid ptEM-raw z) ptEM-raw)) (sym p) (i ∧ k)})
             (transp (λ j₁ → A (merid ptEM-raw ((~ j ∧ ~ i) ∨ j₁)) ptEM-raw) (~ j ∧ ~ i) (g (merid ptEM-raw (~ j ∧ ~ i))))


    llem₄ : (λ i₁ → transp (λ j → A (merid ptEM-raw (j ∧ i₁)) ptEM-raw) (~ i₁) (f ptEM-raw))
        ≡ (λ i₁ → hcomp (λ k → λ { (i₁ = i0) → p (~ k) ; (i₁ = i1) → llem₃ k })
           (g (merid ptEM-raw i₁)))
    llem₄ i j =
      hcomp (λ k → λ { (i = i0) → transp (λ z → A (merid ptEM-raw (z ∧ j)) ptEM-raw) (~ j) (p (~ k))
                      ; (j = i0) → p (~ k)
                      ; (j = i1) → llem₃' k (~ i)})
            (transp (λ z → A (merid ptEM-raw ((i ∨ z) ∧ j)) ptEM-raw) (i ∨ ~ j) (g (merid ptEM-raw (i ∧ j))))

    mmain : (a : _) (y : _)
          → PathP (λ i → A (merid a i) y) (f y)
                   (subst (λ x → A x y) (merid ptEM-raw) (f y))
    mmain =
      wedgeConFun G H l n (suc m) (cong predℕ P)
        (λ _ _ → isOfHLevelPathP' (suc (n + (suc (suc m)))) (hlev _ _) _ _)
        (λ x i → transp (λ j → A (merid ptEM-raw (j ∧ i)) x) (~ i) (f x))
        (λ y i → hcomp (λ k → λ { (i = i0) → p (~ k)
                                  ; (i = i1) → llem₃ k})
                       (g (merid y i)))
        llem₄

    mainR : (x : _) → mmain x ptEM-raw
                    ≡ λ i → hcomp (λ k → λ { (i = i0) → p (~ k)
                                             ; (i = i1) → llem₃ k})
                                               (g (merid x i))
    mainR x =
      wedgeconRight G H l n (suc m) (cong predℕ P)
        (λ _ _ → isOfHLevelPathP' (suc (n + (suc (suc m)))) (hlev _ _) _ _)
        (λ x i → transp (λ j → A (merid ptEM-raw (j ∧ i)) x) (~ i) (f x))
        (λ y i → hcomp (λ k → λ { (i = i0) → p (~ k)
                                  ; (i = i1) → llem₃ k})
                       (g (merid y i)))
        llem₄ x
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
    sym (llem₃ G H _ n m refl hLev f g p ptEM-raw i0 ptEM-raw)
  wedgeconRight G H (suc l) (suc n) (suc m) P {A = A} hLev f g p (merid a i) k =
    help k i
    where
    llem : _
    llem i j =
      hcomp (λ k → λ { (i = i1) → g (merid a j)
                      ; (j = i0) → p (i ∨ ~ k)
                      ; (j = i1) → llem₃ G H l n m P hLev f g p ptEM-raw i0 ptEM-raw (~ i ∧ k)})
            (g (merid a j))

    help : PathP (λ k → PathP (λ i → A (merid a i) ptEM-raw)
                 (p k) (llem₃ G H l n m P hLev f g p ptEM-raw i0 ptEM-raw (~ k)))
                 (λ i → mmain G H l n m P hLev f g p a i north a north i) (cong g (merid a))
    help = mainR G H l n m P hLev f g p a i0 ptEM-raw a ◁ llem

module wedgeConEM (G : AbGroup ℓ) (H : AbGroup ℓ') (n m : ℕ)
                  {A : EM-raw G (suc n) → EM-raw H (suc m) → Type ℓ''}
                  (hLev : ((x : _) (y : _) → isOfHLevel (suc n + suc m) (A x y)))
                  (f : (x : _) → A ptEM-raw x)
                  (g : (x : _) → A x ptEM-raw)
                  (p : f ptEM-raw ≡ g ptEM-raw) where
  fun : (x : EM-raw G (suc n)) (y : EM-raw H (suc m)) → A x y
  fun = wedgeConFun G H (n + m) n m refl hLev f g p

  left : (x : EM-raw H (suc m)) → fun ptEM-raw x ≡ f x
  left = wedgeconLeft G H (n + m) n m refl hLev f g p

  right : (x : EM-raw G (suc n)) → fun x ptEM-raw ≡ g x
  right = wedgeconRight G H (n + m) n m refl hLev f g p
