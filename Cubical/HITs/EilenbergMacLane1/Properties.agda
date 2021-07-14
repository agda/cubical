{-

Eilenberg–Mac Lane type K(G, 1)

-}

{-# OPTIONS --cubical --no-import-sorts --safe  --experimental-lossy-unification #-}
module Cubical.HITs.EilenbergMacLane1.Properties where

open import Cubical.HITs.EilenbergMacLane1.Base

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Univalence

open import Cubical.Data.Sigma
open import Cubical.Data.Empty renaming (rec to ⊥-rec) hiding (elim)


open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties

open import Cubical.Algebra.AbGroup.Base

open import Cubical.Functions.Morphism

open import Cubical.HITs.PropositionalTruncation as PropTrunc using (∥_∥; ∣_∣; squash)
open import Cubical.HITs.SetTruncation as SetTrunc using (∥_∥₂; ∣_∣₂; squash₂)

private
  variable
    ℓG ℓ : Level

module _ ((G , str) : Group ℓG) where

  open GroupStr str

  elimGroupoid :
   {B : EM₁ (G , str) → Type ℓ}
          → ((x : EM₁ (G , str)) → isGroupoid (B x))
          → (b : B embase)
          → (bloop : ((g : G) → PathP (λ i → B (emloop g i)) b b))
          → ((g h : G) → PathP (λ i → PathP (λ j → B (emcomp g h j i))
                                 (bloop g i) (bloop (g · h) i)) (λ _ → b) (bloop h))
          → (x : EM₁ (G , str))
          → B x
  elimGroupoid Bgroup b bloop bcomp embase = b
  elimGroupoid Bgroup b bloop bcomp (emloop x i) = bloop x i
  elimGroupoid Bgroup b bloop bcomp (emcomp g h j i) = bcomp g h i j
  elimGroupoid {B = B} Bgroup b bloop bcomp (emsquash g h p q r s i j k) = help i j k
    where
    help : PathP (λ i → PathP (λ j → PathP (λ k → B (emsquash g h p q r s i j k))
                 (elimGroupoid Bgroup b bloop bcomp g)
                 (elimGroupoid Bgroup b bloop bcomp h))
                 (λ k → elimGroupoid Bgroup b bloop bcomp (p k))
                 λ k → elimGroupoid Bgroup b bloop bcomp (q k))
                 (λ j k → elimGroupoid Bgroup b bloop bcomp (r j k))
                 λ j k → elimGroupoid Bgroup b bloop bcomp (s j k)
    help = toPathP (isOfHLevelPathP' 1 (isOfHLevelPathP' 2 (Bgroup _) _ _) _ _ _ _)

  elimSet : {B : EM₁ (G , str) → Type ℓ}
          → ((x : EM₁ (G , str)) → isSet (B x))
          → (b : B embase)
          → ((g : G) → PathP (λ i → B (emloop g i)) b b)
          → (x : EM₁ (G , str))
          → B x
  elimSet Bset b bloop embase = b
  elimSet Bset b bloop (emloop g i) = bloop g i
  elimSet Bset b bloop (emcomp g h i j) =
    isSet→SquareP
      (λ i j → Bset (emcomp g h i j))
      (λ j → bloop g j) (λ j → bloop (g · h) j)
      (λ i → b) (λ i → bloop h i)
      i j
  elimSet Bset b bloop (emsquash x y p q r s i j k) =
    isOfHLevel→isOfHLevelDep 3 (λ x → isSet→isGroupoid (Bset x))
      _ _ _ _ (λ j k → g (r j k)) (λ j k → g (s j k)) (emsquash x y p q r s) i j k
    where
      g = elimSet Bset b bloop

  elimProp : {B : EM₁ (G , str) → Type ℓ}
             → ((x : EM₁ (G , str)) → isProp (B x))
             → B embase
             → (x : EM₁ (G , str))
             → B x
  elimProp Bprop b x =
    elimSet
      (λ x → isProp→isSet (Bprop x))
      b
      (λ g → isProp→PathP (λ i → Bprop ((emloop g) i)) b b)
      x

  elimProp2 : {C : EM₁ (G , str) → EM₁ (G , str) → Type ℓ}
    → ((x y : EM₁ (G , str)) → isProp (C x y))
    → C embase embase
    → (x y : EM₁ (G , str))
    → C x y
  elimProp2 Cprop c =
    elimProp
      (λ x → isPropΠ (λ y → Cprop x y))
      (elimProp (λ y → Cprop embase y) c)

  elim : {B : EM₁ (G , str) → Type ℓ}
       → ((x : EM₁ (G , str)) → isGroupoid (B x))
       → (b : B embase)
       → (bloop : (g : G) → PathP (λ i → B (emloop g i)) b b)
       → ((g h : G) → SquareP (λ i j → B (emcomp g h i j))
            (bloop g) (bloop (g · h)) (λ j → b) (bloop h))
       → (x : EM₁ (G , str))
       → B x
  elim Bgpd b bloop bcomp embase = b
  elim Bgpd b bloop bcomp (emloop g i) = bloop g i
  elim Bgpd b bloop bcomp (emcomp g h i j) = bcomp g h i j
  elim Bgpd b bloop bcomp (emsquash x y p q r s i j k) =
    isOfHLevel→isOfHLevelDep 3 Bgpd
      _ _ _ _ (λ j k → g (r j k)) (λ j k → g (s j k)) (emsquash x y p q r s) i j k
    where
      g = elim Bgpd b bloop bcomp

  rec : {B : Type ℓ}
      → isGroupoid B
      → (b : B)
      → (bloop : G → b ≡ b)
      → ((g h : G) → Square (bloop g) (bloop (g · h)) refl (bloop h))
      → (x : EM₁ (G , str))
      → B
  rec Bgpd = elim (λ _ → Bgpd)


open import Cubical.HITs.Truncation renaming (elim to trElim ; rec to trRec ; rec2 to trRec2)
open import Cubical.Data.Nat
open import Cubical.HITs.Susp
open import Cubical.Foundations.Pointed

Susp̂ : (n : ℕ) → Type ℓG → Type ℓG
Susp̂ zero A = A
Susp̂ (suc n) A = Susp (Susp̂ n A)

pt-Susp̂ : (n : ℕ) (A : Pointed ℓG) → Susp̂ n (typ A)
pt-Susp̂ zero A = snd A
pt-Susp̂ (suc n) A = north

ptS : {n : ℕ} {G : Group ℓG} → Susp̂ n (EM₁ G)
ptS {n = n}  {G = G} = pt-Susp̂ n (EM₁ G , embase)

EM-raw : (G : AbGroup ℓG) (n : ℕ) → Type ℓG
EM-raw G zero = fst G
EM-raw G (suc n) = Susp̂ n (EM₁ (AbGroup→Group G))

EM-raw-elim : (G : AbGroup ℓG) (n : ℕ) {A : EM-raw G (suc n) → Type ℓ}
            → ((x : _) → isOfHLevel (suc n) (A x) )
            → A ptS
            → (x : _) → A x
EM-raw-elim G zero hlev b = elimProp _ hlev b
EM-raw-elim G (suc n) hlev b north = b
EM-raw-elim G (suc n) {A = A} hlev b south = subst A (merid ptS) b
EM-raw-elim G (suc n) {A = A} hlev b (merid a i) = help a i
  where
  help : (a : _) → PathP (λ i → A (merid a i)) b (subst A (merid ptS) b)
  help = EM-raw-elim G n (λ _ → isOfHLevelPathP' (suc n) (hlev _) _ _)
           λ i → transp (λ j → A (merid ptS (i ∧ j))) (~ i) b

EM∙ : (G : AbGroup ℓG) (n : ℕ) → Pointed ℓG
EM∙ G zero = fst G , AbGroupStr.0g (snd G)
EM∙ G (suc zero) = EM₁ (AbGroup→Group G) , embase
EM∙ G (suc (suc n)) = hLevelTrunc (4 + n) (Susp̂ (suc n) (EM₁ (AbGroup→Group G))) , ∣ north ∣

EM : (G : AbGroup ℓG) (n : ℕ) → Type ℓG
EM G zero = EM-raw G zero
EM G (suc zero) = EM-raw G 1
EM G (suc (suc n)) = hLevelTrunc (4 + n) (EM-raw G (suc (suc n)))

hLevelEM : (G : AbGroup ℓG) (n : ℕ) → isOfHLevel (2 + n) (EM G n)
hLevelEM G zero = AbGroupStr.is-set (snd G)
hLevelEM G (suc zero) = emsquash
hLevelEM G (suc (suc n)) = isOfHLevelTrunc (4 + n)

EM-raw→EM : (G : AbGroup ℓG) (n : ℕ) → EM-raw G n → EM G n
EM-raw→EM G zero x = x
EM-raw→EM G (suc zero) x = x
EM-raw→EM G (suc (suc n)) = ∣_∣

EM-elim : {G : AbGroup ℓG} (n : ℕ) {A : EM G n → Type ℓ}
        → ((x : _) → isOfHLevel (2 + n) (A x))
        → ((x : EM-raw G n) → A (EM-raw→EM G n x))
        → (x : _) → A x
EM-elim zero hlev hyp x = hyp x
EM-elim (suc zero) hlev hyp x = hyp x
EM-elim (suc (suc n)) hlev hyp = trElim (λ _ → hlev _) hyp

wedgeConFun' : (G H : AbGroup ℓG) (n : ℕ) → {A : EM-raw G (suc n) → EM-raw H (suc zero) → Type ℓ}
            → ((x : _) (y : _) → isOfHLevel (suc n + suc zero) (A x y))
            → (f : (x : _) → A ptS x)
            → (g : (x : _) → A x ptS)
            → f ptS ≡ g ptS
            → (x : _) (y : _) → A x y
wedgeConFun'ᵣ : (G H : AbGroup ℓG) (n : ℕ) → {A : EM-raw G (suc n) → EM-raw H (suc zero) → Type ℓ}
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
  wedgeConFun : (G H : AbGroup ℓG) (k n m : ℕ) → (n + m ≡ k) → {A : EM-raw G (suc n) → EM-raw H (suc m) → Type ℓ}
              → ((x : _) (y : _) → isOfHLevel (suc n + suc m) (A x y))
              → (f : (x : _) → A ptS x)
              → (g : (x : _) → A x ptS)
              → f ptS ≡ g ptS
              → (x : _) (y : _) → A x y
  wedgeconLeft : (G H : AbGroup ℓG) (k n m : ℕ) (P : n + m ≡ k) {A : EM-raw G (suc n) → EM-raw H (suc m) → Type ℓ}
              → (hLev : ((x : _) (y : _) → isOfHLevel (suc n + suc m) (A x y)))
              → (f : (x : _) → A ptS x)
              → (g : (x : _) → A x ptS)
              → (p : f ptS ≡ g ptS)
               → (x : _) → wedgeConFun G H k n m P hLev f g p ptS x ≡ f x
  wedgeconRight : (G H : AbGroup ℓG) (k n m : ℕ) (P : n + m ≡ k) {A : EM-raw G (suc n) → EM-raw H (suc m) → Type ℓ}
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


module wedgeConEM (G H : AbGroup ℓG) (n m : ℕ) {A : EM-raw G (suc n) → EM-raw H (suc m) → Type ℓ}
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

module _ {G : AbGroup ℓG} where
  infixr 34 _+ₖ_
  infixr 34 _-ₖ_
  open AbGroupStr (snd G) renaming (_+_ to _+G_ ; -_ to -G_ ; assoc to assocG)

  private
      help : (n : ℕ) → n + (4 + n) ≡ (2 + n) + (2 + n)
      help n = +-suc n (3 + n) ∙ cong suc (+-suc n (suc (suc n)))

  hLevHelp : (n : ℕ) → isOfHLevel ((2 + n) + (2 + n)) (EM G (2 + n))
  hLevHelp n =
    transport (λ i → isOfHLevel (help n i) (EM G (2 + n)))
          (isOfHLevelPlus {n = 4 + n} n (isOfHLevelTrunc (4 + n)))

  helper : (g h : fst G)
    → PathP (λ i → Path (EM₁ (AbGroup→Group G))
             (emloop h i) (emloop h i)) (emloop g) (emloop g)
  helper g h =
    compPathL→PathP
      (cong (sym (emloop h) ∙_)
           (sym (emloop-comp _ g h)
        ∙∙ cong emloop (comm g h)
        ∙∙ emloop-comp _ h g)
   ∙∙ assoc _ _ _
   ∙∙ cong (_∙ emloop g) (lCancel _)
    ∙ sym (lUnit _))
  open import Cubical.Foundations.Path
  _+ₖ_ : {n : ℕ} → EM G n → EM G n → EM G n
  _+ₖ_ {n = zero} = _+G_
  _+ₖ_ {n = suc zero} =
    rec _ (isGroupoidΠ (λ _ → emsquash))
      (λ x → x)
      hi!
      λ g h i j x → el g h x i j
    where
    lol : (g h : fst G)
      → Square (emloop g) (emloop (g +G h)) refl (emloop h)
    lol g h = compPath-filler (emloop g) (emloop h) ▷ sym (emloop-comp _ g h)

    hi! : fst G → (λ x → x) ≡ (λ x → x)
    hi! g = funExt (elimSet _ (λ _ → emsquash _ _)
                     (emloop g)
                     (helper g))
    el : (g h : fst G) (x : EM₁ (AbGroup→Group G))
      → Square (λ j → hi! g j x) (λ j → hi! ((snd (AbGroup→Group G) GroupStr.· g) h) j x)
                refl λ j → hi! h j x
    el g h =
      elimProp _ (λ _ → isOfHLevelPathP' 1 (emsquash _ _) _ _)
        (lol g h)
  _+ₖ_ {n = suc (suc n)} =
    trRec2 (isOfHLevelTrunc (4 + n))
      (wedgeConEM.fun G G (suc n) (suc n)
        (λ _ _ → hLevHelp n)
        ∣_∣ ∣_∣ refl)

  σ-EM : (n : ℕ) → EM-raw G (suc n) → Path (EM-raw G (2 + n)) ptS ptS
  σ-EM n x i = (merid x ∙ sym (merid ptS)) i

  -ₖ_ : {n : ℕ} → EM G n → EM G n
  -ₖ_ {n = zero} x = -G x
  -ₖ_ {n = suc zero} =
    rec _ emsquash
      ptS
      (λ g → sym (emloop g))
      λ g h → sym (emloop-sym _ g)
            ◁ (flipSquare
                (flipSquare (emcomp (-G g) (-G h))
               ▷ emloop-sym _ h)
            ▷ (cong emloop (comm (-G g) (-G h)
                          ∙ sym (GroupTheory.invDistr (AbGroup→Group G) g h))
             ∙ emloop-sym _ (g +G h)))
  -ₖ_ {n = suc (suc n)} =
    map λ { north → north
          ; south → north
          ; (merid a i) → σ-EM n a (~ i)}

  _-ₖ_ : {n : ℕ} → EM G n → EM G n → EM G n
  _-ₖ_ {n = n} x y = _+ₖ_ {n = n} x (-ₖ_ {n = n} y)

  +ₖ-syntax : (n : ℕ) →  EM G n → EM G n → EM G n
  +ₖ-syntax n = _+ₖ_ {n = n}

  -ₖ-syntax : (n : ℕ) → EM G n → EM G n
  -ₖ-syntax n = -ₖ_ {n = n}

  -'ₖ-syntax : (n : ℕ) → EM G n → EM G n → EM G n
  -'ₖ-syntax n = _-ₖ_ {n = n}

  syntax +ₖ-syntax n x y = x +[ n ]ₖ y
  syntax -ₖ-syntax n x = -[ n ]ₖ x
  syntax -'ₖ-syntax n x y = x -[ n ]ₖ y

  0ₖ : (n : ℕ) → EM G n
  0ₖ zero = 0g
  0ₖ (suc zero) = ptS
  0ₖ (suc (suc n)) = ∣ ptS ∣

  lUnitₖ : (n : ℕ) (x : EM G n) → 0ₖ n +[ n ]ₖ x ≡ x
  lUnitₖ zero x = lid x
  lUnitₖ (suc zero) _ = refl
  lUnitₖ (suc (suc n)) =
    trElim (λ _ → isOfHLevelTruncPath {n = 4 + n})
      λ _ → refl

  rUnitₖ : (n : ℕ) (x : EM G n) → x +[ n ]ₖ 0ₖ n ≡ x
  rUnitₖ zero x = rid x
  rUnitₖ (suc zero) =
    elimSet _ (λ _ → emsquash _ _)
            refl
            λ _ _ → refl
  rUnitₖ (suc (suc n)) =
    trElim (λ _ → isOfHLevelTruncPath {n = 4 + n})
      (wedgeConEM.right G G (suc n) (suc n)
      (λ _ _ → hLevHelp n)
      ∣_∣ ∣_∣ refl)

  commₖ : (n : ℕ) (x y : EM G n) → x +[ n ]ₖ y ≡ y +[ n ]ₖ x
  commₖ zero = comm
  commₖ (suc zero) =
    wedgeConEM.fun G G 0 0 (λ _ _ → emsquash _ _)
      (λ x → sym (rUnitₖ 1 x))
      (rUnitₖ 1)
      refl
  commₖ (suc (suc n)) =
    elim2 (λ _ _ → isOfHLevelTruncPath {n = 4 + n})
      (wedgeConEM.fun G G _ _ (λ _ _ → isOfHLevelPath ((2 + n) + (2 + n)) (hLevHelp n) _ _)
      (λ x → sym (rUnitₖ (2 + n) ∣ x ∣))
      (λ x → rUnitₖ (2 + n) ∣ x ∣)
      refl)

  open import Cubical.Homotopy.Loopspace
  cong₂+₁ : (p q : typ (Ω (EM∙ G 1))) → cong₂ (λ x y → x +[ 1 ]ₖ y) p q ≡ p ∙ q
  cong₂+₁ p q =
      (cong₂Funct (λ x y → x +[ 1 ]ₖ y) p q)
   ∙ (λ i → (cong (λ x → rUnitₖ 1 x i) p) ∙ (cong (λ x → lUnitₖ 1 x i) q))

  cong₂+₂ : (n : ℕ) (p q : typ (Ω (EM∙ G (2 + n)))) → cong₂ (λ x y → x +[ (2 + n) ]ₖ y) p q ≡ p ∙ q
  cong₂+₂ n p q =
      (cong₂Funct (λ x y → x +[ (2 + n) ]ₖ y) p q)
   ∙ (λ i → (cong (λ x → rUnitₖ (2 + n) x i) p) ∙ (cong (λ x → lUnitₖ (2 + n) x i) q))

  isCommΩEM : (n : ℕ) (p q : typ (Ω (EM∙ G  (suc n)))) → p ∙ q ≡ q ∙ p
  isCommΩEM zero p q =
       sym (cong₂+₁ p q)
    ∙∙ (λ i j → commₖ 1 (p j) (q j) i)
    ∙∙ cong₂+₁ q p
  isCommΩEM (suc n) p q =
       (sym (cong₂+₂ n p q)
    ∙∙ (λ i j → commₖ (suc (suc n)) (p j) (q j) i)
    ∙∙ cong₂+₂ n q p)

  cong-₁ : (p : typ (Ω (EM∙ G 1))) → cong (λ x → -[ 1 ]ₖ x) p ≡ sym p
  cong-₁ p = main ptS p
    where
    decoder : (x : EM G 1) → ptS ≡ x → x ≡ ptS
    decoder =
      elimSet _
        (λ _ → isSetΠ λ _ → emsquash _ _)
        (λ p i → -[ 1 ]ₖ (p i))
        λ g → toPathP
          (funExt λ x →
            (λ i → transport (λ i → Path (EM G 1) (emloop g i) ptS)
               (cong (-ₖ_ {n = 1})
                 (transp (λ j → Path (EM G 1) ptS (emloop g (~ j ∧ ~ i))) i
                   (compPath-filler x (sym (emloop g)) i) )))
         ∙∙ (λ i → transp (λ j → Path (EM G 1) (emloop g (i ∨ j)) ptS) i
                           (compPath-filler'
                             (sym (emloop g))
                             (cong-∙ (-ₖ_ {n = 1})
                                   x (sym (emloop g)) i) i))
      ∙∙ (cong (sym (emloop g) ∙_) (isCommΩEM 0 (cong (-ₖ_ {n = 1}) x) (emloop g)))
      ∙∙ assoc _ _ _
      ∙∙ cong (_∙ (cong (-ₖ_ {n = 1}) x)) (lCancel (emloop g))
       ∙ sym (lUnit _))

    main : (x : EM G 1) (p : ptS ≡ x) → decoder x p ≡ sym p
    main x = J (λ x p → decoder x p ≡ sym p) refl

  cong-₂ : (n : ℕ) (p : typ (Ω (EM∙ G (2 + n)))) → cong (λ x → -[ 2 + n ]ₖ x) p ≡ sym p
  cong-₂ n p = main _ p
    where
    pp : (a : _) → PathP (λ i → 0ₖ (suc (suc n)) ≡ ∣ merid a i ∣ₕ → ∣ merid a i ∣ₕ ≡ 0ₖ (2 + n))
                          (cong (λ x → -[ 2 + n ]ₖ x)) λ p → cong ∣_∣ₕ (sym (merid ptS)) ∙ cong (λ x → -[ 2 + n ]ₖ x) p
    pp a =
      toPathP
        (funExt λ x →
          (λ k → transp (λ i → Path (EM G (2 + n)) ∣ merid a (i ∨ k) ∣ ∣ ptS ∣) k (compPath-filler' (cong ∣_∣ₕ (sym (merid a)))
                   (cong (-ₖ-syntax (suc (suc n)))
                     (transp (λ j → Path (EM G (2 + n)) ∣ ptS ∣ ∣ merid a (~ j ∧ ~ k) ∣) k (compPath-filler x (sym (cong ∣_∣ₕ (merid a))) k))) k))
               ∙∙ cong (cong ∣_∣ₕ (sym (merid a)) ∙_) (cong-∙ (λ x → -[ 2 + n ]ₖ x) x (sym (cong ∣_∣ₕ (merid a)))
                      ∙ isCommΩEM (suc n) (cong (λ x → -[ 2 + n ]ₖ x) x) (cong ∣_∣ₕ (σ-EM n a)))
               ∙∙ (λ k → (λ i → ∣ merid a (~ i ∨ k) ∣) ∙ (λ i → ∣ compPath-filler' (merid a) (sym (merid ptS)) (~ k) i ∣)
                        ∙ cong (λ x → -ₖ-syntax (suc (suc n)) x) x)
                ∙ sym (lUnit _))

    decoder : (x : EM G (2 + n)) → 0ₖ (2 + n) ≡ x → x ≡ 0ₖ (2 + n)
    decoder =
      trElim (λ _ → isOfHLevelΠ (4 + n) λ _ → isOfHLevelTruncPath {n = 4 + n})
             λ { north → pp ptS i0
               ; south → pp ptS i1
               ; (merid a i) → pp a i}

    main : (x : EM G (2 + n)) (p : 0ₖ (2 + n) ≡ x) → decoder x p ≡ sym p
    main x = J (λ x p → decoder x p ≡ sym p) refl

  rCancelₖ : (n : ℕ) (x : EM G n) → x +[ n ]ₖ (-[ n ]ₖ x) ≡ 0ₖ n
  rCancelₖ zero x = invr x
  rCancelₖ (suc zero) =
    elimSet _ (λ _ → emsquash _ _)
      refl
      λ g → flipSquare (cong₂+₁ (emloop g) (λ i → -ₖ-syntax 1 (emloop g i))
           ∙ rCancel (emloop g))
  rCancelₖ (suc (suc n)) =
    trElim (λ _ → isOfHLevelTruncPath {n = 4 + n})
      λ { north → refl
        ; south i → +ₖ-syntax (suc (suc n)) ∣ merid ptS (~ i) ∣ (-ₖ-syntax (suc (suc n)) ∣ merid ptS (~ i) ∣)
        ; (merid a i) j
          → hcomp (λ r → λ { (i = i0) → 0ₖ (2 + n)
                             ; (i = i1) → ∣ merid ptS (~ j ∧ r) ∣ₕ -[ 2 + n ]ₖ ∣ merid ptS (~ j ∧ r) ∣
                             ; (j = i0) → ∣ compPath-filler (merid a) (sym (merid ptS)) (~ r) i ∣
                                        -[ 2 + n ]ₖ ∣ compPath-filler (merid a) (sym (merid ptS)) (~ r) i ∣
                             ; (j = i1) → 0ₖ (2 + n)})
                   (help' a j i) }
    where
    help' : (a : _) → cong₂ (λ x y → ∣ x ∣ -[ suc (suc n) ]ₖ ∣ y ∣) (σ-EM n a) (σ-EM n a) ≡ refl
    help' a =
         cong₂+₂ n (cong ∣_∣ₕ (σ-EM n a)) (cong (λ x → -[ 2 + n ]ₖ ∣ x ∣) (σ-EM n a))
      ∙∙ cong (cong ∣_∣ₕ (σ-EM n a) ∙_) (cong-₂ n (cong ∣_∣ₕ (σ-EM n a)))
      ∙∙ rCancel _

  lCancelₖ : (n : ℕ) (x : EM G n) → (-[ n ]ₖ x) +[ n ]ₖ x ≡ 0ₖ n
  lCancelₖ n x = commₖ n (-[ n ]ₖ x) x ∙ rCancelₖ n x

  assocₖ : (n : ℕ) (x y z : EM G n)
        → (x +[ n ]ₖ (y +[ n ]ₖ z) ≡ (x +[ n ]ₖ y) +[ n ]ₖ z)
  assocₖ zero = assocG
  assocₖ (suc zero) =
    elimSet _ (λ _ → isSetΠ2 λ _ _ → emsquash _ _)
      (λ _ _ → refl)
      λ g i y z k → lem g y z k i
    where
    lem : (g : fst G) (y z : _) → cong (λ x → x +[ suc zero ]ₖ (y +[ suc zero ]ₖ z)) (emloop g)
                                ≡ cong (λ x → (x +[ suc zero ]ₖ y) +[ suc zero ]ₖ z) (emloop g) 
    lem g =
      elimProp _ (λ _ → isPropΠ λ _ → emsquash _ _ _ _)
        (elimProp _ (λ _ → emsquash _ _ _ _)
          refl)
  assocₖ (suc (suc n)) =
    elim2 (λ _ _ → isOfHLevelΠ (4 + n) λ _ → isOfHLevelTruncPath {n = 4 + n})
      λ a b → trElim (λ _ → isOfHLevelTruncPath {n = 4 + n})
                (λ c → main c a b)
    where
    lem : (c : _) (a b : _)
      → PathP (λ i → (∣ a ∣ₕ +[ suc (suc n) ]ₖ (∣ b ∣ₕ +[ suc (suc n) ]ₖ ∣ merid c i ∣ₕ)
                    ≡ (∣ a ∣ₕ +[ suc (suc n) ]ₖ ∣ b ∣ₕ) +[ suc (suc n) ]ₖ ∣ merid c i ∣ₕ))
               (cong (λ x → ∣ a ∣ₕ +[ suc (suc n) ]ₖ x) (rUnitₖ (suc (suc n)) ∣ b ∣)
                   ∙ sym (rUnitₖ (suc (suc n)) (∣ a ∣ₕ +[ suc (suc n) ]ₖ ∣ b ∣ₕ)))
               ((λ i → ∣ a ∣ₕ +[ suc (suc n) ]ₖ (∣ b ∣ₕ +[ suc (suc n) ]ₖ ∣ merid ptS (~ i) ∣ₕ))
             ∙∙ cong (λ x → ∣ a ∣ₕ +[ suc (suc n) ]ₖ x) (rUnitₖ (suc (suc n)) ∣ b ∣)
                 ∙ sym (rUnitₖ (suc (suc n)) (∣ a ∣ₕ +[ suc (suc n) ]ₖ ∣ b ∣ₕ))
             ∙∙ λ i → (∣ a ∣ₕ +[ suc (suc n) ]ₖ ∣ b ∣ₕ) +[ suc (suc n) ]ₖ ∣ merid ptS i ∣ₕ)
    lem c =
      EM-raw-elim G (suc n)
        (λ _ → isOfHLevelΠ (2 + n) (λ _ → isOfHLevelPathP' (2 + n) (isOfHLevelTrunc (4 + n) _ _) _ _))
          (EM-raw-elim G (suc n) (λ _ → isOfHLevelPathP' (2 + n) (isOfHLevelTrunc (4 + n) _ _) _ _)
            ((sym (rUnit refl)
            ◁ λ _ → refl)
            ▷ (sym (lCancel (cong ∣_∣ₕ (merid ptS)))
            ∙ λ i → (λ j → ∣ merid ptS (~ j ∨ ~ i) ∣ₕ)
                  ∙∙ lUnit (λ j → ∣ merid ptS (~ j ∧ ~ i) ∣ₕ) i
                  ∙∙ cong ∣_∣ₕ (merid ptS))))
    main : (c a b : _) → (∣ a ∣ₕ +[ suc (suc n) ]ₖ (∣ b ∣ₕ +[ suc (suc n) ]ₖ ∣ c ∣ₕ) ≡ (∣ a ∣ₕ +[ suc (suc n) ]ₖ ∣ b ∣ₕ) +[ suc (suc n) ]ₖ ∣ c ∣ₕ)
    main north a b = lem ptS a b i0
    main south a b = lem ptS a b i1
    main (merid c i) a b = lem c a b i

  σ-EM' : (n : ℕ) (x : EM G (suc n))
        → Path (EM G (suc (suc n)))
                (0ₖ (suc (suc n)))
                (0ₖ (suc (suc n)))
  σ-EM' zero x = cong ∣_∣ₕ (σ-EM zero x)
  σ-EM' (suc n) =
    trElim (λ _ → isOfHLevelTrunc (5 + n) _ _)
      λ x → cong ∣_∣ₕ (σ-EM (suc n) x)

  σ-EM'-0ₖ : (n : ℕ) → σ-EM' n (0ₖ (suc n)) ≡ refl
  σ-EM'-0ₖ zero = cong (cong ∣_∣ₕ) (rCancel (merid ptS))
  σ-EM'-0ₖ (suc n) = cong (cong ∣_∣ₕ) (rCancel (merid ptS))

  private
    P : ∀ {ℓ} {A : Type ℓ} {x : A} (p : x ≡ x) (r : refl ≡ p)
        → lUnit p ∙ cong (_∙ p) r
         ≡ rUnit p ∙ cong (p ∙_) r
    P p = J (λ p r → lUnit p ∙ cong (_∙ p) r ≡ rUnit p ∙ cong (p ∙_) r) refl

  σ-EM'-hom : (n : ℕ) → (a b : _) → σ-EM' n (a +ₖ b) ≡ σ-EM' n a ∙ σ-EM' n b
  σ-EM'-hom zero =
    wedgeConEM.fun G G 0 0 (λ _ _ → isOfHLevelTrunc 4 _ _ _ _) l r p
    where
    l : _
    l x = cong (σ-EM' zero) (lUnitₖ 1 x)
        ∙∙ lUnit (σ-EM' zero x)
        ∙∙ cong (_∙ σ-EM' zero x) (sym (σ-EM'-0ₖ zero))

    r : _
    r x =
         cong (σ-EM' zero) (rUnitₖ 1 x) 
      ∙∙ rUnit (σ-EM' zero x)
      ∙∙ cong (σ-EM' zero x ∙_) (sym (σ-EM'-0ₖ zero))

    p : _
    p = P (σ-EM' zero embase) (sym (σ-EM'-0ₖ zero))
  σ-EM'-hom (suc n) =
    elim2 (λ _ _ → isOfHLevelPath (4 + n) (isOfHLevelTrunc (5 + n) _ _) _ _)
      (wedgeConEM.fun G G _ _
        (λ x y → transport (λ i → isOfHLevel (help n i)
                            ((σ-EM' (suc n) (∣ x ∣ₕ +ₖ ∣ y ∣ₕ)
                           ≡ σ-EM' (suc n) ∣ x ∣ₕ ∙ σ-EM' (suc n) ∣ y ∣ₕ)))
                    (isOfHLevelPlus {n = 4 + n} n
                      (isOfHLevelPath (4 + n)
                        (isOfHLevelTrunc (5 + n) _ _) _ _)))
        (λ x → cong (σ-EM' (suc n)) (lUnitₖ (suc (suc n)) ∣ x ∣)
            ∙∙ lUnit (σ-EM' (suc n) ∣ x ∣)
            ∙∙ cong (_∙ σ-EM' (suc n) ∣ x ∣) (sym (σ-EM'-0ₖ (suc n))))
        (λ x → cong (σ-EM' (suc n)) (rUnitₖ (2 + n) ∣ x ∣) 
      ∙∙ rUnit (σ-EM' (suc n) ∣ x ∣)
      ∙∙ cong (σ-EM' (suc n) ∣ x ∣ ∙_) (sym (σ-EM'-0ₖ (suc n))))
        (P (σ-EM' (suc n) (0ₖ (2 + n))) (sym (σ-EM'-0ₖ (suc n)))))

  σ-EM'-ₖ : (n : ℕ) → (a : _) → σ-EM' n (-ₖ a) ≡ sym (σ-EM' n a)
  σ-EM'-ₖ n = 
    morphLemmas.distrMinus
      (λ x y → x +[ suc n ]ₖ y) (_∙_)
      (σ-EM' n) (σ-EM'-hom n)
      (0ₖ (suc n)) refl
      (λ x → -ₖ x) sym
      (λ x → sym (lUnit x)) (λ x → sym (rUnit x))
      (lCancelₖ (suc n)) rCancel
      assoc (σ-EM'-0ₖ n)

  -Dist : (n : ℕ) (x y : EM G n) → -[ n ]ₖ (x +[ n ]ₖ y) ≡ (-[ n ]ₖ x) +[ n ]ₖ (-[ n ]ₖ y)
  -Dist zero x y = (GroupTheory.invDistr (AbGroup→Group G) x y) ∙ commₖ zero _ _
  -Dist (suc zero) = k
    where -- useless where clause. Needed for fast type checking for some reason.
    l : _
    l x = refl

    r : _
    r x = cong (λ z → -[ 1 ]ₖ z) (rUnitₖ 1 x) ∙ sym (rUnitₖ 1 (-[ 1 ]ₖ x))

    p : r ptS ≡ l ptS
    p = sym (rUnit refl)

    k = wedgeConEM.fun G G 0 0 (λ _ _ → emsquash _ _) l r (sym p)

  -Dist (suc (suc n)) =
    elim2 (λ _ _ → isOfHLevelTruncPath {n = 4 + n})
      (wedgeConEM.fun G G (suc n) (suc n)
        (λ _ _ → isOfHLevelPath ((2 + n) + (2 + n)) (hLevHelp n) _ _)
        (λ x → refl)
        (λ x → cong (λ z → -[ (suc (suc n)) ]ₖ z) (rUnitₖ (suc (suc n)) ∣ x ∣ₕ) ∙ sym (rUnitₖ (suc (suc n)) (-[ (suc (suc n)) ]ₖ ∣ x ∣ₕ)))
        (rUnit refl))

  addIso : (n : ℕ) (x : EM G n) → Iso (EM G n) (EM G n)
  Iso.fun (addIso n x) y = y +[ n ]ₖ x
  Iso.inv (addIso n x) y = y -[ n ]ₖ x
  Iso.rightInv (addIso n x) y =
       sym (assocₖ n y (-[ n ]ₖ x) x)
    ∙∙ cong (λ x → y +[ n ]ₖ x) (lCancelₖ n x)
    ∙∙ rUnitₖ n y
  Iso.leftInv (addIso n x) y =
    sym (assocₖ n y x (-[ n ]ₖ x))
    ∙∙ cong (λ x → y +[ n ]ₖ x) (rCancelₖ n x)
    ∙∙ rUnitₖ n y

  CODE : (n : ℕ) → EM G (suc n) → TypeOfHLevel ℓG (2 + n)
  CODE zero =
    rec _ (isOfHLevelTypeOfHLevel 2)
      (typ G , is-set)
      (λ g → Σ≡Prop (λ _ → isPropIsOfHLevel 2)
                     (isoToPath (addIso 0 g)))
      (λ g h → ΣSquareSet {B = isOfHLevel 2}
               (λ _ → isSetΠ2 λ _ _ → isProp→isOfHLevelSuc 1 isPropIsProp)
               (without g h))
    where
    ΣSquareSet : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} (prop : (x : A) → isSet (B x))
               → {x y z w : Σ A B} {p : x ≡ y} {q : y ≡ z} {r : w ≡ z} {s : x ≡ w}
               → Square (cong fst s) (cong fst q) (cong fst p) (cong fst r)
               → Square s q p r
    fst (ΣSquareSet prop sq i j) = sq i j
    snd (ΣSquareSet {B = B} prop {p = p} {q = q} {r = r} {s = s} sq i j) = sqP i j
      where
      sqP : SquareP (λ i j → B (sq i j))
            (cong snd s) (cong snd q) (cong snd p) (cong snd r)
      sqP = toPathP (isOfHLevelPathP' 1 (prop _) _ _ _ _)

    lem : (g h : fst G) → compEquiv (isoToEquiv (addIso 0 g)) (isoToEquiv (addIso 0 h))
                        ≡ isoToEquiv (addIso 0 (snd G .AbGroupStr._+_ g h))
    lem g h =
      Σ≡Prop (λ _ → isPropIsEquiv _)
        (funExt λ x → sym (assocₖ 0 x g h))

    without : (g h : fst G) →
      Square (isoToPath (addIso 0 g))
       (isoToPath (addIso 0 ((snd (AbGroup→Group G) GroupStr.· g) h)))
      refl (isoToPath (addIso 0 h))
    without g h =
      compPathL→PathP
        (sym (lUnit _)
      ∙∙ sym (uaCompEquiv (isoToEquiv (addIso 0 g)) (isoToEquiv (addIso 0 h)))
      ∙∙ cong ua (lem g h))

  CODE (suc n) =
    trElim (λ _ → isOfHLevelTypeOfHLevel (3 + n))
      λ { north → EM G (suc n) , hLevelEM G (suc n)
        ; south → EM G (suc n) , hLevelEM G (suc n)
        ; (merid a i) → fib n a i}
    where
    fib : (n : ℕ) → (a : EM-raw G (suc n))
        → Path (TypeOfHLevel _ (3 + n)) (EM G (suc n) , hLevelEM G (suc n)) (EM G (suc n) , hLevelEM G (suc n))
    fib zero a = Σ≡Prop (λ _ → isPropIsOfHLevel 3)
                   (isoToPath (addIso 1 a))
    fib (suc n) a = Σ≡Prop (λ _ → isPropIsOfHLevel (4 + n))
                            (isoToPath (addIso (suc (suc n)) ∣ a ∣))

  decode : (n : ℕ) (x : EM G (suc n)) → CODE n x .fst → 0ₖ (suc n) ≡ x
  decode zero =
    elimSet _ (λ _ → isSetΠ (λ _ → emsquash _ _))
      emloop main
    where
    main : (g : _) → PathP (λ i → CODE zero (emloop g i) .fst → 0ₖ 1 ≡ emloop g i)
                            emloop emloop
    main g =
      toPathP
        (funExt λ x
            → (λ j → transp (λ i → Path (EM-raw G 1) ptS (emloop g (i ∨ j))) j
                      (compPath-filler (emloop ((transportRefl x j) +G -G g)) (emloop g) j))
            ∙∙ sym (emloop-comp _ (x +G -G g) g)
            ∙∙ cong emloop (sym (assocG x (-G g) g) ∙∙ cong (x +G_) (invl g) ∙∙ rid x))
  decode (suc n) =
    trElim (λ _ → isOfHLevelΠ (4 + n)
            λ _ → isOfHLevelPath (4 + n) (isOfHLevelTrunc (4 + n)) _ _)
           λ { north → f n
             ; south → g n
             ; (merid a i) → main a i}
     where
     f : (n : ℕ) → _
     f n = σ-EM' n

     g : (n : ℕ) → EM G (suc n) → ∣ ptS ∣ ≡ ∣ south ∣
     g n x = σ-EM' n x ∙ cong ∣_∣ₕ (merid ptS)

     lem₂ : (n : ℕ) (a x : _)
       → Path (Path (EM G (suc (suc n))) _ _)
               ((λ i → cong ∣_∣ₕ (σ-EM n x) i) ∙ sym (cong ∣_∣ₕ (σ-EM n a)) ∙ (λ i → ∣ merid a i ∣ₕ))
               (g n (EM-raw→EM G (suc n) x))
     lem₂ zero a x =
       cong (f zero x ∙_)
         (cong (_∙ cong ∣_∣ₕ (merid a)) (cong (cong ∣_∣ₕ) (symDistr (merid a) (sym (merid ptS)))
                                     ∙ cong-∙ ∣_∣ₕ (merid (ptS)) (sym (merid a)))
          ∙∙ sym (assoc _ _ _)
          ∙∙ cong (cong ∣_∣ₕ (merid ptS) ∙_) (lCancel (cong ∣_∣ₕ (merid a)))
           ∙ sym (rUnit _))
     lem₂ (suc n) a x =
       cong (f (suc n) ∣ x ∣ ∙_)
         ((cong (_∙ cong ∣_∣ₕ (merid a)) (cong (cong ∣_∣ₕ) (symDistr (merid a) (sym (merid ptS)))
                                      ∙ cong-∙ ∣_∣ₕ (merid (ptS)) (sym (merid a)))
          ∙∙ sym (assoc _ _ _)
          ∙∙ cong (cong ∣_∣ₕ (merid ptS) ∙_) (lCancel (cong ∣_∣ₕ (merid a)))
           ∙ sym (rUnit _)))

     lem : (n : ℕ) (x a : EM-raw G (suc n))
             → f n (transport (sym (cong (λ x → CODE (suc n) x .fst) (cong ∣_∣ₕ (merid a)))) (EM-raw→EM G (suc n) x))
                ≡ cong ∣_∣ₕ (σ-EM n x) ∙ sym (cong ∣_∣ₕ (σ-EM n a))
     lem zero x a = (λ i → cong ∣_∣ₕ (merid (transportRefl x i -[ 1 ]ₖ a) ∙ sym (merid embase)))
                  ∙∙ σ-EM'-hom zero x (-ₖ a)
                  ∙∙ cong (f zero x ∙_) (σ-EM'-ₖ zero a)
     lem (suc n) x a =
          cong (f (suc n)) (λ i → transportRefl ∣ x ∣ i -[ 2 + n ]ₖ ∣ a ∣)
        ∙∙ σ-EM'-hom (suc n) ∣ x ∣ (-ₖ ∣ a ∣)
        ∙∙ cong (f (suc n) ∣ x ∣ ∙_) (σ-EM'-ₖ (suc n) ∣ a ∣)

     main : (a : _)
         → PathP (λ i → CODE (suc n) ∣ merid a i ∣ₕ .fst
                       → 0ₖ (suc (suc n)) ≡ ∣ merid a i ∣ₕ) (f n) (g n)
     main a =
       toPathP (funExt
         (EM-elim _ (λ _ → isOfHLevelPathP (2 + (suc n)) (isOfHLevelTrunc (4 + n) _ _) _ _)
           λ x →
            (λ i → transp (λ j → Path (EM G (2 + n)) ∣ ptS ∣ ∣ merid a (i ∨ j) ∣)
                         i (compPath-filler (lem n x a i) (cong ∣_∣ₕ (merid a)) i) )
         ∙∙ sym (assoc _ _ _)
         ∙∙ lem₂ n a x))

  private
    ptCode0 : (n : ℕ) → CODE n (0ₖ (suc n)) .fst
    ptCode0 zero = 0g
    ptCode0 (suc n) = 0ₖ (suc n)

  encode : (n : ℕ) (x : EM G (suc n)) → 0ₖ (suc n) ≡ x → CODE n x .fst
  encode n x p = subst (λ x → CODE n x .fst) p (ptCode0 n)

  open import Cubical.Foundations.Transport

  encode-morph : (n : ℕ) → (p q : 0ₖ (suc (suc n)) ≡ 0ₖ (suc (suc n)))
              → (encode (suc n) _ (p ∙ q)) ≡ (encode (suc n) _ p) +[ suc n ]ₖ (encode (suc n) _ q)
  encode-morph n p q =
    substComposite (λ x → CODE (suc n) x .fst) p q (0ₖ (suc n))
    ∙∙ {!!}
    ∙∙ {!!}

  decode-encode : (n : ℕ) (x : EM G (suc n)) (p : 0ₖ (suc n) ≡ x) → decode n x (encode n x p) ≡ p
  decode-encode zero x =
    J (λ x p → decode zero x (encode zero x p) ≡ p)
      (cong emloop (transportRefl 0g) ∙ emloop-1g (AbGroup→Group G))
  decode-encode (suc zero) x =
    J (λ x p → decode 1 x (encode 1 x p) ≡ p)
      (σ-EM'-0ₖ 0)
  decode-encode (suc (suc n)) x =
    J (λ x p → decode (2 + n) x (encode (2 + n) x p) ≡ p)
       (σ-EM'-0ₖ (suc n))

  encode-decode : (n : ℕ) (x : _) → encode n (0ₖ (suc n)) (decode n (0ₖ (suc n)) x) ≡ x
  encode-decode zero x i = transportRefl (lid x i) i
  encode-decode (suc zero) x =
      cong (encode 1 (0ₖ 2)) (cong-∙ ∣_∣ₕ (merid x) (sym (merid ptS)))
    ∙∙ substComposite (λ x → CODE (suc zero) x .fst)
         (cong ∣_∣ₕ (merid x)) (sym (cong ∣_∣ₕ (merid ptS))) ptS
    ∙∙ cong (subst (λ x₁ → CODE 1 x₁ .fst) (λ i → ∣ merid ptS (~ i) ∣ₕ))
            (λ i → lUnitₖ 1 (transportRefl x i) i)
     ∙ (λ i → rUnitₖ 1 (transportRefl x i) i)
  encode-decode (suc (suc n)) =
    trElim (λ _ → isOfHLevelTruncPath {n = 4 + n})
      λ x → cong (encode (2 + n) (0ₖ (3 + n))) (cong-∙ ∣_∣ₕ (merid x) (sym (merid ptS)))
    ∙∙ substComposite (λ x → CODE (suc (suc n)) x .fst)
         (cong ∣_∣ₕ (merid x)) (sym (cong ∣_∣ₕ (merid ptS))) (0ₖ (2 + n))
    ∙∙ cong (subst (λ x₁ → CODE (2 + n) x₁ .fst) (λ i → ∣ merid ptS (~ i) ∣ₕ))
            (λ i → lUnitₖ (2 + n) (transportRefl ∣ x ∣ₕ i) i)
     ∙ (λ i → rUnitₖ (2 + n) (transportRefl ∣ x ∣ₕ i) i)

  EM∙' : (n : ℕ) → Pointed _
  EM∙' n = EM G n , 0ₖ n

  Iso-EM-ΩEM+1 : (n : ℕ) → Iso (EM G n) (typ (Ω (EM∙' (suc n))))
  Iso.fun (Iso-EM-ΩEM+1 zero) = decode zero (0ₖ 1)
  Iso.inv (Iso-EM-ΩEM+1 zero) = encode zero (0ₖ 1)
  Iso.rightInv (Iso-EM-ΩEM+1 zero) = decode-encode zero (0ₖ 1)
  Iso.leftInv (Iso-EM-ΩEM+1 zero) = encode-decode zero
  Iso.fun (Iso-EM-ΩEM+1 (suc zero)) = decode 1 (0ₖ 2)
  Iso.inv (Iso-EM-ΩEM+1 (suc zero)) = encode 1 (0ₖ 2)
  Iso.rightInv (Iso-EM-ΩEM+1 (suc zero)) = decode-encode 1 (0ₖ 2)
  Iso.leftInv (Iso-EM-ΩEM+1 (suc zero)) = encode-decode 1
  Iso.fun (Iso-EM-ΩEM+1 (suc (suc n))) = decode (2 + n) (0ₖ (3 + n))
  Iso.inv (Iso-EM-ΩEM+1 (suc (suc n))) = encode (2 + n) (0ₖ (3 + n))
  Iso.rightInv (Iso-EM-ΩEM+1 (suc (suc n))) = decode-encode (2 + n) (0ₖ (3 + n))
  Iso.leftInv (Iso-EM-ΩEM+1 (suc (suc n))) = encode-decode (2 + n)

  EM→ΩEM+1 : (n : ℕ) → EM G n → typ (Ω (EM∙' (suc n)))
  EM→ΩEM+1 n = Iso.fun (Iso-EM-ΩEM+1 n)

  ΩEM+1→EM : (n : ℕ) → typ (Ω (EM∙' (suc n))) → EM G n
  ΩEM+1→EM n = Iso.inv (Iso-EM-ΩEM+1 n)

  EM→ΩEM+1-hom : (n : ℕ) (x y : EM G n)
    → EM→ΩEM+1 n (x +[ n ]ₖ y) ≡ EM→ΩEM+1 n x ∙ EM→ΩEM+1 n y
  EM→ΩEM+1-hom zero x y = emloop-comp _ x y
  EM→ΩEM+1-hom (suc zero) x y = σ-EM'-hom zero x y
  EM→ΩEM+1-hom (suc (suc n)) x y = σ-EM'-hom (suc n) x y

  ΩEM+1→EM-hom : (n : ℕ) → (p q : typ (Ω (EM∙' (suc n))))
    → ΩEM+1→EM n (p ∙ q) ≡ (ΩEM+1→EM n p) +[ n ]ₖ (ΩEM+1→EM n q)
  ΩEM+1→EM-hom n =
    morphLemmas.isMorphInv (λ x y → x +[ n ]ₖ y) (_∙_) (EM→ΩEM+1 n)
      (EM→ΩEM+1-hom n) (ΩEM+1→EM n)
      (Iso.rightInv (Iso-EM-ΩEM+1 n)) (Iso.leftInv (Iso-EM-ΩEM+1 n))

  EM→ΩEM+1-0ₖ : (n : ℕ) → EM→ΩEM+1 n (0ₖ n) ≡ refl
  EM→ΩEM+1-0ₖ zero = emloop-1g _
  EM→ΩEM+1-0ₖ (suc zero) = cong (cong ∣_∣ₕ) (rCancel (merid ptS))
  EM→ΩEM+1-0ₖ (suc (suc n)) = cong (cong ∣_∣ₕ) (rCancel (merid ptS))

  ΩEM+1→EM-refl : (n : ℕ) → ΩEM+1→EM n refl ≡ 0ₖ n
  ΩEM+1→EM-refl zero = transportRefl 0g
  ΩEM+1→EM-refl (suc zero) = refl
  ΩEM+1→EM-refl (suc (suc n)) = refl
