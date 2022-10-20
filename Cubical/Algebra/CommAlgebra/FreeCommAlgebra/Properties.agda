{-# OPTIONS --safe #-}

module Cubical.Algebra.CommAlgebra.FreeCommAlgebra.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function hiding (const)
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma.Properties using (Σ≡Prop)
open import Cubical.HITs.SetTruncation

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommAlgebra.FreeCommAlgebra.Base
open import Cubical.Algebra.Ring        using ()
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.Instances.Initial
open import Cubical.Algebra.Algebra

open import Cubical.Data.Empty
open import Cubical.Data.Sigma

private
  variable
    ℓ ℓ' ℓ'' : Level

module Theory {R : CommRing ℓ} {I : Type ℓ'} where
  open CommRingStr (snd R)
         using (0r; 1r)
         renaming (_·_ to _·r_; _+_ to _+r_; ·Comm to ·r-comm; ·IdR to ·r-rid)

  module _ (A : CommAlgebra R ℓ'') (φ : I → ⟨ A ⟩) where
    open CommAlgebraStr (A .snd)
    open AlgebraTheory (CommRing→Ring R) (CommAlgebra→Algebra A)
    open Construction using (var; const) renaming (_+_ to _+c_; -_ to -c_; _·_ to _·c_)

    imageOf0Works : 0r ⋆ 1a ≡ 0a
    imageOf0Works = ⋆AnnihilL 1a

    imageOf1Works : 1r ⋆ 1a ≡ 1a
    imageOf1Works = ⋆IdL 1a

    inducedMap : ⟨ R [ I ] ⟩ → ⟨ A ⟩
    inducedMap (var x) = φ x
    inducedMap (const r) = r ⋆ 1a
    inducedMap (P +c Q) = (inducedMap P) + (inducedMap Q)
    inducedMap (-c P) = - inducedMap P
    inducedMap (Construction.+-assoc P Q S i) = +Assoc (inducedMap P) (inducedMap Q) (inducedMap S) i
    inducedMap (Construction.+-rid P i) =
      let
        eq : (inducedMap P) + (inducedMap (const 0r)) ≡ (inducedMap P)
        eq = (inducedMap P) + (inducedMap (const 0r)) ≡⟨ refl ⟩
             (inducedMap P) + (0r ⋆ 1a)               ≡⟨ cong
                                                         (λ u → (inducedMap P) + u)
                                                         (imageOf0Works) ⟩
             (inducedMap P) + 0a                      ≡⟨ +IdR _ ⟩
             (inducedMap P) ∎
      in eq i
    inducedMap (Construction.+-rinv P i) =
      let eq : (inducedMap P - inducedMap P) ≡ (inducedMap (const 0r))
          eq = (inducedMap P - inducedMap P) ≡⟨ +InvR _ ⟩
               0a                            ≡⟨ sym imageOf0Works ⟩
               (inducedMap (const 0r))∎
      in eq i
    inducedMap (Construction.+-comm P Q i) = +Comm (inducedMap P) (inducedMap Q) i
    inducedMap (P ·c Q) = inducedMap P · inducedMap Q
    inducedMap (Construction.·-assoc P Q S i) = ·Assoc (inducedMap P) (inducedMap Q) (inducedMap S) i
    inducedMap (Construction.·-lid P i) =
      let eq = inducedMap (const 1r) · inducedMap P ≡⟨ cong (λ u → u · inducedMap P) imageOf1Works ⟩
               1a · inducedMap P                    ≡⟨ ·IdL (inducedMap P) ⟩
               inducedMap P ∎
      in eq i
    inducedMap (Construction.·-comm P Q i) = ·Comm (inducedMap P) (inducedMap Q) i
    inducedMap (Construction.ldist P Q S i) = ·DistL+ (inducedMap P) (inducedMap Q) (inducedMap S) i
    inducedMap (Construction.+HomConst s t i) = ⋆DistL+ s t 1a i
    inducedMap (Construction.·HomConst s t i) =
      let eq = (s ·r t) ⋆ 1a       ≡⟨ cong (λ u → u ⋆ 1a) (·r-comm _ _) ⟩
               (t ·r s) ⋆ 1a       ≡⟨ ⋆Assoc t s 1a ⟩
               t ⋆ (s ⋆ 1a)        ≡⟨ cong (λ u → t ⋆ u) (sym (·IdR _)) ⟩
               t ⋆ ((s ⋆ 1a) · 1a) ≡⟨ ⋆AssocR t (s ⋆ 1a) 1a ⟩
               (s ⋆ 1a) · (t ⋆ 1a) ∎
      in eq i
    inducedMap (Construction.0-trunc P Q p q i j) =
      isSetAlgebra (CommAlgebra→Algebra A) (inducedMap P) (inducedMap Q) (cong _ p) (cong _ q) i j

    module _ where
      open IsAlgebraHom

      inducedHom : CommAlgebraHom (R [ I ]) A
      inducedHom .fst = inducedMap
      inducedHom .snd .pres0 = ⋆AnnihilL _
      inducedHom .snd .pres1 = imageOf1Works
      inducedHom .snd .pres+ x y = refl
      inducedHom .snd .pres· x y = refl
      inducedHom .snd .pres- x = refl
      inducedHom .snd .pres⋆ r x =
        (r ⋆ 1a) · inducedMap x ≡⟨ ⋆AssocL r 1a (inducedMap x) ⟩
        r ⋆ (1a · inducedMap x) ≡⟨ cong (λ u → r ⋆ u) (·IdL (inducedMap x)) ⟩
        r ⋆ inducedMap x ∎

  module _ (A : CommAlgebra R ℓ'') where
    open CommAlgebraStr (A .snd)
    open AlgebraTheory (CommRing→Ring R) (CommAlgebra→Algebra A)
    open Construction using (var; const) renaming (_+_ to _+c_; -_ to -c_; _·_ to _·c_)

    Hom = CommAlgebraHom  (R [ I ]) A
    open IsAlgebraHom

    evaluateAt : Hom → I → ⟨ A ⟩
    evaluateAt φ x = φ .fst (var x)

    mapRetrievable : ∀ (φ : I → ⟨ A ⟩)
                     → evaluateAt (inducedHom A φ) ≡ φ
    mapRetrievable φ = refl

    proveEq : ∀ {X : Type ℓ''} (isSetX : isSet X) (f g : ⟨ R [ I ] ⟩ → X)
              → (var-eq : (x : I) → f (var x) ≡ g (var x))
              → (const-eq : (r : ⟨ R ⟩) → f (const r) ≡ g (const r))
              → (+-eq : (x y : ⟨ R [ I ] ⟩) → (eq-x : f x ≡ g x) → (eq-y : f y ≡ g y)
                        → f (x +c y) ≡ g (x +c y))
              → (·-eq : (x y : ⟨ R [ I ] ⟩) → (eq-x : f x ≡ g x) → (eq-y : f y ≡ g y)
                        → f (x ·c y) ≡ g (x ·c y))
              → (-eq : (x : ⟨ R [ I ] ⟩) → (eq-x : f x ≡ g x)
                        → f (-c x) ≡ g (-c x))
              → f ≡ g
    proveEq isSetX f g var-eq const-eq +-eq ·-eq -eq i (var x) = var-eq x i
    proveEq isSetX f g var-eq const-eq +-eq ·-eq -eq i (const x) = const-eq x i
    proveEq isSetX f g var-eq const-eq +-eq ·-eq -eq i (x +c y) =
      +-eq x y
           (λ i → proveEq isSetX f g var-eq const-eq +-eq ·-eq -eq i x)
           (λ i → proveEq isSetX f g var-eq const-eq +-eq ·-eq -eq i y)
           i
    proveEq isSetX f g var-eq const-eq +-eq ·-eq -eq i (-c x) =
      -eq x ((λ i → proveEq isSetX f g var-eq const-eq +-eq ·-eq -eq i x)) i
    proveEq isSetX f g var-eq const-eq +-eq ·-eq -eq i (x ·c y) =
      ·-eq x y
           (λ i → proveEq isSetX f g var-eq const-eq +-eq ·-eq -eq i x)
           (λ i → proveEq isSetX f g var-eq const-eq +-eq ·-eq -eq i y)
           i
    proveEq isSetX f g var-eq const-eq +-eq ·-eq -eq i (Construction.+-assoc x y z j) =
       let
        rec : (x : ⟨ R [ I ] ⟩) → f x ≡ g x
        rec x = (λ i → proveEq isSetX f g var-eq const-eq +-eq ·-eq -eq i x)
        a₀₋ : f (x +c (y +c z)) ≡ g (x +c (y +c z))
        a₀₋ = +-eq _ _ (rec x) (+-eq _ _ (rec y) (rec z))
        a₁₋ : f ((x +c y) +c z) ≡ g ((x +c y) +c z)
        a₁₋ = +-eq _ _ (+-eq _ _ (rec x) (rec y)) (rec z)
        a₋₀ : f (x +c (y +c z)) ≡ f ((x +c y) +c z)
        a₋₀ = cong f (Construction.+-assoc x y z)
        a₋₁ : g (x +c (y +c z)) ≡ g ((x +c y) +c z)
        a₋₁ = cong g (Construction.+-assoc x y z)
      in isSet→isSet' isSetX a₀₋ a₁₋ a₋₀ a₋₁ j i

    proveEq isSetX f g var-eq const-eq +-eq ·-eq -eq i (Construction.+-rid x j) =
       let
        rec : (x : ⟨ R [ I ] ⟩) → f x ≡ g x
        rec x = (λ i → proveEq isSetX f g var-eq const-eq +-eq ·-eq -eq i x)
        a₀₋ : f (x +c (const 0r)) ≡ g (x +c (const 0r))
        a₀₋ = +-eq _ _ (rec x) (const-eq 0r)
        a₁₋ : f x ≡ g x
        a₁₋ = rec x
        a₋₀ : f (x +c (const 0r)) ≡ f x
        a₋₀ = cong f (Construction.+-rid x)
        a₋₁ : g (x +c (const 0r)) ≡ g x
        a₋₁ = cong g (Construction.+-rid x)
      in isSet→isSet' isSetX a₀₋ a₁₋ a₋₀ a₋₁ j i

    proveEq isSetX f g var-eq const-eq +-eq ·-eq -eq i (Construction.+-rinv x j) =
       let
        rec : (x : ⟨ R [ I ] ⟩) → f x ≡ g x
        rec x = (λ i → proveEq isSetX f g var-eq const-eq +-eq ·-eq -eq i x)
        a₀₋ : f (x +c (-c x)) ≡ g (x +c (-c x))
        a₀₋ = +-eq x (-c x) (rec x) (-eq x (rec x))
        a₁₋ : f (const 0r) ≡ g (const 0r)
        a₁₋ = const-eq 0r
        a₋₀ : f (x +c (-c x)) ≡ f (const 0r)
        a₋₀ = cong f (Construction.+-rinv x)
        a₋₁ : g (x +c (-c x)) ≡ g (const 0r)
        a₋₁ = cong g (Construction.+-rinv x)
      in isSet→isSet' isSetX a₀₋ a₁₋ a₋₀ a₋₁ j i

    proveEq isSetX f g var-eq const-eq +-eq ·-eq -eq i (Construction.+-comm x y j) =
      let
        rec : (x : ⟨ R [ I ] ⟩) → f x ≡ g x
        rec x = (λ i → proveEq isSetX f g var-eq const-eq +-eq ·-eq -eq i x)
        a₀₋ : f (x +c y) ≡ g (x +c y)
        a₀₋ = +-eq x y (rec x) (rec y)
        a₁₋ : f (y +c x) ≡ g (y +c x)
        a₁₋ = +-eq y x (rec y) (rec x)
        a₋₀ : f (x +c y) ≡ f (y +c x)
        a₋₀ = cong f (Construction.+-comm x y)
        a₋₁ : g (x +c y) ≡ g (y +c x)
        a₋₁ = cong g (Construction.+-comm x y)
      in isSet→isSet' isSetX a₀₋ a₁₋ a₋₀ a₋₁ j i

    proveEq isSetX f g var-eq const-eq +-eq ·-eq -eq i (Construction.·-assoc x y z j) =
       let
        rec : (x : ⟨ R [ I ] ⟩) → f x ≡ g x
        rec x = (λ i → proveEq isSetX f g var-eq const-eq +-eq ·-eq -eq i x)
        a₀₋ : f (x ·c (y ·c z)) ≡ g (x ·c (y ·c z))
        a₀₋ = ·-eq _ _ (rec x) (·-eq _ _ (rec y) (rec z))
        a₁₋ : f ((x ·c y) ·c z) ≡ g ((x ·c y) ·c z)
        a₁₋ = ·-eq _ _ (·-eq _ _ (rec x) (rec y)) (rec z)
        a₋₀ : f (x ·c (y ·c z)) ≡ f ((x ·c y) ·c z)
        a₋₀ = cong f (Construction.·-assoc x y z)
        a₋₁ : g (x ·c (y ·c z)) ≡ g ((x ·c y) ·c z)
        a₋₁ = cong g (Construction.·-assoc x y z)
      in isSet→isSet' isSetX a₀₋ a₁₋ a₋₀ a₋₁ j i

    proveEq isSetX f g var-eq const-eq +-eq ·-eq -eq i (Construction.·-lid x j) =
       let
        rec : (x : ⟨ R [ I ] ⟩) → f x ≡ g x
        rec x = (λ i → proveEq isSetX f g var-eq const-eq +-eq ·-eq -eq i x)
        a₀₋ : f ((const 1r) ·c x) ≡ g ((const 1r) ·c x)
        a₀₋ = ·-eq _ _ (const-eq 1r) (rec x)
        a₁₋ : f x ≡ g x
        a₁₋ = rec x
        a₋₀ : f ((const 1r) ·c x) ≡ f x
        a₋₀ = cong f (Construction.·-lid x)
        a₋₁ : g ((const 1r) ·c x) ≡ g x
        a₋₁ = cong g (Construction.·-lid x)
      in isSet→isSet' isSetX a₀₋ a₁₋ a₋₀ a₋₁ j i

    proveEq isSetX f g var-eq const-eq +-eq ·-eq -eq i (Construction.·-comm x y j) =
       let
        rec : (x : ⟨ R [ I ] ⟩) → f x ≡ g x
        rec x = (λ i → proveEq isSetX f g var-eq const-eq +-eq ·-eq -eq i x)
        a₀₋ : f (x ·c y) ≡ g (x ·c y)
        a₀₋ = ·-eq _ _ (rec x) (rec y)
        a₁₋ : f (y ·c x) ≡ g (y ·c x)
        a₁₋ = ·-eq _ _ (rec y) (rec x)
        a₋₀ : f (x ·c y) ≡ f (y ·c x)
        a₋₀ = cong f (Construction.·-comm x y)
        a₋₁ : g (x ·c y) ≡ g (y ·c x)
        a₋₁ = cong g (Construction.·-comm x y)
      in isSet→isSet' isSetX a₀₋ a₁₋ a₋₀ a₋₁ j i

    proveEq isSetX f g var-eq const-eq +-eq ·-eq -eq i (Construction.ldist x y z j) =
       let
        rec : (x : ⟨ R [ I ] ⟩) → f x ≡ g x
        rec x = (λ i → proveEq isSetX f g var-eq const-eq +-eq ·-eq -eq i x)
        a₀₋ : f ((x +c y) ·c z) ≡ g ((x +c y) ·c z)
        a₀₋ = ·-eq (x +c y) z
           (+-eq _ _ (rec x) (rec y))
           (rec z)
        a₁₋ : f ((x ·c z) +c (y ·c z)) ≡ g ((x ·c z) +c (y ·c z))
        a₁₋ = +-eq _ _ (·-eq _ _ (rec x) (rec z)) (·-eq _ _ (rec y) (rec z))
        a₋₀ : f ((x +c y) ·c z) ≡ f ((x ·c z) +c (y ·c z))
        a₋₀ = cong f (Construction.ldist x y z)
        a₋₁ : g ((x +c y) ·c z) ≡ g ((x ·c z) +c (y ·c z))
        a₋₁ = cong g (Construction.ldist x y z)
      in isSet→isSet' isSetX a₀₋ a₁₋ a₋₀ a₋₁ j i

    proveEq isSetX f g var-eq const-eq +-eq ·-eq -eq i (Construction.+HomConst s t j) =
       let
        rec : (x : ⟨ R [ I ] ⟩) → f x ≡ g x
        rec x = (λ i → proveEq isSetX f g var-eq const-eq +-eq ·-eq -eq i x)
        a₀₋ : f (const (s +r t)) ≡ g (const (s +r t))
        a₀₋ = const-eq (s +r t)
        a₁₋ : f (const s +c const t) ≡ g (const s +c const t)
        a₁₋ = +-eq _ _ (const-eq s) (const-eq t)
        a₋₀ : f (const (s +r t)) ≡ f (const s +c const t)
        a₋₀ = cong f (Construction.+HomConst s t)
        a₋₁ : g (const (s +r t)) ≡ g (const s +c const t)
        a₋₁ = cong g (Construction.+HomConst s t)
      in isSet→isSet' isSetX a₀₋ a₁₋ a₋₀ a₋₁ j i

    proveEq isSetX f g var-eq const-eq +-eq ·-eq -eq i (Construction.·HomConst s t j) =
       let
        rec : (x : ⟨ R [ I ] ⟩) → f x ≡ g x
        rec x = (λ i → proveEq isSetX f g var-eq const-eq +-eq ·-eq -eq i x)
        a₀₋ : f (const (s ·r t)) ≡ g (const (s ·r t))
        a₀₋ = const-eq (s ·r t)
        a₁₋ : f (const s ·c const t) ≡ g (const s ·c const t)
        a₁₋ = ·-eq _ _ (const-eq s) (const-eq t)
        a₋₀ : f (const (s ·r t)) ≡ f (const s ·c const t)
        a₋₀ = cong f (Construction.·HomConst s t)
        a₋₁ : g (const (s ·r t)) ≡ g (const s ·c const t)
        a₋₁ = cong g (Construction.·HomConst s t)
      in isSet→isSet' isSetX a₀₋ a₁₋ a₋₀ a₋₁ j i

    proveEq isSetX f g var-eq const-eq +-eq ·-eq -eq i (Construction.0-trunc x y p q j k) =
      let
        P : (x : ⟨ R [ I ] ⟩) → f x ≡ g x
        P x i = proveEq isSetX f g var-eq const-eq +-eq ·-eq -eq i x
        Q : (x : ⟨ R [ I ] ⟩) → f x ≡ g x
        Q x i = proveEq isSetX f g var-eq const-eq +-eq ·-eq -eq i x
      in isOfHLevel→isOfHLevelDep 2
           (λ z → isProp→isSet (isSetX (f z) (g z))) _ _
           (cong P p)
           (cong Q q)
           (Construction.0-trunc x y p q) j k i


    homRetrievable : ∀ (f : Hom)
                     → inducedMap A (evaluateAt f) ≡ fst f
    homRetrievable f =
       proveEq
        (isSetAlgebra (CommAlgebra→Algebra A))
        (inducedMap A (evaluateAt f))
        (λ x → f $a x)
        (λ x → refl)
        (λ r → r ⋆ 1a                     ≡⟨ cong (λ u → r ⋆ u) (sym f.pres1) ⟩
                r ⋆ (f $a (const 1r))      ≡⟨ sym (f.pres⋆ r _) ⟩
                f $a (const r ·c const 1r) ≡⟨ cong (λ u → f $a u) (sym (Construction.·HomConst r 1r)) ⟩
                f $a (const (r ·r 1r))     ≡⟨ cong (λ u → f $a (const u)) (·r-rid r) ⟩
                f $a (const r) ∎)

        (λ x y eq-x eq-y →
              ι (x +c y)            ≡⟨ refl ⟩
              (ι x + ι y)           ≡⟨ cong (λ u → u + ι y) eq-x ⟩
              ((f $a x) + ι y)      ≡⟨
                                     cong (λ u → (f $a x) + u) eq-y ⟩
              ((f $a x) + (f $a y)) ≡⟨ sym (f.pres+ _ _) ⟩ (f $a (x +c y)) ∎)

        (λ x y eq-x eq-y →
           ι (x ·c y)          ≡⟨ refl ⟩
           ι x     · ι y       ≡⟨ cong (λ u → u · ι y) eq-x ⟩
           (f $a x) · (ι y)    ≡⟨ cong (λ u → (f $a x) · u) eq-y ⟩
           (f $a x) · (f $a y) ≡⟨ sym (f.pres· _ _) ⟩
           f $a (x ·c y) ∎)
       (λ x eq-x →
           ι (-c x)    ≡⟨ refl ⟩
           - ι x       ≡⟨ cong (λ u → - u) eq-x ⟩
           - (f $a x)  ≡⟨ sym (f.pres- x) ⟩
           f $a (-c x) ∎)
      where
      ι = inducedMap A (evaluateAt f)
      module f = IsAlgebraHom (f .snd)


evaluateAt : {R : CommRing ℓ} {I : Type ℓ'} (A : CommAlgebra R ℓ'')
             (f : CommAlgebraHom (R [ I ]) A)
             → (I → fst A)
evaluateAt A f x = f $a (Construction.var x)

inducedHom : {R : CommRing ℓ} {I : Type ℓ'} (A : CommAlgebra R ℓ'')
             (φ : I → fst A )
             → CommAlgebraHom (R [ I ]) A
inducedHom A φ = Theory.inducedHom A φ


homMapIso : {R : CommRing ℓ} {I : Type ℓ''} (A : CommAlgebra R ℓ')
             → Iso (CommAlgebraHom (R [ I ]) A) (I → (fst A))
Iso.fun (homMapIso A) = evaluateAt A
Iso.inv (homMapIso A) = inducedHom A
Iso.rightInv (homMapIso A) = λ ϕ → Theory.mapRetrievable A ϕ
Iso.leftInv (homMapIso {R = R} {I = I} A) =
  λ f → Σ≡Prop (λ f → isPropIsCommAlgebraHom {M = R [ I ]} {N = A} f)
               (Theory.homRetrievable A f)

inducedHomUnique :
  {R : CommRing ℓ} {I : Type ℓ'} (A : CommAlgebra R ℓ'') (φ : I → fst A )
  → (f : CommAlgebraHom (R [ I ]) A) → ((i : I) → fst f (Construction.var i) ≡ φ i)
  → f ≡ inducedHom A φ
inducedHomUnique {I = I} A φ f p =
  isoFunInjective (homMapIso A) f (inducedHom A φ) λ j i → p i j

homMapPath : {R : CommRing ℓ} {I : Type ℓ'} (A : CommAlgebra R (ℓ-max ℓ ℓ'))
             → CommAlgebraHom (R [ I ]) A ≡ (I → fst A)
homMapPath A = isoToPath (homMapIso A)

{- Corollary: Two homomorphisms with the same values on generators are equal -}
equalByUMP : {R : CommRing ℓ} {I : Type ℓ'}
           → (A : CommAlgebra R ℓ'')
           → (f g : CommAlgebraHom (R [ I ]) A)
           → ((i : I) → fst f (Construction.var i) ≡ fst g (Construction.var i))
           → (x : ⟨ R [ I ] ⟩) → fst f x ≡ fst g x
equalByUMP {R = R} {I = I} A f g = funExt⁻ ∘ cong fst ∘ isoFunInjective (homMapIso A) f g ∘ funExt

{- A corollary, which is useful for constructing isomorphisms to
   algebras with the same universal property -}
isIdByUMP : {R : CommRing ℓ} {I : Type ℓ'}
          → (f : CommAlgebraHom (R [ I ]) (R [ I ]))
          → ((i : I) → fst f (Construction.var i) ≡ Construction.var i)
          → (x : ⟨ R [ I ] ⟩) → fst f x ≡ x
isIdByUMP {R = R} {I = I} f p = equalByUMP (R [ I ]) f (idCAlgHom (R [ I ])) p

-- The homomorphism induced by the variables is the identity.
inducedHomVar : (R : CommRing ℓ) (I : Type ℓ')
              → inducedHom (R [ I ]) Construction.var ≡ idCAlgHom (R [ I ])
inducedHomVar R I = isoFunInjective (homMapIso (R [ I ])) _ _ refl

module _ {R : CommRing ℓ} {A B : CommAlgebra R ℓ''} where
  open AlgebraHoms
  A′ = CommAlgebra→Algebra A
  B′ = CommAlgebra→Algebra B
  R′ = (CommRing→Ring R)
  ν : AlgebraHom A′ B′ → (⟨ A ⟩ → ⟨ B ⟩)
  ν φ = φ .fst

  {-
    Hom(R[I],A) → (I → A)
         ↓          ↓ψ
    Hom(R[I],B) → (I → B)
  -}
  naturalEvR : {I : Type ℓ'} (ψ : CommAlgebraHom A B)
             (f : CommAlgebraHom (R [ I ]) A)
             → (fst ψ) ∘ evaluateAt A f ≡ evaluateAt B (ψ ∘a f)
  naturalEvR ψ f = refl

  {-
    Hom(R[I],A) ← (I → A)
         ↓          ↓ψ
    Hom(R[I],B) ← (I → B)
  -}
  natIndHomR : {I : Type ℓ'} (ψ : CommAlgebraHom A B)
               (ϕ : I → ⟨ A ⟩)
               → ψ ∘a inducedHom A ϕ ≡ inducedHom B (fst ψ ∘ ϕ)
  natIndHomR ψ ϕ = isoFunInjective (homMapIso B) _ _
                (evaluateAt B (ψ ∘a (inducedHom A ϕ))        ≡⟨ refl ⟩
                 fst ψ ∘ evaluateAt A (inducedHom A ϕ)       ≡⟨ refl ⟩
                 fst ψ ∘ ϕ                                   ≡⟨ Iso.rightInv (homMapIso B) _ ⟩
                 evaluateAt B (inducedHom B (fst ψ ∘ ϕ))     ∎)

  {-
    Hom(R[I],A) → (I → A)
         ↓          ↓
    Hom(R[J],A) → (J → A)
  -}
  naturalEvL : {I J : Type ℓ'} (φ : J → I)
             (f : CommAlgebraHom (R [ I ]) A)
             → (evaluateAt A f) ∘ φ
               ≡ evaluateAt A (f ∘a (inducedHom (R [ I ]) (λ x → Construction.var (φ x))))
  naturalEvL φ f = refl

module _ {R : CommRing ℓ} where
  {-
    Prove that the FreeCommAlgebra over R on zero generators is
    isomorphic to the initial R-Algebra - R itsself.
  -}
  freeOn⊥ : CommAlgebraEquiv (R [ ⊥ ]) (initialCAlg R)
  freeOn⊥ =
     equivByInitiality
        R (R [ ⊥ ])
          {- Show that R[⊥] has the universal property of the
             initial R-Algbera and conclude that those are isomorphic -}
        λ B →  let to : CommAlgebraHom (R [ ⊥ ]) B → (⊥ → fst B)
                   to = evaluateAt B

                   from :  (⊥ → fst B) → CommAlgebraHom (R [ ⊥ ]) B
                   from = inducedHom B

                   from-to : (x : _) → from (to x) ≡ x
                   from-to x =
                     Σ≡Prop (λ f → isPropIsCommAlgebraHom {M = R [ ⊥ ]} {N = B} f)
                            (Theory.homRetrievable B x)

                   equiv : CommAlgebraHom (R [ ⊥ ]) B ≃ (⊥ → fst B)
                   equiv =
                     isoToEquiv
                       (iso to from (λ x → isContr→isOfHLevel 1 isContr⊥→A _ _) from-to)
               in isOfHLevelRespectEquiv 0 (invEquiv equiv) isContr⊥→A

module _ {R : CommRing ℓ} {I : Type ℓ} where
  baseRingHom : CommRingHom R (CommAlgebra→CommRing (R [ I ]))
  baseRingHom = snd (Iso.fun (CommAlgChar.CommAlgIso R) (R [ I ]))
