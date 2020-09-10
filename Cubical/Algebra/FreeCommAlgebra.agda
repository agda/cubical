{-# OPTIONS --cubical --safe --no-import-sorts #-}

module Cubical.Algebra.FreeCommAlgebra where
{-
  The free commutative algebra over a commutative ring,
  or in other words the ring of polynomials with coefficients in a given ring.
  Note that this is a constructive definition, which entails that polynomials
  cannot be represented by lists of coefficients, where the last one is non-zero.
  For rings with decidable equality, that is still possible.

  I learned about this (and other) definition(s) from David Jaz Myers.
  You can watch him talk about these things here:
  https://www.youtube.com/watch?v=VNp-f_9MnVk

  This file contains
  * the definition of the free commutative algebra on a type I over a commutative ring R as a HIT
    (let us call that R[I])
  * a prove that the construction is an commutative R-algebra
  * definitions of the induced maps appearing in the universal property of R[I],
    that is:  * for any map I → A, where A is a commutative R-algebra,
                the induced algebra homomorphism R[I] → A
                ('inducedHom')
              * for any hom R[I] → A, the 'restricttion to variables' I → A
                ('evaluateAt')
  * a proof that the two constructions are inverse to each other
    ('homRetrievable' and 'mapRetrievable')
  * a proof, that the corresponding pointwise equivalence of functors is natural
    ('naturalR', 'naturalL')
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function hiding (const)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring        using ()
open import Cubical.Algebra.CommAlgebra renaming (⟨_⟩ to ⟨_⟩a)
open import Cubical.Algebra.Algebra     hiding (⟨_⟩)
open import Cubical.HITs.SetTruncation

private
  variable
    ℓ ℓ′ : Level

module Construction (R : CommRing {ℓ}) where
  open CommRing R using (1r; 0r) renaming (_+_ to _+r_; _·_ to _·r_)

  data R[_] (I : Type ℓ′) : Type (ℓ-max ℓ ℓ′) where
    var : I → R[ I ]
    const : ⟨ R ⟩ → R[ I ]
    _+_ : R[ I ] → R[ I ] → R[ I ]
    -_ : R[ I ] → R[ I ]
    _·_ : R[ I ] → R[ I ] → R[ I ]            -- \cdot

    +-assoc : (x y z : R[ I ]) → x + (y + z) ≡ (x + y) + z
    +-rid : (x : R[ I ]) → x + (const 0r) ≡ x
    +-rinv : (x : R[ I ]) → x + (- x) ≡ (const 0r)
    +-comm : (x y : R[ I ]) → x + y ≡ y + x

    ·-assoc : (x y z : R[ I ]) → x · (y · z) ≡ (x · y) · z
    ·-lid : (x : R[ I ]) → (const 1r) · x ≡ x
    ·-comm : (x y : R[ I ]) → x · y ≡ y · x

    ldist : (x y z : R[ I ]) → (x + y) · z ≡ (x · z) + (y · z)

    +HomConst : (s t : ⟨ R ⟩) → const (s +r t) ≡ const s + const t
    ·HomConst : (s t : ⟨ R ⟩) → const (s ·r t) ≡ (const s) · (const t)

    0-trunc : (x y : R[ I ]) (p q : x ≡ y) → p ≡ q

  _⋆_ : {I : Type ℓ′} → ⟨ R ⟩ → R[ I ] → R[ I ]
  r ⋆ x = const r · x

  ⋆-assoc : {I : Type ℓ′} → (s t : ⟨ R ⟩) (x : R[ I ]) → (s ·r t) ⋆ x ≡ s ⋆ (t ⋆ x)
  ⋆-assoc s t x = const (s ·r t) · x       ≡⟨ cong (λ u → u · x) (·HomConst _ _) ⟩
                  (const s · const t) · x  ≡⟨ sym (·-assoc _ _ _) ⟩
                  const s · (const t · x)  ≡⟨ refl ⟩
                  s ⋆ (t ⋆ x) ∎

  ⋆-ldist-+ : {I : Type ℓ′} → (s t : ⟨ R ⟩) (x : R[ I ]) → (s +r t) ⋆ x ≡ (s ⋆ x) + (t ⋆ x)
  ⋆-ldist-+ s t x = (s +r t) ⋆ x             ≡⟨ cong (λ u → u · x) (+HomConst _ _) ⟩
                    (const s + const t) · x  ≡⟨ ldist _ _ _ ⟩
                    (s ⋆ x) + (t ⋆ x) ∎

  ⋆-rdist-+ : {I : Type ℓ′} → (s : ⟨ R ⟩) (x y : R[ I ]) → s ⋆ (x + y) ≡ (s ⋆ x) + (s ⋆ y)
  ⋆-rdist-+ s x y = const s · (x + y)             ≡⟨ ·-comm _ _ ⟩
                    (x + y) · const s             ≡⟨ ldist _ _ _ ⟩
                    (x · const s) + (y · const s) ≡⟨ cong (λ u → u + (y · const s)) (·-comm _ _) ⟩
                    (s ⋆ x) + (y · const s)       ≡⟨ cong (λ u → (s ⋆ x) + u) (·-comm _ _)  ⟩
                    (s ⋆ x) + (s ⋆ y) ∎

  ⋆-assoc-· : {I : Type ℓ′} → (s : ⟨ R ⟩) (x y : R[ I ]) → (s ⋆ x) · y ≡ s ⋆ (x · y)
  ⋆-assoc-· s x y = (s ⋆ x) · y ≡⟨ sym (·-assoc _ _ _) ⟩
                    s ⋆ (x · y) ∎

  0a : {I : Type ℓ′} → R[ I ]
  0a = (const 0r)

  1a : {I : Type ℓ′} → R[ I ]
  1a = (const 1r)

  isCommAlgebra : {I : Type ℓ} → IsCommAlgebra
                                   R {A = R[ I ]}
                                   0a 1a
                                   _+_ _·_ -_ _⋆_
  isCommAlgebra = makeIsCommAlgebra 0-trunc
                                    +-assoc +-rid +-rinv +-comm
                                    ·-assoc ·-lid ldist ·-comm
                                    ⋆-assoc ⋆-ldist-+ ⋆-rdist-+ ·-lid ⋆-assoc-·

_[_] : (R : CommRing {ℓ}) (I : Type ℓ) → CommAlgebra R
R [ I ] = let open Construction R
          in commalgebra R[ I ] 0a 1a _+_ _·_ -_ _⋆_ isCommAlgebra


module Theory {R : CommRing {ℓ}} {I : Type ℓ} where
  open CommRing R using (0r; 1r) renaming (_·_ to _·r_; _+_ to _+r_; ·-comm to ·r-comm; ·-rid to ·r-rid)

  module _ (A : CommAlgebra R) (φ : I → ⟨ A ⟩a) where
    open CommAlgebra A
    open AlgebraTheory (CommRing→Ring R) (CommAlgebra→Algebra A)
    open Construction using (var; const) renaming (_+_ to _+c_; -_ to -c_; _·_ to _·c_)

    imageOf0Works : 0r ⋆ 1a ≡ 0a
    imageOf0Works = 0-actsNullifying 1a

    imageOf1Works : 1r ⋆ 1a ≡ 1a
    imageOf1Works = ⋆-lid 1a

    inducedMap : ⟨ R [ I ] ⟩a → ⟨ A ⟩a
    inducedMap (var x) = φ x
    inducedMap (const r) = r ⋆ 1a
    inducedMap (P +c Q) = (inducedMap P) + (inducedMap Q)
    inducedMap (-c P) = - inducedMap P
    inducedMap (Construction.+-assoc P Q S i) = +-assoc (inducedMap P) (inducedMap Q) (inducedMap S) i
    inducedMap (Construction.+-rid P i) =
      let
        eq : (inducedMap P) + (inducedMap (const 0r)) ≡ (inducedMap P)
        eq = (inducedMap P) + (inducedMap (const 0r)) ≡⟨ refl ⟩
             (inducedMap P) + (0r ⋆ 1a)               ≡⟨ cong
                                                         (λ u → (inducedMap P) + u)
                                                         (imageOf0Works) ⟩
             (inducedMap P) + 0a                      ≡⟨ +-rid _ ⟩
             (inducedMap P) ∎
      in eq i
    inducedMap (Construction.+-rinv P i) =
      let eq : (inducedMap P - inducedMap P) ≡ (inducedMap (const 0r))
          eq = (inducedMap P - inducedMap P) ≡⟨ +-rinv _ ⟩
               0a                            ≡⟨ sym imageOf0Works ⟩
               (inducedMap (const 0r))∎
      in eq i
    inducedMap (Construction.+-comm P Q i) = +-comm (inducedMap P) (inducedMap Q) i
    inducedMap (P ·c Q) = inducedMap P · inducedMap Q
    inducedMap (Construction.·-assoc P Q S i) = ·-assoc (inducedMap P) (inducedMap Q) (inducedMap S) i
    inducedMap (Construction.·-lid P i) =
      let eq = inducedMap (const 1r) · inducedMap P ≡⟨ cong (λ u → u · inducedMap P) imageOf1Works ⟩
               1a · inducedMap P                    ≡⟨ ·-lid (inducedMap P) ⟩
               inducedMap P ∎
      in eq i
    inducedMap (Construction.·-comm P Q i) = ·-comm (inducedMap P) (inducedMap Q) i
    inducedMap (Construction.ldist P Q S i) = ·-ldist-+ (inducedMap P) (inducedMap Q) (inducedMap S) i
    inducedMap (Construction.+HomConst s t i) = ⋆-ldist s t 1a i
    inducedMap (Construction.·HomConst s t i) =
      let eq = (s ·r t) ⋆ 1a       ≡⟨ cong (λ u → u ⋆ 1a) (·r-comm _ _) ⟩
               (t ·r s) ⋆ 1a       ≡⟨ ⋆-assoc t s 1a ⟩
               t ⋆ (s ⋆ 1a)        ≡⟨ cong (λ u → t ⋆ u) (sym (·-rid _)) ⟩
               t ⋆ ((s ⋆ 1a) · 1a) ≡⟨ ⋆-rassoc t (s ⋆ 1a) 1a ⟩
               (s ⋆ 1a) · (t ⋆ 1a) ∎
      in eq i
    inducedMap (Construction.0-trunc P Q p q i j) =
      isSetAlgebra (CommAlgebra→Algebra A) (inducedMap P) (inducedMap Q) (cong _ p) (cong _ q) i j

    inducedHom : AlgebraHom (CommAlgebra→Algebra (R [ I ])) (CommAlgebra→Algebra A)
    inducedHom = algebrahom
                   inducedMap
                   (λ x y → refl)
                   (λ x y → refl)
                   imageOf1Works
                   λ r x → (r ⋆ 1a) · inducedMap x ≡⟨ ⋆-lassoc r 1a (inducedMap x) ⟩
                           r ⋆ (1a · inducedMap x) ≡⟨ cong (λ u → r ⋆ u) (·-lid (inducedMap x)) ⟩
                           r ⋆ inducedMap x ∎

  module _ (A : CommAlgebra R) where
    open CommAlgebra A
    open AlgebraTheory (CommRing→Ring R) (CommAlgebra→Algebra A)
    open Construction using (var; const) renaming (_+_ to _+c_; -_ to -c_; _·_ to _·c_)

    Hom = AlgebraHom (CommAlgebra→Algebra (R [ I ])) (CommAlgebra→Algebra A)
    open AlgebraHom

    evaluateAt : Hom
                 → I → ⟨ A ⟩a
    evaluateAt (algebrahom f _ _ _ _) x = f (var x)

    mapRetrievable : ∀ (φ : I → ⟨ A ⟩a)
                     → evaluateAt (inducedHom A φ) ≡ φ
    mapRetrievable φ = refl

    proveEq : ∀ {X : Type ℓ} (isSetX : isSet X) (f g : ⟨ R [ I ] ⟩a → X)
              → (var-eq : (x : I) → f (var x) ≡ g (var x))
              → (const-eq : (r : ⟨ R ⟩) → f (const r) ≡ g (const r))
              → (+-eq : (x y : ⟨ R [ I ] ⟩a) → (eq-x : f x ≡ g x) → (eq-y : f y ≡ g y)
                        → f (x +c y) ≡ g (x +c y))
              → (·-eq : (x y : ⟨ R [ I ] ⟩a) → (eq-x : f x ≡ g x) → (eq-y : f y ≡ g y)
                        → f (x ·c y) ≡ g (x ·c y))
              → (-eq : (x : ⟨ R [ I ] ⟩a) → (eq-x : f x ≡ g x)
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
        rec : (x : ⟨ R [ I ] ⟩a) → f x ≡ g x
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
        rec : (x : ⟨ R [ I ] ⟩a) → f x ≡ g x
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
        rec : (x : ⟨ R [ I ] ⟩a) → f x ≡ g x
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
        rec : (x : ⟨ R [ I ] ⟩a) → f x ≡ g x
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
        rec : (x : ⟨ R [ I ] ⟩a) → f x ≡ g x
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
        rec : (x : ⟨ R [ I ] ⟩a) → f x ≡ g x
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
        rec : (x : ⟨ R [ I ] ⟩a) → f x ≡ g x
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
        rec : (x : ⟨ R [ I ] ⟩a) → f x ≡ g x
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
        rec : (x : ⟨ R [ I ] ⟩a) → f x ≡ g x
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
        rec : (x : ⟨ R [ I ] ⟩a) → f x ≡ g x
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
        P : (x : ⟨ R [ I ] ⟩a) → f x ≡ g x
        P x i = proveEq isSetX f g var-eq const-eq +-eq ·-eq -eq i x
        Q : (x : ⟨ R [ I ] ⟩a) → f x ≡ g x
        Q x i = proveEq isSetX f g var-eq const-eq +-eq ·-eq -eq i x
      in isOfHLevel→isOfHLevelDep 2
           (λ z → isProp→isSet (isSetX (f z) (g z))) _ _
           (cong P p)
           (cong Q q)
           (Construction.0-trunc x y p q) j k i


    homRetrievable : ∀ (f : Hom)
                     → inducedMap A (evaluateAt f) ≡ AlgebraHom.f f
    homRetrievable f =
      let
        ι = inducedMap A (evaluateAt f)
      in proveEq
          (isSetAlgebra (CommAlgebra→Algebra A))
          (inducedMap A (evaluateAt f))
          (λ x → f $a x)
          (λ x → refl)
          (λ r → r ⋆ 1a                     ≡⟨ cong (λ u → r ⋆ u) (sym (pres1 f)) ⟩
                 r ⋆ (f $a (const 1r))      ≡⟨ sym (comm⋆ f r _) ⟩
                 f $a (const r ·c const 1r) ≡⟨ cong (λ u → f $a u) (sym (Construction.·HomConst r 1r)) ⟩
                 f $a (const (r ·r 1r))     ≡⟨ cong (λ u → f $a (const u)) (·r-rid r) ⟩
                 f $a (const r) ∎)

          (λ x y eq-x eq-y →
                ι (x +c y)            ≡⟨ refl ⟩
                (ι x + ι y)           ≡⟨ cong (λ u → u + ι y) eq-x ⟩
                ((f $a x) + ι y)      ≡⟨
                                       cong (λ u → (f $a x) + u) eq-y ⟩
                ((f $a x) + (f $a y)) ≡⟨ sym (isHom+ f _ _) ⟩ (f $a (x +c y)) ∎)

          (λ x y eq-x eq-y →
             ι (x ·c y)          ≡⟨ refl ⟩
             ι x     · ι y       ≡⟨ cong (λ u → u · ι y) eq-x ⟩
             (f $a x) · (ι y)    ≡⟨ cong (λ u → (f $a x) · u) eq-y ⟩
             (f $a x) · (f $a y) ≡⟨ sym (isHom· f _ _) ⟩
             f $a (x ·c y) ∎)
         (λ x eq-x →
             ι (-c x)    ≡⟨ refl ⟩
             - ι x       ≡⟨ cong (λ u → - u) eq-x ⟩
             - (f $a x)  ≡⟨ sym (isHom- f x) ⟩
             f $a (-c x) ∎)

evaluateAt : {R : CommRing {ℓ}} {I : Type ℓ} (A : CommAlgebra R)
             (f : AlgebraHom (CommAlgebra→Algebra (R [ I ])) (CommAlgebra→Algebra A))
             → (I → ⟨ A ⟩a)
evaluateAt A f x = f $a (Construction.var x)

inducedHom : {R : CommRing {ℓ}} {I : Type ℓ} (A : CommAlgebra R)
             (φ : I → ⟨ A ⟩a)
             → AlgebraHom (CommAlgebra→Algebra (R [ I ])) (CommAlgebra→Algebra A)
inducedHom A φ = Theory.inducedHom A φ

module _ {R : CommRing {ℓ}} {A B : CommAlgebra R} where
  A′ = CommAlgebra→Algebra A
  B′ = CommAlgebra→Algebra B
  R′ = (CommRing→Ring R)
  ν : AlgebraHom A′ B′ → (⟨ A ⟩a → ⟨ B ⟩a)
  ν (algebrahom f _ _ _ _) = f

  {-
    Hom(R[I],A) → (I → A)
         ↓          ↓
    Hom(R[I],B) → (I → B)
  -}
  naturalR : {I : Type ℓ} (ψ : AlgebraHom A′ B′)
             (f : AlgebraHom (CommAlgebra→Algebra (R [ I ])) A′)
             → (ν ψ) ∘ evaluateAt A f ≡ evaluateAt B (ψ ∘a f)
  naturalR ψ f = refl

  {-
    Hom(R[I],A) → (I → A)
         ↓          ↓
    Hom(R[J],A) → (J → A)
  -}
  naturalL : {I J : Type ℓ} (φ : J → I)
             (f : AlgebraHom (CommAlgebra→Algebra (R [ I ])) A′)
             → (evaluateAt A f) ∘ φ
               ≡ evaluateAt A (f ∘a (inducedHom (R [ I ]) (λ x → Construction.var (φ x))))
  naturalL φ f = refl
