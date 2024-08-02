{-# OPTIONS --safe #-}

module Cubical.Algebra.CommRing.Instances.Polynomials.Typevariate.Properties where
{-
  This file contains
  * an elimination principle for proving some proposition for all elements of R[I]
    ('elimProp')
  * definitions of the induced maps appearing in the universal property of R[I],
    that is:  * for any map I → A, where A is a commutative R-algebra,
                the induced algebra homomorphism R[I] → A
                ('inducedHom')
              * for any hom R[I] → A, the 'restricttion to variables' I → A
                ('evaluateAt')
  * a proof that the two constructions are inverse to each other
    ('homMapIso')
  * proofs that the constructions are natural in various ways
  * a proof that the Polynomials on zero generators are the initial R-Algebra
    ('freeOn⊥')
-}

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
open import Cubical.Algebra.CommRing.Instances.Polynomials.Typevariate.Base
open import Cubical.Algebra.Ring.Properties

open import Cubical.Data.Empty
open import Cubical.Data.Sigma

open import Cubical.Tactics.CommRingSolver

private
  variable
    ℓ ℓ' ℓ'' : Level

module _ {R : CommRing ℓ} {I : Type ℓ'} where
  open CommRingStr ⦃...⦄ -- (snd R)
  private instance
    _ = snd R
    _ = snd (R [ I ]ᵣ)

  module C = Construction
  open C using (var; const)

  {-
    Construction of the 'elimProp' eliminator.
  -}
  module _
    {P : ⟨ R [ I ]ᵣ ⟩ → Type ℓ''}
    (isPropP : {x : _} → isProp (P x))
    (onVar : {x : I} → P (var x))
    (onConst : {r : ⟨ R ⟩} → P (const r))
    (on+ : {x y : ⟨ R [ I ]ᵣ ⟩} → P x → P y → P (x + y))
    (on· : {x y : ⟨ R [ I ]ᵣ ⟩} → P x → P y → P (x · y))
    where

    private
      on- : {x : ⟨ R [ I ]ᵣ ⟩} → P x → P (- x)
      on- {x} Px = subst P (minusByMult x) (on· onConst Px)
        where minusByMult : (x : _) → (const (- 1r)) · x ≡ - x
              minusByMult x =
                (const (- 1r)) · x ≡⟨ cong (_· x) (pres- 1r) ⟩
                (- const (1r)) · x ≡⟨ cong (λ u → (- u) · x) pres1 ⟩
                (- 1r) · x         ≡⟨ sym (-IsMult-1 x) ⟩
                - x  ∎
                where open RingTheory (CommRing→Ring (R [ I ]ᵣ)) using (-IsMult-1)
                      open IsCommRingHom (constPolynomial R I .snd)

      -- A helper to deal with the path constructor cases.
      mkPathP :
        {x0 x1 : ⟨ R [ I ]ᵣ ⟩} →
        (p : x0 ≡ x1) →
        (Px0 : P (x0)) →
        (Px1 : P (x1)) →
        PathP (λ i → P (p i)) Px0 Px1
      mkPathP _ = isProp→PathP λ i → isPropP

    elimProp : ((x : _) → P x)

    elimProp (var _) = onVar
    elimProp (const _) = onConst
    elimProp (x C.+ y) = on+ (elimProp x) (elimProp y)
    elimProp (C.- x) = on- (elimProp x)
    elimProp (x C.· y) = on· (elimProp x) (elimProp y)

    elimProp (C.+-assoc x y z i) =
      mkPathP (C.+-assoc x y z)
        (on+ (elimProp x) (on+ (elimProp y) (elimProp z)))
        (on+ (on+ (elimProp x) (elimProp y)) (elimProp z))
        i
    elimProp (C.+-rid x i) =
      mkPathP (C.+-rid x)
        (on+ (elimProp x) onConst)
        (elimProp x)
        i
    elimProp (C.+-rinv x i) =
      mkPathP (C.+-rinv x)
        (on+ (elimProp x) (on- (elimProp x)))
        onConst
        i
    elimProp (C.+-comm x y i) =
      mkPathP (C.+-comm x y)
        (on+ (elimProp x) (elimProp y))
        (on+ (elimProp y) (elimProp x))
        i
    elimProp (C.·-assoc x y z i) =
      mkPathP (C.·-assoc x y z)
        (on· (elimProp x) (on· (elimProp y) (elimProp z)))
        (on· (on· (elimProp x) (elimProp y)) (elimProp z))
        i
    elimProp (C.·-lid x i) =
      mkPathP (C.·-lid x)
        (on· onConst (elimProp x))
        (elimProp x)
        i
    elimProp (C.·-comm x y i) =
      mkPathP (C.·-comm x y)
        (on· (elimProp x) (elimProp y))
        (on· (elimProp y) (elimProp x))
        i
    elimProp (C.ldist x y z i) =
      mkPathP (C.ldist x y z)
        (on· (on+ (elimProp x) (elimProp y)) (elimProp z))
        (on+ (on· (elimProp x) (elimProp z)) (on· (elimProp y) (elimProp z)))
        i
    elimProp (C.+HomConst s t i) =
      mkPathP (C.+HomConst s t)
        onConst
        (on+ onConst onConst)
        i
    elimProp (C.·HomConst s t i) =
      mkPathP (C.·HomConst s t)
        onConst
        (on· onConst onConst)
        i

    elimProp (C.0-trunc x y p q i j) =
      isOfHLevel→isOfHLevelDep 2 (λ _ → isProp→isSet isPropP)
        (elimProp x)
        (elimProp y)
        (cong elimProp p)
        (cong elimProp q)
        (C.0-trunc x y p q)
        i
        j

  {-
    Construction of the induced map.
  -}
  module _ (S : CommRing ℓ'') (f : CommRingHom R S) (φ : I → ⟨ S ⟩) where
    private instance
      _ = S .snd

    open IsCommRingHom

    inducedMap : ⟨ R [ I ]ᵣ ⟩ → ⟨ S ⟩
    inducedMap (var x) = φ x
    inducedMap (const r) = (f .fst r)
    inducedMap (P C.+ Q) = (inducedMap P) + (inducedMap Q)
    inducedMap (C.- P) = - inducedMap P
    inducedMap (C.+-assoc P Q S i) = +Assoc (inducedMap P) (inducedMap Q) (inducedMap S) i
    inducedMap (C.+-rid P i) =
      let
        eq : (inducedMap P) + (inducedMap (const 0r)) ≡ (inducedMap P)
        eq = (inducedMap P) + (inducedMap (const 0r)) ≡⟨⟩
             (inducedMap P) + ((f .fst 0r))           ≡⟨ cong ((inducedMap P) +_) (pres0 (f .snd)) ⟩
             (inducedMap P) + 0r                      ≡⟨ +IdR _ ⟩
             (inducedMap P) ∎
      in eq i
    inducedMap (C.+-rinv P i) =
      let eq : (inducedMap P - inducedMap P) ≡ (inducedMap (const 0r))
          eq = (inducedMap P - inducedMap P) ≡⟨ +InvR _ ⟩
               0r                            ≡⟨ sym (pres0 (f .snd)) ⟩
               (inducedMap (const 0r))∎
      in eq i
    inducedMap (C.+-comm P Q i) = +Comm (inducedMap P) (inducedMap Q) i
    inducedMap (P C.· Q) = inducedMap P · inducedMap Q
    inducedMap (C.·-assoc P Q S i) = ·Assoc (inducedMap P) (inducedMap Q) (inducedMap S) i
    inducedMap (C.·-lid P i) =
      let eq = inducedMap (const 1r) · inducedMap P ≡⟨ cong (λ u → u · inducedMap P) (pres1 (f .snd)) ⟩
               1r · inducedMap P                    ≡⟨ ·IdL (inducedMap P) ⟩
               inducedMap P ∎
      in eq i
    inducedMap (C.·-comm P Q i) = ·Comm (inducedMap P) (inducedMap Q) i
    inducedMap (C.ldist P Q S i) = ·DistL+ (inducedMap P) (inducedMap Q) (inducedMap S) i
    inducedMap (C.+HomConst s t i) = pres+ (f .snd) s t i
    inducedMap (C.·HomConst s t i) = pres· (f .snd) s t i
    inducedMap (C.0-trunc P Q p q i j) =
      is-set (inducedMap P) (inducedMap Q) (cong _ p) (cong _ q) i j

    module _ where
      open IsCommRingHom

      inducedHom : CommRingHom (R [ I ]ᵣ) S
      inducedHom .fst = inducedMap
      inducedHom .snd .pres0 = pres0 (f .snd)
      inducedHom .snd .pres1 = pres1 (f. snd)
      inducedHom .snd .pres+ = λ _ _ → refl
      inducedHom .snd .pres· = λ _ _ → refl
      inducedHom .snd .pres- = λ _ → refl

{-

  module _ (A : CommAlgebra R ℓ'') where
    open CommAlgebraStr (A .snd)
    open AlgebraTheory (CommRing→Ring R) (CommAlgebra→Algebra A)

    Hom = CommAlgebraHom  (R [ I ]) A
    open IsAlgebraHom

    evaluateAt : Hom → I → ⟨ A ⟩
    evaluateAt φ x = φ .fst (var x)

    mapRetrievable : ∀ (φ : I → ⟨ A ⟩)
                     → evaluateAt (inducedHom A φ) ≡ φ
    mapRetrievable φ = refl

    homRetrievable : ∀ (f : Hom)
                     → inducedMap A (evaluateAt f) ≡ fst f
    homRetrievable f = funExt (
      elimProp
        {P = λ x → ι x ≡ f $a x}
        (is-set _ _)
        (λ {x} → refl)
        (λ {r} →
          r ⋆ 1a                      ≡⟨ cong (λ u → r ⋆ u) (sym f.pres1) ⟩
          r ⋆ (f $a (const 1r))       ≡⟨ sym (f.pres⋆ r _) ⟩
          f $a (const r C.· const 1r) ≡⟨ cong (λ u → f $a u) (sym (C.·HomConst r 1r)) ⟩
          f $a (const (r ·r 1r))      ≡⟨ cong (λ u → f $a (const u)) (·r-rid r) ⟩
          f $a (const r) ∎)

        (λ {x} {y} eq-x eq-y →
          ι (x C.+ y)           ≡⟨ refl ⟩
          (ι x + ι y)           ≡⟨ cong (λ u → u + ι y) eq-x ⟩
          ((f $a x) + ι y)      ≡⟨ cong (λ u → (f $a x) + u) eq-y ⟩
          ((f $a x) + (f $a y)) ≡⟨ sym (f.pres+ _ _) ⟩
          (f $a (x C.+ y)) ∎)

        (λ {x} {y} eq-x eq-y →
          ι (x C.· y)         ≡⟨ refl ⟩
          ι x     · ι y       ≡⟨ cong (λ u → u · ι y) eq-x ⟩
          (f $a x) · (ι y)    ≡⟨ cong (λ u → (f $a x) · u) eq-y ⟩
          (f $a x) · (f $a y) ≡⟨ sym (f.pres· _ _) ⟩
          f $a (x C.· y) ∎)
      )
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
-}
