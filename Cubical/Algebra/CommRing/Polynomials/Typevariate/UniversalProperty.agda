module Cubical.Algebra.CommRing.Polynomials.Typevariate.UniversalProperty where
{-
  This file contains
  * an elimination principle for proving some proposition for all elements of R[I]ᵣ
    ('elimProp')
  * definitions of the induced maps appearing in the universal property of R[I],
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
open import Cubical.Algebra.CommRing.Polynomials.Typevariate.Base
open import Cubical.Algebra.Ring.Properties

open import Cubical.Data.Empty
open import Cubical.Data.Sigma

open import Cubical.Tactics.CommRingSolver

private
  variable
    ℓ ℓ' ℓ'' : Level

module _ {R : CommRing ℓ} {I : Type ℓ'} where
  open CommRingStr ⦃...⦄
  private instance
    _ = snd R
    _ = snd (R [ I ])

  module C = Construction
  open C using (const)

  {-
    Construction of the 'elimProp' eliminator.
  -}
  module _
    {P : ⟨ R [ I ] ⟩ → Type ℓ''}
    (isPropP : {x : _} → isProp (P x))
    (onVar : {x : I} → P (C.var x))
    (onConst : {r : ⟨ R ⟩} → P (const r))
    (on+ : {x y : ⟨ R [ I ] ⟩} → P x → P y → P (x + y))
    (on· : {x y : ⟨ R [ I ] ⟩} → P x → P y → P (x · y))
    where

    private
      on- : {x : ⟨ R [ I ] ⟩} → P x → P (- x)
      on- {x} Px = subst P (minusByMult x) (on· onConst Px)
        where minusByMult : (x : _) → (const (- 1r)) · x ≡ - x
              minusByMult x =
                (const (- 1r)) · x ≡⟨ cong (_· x) (pres- 1r) ⟩
                (- const (1r)) · x ≡⟨ cong (λ u → (- u) · x) pres1 ⟩
                (- 1r) · x         ≡⟨ sym (-IsMult-1 x) ⟩
                - x  ∎
                where open RingTheory (CommRing→Ring (R [ I ])) using (-IsMult-1)
                      open IsCommRingHom (constPolynomial R I .snd)

      -- A helper to deal with the path constructor cases.
      mkPathP :
        {x0 x1 : ⟨ R [ I ] ⟩} →
        (p : x0 ≡ x1) →
        (Px0 : P (x0)) →
        (Px1 : P (x1)) →
        PathP (λ i → P (p i)) Px0 Px1
      mkPathP _ = isProp→PathP λ i → isPropP

    elimProp : ((x : _) → P x)

    elimProp (C.var _) = onVar
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
    In this module and the module below, we will show the universal property
    of the polynomial ring as a commutative ring.

       R ──→ R[I]
        \     ∣
         f    ∃!          for a given φ : I → S
          ↘  ↙
            S

  -}
  module _ (S : CommRing ℓ'') (f : CommRingHom R S) (φ : I → ⟨ S ⟩) where
    private instance
      _ = S .snd

    open IsCommRingHom

    inducedMap : ⟨ R [ I ] ⟩ → ⟨ S ⟩
    inducedMap (C.var x) = φ x
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

      inducedHom : CommRingHom (R [ I ]) S
      inducedHom .fst = inducedMap
      inducedHom .snd .pres0 = pres0 (f .snd)
      inducedHom .snd .pres1 = pres1 (f. snd)
      inducedHom .snd .pres+ = λ _ _ → refl
      inducedHom .snd .pres· = λ _ _ → refl
      inducedHom .snd .pres- = λ _ → refl

    opaque
      inducedHomComm : inducedHom ∘cr constPolynomial R I ≡ f
      inducedHomComm = CommRingHom≡ $ funExt (λ r → refl)

module _  {R : CommRing ℓ} {I : Type ℓ'} (S : CommRing ℓ'') (f : CommRingHom R S) where
  open CommRingStr ⦃...⦄
  private instance
    _ = S .snd
    _ = (R [ I ]) .snd
  open IsCommRingHom

  evalVar : CommRingHom (R [ I ]) S → I → ⟨ S ⟩
  evalVar h = h .fst ∘ var

  opaque
    unfolding var
    evalInduce : ∀ (φ : I → ⟨ S ⟩)
                 → evalVar (inducedHom S f φ) ≡ φ
    evalInduce φ = refl

  opaque
    unfolding var
    evalOnVars : ∀ (φ : I → ⟨ S ⟩)
                 → (i : I) → inducedHom S f φ .fst (var i) ≡ φ i
    evalOnVars φ i = refl

  opaque
    unfolding var
    induceEval : (g : CommRingHom (R [ I ]) S)
                 (p : g .fst ∘ constPolynomial R I .fst ≡ f .fst)
                 → (inducedHom S f (evalVar g)) ≡ g
    induceEval g p =
      let theMap : ⟨ R [ I ] ⟩ → ⟨ S ⟩
          theMap = inducedMap S f (evalVar g)
      in
      CommRingHom≡ $
      funExt $
      elimProp
        (is-set _ _)
        (λ {x} → refl)
        (λ {r} →  sym (cong (λ f → f r) p))
        (λ {x} {y} eq-x eq-y →
          theMap (x + y)        ≡⟨ pres+ (inducedHom S f (evalVar g) .snd) x y ⟩
          theMap x + theMap y   ≡[ i ]⟨ (eq-x i + eq-y i) ⟩
          (g $cr x + g $cr y)   ≡⟨ sym (pres+ (g .snd) _ _) ⟩
          (g $cr (x + y)) ∎)
        λ {x} {y} eq-x eq-y →
          theMap (x · y)        ≡⟨ pres· (inducedHom S f (evalVar g) .snd) x y ⟩
          theMap x · theMap y   ≡[ i ]⟨ (eq-x i · eq-y i) ⟩
          (g $cr x · g $cr y)   ≡⟨ sym (pres· (g .snd) _ _) ⟩
          (g $cr (x · y)) ∎

  opaque
    inducedHomUnique : (φ : I → ⟨ S ⟩)
                 (g : CommRingHom (R [ I ]) S)
                 (p : g .fst ∘ constPolynomial R I .fst ≡ f .fst)
                 (q : evalVar g ≡ φ)
                 → inducedHom S f φ ≡ g
    inducedHomUnique φ g p q = cong (inducedHom S f) (sym q) ∙ induceEval g p

  opaque
    hom≡ByValuesOnVars : (g h : CommRingHom (R [ I ]) S)
                         (p : g .fst ∘ constPolynomial _ _ .fst ≡ f .fst) (q : h .fst ∘ constPolynomial _ _ .fst ≡ f .fst)
                         → (evalVar g ≡ evalVar h)
                         → g ≡ h
    hom≡ByValuesOnVars g h p q ≡OnVars =
      sym (inducedHomUnique ϕ g p refl) ∙ inducedHomUnique ϕ h q (sym ≡OnVars)
      where ϕ : I → ⟨ S ⟩
            ϕ = evalVar g

opaque
  idByIdOnVars : {R : CommRing ℓ} {I : Type ℓ'}
                 (g : CommRingHom (R [ I ]) (R [ I ]))
                 (p : g .fst ∘ constPolynomial _ _ .fst ≡ constPolynomial _ _ .fst)
                 → (g .fst ∘ var ≡ idfun _ ∘ var)
                 → g ≡ idCommRingHom (R [ I ])
  idByIdOnVars g p idOnVars = hom≡ByValuesOnVars _ (constPolynomial _ _) g (idCommRingHom _) p refl idOnVars
