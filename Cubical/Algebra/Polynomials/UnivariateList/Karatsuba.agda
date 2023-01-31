{-# OPTIONS --safe #-}
module Cubical.Algebra.Polynomials.UnivariateList.Karatsuba where

open import Cubical.HITs.PropositionalTruncation
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.Nat renaming ( _+_ to _+ℕ_ ; _·_ to _·ℕ_ ; _^_ to _^ℕ_
                                      ; ·-assoc to ·ℕ-assoc ; ·-comm to ·ℕ-comm)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty.Base renaming (rec to ⊥rec )
open import Cubical.Data.Bool

open import Cubical.Algebra.Group
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Algebra
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommRing.Instances.Polynomials.UnivariatePolyList
open import Cubical.Tactics.CommRingSolver.Reflection

open import Cubical.Algebra.Polynomials.UnivariateList.Base
open import Cubical.Algebra.Polynomials.UnivariateList.Properties
open import Cubical.Algebra.Polynomials.UnivariateList.UniversalProperty

open import Cubical.Algebra.CommAlgebra.UnivariatePolyList

private
  variable
    ℓ ℓ' : Level


module _ (R' : CommRing ℓ) where

  open PolyMod R'
  open PolyModTheory R'
  open CommRingStr ⦃...⦄

  private
    R = fst R'
    instance
      _ = snd R'
      _ = snd (UnivariatePolyList R')

    X : Poly R'
    X = 0r ∷ 1r ∷ []

    X² = X · X

    R[X] = Poly R'


  -- p(X) ↦ p(X²)
  evalAtX² : R[X] → R[X]
  evalAtX² = RecPoly.f []
                       (λ a p → a ∷ 0r ∷ p)
                       (cong (0r ∷_) drop0 ∙ drop0)

  inducedEvalAtX² : AlgebraHom (CommAlgebra→Algebra (ListPolyCommAlgebra R'))
                               (CommAlgebra→Algebra (ListPolyCommAlgebra R'))
  inducedEvalAtX² = inducedHom _ _ X²

  -- this gives us homomorphism properties
  evalAtX²≡ : fst inducedEvalAtX² ≡ evalAtX²
  evalAtX²≡ = funExt (ElimProp _ refl step (isSetPoly _ _))
    where
    useSolver : ∀ r → r · 1r + 0r ≡ r
    useSolver = solve R'

    step : ∀ (r : R) (p : R[X])
         → inducedMap _ _ X² p ≡ evalAtX² p
         → fst inducedEvalAtX² (r ∷ p) ≡ evalAtX² (r ∷ p)
    step r p hyp =
        [ r · 1r + 0r ] + (X² · inducedMap _ _ X² p)

      ≡⟨ cong₂ (λ x y → [ x ] + y) (useSolver _) (sym (·Assoc X X (inducedMap _ _ X² p))) ⟩

        [ r ] + X · (X · inducedMap _ _ X² p)

      ≡⟨ cong (λ x → [ r ] + X · x) (X*Poly (inducedMap _ _ X² p)) ⟩

        [ r ] + X · (0r ∷ inducedMap _ _ X² p)

      ≡⟨ cong (λ x → [ r ] + x) (X*Poly (0r ∷ inducedMap _ _ X² p)) ⟩

        (r + 0r) ∷ 0r ∷ inducedMap _ _ X² p

      ≡⟨ cong (λ x → x ∷ 0r ∷ inducedMap _ _ X² p) (+IdR r) ⟩

        r ∷ 0r ∷ inducedMap _ _ X² p

      ≡⟨ cong (λ x → r ∷ 0r ∷ x) hyp ⟩

        r ∷ 0r ∷ evalAtX² p ∎


  open IsAlgebraHom
  evalAtX²Pres+ : ∀ (p q : R[X]) → evalAtX² (p + q) ≡ evalAtX² p + evalAtX² q
  evalAtX²Pres+ = subst (λ f → ∀ (p q : R[X]) → f (p + q) ≡ f p + f q)
                        evalAtX²≡ (inducedHom _ _ X² .snd .pres+)

  evalAtX²Pres· : ∀ (p q : R[X]) → evalAtX² (p · q) ≡ evalAtX² p · evalAtX² q
  evalAtX²Pres· = subst (λ f → ∀ (p q : R[X]) → f (p · q) ≡ f p · f q)
                        evalAtX²≡ (inducedHom _ _ X² .snd .pres·)

  evalAtX²Pres- : ∀ (p : R[X]) → evalAtX² (- p) ≡ - evalAtX² p
  evalAtX²Pres- = subst (λ f → ∀ (p : R[X]) → f (- p) ≡ - f p)
                        evalAtX²≡ (inducedHom _ _ X² .snd .pres-)

  evalAtX²Pres-bin : ∀ (p q : R[X]) → evalAtX² (p - q) ≡ evalAtX² p - evalAtX² q
  evalAtX²Pres-bin p q = evalAtX²Pres+ p (- q) ∙ cong (evalAtX² p +_) (evalAtX²Pres- q)

  -- split into coefficients of even and odd degree
  -- a₀ + a₁X + a₂X² + ... ↦ a₀ + a₂X + ...
  evenDegCoeff : R[X] → R[X]
  evenDegCoeff [] = []
  evenDegCoeff [ a ] = [ a ]
  evenDegCoeff (a ∷ b ∷ p) = a ∷ evenDegCoeff p
  evenDegCoeff (a ∷ drop0 i) = [ a ]
  evenDegCoeff (drop0 i) = drop0 i

  syntax evenDegCoeff p = p ₑ

  -- a₀ + a₁X + a₂X² + a₃X³ + ... ↦ a₁ + a₃X + ...
  oddDegCoeff : R[X] → R[X]
  oddDegCoeff [] = []
  oddDegCoeff [ a ] = []
  oddDegCoeff (a ∷ b ∷ p) = b ∷ oddDegCoeff p
  oddDegCoeff (a ∷ drop0 i) = drop0 i
  oddDegCoeff (drop0 i) = []

  syntax oddDegCoeff p = p ₒ

  -- custom eliminator
  -- should be erased module (in development version)
  module _ (B : R[X] → Type ℓ')
           (BProp : ∀ p → isProp (B p))
           ([]* : B [])
           (cons* : ∀ a b p → B p → B (a ∷ b ∷ p)) where

    private
      sing* : ∀ a → B [ a ]
      sing* a = subst B (cong (a ∷_) drop0) (cons* a 0r [] []*)

      B' : R[X] → Type (ℓ-max ℓ ℓ')
      B' p = B p × (∀ a → B (a ∷ p))

      foo : ∀ p → B' p
      foo = ElimProp _ ([]* , sing*)
                       (λ b p B'p → (B'p .snd b) , λ a → cons* a b p (B'p .fst))
                       (isProp× (BProp _) (isPropΠ (λ _ → BProp _)))

    ElimPropDoubleCons : ∀ p → B p
    ElimPropDoubleCons p = foo p .fst

  -- observation:
  splitPoly : ∀ (p : R[X]) → evalAtX² (p ₑ) + X · evalAtX² (p ₒ) ≡ p
  splitPoly = ElimPropDoubleCons _ (λ _ → isSetPoly _ _)
                                   (cong (0r ∷_) drop0 ∙ drop0) step
    where
    step : ∀ (a b : R) (p : R[X])
         → evalAtX² (p ₑ) + X · evalAtX² (p ₒ) ≡ p
         → evalAtX² ((a ∷ b ∷ p) ₑ) + X · evalAtX² ((a ∷ b ∷ p) ₒ) ≡ (a ∷ b ∷ p)
    step a b p hyp =
        (a ∷ 0r ∷ evalAtX² (p ₑ)) + X · (b ∷ 0r ∷ evalAtX² (p ₒ))

      ≡⟨ cong ((a ∷ 0r ∷ evalAtX² (evenDegCoeff p)) +_) (X*Poly (b ∷ 0r ∷ evalAtX² (p ₒ))) ⟩

        (a ∷ 0r ∷ evalAtX² (p ₑ)) + (0r ∷ b ∷ 0r ∷ evalAtX² (p ₒ))

      ≡⟨ refl ⟩

        (a + 0r) ∷ (0r + b) ∷ (evalAtX² (p ₑ) + (0r ∷ evalAtX² (p ₒ)))

      ≡⟨ (λ i → (+IdR a i) ∷ (+IdL b i) ∷ (evalAtX² (p ₑ) + X*Poly (evalAtX² (p ₒ)) (~ i))) ⟩

        a ∷ b ∷ (evalAtX² (p ₑ) + X · evalAtX² (p ₒ))

      ≡⟨ cong (λ x → a ∷ b ∷ x) hyp ⟩

        a ∷ b ∷ p ∎


  -- the algorithm
  karatsubaRec : ℕ → R[X] → R[X] → R[X]
  karatsubaRec zero p q = p · q
  -- should do pattern-matching on p and q!!!!!
  -- or two args ℕ,
  -- and only do algorithm when "deg p & q ≥ 2"
  karatsubaRec (suc n) p q = let
    pₑqₑ = karatsubaRec n  (p ₑ) (q ₑ)
    pₒqₒ = karatsubaRec n  (p ₒ) (q ₒ)
    [pₑ+pₒ][qₑ+qₒ] = karatsubaRec n  (p ₑ + p ₒ) (q ₑ + q ₒ)
    in evalAtX² pₑqₑ + X · evalAtX²([pₑ+pₒ][qₑ+qₒ] - pₑqₑ - pₒqₒ) + X² · evalAtX² pₒqₒ


  karatsubaRec≡ : ∀ (n : ℕ) (p q : R[X]) → karatsubaRec n p q ≡ p · q
  karatsubaRec≡ zero _ _ = refl
  karatsubaRec≡ (suc n) p q = path
    where
    pₑqₑ = karatsubaRec n  (p ₑ) (q ₑ)
    pₒqₒ = karatsubaRec n  (p ₒ) (q ₒ)
    [pₑ+pₒ][qₑ+qₒ] = karatsubaRec n  (p ₑ + p ₒ) (q ₑ + q ₒ)

    -- why doesn't this work
    useSolver : ∀ (x pₑX² pₒX² qₑX² qₒX² : R[X])
              → pₑX² · qₑX²
                  + x · ((pₑX² + pₒX²) · (qₑX² + qₒX²) - (pₑX² · qₑX²) - (pₒX² · qₒX²))
                  + (x · x) · (pₒX² · qₒX²)
              ≡ (pₑX² + x · pₒX²) · (qₑX² + x · qₒX²)
    useSolver = solve (UnivariatePolyList R')

    path : evalAtX² pₑqₑ + X · evalAtX²([pₑ+pₒ][qₑ+qₒ] - pₑqₑ - pₒqₒ) + X² · evalAtX² pₒqₒ
         ≡ p · q
    path =
       evalAtX² pₑqₑ + X · evalAtX²([pₑ+pₒ][qₑ+qₒ] - pₑqₑ - pₒqₒ) + X² · evalAtX² pₒqₒ

     ≡⟨ cong₂
          (λ x y →
             evalAtX² x + X · evalAtX² ([pₑ+pₒ][qₑ+qₒ] - x - y) + X² · evalAtX² y)
          (karatsubaRec≡ n  (p ₑ) (q ₑ))
          (karatsubaRec≡ n  (p ₒ) (q ₒ)) ⟩

       evalAtX² (p ₑ · q ₑ)
         + X · evalAtX²([pₑ+pₒ][qₑ+qₒ] - (p ₑ · q ₑ) - (p ₒ · q ₒ))
         + X² · evalAtX² (p ₒ · q ₒ)

     ≡⟨ cong (λ x → evalAtX² (p ₑ · q ₑ)
         + X · evalAtX²(x - (p ₑ · q ₑ) - (p ₒ · q ₒ))
         + X² · evalAtX² (p ₒ · q ₒ)) (karatsubaRec≡ n  (p ₑ + p ₒ) (q ₑ + q ₒ)) ⟩

       evalAtX² (p ₑ · q ₑ)
         + X · evalAtX²((p ₑ + p ₒ) · (q ₑ + q ₒ) - p ₑ · q ₑ - p ₒ · q ₒ)
         + X² · evalAtX² (p ₒ · q ₒ)

     ≡⟨ cong (λ x → evalAtX² (p ₑ · q ₑ) + X · x +  X² · evalAtX² (p ₒ · q ₒ))
             (evalAtX²Pres-bin _ (p ₒ · q ₒ)) ⟩

       evalAtX² (p ₑ · q ₑ)
         + X · (evalAtX² ((p ₑ + p ₒ) · (q ₑ + q ₒ) - p ₑ · q ₑ)
                  - evalAtX² (p ₒ · q ₒ))
         + X² · evalAtX² (p ₒ · q ₒ)

     ≡⟨ cong (λ x → evalAtX² (p ₑ · q ₑ)
               + X · (x - evalAtX² (p ₒ · q ₒ)) +  X² · evalAtX² (p ₒ · q ₒ))
             (evalAtX²Pres-bin _ (p ₑ · q ₑ)) ⟩

       evalAtX² (p ₑ · q ₑ)
         + X · (evalAtX² ((p ₑ + p ₒ) · (q ₑ + q ₒ))
                 - evalAtX² (p ₑ · q ₑ) - evalAtX² (p ₒ · q ₒ))
         + X² · evalAtX² (p ₒ · q ₒ)

     ≡⟨ cong (λ x → evalAtX² (p ₑ · q ₑ)
         + X · (x - evalAtX² (p ₑ · q ₑ) - evalAtX² (p ₒ · q ₒ))
         + X² · evalAtX² (p ₒ · q ₒ)) (evalAtX²Pres· (p ₑ + p ₒ) _) ⟩

       evalAtX² (p ₑ · q ₑ)
         + X · (evalAtX² (p ₑ + p ₒ) · evalAtX² (q ₑ + q ₒ)
                 - evalAtX² (p ₑ · q ₑ) - evalAtX² (p ₒ · q ₒ))
         + X² · evalAtX² (p ₒ · q ₒ)

     ≡⟨  cong₂ (λ x y → evalAtX² (p ₑ · q ₑ)
         + X · (x · y - evalAtX² (p ₑ · q ₑ) - evalAtX² (p ₒ · q ₒ))
         + X² · evalAtX² (p ₒ · q ₒ)) (evalAtX²Pres+ (p ₑ) (p ₒ))
                                      (evalAtX²Pres+ (q ₑ) (q ₒ)) ⟩

       evalAtX² (p ₑ · q ₑ)
         + X · ((evalAtX² (p ₑ) + evalAtX² (p ₒ)) · (evalAtX² (q ₑ) + evalAtX² (q ₒ))
                 - evalAtX² (p ₑ · q ₑ) - evalAtX² (p ₒ · q ₒ))
         + X² · evalAtX² (p ₒ · q ₒ)

     ≡⟨ cong₂ (λ x y → x
         + X · ((evalAtX² (p ₑ) + evalAtX² (p ₒ)) · (evalAtX² (q ₑ) + evalAtX² (q ₒ))
                 - x - y)
         + X² · y) (evalAtX²Pres· (p ₑ) (q ₑ)) (evalAtX²Pres· (p ₒ) (q ₒ)) ⟩

       evalAtX² (p ₑ) · evalAtX² (q ₑ)
         + X · ((evalAtX² (p ₑ) + evalAtX² (p ₒ)) · (evalAtX² (q ₑ) + evalAtX² (q ₒ))
                 - evalAtX² (p ₑ) · evalAtX² (q ₑ) - evalAtX² (p ₒ) · evalAtX² (q ₒ))
         + X² · (evalAtX² (p ₒ) · evalAtX² (q ₒ))

     ≡⟨ useSolver X (evalAtX² (p ₑ)) (evalAtX² (p ₒ)) (evalAtX² (q ₑ)) (evalAtX² (q ₒ)) ⟩

       (evalAtX² (p ₑ) + X · evalAtX² (p ₒ)) · (evalAtX² (q ₑ) + X · evalAtX² (q ₒ))

     ≡⟨ cong₂ (_·_) (splitPoly p) (splitPoly q) ⟩

       p · q ∎


  karatsubaTruncRec : ∥ ℕ ∥₁ → R[X] → R[X] → R[X]
  karatsubaTruncRec = rec→Set (isSetΠ2 λ _ _ → isSetPoly)
                        karatsubaRec
                        λ n m → funExt
                          λ p → funExt
                            λ q → karatsubaRec≡ n p q ∙ sym (karatsubaRec≡ m p q)


  -- can't define a degree or even upper bound (i.e. length of representing list)
  -- but something like it:
  truncLength : R[X] → ∥ ℕ ∥₁
  truncLength [] = ∣ 0 ∣₁
  truncLength (a ∷ p) = map suc (truncLength p)
  truncLength (drop0 i) = squash₁ ∣ 1 ∣₁ ∣ 0 ∣₁ i

  karatsuba : R[X] → R[X] → R[X]
  karatsuba p q =
    let upperBound = map2 max (truncLength p) (truncLength q)
    in karatsubaTruncRec upperBound p q

  -- to be erased:
  -- Rings and polynomials in files --erased-cubical
  -- erase all the proofs (of equality)
  -- erased prop trunc
  -- erased version rec→Set

  -- optional
  -- erased polynomials
  -- accessibility relation
