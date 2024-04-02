{- Localisation of an algebra at an arbitrary multiplicatively closed subset.

There are multiple ways one might want to go about formalizing this, from simply
extending the ring construction mechanically to using the fact the category of
algebras is a coslice category and exactly re-using the localization of rings.
Here, we chose the former, because after trying out the latter for some time, it
turned out that its computational behavior wasn't as nice as expected, and it
made Agda struggle a lot.
-}

{-# OPTIONS --safe #-}

open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma

import      Cubical.HITs.SetQuotients as SQ
import      Cubical.HITs.PropositionalTruncation as PropTrunc

open import Cubical.Algebra.Algebra
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.Subalgebra
open import Cubical.Algebra.CommRing as CommRing hiding (_ˣ;module Units)
open import Cubical.Algebra.CommRing.Localisation using (isMultClosedSubset)
open import Cubical.Algebra.Ring

module Cubical.Algebra.CommAlgebra.LocalisationAlgebra
  {ℓR : Level}
  (R : CommRing ℓR)
  where

module _
  {ℓAlg : Level} (A : CommAlgebra R ℓAlg)
  (S : ℙ ⟨ A ⟩)
  (SMultClosedSubset : isMultClosedSubset (CommAlgebra→CommRing A) S)
  where

  private module RLoc = Cubical.Algebra.CommRing.Localisation.Loc
                        (CommAlgebra→CommRing A) S SMultClosedSubset

  private module Units (A : CommAlgebra R ℓAlg) where
    _ˣ :  ℙ ⟨ A ⟩
    _ˣ = CommRing._ˣ (CommAlgebra→CommRing A)

    _⁻¹ : (a : ⟨ A ⟩) → ⦃ a ∈ _ˣ ⦄ → ⟨ A ⟩
    _⁻¹ a ⦃ a-inv ⦄ = fst a-inv

  open Units

  open isMultClosedSubset SMultClosedSubset
  private Aᵣ = CommAlgebra→CommRing A

  private module AlgebraStructureOnLocalisation where
    module A = CommAlgebraStr (snd A)
    S⁻¹Aᵣ : CommRing ℓAlg
    S⁻¹Aᵣ = RLoc.S⁻¹RAsCommRing

    open CommRingStr {{ ... }}
    instance
      _ = str R
      _ = str S⁻¹Aᵣ
      _ = str (CommAlgebra→CommRing A)

    _⋆ₚ_ : ⟨ R ⟩ → ⟨ A ⟩ × RLoc.S → ⟨ A ⟩ × RLoc.S
    r ⋆ₚ (a , s) = (r A.⋆ a) , s

    _⋆_ : ⟨ R ⟩ → ⟨ S⁻¹Aᵣ ⟩ → ⟨ S⁻¹Aᵣ ⟩
    _⋆_ r = SQ.setQuotUnaryOp
      (_⋆ₚ_ r)
      (λ (a , s) (a' , s') →
         λ (s-com , eq) →
           s-com , rearrange r (fst s-com) a (fst s')
                 ∙ cong (A._⋆_ r) eq
                 ∙ sym (rearrange r (fst s-com) a' (fst s)))
      where
        rearrange : (r : ⟨ R ⟩) (x y z : ⟨ A ⟩) → x · (r A.⋆ y) · z ≡ r A.⋆ (x · y · z)
        rearrange r x y z = cong (_· z) (sym (A.⋆AssocR r x y))
                          ∙ A.⋆AssocL r (x · y) z

    ·Assoc⋆ : (r r' : ⟨ R ⟩) (x : ⟨ S⁻¹Aᵣ ⟩) → (r · r') ⋆ x ≡ r ⋆ (r' ⋆ x)
    ·Assoc⋆ r r' = SQ.elimProp (λ _ → SQ.squash/ _ _)
      λ (a , _) → cong SQ.[_] (≡-× (A.⋆Assoc r r' a) refl)

    ⋆DistR+ : (r : ⟨ R ⟩) (x y : ⟨ S⁻¹Aᵣ ⟩) → r ⋆ (x + y) ≡ (r ⋆ x) + (r ⋆ y)
    ⋆DistR+ r = SQ.elimProp2 (λ _ _ → SQ.squash/ _ _)
      λ (a , s , _) (b , s' , _) → cong SQ.[_] (≡-× (rearrange a b s s') refl)
      where rearrange : (a b s s' : ⟨ A ⟩)
                      → r A.⋆ (a · s' + b · s) ≡ (r A.⋆ a) · s' + (r A.⋆ b) · s
            rearrange a b s s' = A.⋆DistR+ r _ _
                               ∙ cong₂ _+_ (sym $ A.⋆AssocL r a s')
                                           (sym $ A.⋆AssocL r b s)

    ⋆DistL+ : (r r' : ⟨ R ⟩) (x : ⟨ S⁻¹Aᵣ ⟩) → (r + r') ⋆ x ≡ (r ⋆ x) + (r' ⋆ x)
    ⋆DistL+ r r' = SQ.elimProp (λ _ → SQ.squash/ _ _)
      λ (a , s , _) → SQ.eq/ _ _
        ( (1r , containsOne)
        , sym (·Assoc 1r _ _)
        ∙ cong (1r ·_) (rearrange a s)
        ∙ ·Assoc 1r _ _)
      where rearrange : (a s : ⟨ A ⟩)
                      → (r + r') A.⋆ a · (s · s) ≡ ((r A.⋆ a) · s + (r' A.⋆ a) · s) · s
            rearrange a s = A.⋆AssocL (r + r') a (s · s)
                          ∙ cong ((r + r') A.⋆_) (·Assoc a s s)
                          ∙ sym (A.⋆AssocL (r + r') (a · s) s)
                          ∙ cong (_· s) (A.⋆DistL+ r r' (a · s)
                                       ∙ cong₂ _+_ (sym $ A.⋆AssocL r a s)
                                                   (sym $ A.⋆AssocL r' a s))

    ⋆IdL : (x : ⟨ S⁻¹Aᵣ ⟩) → 1r ⋆ x ≡ x
    ⋆IdL = SQ.elimProp (λ _ → SQ.squash/ _ _)
      λ (a , _) → cong SQ.[_] (≡-× (A.⋆IdL a) refl)

    ⋆AssocL : (r : ⟨ R ⟩) (x y : ⟨ S⁻¹Aᵣ ⟩) → (r ⋆ x) · y ≡ r ⋆ (x · y)
    ⋆AssocL r = SQ.elimProp2 (λ _ _ → SQ.squash/ _ _)
      λ (a , _) (b , _) → cong SQ.[_] (≡-× (A.⋆AssocL r a b) refl)

  S⁻¹AAsCommAlgebra : CommAlgebra R ℓAlg
  S⁻¹AAsCommAlgebra = let open AlgebraStructureOnLocalisation
    in commAlgebraFromCommRing {R = R} S⁻¹Aᵣ _⋆_ ·Assoc⋆ ⋆DistR+ ⋆DistL+ ⋆IdL ⋆AssocL

  S⁻¹AAsCommAlgebra→CommRing : CommAlgebra→CommRing S⁻¹AAsCommAlgebra ≡ RLoc.S⁻¹RAsCommRing
  S⁻¹AAsCommAlgebra→CommRing = let open AlgebraStructureOnLocalisation
    in commAlgebraFromCommRing→CommRing {R = R} S⁻¹Aᵣ _⋆_ ·Assoc⋆ ⋆DistR+
                                        ⋆DistL+ ⋆IdL ⋆AssocL

  module S⁻¹AUniversalProp where
    private module RUniv = Cubical.Algebra.CommRing.Localisation.S⁻¹RUniversalProp
                           (CommAlgebra→CommRing A) S SMultClosedSubset

    open CommAlgebraStr {{ ... }}
    instance
      _ = str A
      _ = str S⁻¹AAsCommAlgebra

    hasLocUniversalProp : (X : CommAlgebra R ℓAlg) (φ : CommAlgebraHom A X)
                        → (∀ s → s ∈ S → fst φ s ∈ X ˣ)
                        → Type (ℓ-max ℓR (ℓ-suc ℓAlg))
    hasLocUniversalProp X φ _ = (B : CommAlgebra R ℓAlg) (ψ : CommAlgebraHom A B)
                              → (∀ s → s ∈ S → fst ψ s ∈ B ˣ)
                              → ∃![ χ ∈ CommAlgebraHom X B ] (fst χ) ∘ (fst φ) ≡ (fst ψ)

    -- Can't use CommAlgebraHomFromRingHom directly for this as
    -- CommAlgebra→CommRing (commAlgebraFromCommRing R ...) is not
    -- definitionally equal to R.  We could use transports, but a manual
    -- definition works just as well.
    /1AsCommAlgebraHom : CommAlgebraHom A S⁻¹AAsCommAlgebra
    /1AsCommAlgebraHom =
        RUniv./1AsCommRingHom .fst
      , record
        { IsRingHom (RUniv./1AsCommRingHom .snd)
        ; pres⋆ = λ r x → refl}

    -- /1AsCommAlgebraHom and /1AsCommRingHom are equal over equality of the
    -- codomain rings.
    /1AsCommAlgebraHom→CommRingHom : PathP
      (λ i → CommRingHom Aᵣ (S⁻¹AAsCommAlgebra→CommRing i))
      (CommAlgebraHom→CommRingHom A S⁻¹AAsCommAlgebra /1AsCommAlgebraHom)
      RUniv./1AsCommRingHom
    /1AsCommAlgebraHom→CommRingHom = ΣPathPProp (λ f → isPropIsRingHom _ f _)
      (λ i → RUniv._/1)

    S⁻¹AHasUniversalProp : hasLocUniversalProp S⁻¹AAsCommAlgebra
                                               /1AsCommAlgebraHom RUniv.S/1⊆S⁻¹Rˣ
    S⁻¹AHasUniversalProp B ψ ψS⊂Bˣ =
      (χₐ , χₐcomm) , χₐunique
      where
        instance _ = str B

        -- Our strategy to build the above 3 using the ring equivalents is as
        -- follows:
        --
        -- 1) we know that our construction when reduced to rings
        -- gives something *propositionally* equal to the ring construction, we
        -- transport all of the relevant structure of the ring construction to
        -- the reduction of our construction.

        -- This is the template type for rings and ring morphisms satisfying the
        -- universal property for B,ψ.
        type-univ : (S : CommRing ℓAlg) → CommRingHom Aᵣ S → Type _
        type-univ S f = ∃![ χ ∈ CommRingHom S (CommAlgebra→CommRing B) ]
                            (fst χ) ∘ (fst f) ≡ (fst ψ)

        original-univ : type-univ RLoc.S⁻¹RAsCommRing RUniv./1AsCommRingHom
        original-univ = RUniv.S⁻¹RHasUniversalProp (CommAlgebra→CommRing B)
          (CommAlgebraHom→RingHom {A = A} {B = B} ψ)
          ψS⊂Bˣ

        univ : type-univ (CommAlgebra→CommRing S⁻¹AAsCommAlgebra)
                         (CommAlgebraHom→CommRingHom A S⁻¹AAsCommAlgebra /1AsCommAlgebraHom)
        univ = transport
          (sym $ cong₂ type-univ
                       S⁻¹AAsCommAlgebra→CommRing
                         /1AsCommAlgebraHom→CommRingHom)
          original-univ

        -- original-univ and univ are equal over the equalities of the ring
        -- constructions.
        univ-transport-filler : PathP
          (λ i → type-univ (S⁻¹AAsCommAlgebra→CommRing (~ i))
                           (/1AsCommAlgebraHom→CommRingHom (~ i)))
          original-univ univ
        univ-transport-filler = transport-filler
          (λ i → type-univ (S⁻¹AAsCommAlgebra→CommRing (~ i))
                      (/1AsCommAlgebraHom→CommRingHom (~ i)))
          original-univ

        -- 2) we prove that in our case, the ring construction also respects
        -- algebra multiplication, and then transport that property.

        -- This is the template type for the _⋆_ preservation property we want
        -- to transport.
        type-pres⋆ : (S : CommRing ℓAlg) (_⋆_ : ⟨ R ⟩ → ⟨ S ⟩ → ⟨ S ⟩)
                   → (f : CommRingHom S (CommAlgebra→CommRing B)) → Type _
        type-pres⋆ S _S⋆_ f =
          (r : ⟨ R ⟩) (a : ⟨ S ⟩) → (f .fst) (r S⋆ a) ≡ r ⋆ (f .fst) a

        -- The original function we get with the UP respects ⋆.
        original-pres⋆ : type-pres⋆ RLoc.S⁻¹RAsCommRing _⋆_ (original-univ .fst .fst)
        original-pres⋆ r = SQ.elimProp
          (λ _ _ _ → is-set _ _ _ _)
          (λ (a , s , s∈S') → cong (_· _) (ψ .snd .IsAlgebraHom.pres⋆ r a)
                            ∙ ⋆AssocL _ _ _)

        -- The transported function respects UP also, by transporting original-pres⋆.
        pres⋆ : type-pres⋆ (CommAlgebra→CommRing S⁻¹AAsCommAlgebra) _⋆_ (univ .fst .fst)
        pres⋆ = transport
          (λ i → type-pres⋆ (S⁻¹AAsCommAlgebra→CommRing (~ i))
                            (_⋆_ ⦃ str S⁻¹AAsCommAlgebra ⦄)
                            (univ-transport-filler i .fst .fst))
          original-pres⋆

        -- We can now define χₐ as an algebra morphism.
        χₐ : CommAlgebraHom S⁻¹AAsCommAlgebra B
        χₐ = univ .fst .fst .fst
           , record
             { IsRingHom (univ .fst .fst .snd)
             ; pres⋆ = pres⋆ }

        -- Commutativity is the same as the one for rings, since it only cares
        -- about the underlying function.
        χₐcomm : (fst χₐ) ∘ RUniv._/1 ≡ fst ψ
        χₐcomm = univ .fst .snd

        -- Lift unicity from the ring unicity.
        χₐunique : (el : Σ[ φ ∈ CommAlgebraHom S⁻¹AAsCommAlgebra B ]
                            (fst φ) ∘ RUniv._/1 ≡ (fst ψ))
                 → (χₐ , χₐcomm) ≡ el
        χₐunique (φ' , φ'comm) =
          Σ≡Prop ((λ _ → isSetΠ (λ _ → is-set) _ _)) $ AlgebraHom≡ $
          cong (fst ∘ fst) -- Get underlying bare function.
               (univ .snd (CommAlgebraHom→RingHom {A = S⁻¹AAsCommAlgebra} {B = B}
                                                  φ' , φ'comm))

    -- The above universal property leads to a generic induction principle for
    -- displayed algebras over S⁻¹A (which are equivalently just morphisms into
    -- S⁻¹A).  We don't have displayed algebras, but we have subalgebras, which
    -- are "displayed algebra propositions".
    --
    -- The statement is then: a subalgebra of S⁻¹A is the whole algebra iff. it
    -- contains the image of A and the inverses in the image of S.  This was
    -- suggested by David Wärn as an alternative to working with the
    -- construction above.
    private
      module Rec
        (P : Subalgebra R S⁻¹AAsCommAlgebra)
        (A/1∈P : (a : ⟨ A ⟩) → (/1AsCommAlgebraHom .fst a) ∈ (P .fst))
        (1/S∈P : (s : ⟨ A ⟩) → (s∈S : s ∈ S) →
                    (_⁻¹ S⁻¹AAsCommAlgebra ((/1AsCommAlgebraHom .fst) s)
                                           ⦃ RUniv.S/1⊆S⁻¹Rˣ s s∈S ⦄)
                    ∈ (P .fst))
        where

        totalg = Subalgebra→CommAlgebra R S⁻¹AAsCommAlgebra P
        totalg≡ = Subalgebra→CommAlgebra≡ R S⁻¹AAsCommAlgebra P
        ι = Subalgebra→CommAlgebraHom R S⁻¹AAsCommAlgebra P

        mor : CommAlgebraHom A totalg
        mor = SubalgebraHom R S⁻¹AAsCommAlgebra P A /1AsCommAlgebraHom A/1∈P

        morS⊂totalgˣ : (s : ⟨ A ⟩) → (s∈S : s ∈ S) → (fst mor s ∈ totalg ˣ)
        morS⊂totalgˣ s s∈S =
          let inv = RUniv.S/1⊆S⁻¹Rˣ s s∈S
          in (inv .fst , 1/S∈P s s∈S) , totalg≡ (inv .snd)

        sec : Σ[ f ∈ CommAlgebraHom S⁻¹AAsCommAlgebra totalg ]
                (fst f) ∘ (fst /1AsCommAlgebraHom) ≡ (fst mor)
        sec = S⁻¹AHasUniversalProp totalg mor morS⊂totalgˣ .fst

        post-composed : Σ[ f ∈ CommAlgebraHom S⁻¹AAsCommAlgebra S⁻¹AAsCommAlgebra ]
                          (fst f) ∘ (fst /1AsCommAlgebraHom) ≡ (fst /1AsCommAlgebraHom)
        post-composed =
            compCommAlgebraHom
              S⁻¹AAsCommAlgebra totalg S⁻¹AAsCommAlgebra
              (fst sec) ι
          , cong (fst ι ∘_) (snd sec)
          where open CommAlgebraHoms

        id-also-good : Σ[ f ∈ CommAlgebraHom S⁻¹AAsCommAlgebra S⁻¹AAsCommAlgebra ]
                          (fst f) ∘ (fst /1AsCommAlgebraHom) ≡ (fst /1AsCommAlgebraHom)
        id-also-good =
            ((λ x → x) , makeIsAlgebraHom refl (λ x y → refl)
                                                      (λ x y → refl)
                                                      (λ x y → refl))
          , refl

        contr-at-/1AsCommAlgebraHom :
          isContr (Σ[ f ∈ CommAlgebraHom S⁻¹AAsCommAlgebra S⁻¹AAsCommAlgebra ]
                      (fst f) ∘ (fst /1AsCommAlgebraHom) ≡ (fst /1AsCommAlgebraHom))
        contr-at-/1AsCommAlgebraHom =
          S⁻¹AHasUniversalProp S⁻¹AAsCommAlgebra
                               /1AsCommAlgebraHom
                               RUniv.S/1⊆S⁻¹Rˣ

        eq : fst post-composed ≡ fst id-also-good
        eq = (sym $ cong fst $ snd contr-at-/1AsCommAlgebraHom post-composed)
           ∙ (cong fst $ snd contr-at-/1AsCommAlgebraHom id-also-good)

        rec : (x : ⟨ S⁻¹AAsCommAlgebra ⟩) → x ∈ (P .fst)
        rec x = transport (cong (λ f → fst f x ∈ (P .fst)) eq)
                          (fst (fst sec) x .snd)

    rec = Rec.rec
