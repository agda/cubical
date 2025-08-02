{-# OPTIONS --lossy-unification #-}

module Cubical.ZCohomology.CohomologyRings.S2wedgeS4 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels

open import Cubical.Relation.Nullary

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; discreteℕ ; suc-predℕ ; +-comm)
open import Cubical.Data.Int
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Vec
open import Cubical.Data.FinData

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group.Instances.Unit
open import Cubical.Algebra.Group.Instances.Bool
open import Cubical.Algebra.Group.Instances.Int
open import Cubical.Algebra.DirectSum.DirectSumHIT.Base
open import Cubical.Algebra.Ring

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.FGIdeal
open import Cubical.Algebra.CommRing.Quotient
open import Cubical.Algebra.CommRing.Instances.Int renaming (ℤCommRing to ℤCR)
open import Cubical.Algebra.CommRing.Polynomials.MultivariatePoly
open import Cubical.Algebra.CommRing.Polynomials.MultivariatePoly-Quotient
open import Cubical.Algebra.CommRing.Polynomials.MultivariatePoly-notationZ

open import Cubical.HITs.Truncation
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetQuotients as SQ renaming (_/_ to _/sq_)
open import Cubical.HITs.RPn.Base

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.RingStructure.CupProduct
open import Cubical.ZCohomology.RingStructure.RingLaws
open import Cubical.ZCohomology.RingStructure.CohomologyRing
open import Cubical.ZCohomology.Groups.S2wedgeS4
open import Cubical.ZCohomology.CohomologyRings.CupProductProperties

open Iso


module Equiv-RP2-Properties where

-----------------------------------------------------------------------------
-- Definitions, Import with notations, Partition

  -- Definition
  private
    ℤAG = Ring→AbGroup (CommRing→Ring ℤCR)

  <XY,X²,Y²> : FinVec ℤ[x,y] 3
  <XY,X²,Y²> zero = base (1 ∷ 1 ∷ []) 1
  <XY,X²,Y²> one = base (2 ∷ 0 ∷ []) 1
  <XY,X²,Y²> two = base (0 ∷ 2 ∷ []) 1

  ℤ[X,Y]/<XY,X²,Y²> : CommRing ℓ-zero
  ℤ[X,Y]/<XY,X²,Y²> = PolyCommRing-Quotient ℤCR <XY,X²,Y²>

  ℤ[x,y]/<xy,x²,y²> : Type ℓ-zero
  ℤ[x,y]/<xy,x²,y²> = fst ℤ[X,Y]/<XY,X²,Y²>

  -- Import with notation
  open IsGroupHom
  open gradedRingProperties

  open CommRingStr (snd ℤCR) using ()
    renaming
    ( 0r        to 0ℤ
    ; 1r        to 1ℤ
    ; _+_       to _+ℤ_
    ; -_        to -ℤ_
    ; _·_       to _·ℤ_
    ; +Assoc    to +ℤAssoc
    ; +IdL      to +ℤIdL
    ; +IdR      to +ℤIdR
    ; +Comm     to +ℤComm
    ; ·Assoc    to ·ℤAssoc
    ; ·IdL      to ·ℤIdL
    ; ·IdR      to ·ℤIdR
    ; ·DistR+   to ·ℤDistR+
    ; ·Comm     to ·ℤComm
    ; is-set    to isSetℤ     )

  open RingStr (snd (H*R S²⋁S⁴)) using ()
    renaming
    ( 0r        to 0H*
    ; 1r        to 1H*
    ; _+_       to _+H*_
    ; -_        to -H*_
    ; _·_       to _cup_
    ; +Assoc    to +H*Assoc
    ; +IdL      to +H*IdL
    ; +IdR      to +H*IdR
    ; +Comm     to +H*Comm
    ; ·Assoc    to ·H*Assoc
    ; ·IdL      to ·H*IdL
    ; ·IdR      to ·H*IdR
    ; ·DistR+   to ·H*DistR+
    ; is-set    to isSetH*     )

  open CommRingStr (snd ℤ[X,Y]) using ()
    renaming
    ( 0r        to 0Pℤ
    ; 1r        to 1Pℤ
    ; _+_       to _+Pℤ_
    ; -_        to -Pℤ_
    ; _·_       to _·Pℤ_
    ; +Assoc    to +PℤAssoc
    ; +IdL      to +PℤIdL
    ; +IdR      to +PℤIdR
    ; +Comm     to +PℤComm
    ; ·Assoc    to ·PℤAssoc
    ; ·IdL      to ·PℤIdL
    ; ·IdR      to ·PℤIdR
    ; ·Comm     to ·PℤComm
    ; ·DistR+   to ·PℤDistR+
    ; is-set    to isSetPℤ     )

  open CommRingStr (snd ℤ[X,Y]/<XY,X²,Y²>) using ()
    renaming
    ( 0r        to 0PℤI
    ; 1r        to 1PℤI
    ; _+_       to _+PℤI_
    ; -_        to -PℤI_
    ; _·_       to _·PℤI_
    ; +Assoc    to +PℤIAssoc
    ; +IdL      to +PℤIIdL
    ; +IdR      to +PℤIIdR
    ; +Comm     to +PℤIComm
    ; ·Assoc    to ·PℤIAssoc
    ; ·IdL      to ·PℤIIdL
    ; ·IdR      to ·PℤIIdR
    ; ·DistR+   to ·PℤIDistR+
    ; is-set    to isSetPℤI     )


  e₀ = invGroupIso H⁰-S²⋁S⁴≅ℤ
  ϕ₀ = fun (fst e₀)
  ϕ₀str = snd e₀
  ϕ₀⁻¹ = inv (fst e₀)
  ϕ₀⁻¹str = snd (invGroupIso e₀)
  ϕ₀-sect = rightInv (fst e₀)
  ϕ₀-retr = leftInv (fst e₀)

  e₂ = invGroupIso H²-S²⋁S⁴≅ℤ
  ϕ₂ = fun (fst e₂)
  ϕ₂str = snd e₂
  ϕ₂⁻¹ = inv (fst e₂)
  ϕ₂⁻¹str = snd (invGroupIso e₂)
  ϕ₂-sect = rightInv (fst e₂)
  ϕ₂-retr = leftInv (fst e₂)

  -- This equivalence need to be put in module
  -- However, it never type checks
  module IssueComputation
    (HH : GroupIso ℤGroup (coHomGr 4 S²⋁S⁴))
    where

    e₄ = HH
    ϕ₄ : ℤ → coHom 4 S²⋁S⁴
    ϕ₄ = fun (fst e₄)
    ϕ₄str = snd e₄
    ϕ₄⁻¹ : coHom 4 S²⋁S⁴ → ℤ
    ϕ₄⁻¹ = inv (fst e₄)
    ϕ₄⁻¹str = snd (invGroupIso e₄)
    ϕ₄-sect = rightInv (fst e₄)
    ϕ₄-retr = leftInv (fst e₄)

    -- Partition
    data partℕ (k : ℕ) : Type ℓ-zero where
      is0  : (k ≡ 0)            → partℕ k
      is2  : (k ≡ 2)            → partℕ k
      is4  : (k ≡ 4)            → partℕ k
      else : (k ≡ 0 → ⊥)
             × ((k ≡ 2 → ⊥)
                × (k ≡ 4 → ⊥)) → partℕ k

    part : (k : ℕ) → partℕ k
    part k with (discreteℕ k 0)
    ... | yes p = is0 p
    ... | no ¬p with (discreteℕ k 2)
    ... |       yes q = is2 q
    ... |       no ¬q with (discreteℕ k 4)
    ... |             yes r = is4 r
    ... |             no ¬r = else (¬p , (¬q , ¬r))


    part0 : part 0 ≡ is0 refl
    part0 = refl

    part2 : part 2 ≡ is2 refl
    part2 = refl

    part4 : part 4 ≡ is4 refl
    part4 = refl


  -----------------------------------------------------------------------------
  -- Direct Sens on ℤ[x]

    ℤ[x,y]→H*-S²⋁S⁴ : ℤ[x,y] → H* S²⋁S⁴
    ℤ[x,y]→H*-S²⋁S⁴ = DS-Rec-Set.f _ _ _ _ isSetH*
                        0H*
                        ϕ
                        _+H*_
                        +H*Assoc
                        +H*IdR
                        +H*Comm
                        base-neutral-eq
                        base-add-eq
                    where
                    ϕ : _
                    ϕ (zero        ∷ zero        ∷ []) a = base 0 (ϕ₀ a)
                    ϕ (zero        ∷ one         ∷ []) a = base 4 (ϕ₄ a)
                    ϕ (zero        ∷ suc (suc m) ∷ []) a = 0H*
                    ϕ (one         ∷ zero        ∷ []) a = base 2 (ϕ₂ a)
                    ϕ (one         ∷ suc m       ∷ []) a = 0H*
                    ϕ (suc (suc n) ∷ m           ∷ []) a = 0H*

                    base-neutral-eq : _
                    base-neutral-eq (zero        ∷ zero        ∷ []) = cong (base 0) (pres1 ϕ₀str) ∙ base-neutral _
                    base-neutral-eq (zero        ∷ one         ∷ []) = cong (base 4) (pres1 ϕ₄str) ∙ base-neutral _
                    base-neutral-eq (zero        ∷ suc (suc m) ∷ []) = refl
                    base-neutral-eq (one         ∷ zero        ∷ []) = cong (base 2) (pres1 ϕ₂str) ∙ base-neutral _
                    base-neutral-eq (one         ∷ suc m       ∷ []) = refl
                    base-neutral-eq (suc (suc n) ∷ m           ∷ []) = refl

                    base-add-eq : _
                    base-add-eq (zero        ∷ zero        ∷ []) a b = base-add _ _ _ ∙ cong (base 0) (sym (pres· ϕ₀str _ _))
                    base-add-eq (zero        ∷ one         ∷ []) a b = base-add _ _ _ ∙ cong (base 4) (sym (pres· ϕ₄str _ _))
                    base-add-eq (zero        ∷ suc (suc m) ∷ []) a b = +H*IdR _
                    base-add-eq (one         ∷ zero        ∷ []) a b = base-add _ _ _ ∙ cong (base 2) (sym (pres· ϕ₂str _ _))
                    base-add-eq (one         ∷ suc m       ∷ []) a b = +H*IdR _
                    base-add-eq (suc (suc n) ∷ m           ∷ []) a b = +H*IdR _

  -----------------------------------------------------------------------------
  -- Morphism on ℤ[x]

    ℤ[x,y]→H*-S²⋁S⁴-pres1Pℤ : ℤ[x,y]→H*-S²⋁S⁴ (1Pℤ) ≡ 1H*
    ℤ[x,y]→H*-S²⋁S⁴-pres1Pℤ = refl

    ℤ[x,y]→H*-S²⋁S⁴-pres+ : (x y : ℤ[x,y]) → ℤ[x,y]→H*-S²⋁S⁴ (x +Pℤ y) ≡ ℤ[x,y]→H*-S²⋁S⁴ x +H* ℤ[x,y]→H*-S²⋁S⁴ y
    ℤ[x,y]→H*-S²⋁S⁴-pres+ x y = refl

    --           Explanation of the product proof
    --
    --           -------------------------------------------------------
    --           | (0,0) | (0,1) | (0,m+2) | (1,0) | (1,m+1) | (n+2,m) |
    -- -----------------------------------------------------------------
    -- | (0,0)   |   H⁰  |   H⁰  |    0    |   H⁰  |    0    |    0    |
    -- -----------------------------------------------------------------
    -- | (0,1)   |  Sym  |   0₈  |    0    |   0₆  |    0    |    0    |
    -- -----------------------------------------------------------------
    -- | (0,m+2) | ==========================================> triv    |
    -- -----------------------------------------------------------------
    -- | (1,0)   |  Sym  |  Sym  |    0    |   ★  |    0    |    0    |
    -- -----------------------------------------------------------------
    -- | (1,m+1) | ==========================================> triv    |
    -- -----------------------------------------------------------------
    -- | (n+2,m) | ==========================================> triv    |
    -- -----------------------------------------------------------------

    -- ★ : prove that ϕ₂(1) ⌣ ϕ₂(1) ≡ 0 => ok because equiv H²(S²) and H⁴(S²) is trivial

    open pres⌣


    ϕ₀-gen : (n : ℕ) → (f : coHom n S²⋁S⁴) → ϕ₀ (pos 1) ⌣ f ≡ f
    ϕ₀-gen n = ST.elim (λ _ → isProp→isSet (GroupStr.is-set (snd (coHomGr n S²⋁S⁴)) _ _))
                       (λ f → cong ∣_∣₂ (funExt (λ x → rUnitₖ n (f x))))

    -- note that the proof might be simpliale by adding a second partition on T
    -- side, though it might complicated a bunch of things
    pres·-int : (n m : ℕ) → (a : ℤ) → (k l : ℕ) → (b : ℤ) →
                   ℤ[x,y]→H*-S²⋁S⁴ (base (n ∷ m ∷ []) a ·Pℤ base (k ∷ l ∷ []) b)
                ≡ ℤ[x,y]→H*-S²⋁S⁴ (base (n ∷ m ∷ []) a) cup ℤ[x,y]→H*-S²⋁S⁴ (base (k ∷ l ∷ []) b)

      -- non trivial case (0,0)
    pres·-int zero zero a zero zero          b = cong (base 0) (ϕₙ⌣ϕₘ _ ϕ₀str _ ϕ₀str _ ϕ₀str (ϕ₀-gen _ _) _ _)
    pres·-int zero zero a zero one           b = cong (base 4) (ϕₙ⌣ϕₘ _ ϕ₀str _ ϕ₄str _ ϕ₄str (ϕ₀-gen _ _) _ _)
    pres·-int zero zero a zero (suc (suc l)) b = refl
    pres·-int zero zero a one zero           b = cong (base 2) (ϕₙ⌣ϕₘ _ ϕ₀str _ ϕ₂str _ ϕ₂str (ϕ₀-gen _ _) _ _)
    pres·-int zero zero a one (suc l)        b = refl
    pres·-int zero zero a (suc (suc k)) l    b = refl
      -- non trivial case (0,1)
    pres·-int zero one a zero  zero         b = cong ℤ[x,y]→H*-S²⋁S⁴ (·PℤComm (base (0 ∷ 1 ∷ []) a) (base (0 ∷ 0 ∷ []) b))
                                                ∙ pres·-int 0 0 b 0 1 a
                                                ∙ gradCommRing S²⋁S⁴ _ _ _ _
    pres·-int zero one a zero  one          b = sym (base-neutral 8)
                                                ∙ cong (base 8) (unitGroupEq (Hⁿ-S²⋁S⁴≅0 _) _ _)
    pres·-int zero one a zero (suc (suc l)) b = refl
    pres·-int zero one a one zero           b = sym (base-neutral 6)
                                                ∙ cong (base 6) (unitGroupEq (Hⁿ-S²⋁S⁴≅0 _) _ _)
    pres·-int zero one a one (suc l)        b = refl
    pres·-int zero one a (suc (suc k)) l    b = refl
      -- trivial case (0, m+2)
    pres·-int zero (suc (suc m)) a  zero         l b = refl
    pres·-int zero (suc (suc m)) a  one          l b = refl
    pres·-int zero (suc (suc m)) a (suc (suc k)) l b = refl
      -- non trivial case (1,0)
    pres·-int one zero a zero zero          b = cong ℤ[x,y]→H*-S²⋁S⁴ (·PℤComm (base (1 ∷ 0 ∷ []) a) (base (0 ∷ 0 ∷ []) b))
                                                ∙ pres·-int 0 0 b 1 0 a
                                                ∙ gradCommRing S²⋁S⁴ _ _ _ _
    pres·-int one zero a zero one           b = cong ℤ[x,y]→H*-S²⋁S⁴ (·PℤComm (base (1 ∷ 0 ∷ []) a) (base (0 ∷ 1 ∷ []) b))
                                                ∙ pres·-int 0 1 b 1 0 a
                                                ∙ gradCommRing S²⋁S⁴ _ _ _ _
    pres·-int one zero a zero (suc (suc l)) b = refl
    pres·-int one zero a one zero           b = sym (base-neutral 4)
                                                ∙ cong (base 4) (sym (null-H² _ _))
    pres·-int one zero a one (suc l)        b = refl
    pres·-int one zero a (suc (suc k)) l    b = refl
      -- trivial case (1,m+1)
    pres·-int one (suc m) a  zero   l b = refl
    pres·-int one (suc m) a (suc k) l b = refl
      -- trivial case (n+2,m)
    pres·-int (suc (suc n)) m a k l b = refl



    pres·-base-case-vec : (v : Vec ℕ 2) → (a : ℤ) → (v' : Vec ℕ 2) → (b : ℤ) →
                             ℤ[x,y]→H*-S²⋁S⁴ (base v a ·Pℤ base v' b)
                          ≡ ℤ[x,y]→H*-S²⋁S⁴ (base v a) cup ℤ[x,y]→H*-S²⋁S⁴ (base v' b)
    pres·-base-case-vec (n ∷ m ∷ []) a (k ∷ l ∷ []) b = pres·-int n m a k l b

    -- proof of the morphism
    ℤ[x,y]→H*-S²⋁S⁴-pres· : (x y : ℤ[x,y]) → ℤ[x,y]→H*-S²⋁S⁴ (x ·Pℤ y) ≡ ℤ[x,y]→H*-S²⋁S⁴ x cup ℤ[x,y]→H*-S²⋁S⁴ y
    ℤ[x,y]→H*-S²⋁S⁴-pres· = DS-Ind-Prop.f _ _ _ _
                           (λ x p q i y j → isSetH* _ _ (p y) (q y) i j)
                           (λ y → refl)
                           base-case
                           λ {U V} ind-U ind-V y → cong₂ _+H*_ (ind-U y) (ind-V y)
      where
      base-case : _
      base-case v a = DS-Ind-Prop.f _ _ _ _ (λ _ → isSetH* _ _)
                             (sym (RingTheory.0RightAnnihilates (H*R S²⋁S⁴) _))
                             (λ v' b → pres·-base-case-vec v a v' b )
                             λ {U V} ind-U ind-V → (cong₂ _+H*_ ind-U ind-V) ∙ sym (·H*DistR+ _ _ _)


  -----------------------------------------------------------------------------
  -- Function on ℤ[x]/x + morphism

    -- not a trivial cancel ?
    ℤ[x,y]→H*-S²⋁S⁴-cancel : (x : Fin 3) → ℤ[x,y]→H*-S²⋁S⁴ (<XY,X²,Y²> x) ≡ 0H*
    ℤ[x,y]→H*-S²⋁S⁴-cancel zero = refl
    ℤ[x,y]→H*-S²⋁S⁴-cancel one = refl
    ℤ[x,y]→H*-S²⋁S⁴-cancel two = refl

    ℤ[X,Y]→H*-S²⋁S⁴ : RingHom (CommRing→Ring ℤ[X,Y]) (H*R S²⋁S⁴)
    fst ℤ[X,Y]→H*-S²⋁S⁴ = ℤ[x,y]→H*-S²⋁S⁴
    snd ℤ[X,Y]→H*-S²⋁S⁴ = makeIsRingHom ℤ[x,y]→H*-S²⋁S⁴-pres1Pℤ
                                          ℤ[x,y]→H*-S²⋁S⁴-pres+
                                          ℤ[x,y]→H*-S²⋁S⁴-pres·

    -- hence not a trivial pres+, yet pres0 still is
    ℤ[X,Y]/<XY,X²,Y²>→H*R-S²⋁S⁴ : RingHom (CommRing→Ring ℤ[X,Y]/<XY,X²,Y²>) (H*R S²⋁S⁴)
    ℤ[X,Y]/<XY,X²,Y²>→H*R-S²⋁S⁴ = Quotient-FGideal-CommRing-Ring.inducedHom
                                    ℤ[X,Y] (H*R S²⋁S⁴) ℤ[X,Y]→H*-S²⋁S⁴
                                    <XY,X²,Y²> ℤ[x,y]→H*-S²⋁S⁴-cancel

    ℤ[x,y]/<xy,x²,y²>→H*-S²⋁S⁴ : ℤ[x,y]/<xy,x²,y²> → H* S²⋁S⁴
    ℤ[x,y]/<xy,x²,y²>→H*-S²⋁S⁴ = fst ℤ[X,Y]/<XY,X²,Y²>→H*R-S²⋁S⁴

    ℤ[x,y]/<xy,x²,y²>→H*-S²⋁S⁴-pres0 : ℤ[x,y]/<xy,x²,y²>→H*-S²⋁S⁴ 0PℤI ≡ 0H*
    ℤ[x,y]/<xy,x²,y²>→H*-S²⋁S⁴-pres0 = refl

    ℤ[x,y]/<xy,x²,y²>→H*-S²⋁S⁴-pres+ : (x y : ℤ[x,y]/<xy,x²,y²>) →
                                             ℤ[x,y]/<xy,x²,y²>→H*-S²⋁S⁴ ( x +PℤI y)
                                          ≡ ℤ[x,y]/<xy,x²,y²>→H*-S²⋁S⁴ x +H* ℤ[x,y]/<xy,x²,y²>→H*-S²⋁S⁴ y
    ℤ[x,y]/<xy,x²,y²>→H*-S²⋁S⁴-pres+ x y = IsRingHom.pres+ (snd ℤ[X,Y]/<XY,X²,Y²>→H*R-S²⋁S⁴) x y


  -----------------------------------------------------------------------------
  -- Converse Sens on H* → ℤ[X,Y]

    ϕ⁻¹ : (k : ℕ) → (a : coHom k S²⋁S⁴) → (x : partℕ k) → ℤ[x,y]
    ϕ⁻¹ k a (is0 x) = base (0 ∷ 0 ∷ []) (ϕ₀⁻¹ (substG x a))
    ϕ⁻¹ k a (is2 x) = base (1 ∷ 0 ∷ []) (ϕ₂⁻¹ (substG x a))
    ϕ⁻¹ k a (is4 x) = base (0 ∷ 1 ∷ []) (ϕ₄⁻¹ (substG x a))
    ϕ⁻¹ k a (else x) = 0Pℤ

    H*-S²⋁S⁴→ℤ[x,y] : H* S²⋁S⁴ → ℤ[x,y]
    H*-S²⋁S⁴→ℤ[x,y] = DS-Rec-Set.f _ _ _ _ isSetPℤ
         0Pℤ
         (λ k a → ϕ⁻¹ k a (part k))
         _+Pℤ_
         +PℤAssoc
         +PℤIdR
         +PℤComm
         (λ k → base-neutral-eq k (part k))
         λ k a b → base-add-eq k a b (part k)
      where

      base-neutral-eq : (k : ℕ) → (x : partℕ k) → ϕ⁻¹ k (0ₕ k) x ≡ 0Pℤ
      base-neutral-eq k (is0 x) = cong (base (0 ∷ 0 ∷ [])) (cong ϕ₀⁻¹ (substG0 x))
                                  ∙ cong (base (0 ∷ 0 ∷ [])) (pres1 ϕ₀⁻¹str)
                                  ∙ base-neutral (0 ∷ 0 ∷ [])
      base-neutral-eq k (is2 x) = cong (base (1 ∷ 0 ∷ [])) (cong ϕ₂⁻¹ (substG0 x))
                                  ∙ cong (base (1 ∷ 0 ∷ [])) (pres1 ϕ₂⁻¹str)
                                  ∙ base-neutral (1 ∷ 0 ∷ [])
      base-neutral-eq k (is4 x) = cong (base (0 ∷ 1 ∷ [])) (cong ϕ₄⁻¹ (substG0 x))
                                  ∙ cong (base (0 ∷ 1 ∷ [])) (pres1 ϕ₄⁻¹str)
                                  ∙ base-neutral (0 ∷ 1 ∷ [])
      base-neutral-eq k (else x) = refl

      base-add-eq : (k : ℕ) → (a b : coHom k S²⋁S⁴) → (x : partℕ k)
                    → ϕ⁻¹ k a x +Pℤ ϕ⁻¹ k b x ≡ ϕ⁻¹ k (a +ₕ b) x
      base-add-eq k a b (is0 x) = base-add _ _ _
                                  ∙ cong (base (0 ∷ 0 ∷ [])) (sym (pres· ϕ₀⁻¹str _ _) ∙ cong ϕ₀⁻¹ (substG+ a b x))
      base-add-eq k a b (is2 x) = base-add _ _ _
                                  ∙ cong (base (1 ∷ 0 ∷ [])) (sym (pres· ϕ₂⁻¹str _ _) ∙ cong ϕ₂⁻¹ (substG+ a b x))
      base-add-eq k a b (is4 x) = base-add _ _ _
                                  ∙ cong (base (0 ∷ 1 ∷ [])) (sym (pres· ϕ₄⁻¹str _ _) ∙ cong ϕ₄⁻¹ (substG+ a b x))
      base-add-eq k a b (else x) = +PℤIdR _


    H*-S²⋁S⁴→ℤ[x,y]/<xy,x²,y²> : H* S²⋁S⁴ → ℤ[x,y]/<xy,x²,y²>
    H*-S²⋁S⁴→ℤ[x,y]/<xy,x²,y²> = [_] ∘ H*-S²⋁S⁴→ℤ[x,y]

    H*-S²⋁S⁴→ℤ[x,y]/<xy,x²,y²>-pres0 : H*-S²⋁S⁴→ℤ[x,y]/<xy,x²,y²> 0H* ≡ 0PℤI
    H*-S²⋁S⁴→ℤ[x,y]/<xy,x²,y²>-pres0 = refl

    H*-S²⋁S⁴→ℤ[x,y]/<xy,x²,y²>-pres+ : (x y : H* S²⋁S⁴) →
                                               H*-S²⋁S⁴→ℤ[x,y]/<xy,x²,y²> (x +H* y)
                                           ≡ (H*-S²⋁S⁴→ℤ[x,y]/<xy,x²,y²> x) +PℤI (H*-S²⋁S⁴→ℤ[x,y]/<xy,x²,y²> y)
    H*-S²⋁S⁴→ℤ[x,y]/<xy,x²,y²>-pres+ x y = refl



  -----------------------------------------------------------------------------
  -- Section

    e-sect-base : (k : ℕ) → (a : coHom k S²⋁S⁴) → (x : partℕ k) →
                  ℤ[x,y]→H*-S²⋁S⁴ (ϕ⁻¹ k a x) ≡ base k a
    e-sect-base k a (is0 x) = cong (base 0) (ϕ₀-sect (substG x a))
                              ∙ sym (constSubstCommSlice _ _ base x a)
    e-sect-base k a (is2 x) = cong (base 2) (ϕ₂-sect _)
                              ∙ sym (constSubstCommSlice _ _ base x a)
    e-sect-base k a (is4 x) = cong (base 4) (ϕ₄-sect _)
                              ∙ sym (constSubstCommSlice _ _ base x a)
    e-sect-base k a (else x) = sym (base-neutral k)
                               ∙ cong (base k) (unitGroupEq (Hⁿ-S²⋁S⁴≅0-bis k x) _ _)

    e-sect : (x : H* S²⋁S⁴) → ℤ[x,y]/<xy,x²,y²>→H*-S²⋁S⁴ (H*-S²⋁S⁴→ℤ[x,y]/<xy,x²,y²> x) ≡ x
    e-sect = DS-Ind-Prop.f _ _ _ _ (λ _ → isSetH* _ _)
             refl
             (λ k a → e-sect-base k a (part k))
             λ {U V} ind-U ind-V → ℤ[x,y]/<xy,x²,y²>→H*-S²⋁S⁴-pres+ _ _ ∙ cong₂ _+H*_ ind-U ind-V



  -----------------------------------------------------------------------------
  -- Retraction

    e-retr-base : (v : Vec ℕ 2) → (a : ℤ) →
                  H*-S²⋁S⁴→ℤ[x,y]/<xy,x²,y²> (ℤ[x,y]/<xy,x²,y²>→H*-S²⋁S⁴ [ base v a ]) ≡ [ base v a ]
    e-retr-base (zero        ∷ zero        ∷ []) a = cong [_] (cong (base (0 ∷ 0 ∷ [])) (cong ϕ₀⁻¹ (transportRefl (ϕ₀ a))))
                                                      ∙ cong [_] (cong (base (0 ∷ 0 ∷ [])) (ϕ₀-retr a))
    e-retr-base (zero        ∷ one         ∷ []) a = cong [_] (cong (base (0 ∷ 1 ∷ [])) (cong ϕ₄⁻¹ (transportRefl (ϕ₄ a))))
                                                      ∙ cong [_] (cong (base (0 ∷ 1 ∷ [])) (ϕ₄-retr a))
    e-retr-base (zero        ∷ suc (suc m) ∷ []) a = eq/ 0Pℤ (base (zero ∷ suc (suc m) ∷ []) a) ∣ (v , helper) ∣₁
                where
                v = λ { zero → 0Pℤ ; one → 0Pℤ ; two → base (0 ∷ m ∷ []) (-ℤ a) }
                helper : _
                helper = +PℤIdL _ ∙ sym (+PℤIdL _ ∙ +PℤIdL _ ∙ +PℤIdR _
                         ∙ cong₂ base (cong (λ X → 0 ∷ X ∷ []) (+-comm _ _)) (·ℤIdR _))
    e-retr-base (one         ∷ zero        ∷ []) a = cong [_] (cong (base (1 ∷ 0 ∷ [])) (cong ϕ₂⁻¹ (transportRefl (ϕ₂ a))))
                                                      ∙ cong [_] (cong (base (1 ∷ 0 ∷ [])) (ϕ₂-retr a))
    e-retr-base (one         ∷ suc m       ∷ []) a = eq/ 0Pℤ (base (one ∷ suc m ∷ []) a) ∣ (v , helper) ∣₁
                where
                v = λ { zero → base (0 ∷ m ∷ []) (-ℤ a) ; one → 0Pℤ ; two → 0Pℤ }
                helper : _
                helper = +PℤIdL _ ∙ sym (cong₂ _+Pℤ_ (cong₂ base (cong (λ X → 1 ∷ X ∷ []) (+-comm _ _)) (·ℤIdR _))
                         (+PℤIdL _ ∙ +PℤIdL _) ∙ +PℤIdR _)
    e-retr-base (suc (suc n) ∷ m           ∷ []) a = eq/ 0Pℤ (base (suc (suc n) ∷ m ∷ []) a) ∣ (v , helper) ∣₁
                where
                v = λ {zero → 0Pℤ ; one → base (n ∷ m ∷ []) (-ℤ a) ; two → 0Pℤ }
                helper : _
                helper = +PℤIdL _ ∙ sym (+PℤIdL _ ∙
                         cong₂ _+Pℤ_ (cong₂ base  (cong₂ (λ X → λ Y → X ∷ Y ∷ []) (+-comm _ _) (+-comm _ _)) (·ℤIdR _))
                         (+PℤIdL _) ∙ +PℤIdR _)
    e-retr : (x : ℤ[x,y]/<xy,x²,y²>) → H*-S²⋁S⁴→ℤ[x,y]/<xy,x²,y²> (ℤ[x,y]/<xy,x²,y²>→H*-S²⋁S⁴ x) ≡ x
    e-retr = SQ.elimProp (λ _ → isSetPℤI _ _)
             (DS-Ind-Prop.f _ _ _ _ (λ _ → isSetPℤI _ _)
             refl
             e-retr-base
             λ {U V} ind-U ind-V → cong₂ _+PℤI_ ind-U ind-V)

-----------------------------------------------------------------------------
-- Computation of the Cohomology Ring

module _ where

  open Equiv-RP2-Properties
  open IssueComputation (invGroupIso H⁴-S²⋁S⁴≅ℤ)

  S²⋁S⁴-CohomologyRing : RingEquiv (CommRing→Ring ℤ[X,Y]/<XY,X²,Y²>) (H*R S²⋁S⁴)
  fst S²⋁S⁴-CohomologyRing = isoToEquiv is
    where
    is : Iso ℤ[x,y]/<xy,x²,y²> (H* S²⋁S⁴)
    fun is = ℤ[x,y]/<xy,x²,y²>→H*-S²⋁S⁴
    inv is = H*-S²⋁S⁴→ℤ[x,y]/<xy,x²,y²>
    rightInv is = e-sect
    leftInv is = e-retr
  snd S²⋁S⁴-CohomologyRing = snd ℤ[X,Y]/<XY,X²,Y²>→H*R-S²⋁S⁴

  CohomologyRing-S²⋁S⁴ : RingEquiv (H*R S²⋁S⁴) (CommRing→Ring ℤ[X,Y]/<XY,X²,Y²>)
  CohomologyRing-S²⋁S⁴ = RingEquivs.invRingEquiv S²⋁S⁴-CohomologyRing
