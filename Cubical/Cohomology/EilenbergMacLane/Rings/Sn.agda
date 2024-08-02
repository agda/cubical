{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Cohomology.EilenbergMacLane.Rings.Sn where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Cohomology.EilenbergMacLane.Base
open import Cubical.Cohomology.EilenbergMacLane.Groups.Sn
open import Cubical.Cohomology.EilenbergMacLane.CupProduct
open import Cubical.Cohomology.EilenbergMacLane.RingStructure

open import Cubical.Homotopy.EilenbergMacLane.Base
open import Cubical.Homotopy.EilenbergMacLane.Properties
open import Cubical.Homotopy.EilenbergMacLane.CupProduct
open import Cubical.Homotopy.Connected

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Unit
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Vec
open import Cubical.Data.FinData
open import Cubical.Data.Sum

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.SetQuotients as SQ renaming (_/_ to _sq/_)
open import Cubical.HITs.EilenbergMacLane1
open import Cubical.HITs.Susp
open import Cubical.HITs.S1 renaming (rec to S¹Fun)
open import Cubical.HITs.Sn

open import Cubical.Algebra.GradedRing.DirectSumHIT
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.DirectSum.DirectSumHIT.Base
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Quotient
open import Cubical.Algebra.CommRing.Instances.Polynomials.MultivariatePoly
open import Cubical.Algebra.CommRing.Instances.Polynomials.MultivariatePoly-Quotient
open import Cubical.Algebra.Monoid.Instances.Nat

open PlusBis
open RingTheory


-- open import Cubical.Agebra.Monoids.Instance.NatVec

module _ {ℓ : Level} (G : CommRing ℓ) (n : ℕ) where
  G[x] = Poly G 1

  G[X] = CommRing→Ring (PolyCommRing G 1)

  G[X]/<X²> = A[X1,···,Xn]/<Xkʲ> G 1 0 2

  private
    GRing = CommRing→Ring G
    GAb = CommRing→AbGroup G

  open GradedRing-⊕HIT-index
    NatMonoid
    (Poly G)
    (λ n → CommRing→AbGroup (PolyCommRing G n) .snd)

  module H*Sⁿ = RingStr (snd (H*R GRing (S₊ (suc n))))
  module G[X]Str = RingStr (snd G[X])

  private
    _cupS_ = H*Sⁿ._·_
    _·GX_ = G[X]Str._·_

  G[X]→H*[Sⁿ,G]-main : Vec ℕ 1 → fst G → fst (H*R GRing (S₊ (suc n)))
  G[X]→H*[Sⁿ,G]-main (zero ∷ []) g = base 0 (invEquiv (H⁰[Sⁿ,G]≅G GAb n .fst) .fst g)
  G[X]→H*[Sⁿ,G]-main (one ∷ []) g = base (suc n) (invEq (Hⁿ[Sⁿ,G]≅G GAb n .fst) g)
  G[X]→H*[Sⁿ,G]-main (suc (suc x) ∷ []) g = ⊕HIT.neutral

  G[X]→H*[Sⁿ,G]-main-coh₁ : (r : Vec ℕ 1)
    → G[X]→H*[Sⁿ,G]-main r (CommRingStr.0r (snd G)) ≡ neutral
  G[X]→H*[Sⁿ,G]-main-coh₁ (zero ∷ []) = base-neutral 0
  G[X]→H*[Sⁿ,G]-main-coh₁ (one ∷ []) =
      cong (base (suc n)) (IsGroupHom.pres1 (invGroupEquiv (Hⁿ[Sⁿ,G]≅G GAb n) .snd) )
    ∙ base-neutral (suc n)
  G[X]→H*[Sⁿ,G]-main-coh₁ (suc (suc x) ∷ []) = refl

  G[X]→H*[Sⁿ,G]-main-coh₂ : (r : Vec ℕ 1) (a b : fst G)
     → (G[X]→H*[Sⁿ,G]-main r a add G[X]→H*[Sⁿ,G]-main r b)
      ≡ G[X]→H*[Sⁿ,G]-main r ((snd (CommRing→Ring G) RingStr.+ a) b)
  G[X]→H*[Sⁿ,G]-main-coh₂ (zero ∷ []) a b = base-add 0 ∣ (λ _ → a) ∣₂ ∣ (λ _ → b) ∣₂
  G[X]→H*[Sⁿ,G]-main-coh₂ (one ∷ []) a b =
    base-add (suc n) _ _
    ∙ cong (base (suc n))
       (sym (IsGroupHom.pres· (invGroupEquiv (Hⁿ[Sⁿ,G]≅G GAb n) .snd) a b))
  G[X]→H*[Sⁿ,G]-main-coh₂ (suc (suc x) ∷ []) a b = addRid neutral

  G[X]→H*[Sⁿ,G]-fun : G[x] → fst (H*R GRing (S₊ (suc n)))
  G[X]→H*[Sⁿ,G]-fun =
    DS-Rec-Set.f _ _ _ _  H*Sⁿ.is-set
      neutral
      G[X]→H*[Sⁿ,G]-main
      _add_
      addAssoc
      addRid
      addComm
      G[X]→H*[Sⁿ,G]-main-coh₁
      G[X]→H*[Sⁿ,G]-main-coh₂

  Hⁿ[Sⁿ,G]≅G-pres⌣ : (n : ℕ) (G : Ring ℓ) (g : fst G)
    (x : coHom (suc n) (Ring→AbGroup G) (S₊ (suc n)))
    → Hⁿ[Sⁿ,G]≅G (Ring→AbGroup G)  n .fst .fst
        (_⌣_ {G'' = G} {n = 0} {suc n} ∣ (λ _ → g) ∣₂ x)
    ≡ RingStr._·_ (snd G) g (Hⁿ[Sⁿ,G]≅G (Ring→AbGroup G)  n .fst .fst x)
  Hⁿ[Sⁿ,G]≅G-pres⌣ zero G g =
    ST.elim (λ _ → isOfHLevelPath 2 (RingStr.is-set (snd G)) _ _)
      (S¹-connElim (isConnectedEM 1)
        (λ _ → RingStr.is-set (snd G) _ _)
        embase
        λ p → cong (H¹S¹→G (Ring→AbGroup G))
                (cong (_⌣_ {G'' = G} {n = 0} {1} ∣ (λ _ → g) ∣₂)
                  (cong (∣_∣₂ ∘ S¹Fun embase)
                    (sym (Iso.rightInv (Iso-EM-ΩEM+1 0) p))))
            ∙∙ help (ΩEM+1→EM 0 p)
            ∙∙ cong (RingStr._·_ (snd G) g) (λ _ → ΩEM+1→EM 0 p))
    where
    help : (h : fst G)
      → H¹S¹→G (Ring→AbGroup G)
          (_⌣_ {G'' = G} {n = 0} {1} ∣ (λ _ → g) ∣₂
                                     ∣ S¹Fun embase (emloop h) ∣₂)
        ≡ RingStr._·_ (snd G) g h
    help h = Iso.leftInv (Iso-EM-ΩEM+1 0) (RingStr._·_ (snd G) g h)
  Hⁿ[Sⁿ,G]≅G-pres⌣ (suc n) G g =
    ST.elim (λ _ → isOfHLevelPath 2 (RingStr.is-set (snd G)) _ _)
      (Sⁿ-connElim n (isConnectedSubtr 2 (suc n)
        (subst (λ k → isConnected (suc k) (EM (Ring→AbGroup G) (suc (suc n))))
               (+-comm 2 n) (isConnectedEM (2 +ℕ n))))
        (λ _ → RingStr.is-set (snd G) _ _) ∣ north ∣ₕ
        λ f → cong (fst (Hⁿ[Sⁿ,G]≅G (Ring→AbGroup G) n) .fst)
          (cong ∣_∣₂ (funExt (λ x → sym (ΩEM+1→EM-distr⌣ₖ0n {G'' = G} (suc n) g _))))
        ∙ Hⁿ[Sⁿ,G]≅G-pres⌣ n G g _)

  G[X]→H*[Sⁿ,G]-pres· : (x y : G[x])
    → G[X]→H*[Sⁿ,G]-fun (x ·GX y)
    ≡ (G[X]→H*[Sⁿ,G]-fun x cupS G[X]→H*[Sⁿ,G]-fun y)
  G[X]→H*[Sⁿ,G]-pres· = DS-Ind-Prop.f _ _ _ _
    (λ _ → isPropΠ λ _ → H*Sⁿ.is-set _ _)
    (λ _ → refl)
    G[X]→H*[Sⁿ,G]-pres·+
    λ {x} {y} p q s → cong (G[X]→H*[Sⁿ,G]-fun) (G[X]Str.·DistL+ x y s)
                     ∙ cong₂ _add_ (p s) (q s)
                     ∙ sym (H*Sⁿ.·DistL+ (G[X]→H*[Sⁿ,G]-fun x)
                         (G[X]→H*[Sⁿ,G]-fun y) (G[X]→H*[Sⁿ,G]-fun s))
    where
    main₀₁ : (g g' : fst G) → _ ≡ _
    main₀₁ g g' =
        (cong (invEq (Hⁿ[Sⁿ,G]≅G GAb n .fst))
           (cong₂ (CommRingStr._·_ (snd G)) refl
             (sym (secEq (Hⁿ[Sⁿ,G]≅G (Ring→AbGroup GRing) n .fst) g')))
      ∙∙ cong (invEq (Hⁿ[Sⁿ,G]≅G (Ring→AbGroup GRing) n .fst))
                (sym (Hⁿ[Sⁿ,G]≅G-pres⌣ n GRing g (invEq (Hⁿ[Sⁿ,G]≅G GAb n .fst) g')))
      ∙∙ retEq (Hⁿ[Sⁿ,G]≅G (Ring→AbGroup GRing) n .fst) _)

    main : (v v' : Vec ℕ 1) (g g' : fst G)
      → G[X]→H*[Sⁿ,G]-fun (base v g ·GX base v' g')
       ≡ (G[X]→H*[Sⁿ,G]-fun (base v g) cupS G[X]→H*[Sⁿ,G]-fun (base v' g'))
    main (zero ∷ []) (zero ∷ []) g g' = refl
    main (zero ∷ []) (one ∷ []) g g' = cong (base (suc n)) (main₀₁ g g')
    main (zero ∷ []) (suc (suc w) ∷ []) g g' = refl
    main (one ∷ []) (zero ∷ []) g g' =
        (λ j → base (+'-comm 0 (suc n) j)
                (transp (λ k → coHom (+'-comm 0 (suc n) (k ∧ j))
                                 GAb (S₊ (suc n))) (~ j)
                 (invEq (Hⁿ[Sⁿ,G]≅G GAb n .fst) (CommRingStr._·_ (snd G) g g'))))
      ∙ cong (base (suc n +' zero))
        (cong (subst (λ k → coHom k GAb (S₊ (suc n))) (+'-comm 0 (suc n)))
             (cong (invEq (Hⁿ[Sⁿ,G]≅G GAb n .fst)) (CommRingStr.·Comm (snd G) g g')
            ∙ main₀₁ g' g
            ∙ sym (-ₕ^[_·_]-even (suc n) 0 (inr tt) _))
      ∙ sym (comm⌣ (suc n) 0 (invEq (Hⁿ[Sⁿ,G]≅G GAb n .fst) g)
             (invEquiv (H⁰[Sⁿ,G]≅G GAb n .fst) .fst g')))
    main (one ∷ []) (one ∷ []) g g' =
        sym (base-neutral (suc n +' suc n))
      ∙ cong (base (suc n +' suc n))
        (isContr→isProp
          (subst (λ k → isContr (coHom (suc k) GAb (S₊ (suc n))))
            (+-suc n n) (isContr-Hᵐ⁺ⁿ[Sⁿ,G] GAb n n)) _ _)
    main (one ∷ []) (suc (suc w) ∷ []) g g' = refl
    main (suc (suc v) ∷ []) (w ∷ []) g g' = refl

    G[X]→H*[Sⁿ,G]-pres·+ : (r : Vec ℕ 1) (a : fst G) (y : G[x])
      → G[X]→H*[Sⁿ,G]-fun (base r a ·GX y)
      ≡ G[X]→H*[Sⁿ,G]-fun (base r a) cupS G[X]→H*[Sⁿ,G]-fun y
    G[X]→H*[Sⁿ,G]-pres·+ v a = DS-Ind-Prop.f _ _ _ _ (λ _ → H*Sⁿ.is-set _ _)
      (cong (G[X]→H*[Sⁿ,G]-fun)
          (0RightAnnihilates G[X] (base v a))
         ∙ sym (0RightAnnihilates
        (H*R GRing (S₊ (suc n))) (G[X]→H*[Sⁿ,G]-fun (base v a) )))
      (λ r t → main v r a t)
      λ {x} {y} p q → cong (G[X]→H*[Sⁿ,G]-fun) (G[X]Str.·DistR+ (base v a) x y)
                     ∙ cong₂ _add_ p q
                     ∙ sym (H*Sⁿ.·DistR+ (G[X]→H*[Sⁿ,G]-fun (base v a))
                         (G[X]→H*[Sⁿ,G]-fun x) (G[X]→H*[Sⁿ,G]-fun y))

  G[X]→H*[Sⁿ,G] : RingHom G[X] (H*R GRing (S₊ (suc n)))
  fst G[X]→H*[Sⁿ,G] = G[X]→H*[Sⁿ,G]-fun
  snd G[X]→H*[Sⁿ,G] = makeIsRingHom refl (λ _ _ → refl) G[X]→H*[Sⁿ,G]-pres·

  open Quotient-FGideal-CommRing-Ring (PolyCommRing G 1) (H*R GRing (S₊ (suc n)))
     G[X]→H*[Sⁿ,G] (<Xkʲ> G 1 0 2)
      (λ { zero → refl})

  G[X]/<X²>→H*[Sⁿ,G] : RingHom (CommRing→Ring G[X]/<X²>) (H*R GRing (S₊ (suc n)))
  G[X]/<X²>→H*[Sⁿ,G] = inducedHom

  H*[Sⁿ,G]→G[X]/<X²>-fun^ : (m : ℕ) → Trichotomy n m
    → (x : coHom (suc m) GAb (S₊ (suc n))) → G[X]/<X²> .fst
  H*[Sⁿ,G]→G[X]/<X²>-fun^ m (lt p) x = [ neutral ]
  H*[Sⁿ,G]→G[X]/<X²>-fun^ m (eq e) x =
    [ base (1 ∷ []) (Hⁿ[Sⁿ,G]≅G GAb n .fst .fst (subst (λ k → coHom (suc k) GAb (S₊ (suc n))) (sym e) x)) ]
  H*[Sⁿ,G]→G[X]/<X²>-fun^ m (gt q) x = [ neutral ]

  H*[Sⁿ,G]→G[X]/<X²>-fun : (m : ℕ) (x : coHom m GAb (S₊ (suc n)))
    → G[X]/<X²> .fst
  H*[Sⁿ,G]→G[X]/<X²>-fun zero x = [ base (0 ∷ []) (H⁰[Sⁿ,G]≅G GAb n .fst .fst x) ]
  H*[Sⁿ,G]→G[X]/<X²>-fun (suc m) x = H*[Sⁿ,G]→G[X]/<X²>-fun^ m (n ≟ m) x

  H*[Sⁿ,G]→G[X]/<X²>-fun-coh₁ : (r : ℕ) → H*[Sⁿ,G]→G[X]/<X²>-fun r (0ₕ r) ≡ [ neutral ]
  H*[Sⁿ,G]→G[X]/<X²>-fun-coh₁ zero =
    cong [_] (cong (base (0 ∷ [])) (IsGroupHom.pres1 (H⁰[Sⁿ,G]≅G GAb n .snd))
    ∙ base-neutral (0 ∷ []))
  H*[Sⁿ,G]→G[X]/<X²>-fun-coh₁ (suc r) = help (n ≟ r)
    where
    help : (e : _) → H*[Sⁿ,G]→G[X]/<X²>-fun^ r e (0ₕ (suc r)) ≡ [ neutral ]
    help (lt x) = refl
    help (eq x) = cong [_]
      (cong (base (1 ∷ []))
         (cong (Hⁿ[Sⁿ,G]≅G GAb n .fst .fst)
           (λ j → transp (λ i → coHom (suc (x (~ i ∧ ~ j))) GAb (S₊ (suc n)))
                    j (0ₕ (suc (x (~ j)))))
        ∙ IsGroupHom.pres1 (Hⁿ[Sⁿ,G]≅G GAb n .snd))
        ∙ base-neutral (1 ∷ []))
    help (gt x) = refl

  H*[Sⁿ,G]→G[X]/<X²>-fun-coh₂ : (r : ℕ) (x y : coHom r GAb (S₊ (suc n)))
    → CommRingStr._+_ (snd (G[X]/<X²>))
        (H*[Sⁿ,G]→G[X]/<X²>-fun r x) (H*[Sⁿ,G]→G[X]/<X²>-fun r y)
     ≡ H*[Sⁿ,G]→G[X]/<X²>-fun r (x +ₕ y)
  H*[Sⁿ,G]→G[X]/<X²>-fun-coh₂ zero x y =
    cong [_] (base-add (0 ∷ []) _ _
    ∙ cong (base (0 ∷ [])) (sym (IsGroupHom.pres· (H⁰[Sⁿ,G]≅G GAb n .snd) _ _)))
  H*[Sⁿ,G]→G[X]/<X²>-fun-coh₂ (suc r) x y = help (n ≟ r) x y
    where
    help : (p : _) (x y : coHom (suc r) GAb (S₊ (suc n)))
      → CommRingStr._+_ (snd (G[X]/<X²>))
          (H*[Sⁿ,G]→G[X]/<X²>-fun^ r p x)
          (H*[Sⁿ,G]→G[X]/<X²>-fun^ r p y)
       ≡ H*[Sⁿ,G]→G[X]/<X²>-fun^ r p (x +ₕ y)
    help (lt p) x y = cong [_] (addRid neutral)
    help (eq p) = help' r p
      where
      help' : (r : ℕ) (p : n ≡ r) (x y : _)
        → CommRingStr._+_ (snd G[X]/<X²>)
           (H*[Sⁿ,G]→G[X]/<X²>-fun^ r (eq p) x)
           (H*[Sⁿ,G]→G[X]/<X²>-fun^ r (eq p) y)
        ≡ H*[Sⁿ,G]→G[X]/<X²>-fun^ r (eq p) (x +ₕ y)
      help' = J> λ a b → cong [_]
        (cong₂ (λ x y → (base (1 ∷ []) x) add (base (1 ∷ []) y))
               (cong (Hⁿ[Sⁿ,G]≅G GAb n .fst .fst) (transportRefl a))
               (cong (Hⁿ[Sⁿ,G]≅G GAb n .fst .fst) (transportRefl b))
            ∙ base-add _ _ _
            ∙ cong (base (1 ∷ []))
               (sym (IsGroupHom.pres· (Hⁿ[Sⁿ,G]≅G GAb n .snd) _ _)
              ∙ cong (Hⁿ[Sⁿ,G]≅G GAb n .fst .fst) (sym (transportRefl (a +ₕ b)))))
    help (gt p) x y = cong [_] (addRid neutral)

  H*[Sⁿ,G]→G[X]/<X²> : fst (H*R GRing (S₊ (suc n))) → G[X]/<X²> .fst
  H*[Sⁿ,G]→G[X]/<X²> = DS-Rec-Set.f _ _ _ _ squash/
    [ neutral ]
    H*[Sⁿ,G]→G[X]/<X²>-fun
    (CommRingStr._+_ (snd (G[X]/<X²>)))
    (λ _ _ _ → CommRingStr.+Assoc (snd (G[X]/<X²>)) _ _ _)
    (λ _ → CommRingStr.+IdR (snd (G[X]/<X²>)) _)
    (λ _ _ → CommRingStr.+Comm (snd (G[X]/<X²>)) _ _)
    H*[Sⁿ,G]→G[X]/<X²>-fun-coh₁
    H*[Sⁿ,G]→G[X]/<X²>-fun-coh₂

  H*[Sⁿ,G]→G[X]/<X²>→H*[Sⁿ,G] : (x : fst (H*R GRing (S₊ (suc n))))
    → G[X]/<X²>→H*[Sⁿ,G] .fst (H*[Sⁿ,G]→G[X]/<X²> x) ≡ x
  H*[Sⁿ,G]→G[X]/<X²>→H*[Sⁿ,G] =
    DS-Ind-Prop.f _ _ _ _ (λ _ → trunc _ _)
      refl
      (λ { zero a → cong (base zero) (retEq (H⁰[Sⁿ,G]≅G GAb n .fst) a)
        ; (suc r) → help r (n ≟ r)})
      λ p q → IsRingHom.pres+ (G[X]/<X²>→H*[Sⁿ,G] .snd) _ _
            ∙ cong₂ _add_ p q
    where
    help : (r : ℕ) (p : _) (a : _)
      → G[X]/<X²>→H*[Sⁿ,G] .fst (H*[Sⁿ,G]→G[X]/<X²>-fun^ r p a)
       ≡ base (suc r) a
    help r (lt x) a =
      sym (base-neutral (suc r))
      ∙ cong (base (suc r))
        (isContr→isProp
          (subst (λ k → isContr (coHom k GAb (S₊ (suc n))))
            (cong suc (snd x))
           (isContr-Hᵐ⁺ⁿ[Sⁿ,G] GAb n (fst x))) _ _)
    help r (eq x) a =
      J (λ r x → (a :  coHom (suc r) GAb (S₊ (suc n)))
        → G[X]/<X²>→H*[Sⁿ,G] .fst (H*[Sⁿ,G]→G[X]/<X²>-fun^ r (eq x) a)
         ≡ base (suc r) a)
         (λ a → cong (base (suc n))
           (retEq (Hⁿ[Sⁿ,G]≅G GAb n .fst) _ ∙ transportRefl a)) x a
    help r (gt x) a =
      sym (base-neutral (suc r))
      ∙ cong (base (suc r))
        (isContr→isProp
          (subst (λ k → isContr (coHom (suc r) GAb (S₊ k)))
            (cong suc (snd x))
           (isOfHLevelRetractFromIso 0
             (equivToIso (fst (Hⁿ[Sᵐ⁺ⁿ,G]≅0 GAb r (fst x))))
              isContrUnit*)) _ _)

  G[X]/<X²>→H*[Sⁿ,G]→H*[Sⁿ,G] : (x : G[X]/<X²> .fst)
    → H*[Sⁿ,G]→G[X]/<X²> (G[X]/<X²>→H*[Sⁿ,G] .fst x) ≡ x
  G[X]/<X²>→H*[Sⁿ,G]→H*[Sⁿ,G] = SQ.elimProp (λ _ → squash/ _ _)
    (DS-Ind-Prop.f _ _ _ _ (λ _ → squash/ _ _)
      refl
      (λ { (zero ∷ []) g → cong [_] (cong (base (0 ∷ []))
             (secEq (H⁰[Sⁿ,G]≅G GAb n .fst) g))
         ; (one ∷ []) g → h2 g _
         ; (suc (suc x) ∷ []) g
           → sym (eq/ _ neutral ∣ hh x g
             , (λ i → base (+-comm 2 x i ∷ []) (CommRingStr.·IdR (snd G) g (~ i))
                   add neutral) ∣₁)})
      λ p q → cong₂ (CommRingStr._+_ (snd (G[X]/<X²>))) p q)
    where
    hh : (x : ℕ) (g : fst G) → FinVec (fst (PolyCommRing G 1)) 1
    hh x g zero = base (x ∷ []) g

    h2 : (g : fst G) (p : _)
      → H*[Sⁿ,G]→G[X]/<X²>-fun^ n p
           (invEq (Hⁿ[Sⁿ,G]≅G GAb n .fst) g)
       ≡ [ base (one ∷ []) g ]
    h2 g (lt x) = ⊥.rec (¬m<m x)
    h2 g (eq x) = cong [_]
      (cong (base (1 ∷ []))
        (cong (Hⁿ[Sⁿ,G]≅G GAb n .fst .fst)
          ((λ j → subst (λ k → coHom (suc k) GAb (S₊ (suc n)))
                  (isSetℕ n n (sym x) refl j)
                  (invEq (Hⁿ[Sⁿ,G]≅G GAb n .fst) g))
        ∙ transportRefl (invEq (Hⁿ[Sⁿ,G]≅G GAb n .fst) g))
        ∙ secEq (Hⁿ[Sⁿ,G]≅G GAb n .fst) g))
    h2 g (gt x) = ⊥.rec (¬m<m x)


  G[X]/<X²>≅H*[Sⁿ,G] : RingEquiv (CommRing→Ring G[X]/<X²>) (H*R GRing (S₊ (suc n)))
  fst G[X]/<X²>≅H*[Sⁿ,G] =
    isoToEquiv (iso (G[X]/<X²>→H*[Sⁿ,G] .fst) H*[Sⁿ,G]→G[X]/<X²>
                    H*[Sⁿ,G]→G[X]/<X²>→H*[Sⁿ,G] G[X]/<X²>→H*[Sⁿ,G]→H*[Sⁿ,G])
  snd G[X]/<X²>≅H*[Sⁿ,G] = G[X]/<X²>→H*[Sⁿ,G] .snd

  H*[Sⁿ,G]≅G[X]/<X²> : RingEquiv (H*R GRing (S₊ (suc n))) (CommRing→Ring G[X]/<X²>)
  H*[Sⁿ,G]≅G[X]/<X²> = RingEquivs.invRingEquiv G[X]/<X²>≅H*[Sⁿ,G]
