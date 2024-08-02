{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Cohomology.EilenbergMacLane.Rings.RP2 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Cohomology.EilenbergMacLane.Base
open import Cubical.Cohomology.EilenbergMacLane.Groups.RP2
open import Cubical.Cohomology.EilenbergMacLane.CupProduct
open import Cubical.Cohomology.EilenbergMacLane.Rings.KleinBottle hiding (α↦1)
open import Cubical.Cohomology.EilenbergMacLane.Rings.RP2wedgeS1
open import Cubical.Cohomology.EilenbergMacLane.RingStructure

open import Cubical.Homotopy.EilenbergMacLane.Base
open import Cubical.Homotopy.EilenbergMacLane.GroupStructure
open import Cubical.Homotopy.EilenbergMacLane.Properties
open import Cubical.Homotopy.EilenbergMacLane.CupProduct
open import Cubical.Homotopy.EilenbergMacLane.CupProductTensor
  renaming (_⌣ₖ_ to _⌣ₖ⊗_ ; ⌣ₖ-0ₖ to ⌣ₖ-0ₖ⊗ ; 0ₖ-⌣ₖ to 0ₖ-⌣ₖ⊗)
open import Cubical.Homotopy.Loopspace

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Unit
open import Cubical.Data.Fin
open import Cubical.Data.Fin.Arithmetic
open import Cubical.Data.Vec
open import Cubical.Data.FinData renaming (Fin to FinI)

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.SetQuotients as SQ renaming (_/_ to _sq/_)
open import Cubical.HITs.EilenbergMacLane1 hiding (elimProp ; elimSet)
open import Cubical.HITs.Susp
open import Cubical.HITs.RPn

open import Cubical.Algebra.GradedRing.DirectSumHIT
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.IntMod
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.DirectSum.DirectSumHIT.Base
open import Cubical.Algebra.Ring
open import Cubical.Algebra.AbGroup.TensorProduct
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Quotient
open import Cubical.Algebra.CommRing.Instances.IntMod
open import Cubical.Algebra.CommRing.Instances.Polynomials.MultivariatePoly
open import Cubical.Algebra.CommRing.Instances.Polynomials.MultivariatePoly-Quotient
open import Cubical.Algebra.AbGroup.Instances.IntMod
open import Cubical.Algebra.Monoid.Instances.Nat

open PlusBis
open RingTheory


private
  α-raw : RP² → EM ℤ/2 1
  α-raw = gen-H¹RP²-raw

  α = ∣ α-raw ∣₂

  α↦1 : H¹[RP²,ℤ/2]≅ℤ/2 .fst .fst α ≡ 1
  α↦1 = refl

  γ-raw : RP² → EM ℤ/2 2
  γ-raw = RP²Fun (0ₖ 2) refl (Iso.inv Iso-Ω²K₂-ℤ/2 1)

  γ-raw⨂ : RP² → EM (ℤ/2 ⨂ ℤ/2) 2
  γ-raw⨂ = RP²Fun (0ₖ 2) refl (ℤ/2→Ω²K₂⨂ 1)

  γ : coHom 2 ℤ/2 RP²
  γ = ∣ γ-raw ∣₂

  γ↦1' : fst (fst H²[RP²,ℤ/2]≅ℤ/2) γ ≡ 1
  γ↦1' = γ↦1'' _ refl
    where
    -- silly lemma for faster type checking
    γ↦1'' : (p : fst ((Ω^ 2) (EM∙ ℤ/2 2)))
      → (p ≡ Iso.inv Iso-Ω²K₂-ℤ/2 1)
      → fst (fst H²[RP²,ℤ/2]≅ℤ/2) (∣ RP²Fun (0ₖ 2) refl p ∣₂) ≡ 1
    γ↦1'' p q =
        H²[RP²,ℤ/2]→ℤ/2-Id p
      ∙ cong (Iso.fun Iso-Ω²K₂-ℤ/2) q
      ∙ Iso.rightInv Iso-Ω²K₂-ℤ/2 1

  cp : EM ℤ/2 1 → EM ℤ/2 1 → EM (ℤ/2 ⨂ ℤ/2) 2
  cp = _⌣ₖ⊗_ {G' = ℤ/2} {H' = ℤ/2} {n = 1} {m = 1}

α²-raw⨂' : (x : RP²) → cp (α-raw x) (α-raw x) ≡ γ-raw⨂ x
α²-raw⨂' point = refl
α²-raw⨂' (line i) j = cong₂-⌣ (emloop 1) j i
α²-raw⨂' (square i j) k = filler i j k
  where
  Typ : (p : fst ((Ω^ 2) (EM∙ (ℤ/2 ⨂ ℤ/2) 2))) → Type
  Typ p =
    Cube (λ j k → cong₂-⌣ (emloop 1) k j)
         (λ j k → cong₂-⌣ (emloop (fsuc fzero)) k (~ j))
         (λ _ _ → ∣ north ∣) (λ _ _ → ∣ north ∣)
         (λ i j → cp (emloop-inv (ℤGroup/ 2) 1 i j)
                    (emloop-inv (ℤGroup/ 2) 1 i j))
         p

  filler : Typ (ℤ/2→Ω²K₂⨂ (fsuc fzero))
  filler = subst Typ (sym (ℤ/2→Flip₁ 1 1)) λ i j k → ▣₇ j (~ i) k

α²-raw' : (x : RP²) → _⌣ₖ_ {G'' = ℤ/2Ring} {n = 1} {m = 1} (α-raw x) (α-raw x)
                  ≡ γ-raw x
α²-raw' x = cong (EMTensorMult 2) (α²-raw⨂' x)
     ∙ lem x
     ∙ γ-raw≡ x
  where
  γ-raw' : RP² → EM ℤ/2 2
  γ-raw' point = 0ₖ 2
  γ-raw' (line i) = 0ₖ 2
  γ-raw' (square i j) = ℤ/2→Ω²K₂' 1 i j

  γ-raw≡ : (x : _) → γ-raw' x ≡ γ-raw x
  γ-raw≡ point = refl
  γ-raw≡ (line i) = refl
  γ-raw≡ (square i j) k = ℤ/2→Ω²K₂'≡ (~ k) i j

  lem : (x : _) → EMTensorMult {G'' = ℤ/2Ring} 2 (γ-raw⨂ x) ≡ γ-raw' x
  lem point = refl
  lem (line i) = refl
  lem (square i j) k =
    hcomp (λ r
      → λ {(i = i0) → EMTensorMult {G'' = ℤ/2Ring} 2
                         (EM→ΩEM+1-0ₖ 1 (r ∨ k) j)
          ; (i = i1) → EMTensorMult {G'' = ℤ/2Ring} 2
                         (EM→ΩEM+1-0ₖ 1 (r ∨ k) j)
          ; (j = i0) → 0ₖ 2
          ; (j = i1) → 0ₖ 2
          ; (k = i0) → EMTensorMult {G'' = ℤ/2Ring} 2
                         (doubleCompPath-filler
                           (sym (EM→ΩEM+1-0ₖ 1))
                           (cong (EM→ΩEM+1 1) (EM→ΩEM+1 0 (1 ⊗ 1)))
                           (EM→ΩEM+1-0ₖ 1) r i j)
          ; (k = i1) → ℤ/2→Ω²K₂' 1 i j})
      (hcomp (λ r
        → λ {(i = i0) → EMTensorMult {G'' = ℤ/2Ring} 2
                           ∣ rCancel-filler (merid embase) r k j ∣ₕ
            ; (i = i1) → EMTensorMult {G'' = ℤ/2Ring} 2
                           ∣ rCancel-filler (merid embase) r k j ∣ₕ
            ; (j = i0) → 0ₖ 2
            ; (j = i1) → EMTensorMult {G'' = ℤ/2Ring} 2
                           ∣ merid embase (~ r ∧ ~ k) ∣ₕ
            ; (k = i0) → EMTensorMult {G'' = ℤ/2Ring} 2
                           ∣ compPath-filler (merid (EM→ΩEM+1 0 (1 ⊗ 1) i))
                                             (sym (merid embase)) r j ∣ₕ
            ; (k = i1) → ℤ/2→Ω²K₂' 1 i j})
        (hcomp (λ r
          → λ {(i = i0) → ∣ rCancel-filler (merid embase) (~ r) k j ∣ₕ
              ; (i = i1) → ∣ rCancel-filler (merid embase) (~ r) k j ∣ₕ
              ; (j = i0) → 0ₖ 2
              ; (j = i1) → ∣ merid embase (~ k ∧ r) ∣ₕ
              ; (k = i0) → ∣ compPath-filler (merid (EM→ΩEM+1 0 1 i))
                                             (sym (merid embase)) (~ r) j ∣ₕ
              ; (k = i1) → ℤ/2→Ω²K₂' 1 i j})
         (doubleCompPath-filler
           (sym (EM→ΩEM+1-0ₖ 1))
           (cong (EM→ΩEM+1 1) (EM→ΩEM+1 0 1))
           (EM→ΩEM+1-0ₖ 1) k i j)))

α²≡γ : _⌣_ {G'' = ℤ/2Ring} α α ≡ γ
α²≡γ = cong ∣_∣₂ (funExt α²-raw')

-- open import Cubical.Agebra.Monoids.Instance.NatVec

module _ {ℓ : Level} (n : ℕ) where
  ℤ₂[x] = Poly ℤ/2CommRing 1

  ℤ₂[X] = CommRing→Ring (PolyCommRing ℤ/2CommRing 1)

  ℤ₂[X]/<X³> = A[X1,···,Xn]/<Xkʲ> ℤ/2CommRing 1 0 3

  open GradedRing-⊕HIT-index
    NatMonoid
    (Poly ℤ/2CommRing)
    (λ n → CommRing→AbGroup (PolyCommRing ℤ/2CommRing n) .snd)

  open RingStr (snd (H*R ℤ/2Ring RP²))
    renaming
    ( 0r        to 0H*RP
    ; 1r        to 1H*RP
    ; _+_       to _+H*RP_
    ; -_        to -H*RP_
    ; _·_       to _cupS_
    ; +Assoc    to +H*RPAssoc
    ; +IdR      to +H*RPIdR
    ; +Comm     to +H*RPComm
    ; ·Assoc    to ·H*RPAssoc
    ; is-set    to isSetH*RP
    ; ·DistR+   to ·DistR+H*
    ; ·DistL+   to ·DistL+H*)

  open RingStr (snd ℤ₂[X])
    renaming
    ( 0r        to 0Z₂X
    ; 1r        to 1Z₂X
    ; _+_       to _+Z₂X_
    ; -_        to -Z₂X_
    ; _·_       to _·Z₂X_
    ; +Assoc    to +Z₂XAssoc
    ; +IdR      to +Z₂XIdR
    ; +Comm     to +Z₂XComm
    ; ·Assoc    to ·Z₂XAssoc
    ; is-set    to isSetZ₂X
    ; ·DistR+   to ·DistR+Z₂
    ; ·DistL+   to ·DistL+Z₂)

  private
    H⁰[RP²,ℤ/2]≅ℤ/2 = H⁰[RP²,G]≅G ℤ/2

  α* : fst (H*R ℤ/2Ring RP²)
  α* = base 1 α

  γ* : fst (H*R ℤ/2Ring RP²)
  γ* = base 2 γ

  α*²≡γ* : α* cupS α* ≡ γ*
  α*²≡γ* = cong (base 2) α²≡γ

  α-isGen : base 1 (invEq (fst (H¹[RP²,ℤ/2]≅ℤ/2)) fone) ≡ α*
  α-isGen = cong (base 1)
    (cong (invEq (fst (H¹[RP²,ℤ/2]≅ℤ/2))) (sym α↦1)
    ∙ retEq (fst (H¹[RP²,ℤ/2]≅ℤ/2)) α)

  γ-isGen : base 2 (invEq (fst (H²[RP²,ℤ/2]≅ℤ/2)) fone) ≡ γ*
  γ-isGen = cong (base 2)
    (cong (invEq (fst (H²[RP²,ℤ/2]≅ℤ/2))) (sym γ↦1')
    ∙ retEq (fst (H²[RP²,ℤ/2]≅ℤ/2)) γ)

  ℤ₂[X]→H*[RP²,ℤ₂]-main' : (n : ℕ) (g : ℤ/2 .fst) → coHom n ℤ/2 RP²
  ℤ₂[X]→H*[RP²,ℤ₂]-main' zero g = invEq (H⁰[RP²,ℤ/2]≅ℤ/2 .fst) g
  ℤ₂[X]→H*[RP²,ℤ₂]-main' one g = invEq (H¹[RP²,ℤ/2]≅ℤ/2 .fst) g
  ℤ₂[X]→H*[RP²,ℤ₂]-main' two g = invEq (H²[RP²,ℤ/2]≅ℤ/2 .fst) g
  ℤ₂[X]→H*[RP²,ℤ₂]-main' (suc (suc (suc n))) g = 0ₕ (3 +ℕ n)

  ℤ₂[X]→H*[RP²,ℤ₂]-main : Vec ℕ 1 → ℤ/2 .fst → fst (H*R ℤ/2Ring RP²)
  ℤ₂[X]→H*[RP²,ℤ₂]-main (n ∷ []) g = base n (ℤ₂[X]→H*[RP²,ℤ₂]-main' n g)

  ℤ₂[X]→H*[RP²,ℤ₂]-main-coh₁ : (r : Vec ℕ 1) →
      ℤ₂[X]→H*[RP²,ℤ₂]-main r fzero ≡ neutral
  ℤ₂[X]→H*[RP²,ℤ₂]-main-coh₁ (zero ∷ []) = base-neutral 0
  ℤ₂[X]→H*[RP²,ℤ₂]-main-coh₁ (one ∷ []) =
    cong (base 1) (IsGroupHom.pres1 (invGroupEquiv (H¹[RP²,ℤ/2]≅ℤ/2) .snd))
    ∙ base-neutral 1
  ℤ₂[X]→H*[RP²,ℤ₂]-main-coh₁ (two ∷ []) =
    cong (base 2) (IsGroupHom.pres1 (invGroupEquiv (H²[RP²,ℤ/2]≅ℤ/2) .snd))
    ∙ base-neutral 2
  ℤ₂[X]→H*[RP²,ℤ₂]-main-coh₁ (suc (suc (suc s)) ∷ []) = base-neutral _

  ℤ₂[X]→H*[RP²,ℤ₂]-main-coh₂ : (r : Vec ℕ 1) (a b : Fin 2)
    → (ℤ₂[X]→H*[RP²,ℤ₂]-main r a add ℤ₂[X]→H*[RP²,ℤ₂]-main r b)
     ≡ ℤ₂[X]→H*[RP²,ℤ₂]-main r (a +ₘ b)
  ℤ₂[X]→H*[RP²,ℤ₂]-main-coh₂ (zero ∷ []) a b = base-add 0 _ _
  ℤ₂[X]→H*[RP²,ℤ₂]-main-coh₂ (one ∷ []) a b = base-add 1 _ _
    ∙ cong (base 1) (sym (IsGroupHom.pres· (invGroupEquiv (H¹[RP²,ℤ/2]≅ℤ/2) .snd) a b))
  ℤ₂[X]→H*[RP²,ℤ₂]-main-coh₂ (two ∷ []) a b = base-add 2 _ _
    ∙ cong (base 2) (sym (IsGroupHom.pres· (invGroupEquiv (H²[RP²,ℤ/2]≅ℤ/2) .snd) a b))
  ℤ₂[X]→H*[RP²,ℤ₂]-main-coh₂ (suc (suc (suc x)) ∷ []) a b =
    cong (base (suc (suc (suc x))) (0ₕ (suc (suc (suc x)))) add_) (base-neutral _)
    ∙ addRid _

  ℤ₂[X]→H*[RP²,ℤ₂]-fun : ℤ₂[x] → fst (H*R ℤ/2Ring RP²)
  ℤ₂[X]→H*[RP²,ℤ₂]-fun =
    DS-Rec-Set.f _ _ _ _ isSetH*RP
      neutral
      ℤ₂[X]→H*[RP²,ℤ₂]-main
      _add_
      addAssoc
      addRid
      addComm
      ℤ₂[X]→H*[RP²,ℤ₂]-main-coh₁
      ℤ₂[X]→H*[RP²,ℤ₂]-main-coh₂

  private
    isContrH³⁺ⁿ[RP²,G] : ∀ {ℓ} (n : ℕ) (G : AbGroup ℓ) → isContr (coHom (3 +ℕ n) G RP²)
    isContrH³⁺ⁿ[RP²,G] n G =
      isOfHLevelRetractFromIso 0
        (equivToIso (fst (H³⁺ⁿ[RP²,G]≅0 G n))) isContrUnit*

  ℤ/2[X]→H*[RP²,ℤ/2]-pres· : (x y : ℤ₂[x])
    → ℤ₂[X]→H*[RP²,ℤ₂]-fun (RingStr._·_ (snd ℤ₂[X]) x y)
    ≡ (ℤ₂[X]→H*[RP²,ℤ₂]-fun x cupS ℤ₂[X]→H*[RP²,ℤ₂]-fun y)
  ℤ/2[X]→H*[RP²,ℤ/2]-pres· =
    DS-Ind-Prop.f _ _ _ _
      (λ _ → isPropΠ λ _ → trunc _ _)
      (λ _ → refl)
      (λ v a →
      DS-Ind-Prop.f _ _ _ _
      (λ _ → trunc _ _)
      (cong (ℤ₂[X]→H*[RP²,ℤ₂]-fun)
        (0RightAnnihilates ℤ₂[X] (base v a))
        ∙ sym (0RightAnnihilates (H*R ℤ/2Ring RP²)
                (ℤ₂[X]→H*[RP²,ℤ₂]-fun (base v a))))
      (λ w b → main v w a b)
      λ {x} {y} p q → cong ℤ₂[X]→H*[RP²,ℤ₂]-fun (·DistR+Z₂ (base v a) x y)
                    ∙ cong₂ _add_ p q
                    ∙ sym (·DistR+H* (ℤ₂[X]→H*[RP²,ℤ₂]-fun (base v a))
                            (ℤ₂[X]→H*[RP²,ℤ₂]-fun x)
                            (ℤ₂[X]→H*[RP²,ℤ₂]-fun y)))
      λ {x} {y} p q z
       → cong (ℤ₂[X]→H*[RP²,ℤ₂]-fun)
           (·DistL+Z₂ x y z)
        ∙ cong₂ _add_ (p z) (q z)
    where
    main-main : (v w : Vec ℕ 1)
          → ℤ₂[X]→H*[RP²,ℤ₂]-fun (base v fone ·Z₂X base w fone)
           ≡ ℤ₂[X]→H*[RP²,ℤ₂]-fun (base v fone)
       cupS (ℤ₂[X]→H*[RP²,ℤ₂]-fun (base w fone))
    main-main (zero ∷ []) (w ∷ []) =
      cong (ℤ₂[X]→H*[RP²,ℤ₂]-fun)
         (RingStr.·IdL (snd ℤ₂[X]) (base (w ∷ []) fone))
        ∙ sym (RingStr.·IdL (snd (H*R ℤ/2Ring RP²))
                (ℤ₂[X]→H*[RP²,ℤ₂]-fun (base (w ∷ []) fone)))
    main-main (suc v ∷ []) (zero ∷ []) =
      cong (ℤ₂[X]→H*[RP²,ℤ₂]-fun)
         (RingStr.·IdR (snd ℤ₂[X]) (base (suc v ∷ []) fone))
        ∙ sym (RingStr.·IdR (snd (H*R ℤ/2Ring RP²))
                (ℤ₂[X]→H*[RP²,ℤ₂]-fun (base (suc v ∷ []) fone)))
    main-main (one ∷ []) (one ∷ []) =
      γ-isGen ∙ sym α*²≡γ* ∙ cong (λ x → x cupS x) (sym (α-isGen))
    main-main (one ∷ []) (suc (suc w₁) ∷ []) =
      cong (base (suc (suc (suc w₁))))
        (isContr→isProp (isContrH³⁺ⁿ[RP²,G] w₁ ℤ/2) _ _)
    main-main (suc (suc v) ∷ []) (suc w ∷ []) =
      cong (base (suc (suc v) +ℕ suc w))
        (isContr→isProp
          (subst (λ k → isContr (coHom (suc (suc k)) ℤ/2 RP²)) (sym (+-suc v w))
            (isContrH³⁺ⁿ[RP²,G] (v +ℕ w) ℤ/2)) _ (0ₕ _))
      ∙ (base-neutral _
      ∙ sym (base-neutral _))
      ∙ cong (base (suc (suc v) +' suc w))
        (isContr→isProp (isContrH³⁺ⁿ[RP²,G] (v +ℕ w) ℤ/2) (0ₕ _) _)

    main : (v w : Vec ℕ 1) (a b : ℤ/2 .fst)
      → ℤ₂[X]→H*[RP²,ℤ₂]-fun (base v a ·Z₂X base w b)
       ≡ ℤ₂[X]→H*[RP²,ℤ₂]-fun (base v a) cupS ℤ₂[X]→H*[RP²,ℤ₂]-fun (base w b)
    main v w = ℤ/2-elim
      (λ b →
        (cong ℤ₂[X]→H*[RP²,ℤ₂]-fun
          (cong (_·Z₂X base w b) (base-neutral v)
         ∙ 0LeftAnnihilates ℤ₂[X] (base w b))
         ∙ cong₂ _cupS_ (cong (ℤ₂[X]→H*[RP²,ℤ₂]-fun)
                        (sym (base-neutral v))) refl))
        (ℤ/2-elim
          (cong ℤ₂[X]→H*[RP²,ℤ₂]-fun
            (cong (base v fone ·Z₂X_) (base-neutral w)
            ∙ 0RightAnnihilates ℤ₂[X] (base w fone))
          ∙ sym (0RightAnnihilates (H*R ℤ/2Ring RP²)
                  (ℤ₂[X]→H*[RP²,ℤ₂]-fun (base v fone)))
          ∙ cong₂ _cupS_
                  (λ _ → ℤ₂[X]→H*[RP²,ℤ₂]-fun (base v fone))
                  (cong (ℤ₂[X]→H*[RP²,ℤ₂]-fun) (sym (base-neutral w))))
          (main-main v w))

  ℤ₂[X]→H*[RP²,ℤ₂] : RingHom ℤ₂[X] (H*R ℤ/2Ring RP²)
  fst ℤ₂[X]→H*[RP²,ℤ₂] = ℤ₂[X]→H*[RP²,ℤ₂]-fun
  snd ℤ₂[X]→H*[RP²,ℤ₂] = makeIsRingHom refl (λ _ _ → refl) ℤ/2[X]→H*[RP²,ℤ/2]-pres·

  open Quotient-FGideal-CommRing-Ring (PolyCommRing ℤ/2CommRing 1) (H*R ℤ/2Ring RP²)
     ℤ₂[X]→H*[RP²,ℤ₂] (<Xkʲ> ℤ/2CommRing 1 0 3)
      (λ { zero → base-neutral _})

  ℤ₂[X]/<X³>→H*[RP²,ℤ₂] : RingHom (CommRing→Ring ℤ₂[X]/<X³>) (H*R ℤ/2Ring RP²)
  ℤ₂[X]/<X³>→H*[RP²,ℤ₂] = inducedHom

  H*[RP²,ℤ₂]→ℤ₂[X]/<X³>-fun' : (r : ℕ) → coHom r ℤ/2 RP² → ℤ/2 .fst
  H*[RP²,ℤ₂]→ℤ₂[X]/<X³>-fun' zero x = H⁰[RP²,ℤ/2]≅ℤ/2 .fst .fst x
  H*[RP²,ℤ₂]→ℤ₂[X]/<X³>-fun' one x = H¹[RP²,ℤ/2]≅ℤ/2 .fst .fst x
  H*[RP²,ℤ₂]→ℤ₂[X]/<X³>-fun' two x = H²[RP²,ℤ/2]≅ℤ/2 .fst .fst x
  H*[RP²,ℤ₂]→ℤ₂[X]/<X³>-fun' (suc (suc (suc r))) x = fzero

  H*[RP²,ℤ₂]→ℤ₂[X]/<X³>-fun : (r : ℕ) → coHom r ℤ/2 RP² → ℤ₂[X]/<X³> .fst
  H*[RP²,ℤ₂]→ℤ₂[X]/<X³>-fun r x = [ base (r ∷ []) (H*[RP²,ℤ₂]→ℤ₂[X]/<X³>-fun' r x) ]

  H*[RP²,ℤ₂]→ℤ₂[X]/<X³> : H*R ℤ/2Ring RP² .fst → ℤ₂[X]/<X³> .fst
  H*[RP²,ℤ₂]→ℤ₂[X]/<X³> = DS-Rec-Set.f _ _ _ _ squash/
    [ neutral ]
    H*[RP²,ℤ₂]→ℤ₂[X]/<X³>-fun
    (CommRingStr._+_ (snd ℤ₂[X]/<X³>))
    (CommRingStr.+Assoc (snd ℤ₂[X]/<X³>))
    (CommRingStr.+IdR (snd ℤ₂[X]/<X³>))
    (CommRingStr.+Comm (snd ℤ₂[X]/<X³>))
    (λ { zero → cong [_] (base-neutral (0 ∷ []))
        ; one → cong [_] (cong (base (1 ∷ [])) (IsGroupHom.pres1 (snd (H¹[RP²,ℤ/2]≅ℤ/2)))
                ∙ base-neutral (1 ∷ []))
        ; two → cong [_] (cong (base (2 ∷ [])) (IsGroupHom.pres1 (snd (H²[RP²,ℤ/2]≅ℤ/2)))
                ∙ base-neutral (2 ∷ []))
        ; (suc (suc (suc r))) → cong [_] (base-neutral _)})
    (λ { zero a b → cong [_] (base-add (0 ∷ []) _ _
                             ∙ cong (base (0 ∷ []))
                                (sym (IsGroupHom.pres· (snd (H⁰[RP²,ℤ/2]≅ℤ/2)) a b)))
        ; one a b → cong [_] (base-add (1 ∷ []) _ _
                             ∙ cong (base (1 ∷ []))
                                (sym (IsGroupHom.pres· (snd (H¹[RP²,ℤ/2]≅ℤ/2)) a b)))
        ; two a b → cong [_] (base-add (2 ∷ []) _ _
                             ∙ cong (base (2 ∷ []))
                                (sym (IsGroupHom.pres· (snd (H²[RP²,ℤ/2]≅ℤ/2)) a b)))
        ; (suc (suc (suc r))) a b
          → cong [_] (cong₂ _add_ refl (base-neutral (3 +ℕ r ∷ []))
                     ∙ addRid _)})

  ℤ₂[X]/<X³>→H*[RP²,ℤ₂]→ℤ₂[X]/<X³> : (x : _)
    → H*[RP²,ℤ₂]→ℤ₂[X]/<X³> (ℤ₂[X]/<X³>→H*[RP²,ℤ₂] .fst x) ≡ x
  ℤ₂[X]/<X³>→H*[RP²,ℤ₂]→ℤ₂[X]/<X³> = SQ.elimProp (λ _ → squash/ _ _)
    (DS-Ind-Prop.f _ _ _ _ (λ _ → squash/ _ _)
    refl
    (λ { (zero ∷ []) a → cong [_] (cong (base (zero ∷ []))
                           (secEq (H⁰[RP²,ℤ/2]≅ℤ/2 .fst) a))
       ; (one ∷ []) a → cong [_] (cong (base (one ∷ []))
                           (secEq (H¹[RP²,ℤ/2]≅ℤ/2 .fst) a))
       ; (two ∷ []) a → cong [_] (cong (base (two ∷ []))
                           (secEq (H²[RP²,ℤ/2]≅ℤ/2 .fst) a))
       ; (suc (suc (suc r)) ∷ []) → ℤ/2-elim refl
         (sym (eq/ _ _ ∣ (λ {zero → base (r ∷ []) fone})
           , ((cong₂ _add_ refl (base-neutral _)
           ∙ addRid _
           ∙ λ i → base (+-comm 3 r i ∷ []) fone))
           ∙ sym (addRid _) ∣₁))})
    (λ p q → cong₂ (CommRingStr._+_ (snd ℤ₂[X]/<X³>)) p q))

  H*[RP²,ℤ₂]→ℤ₂[X]/<X³>→H*[RP²,ℤ₂] : (x : H*R ℤ/2Ring RP² .fst)
    → ℤ₂[X]/<X³>→H*[RP²,ℤ₂] .fst (H*[RP²,ℤ₂]→ℤ₂[X]/<X³> x) ≡ x
  H*[RP²,ℤ₂]→ℤ₂[X]/<X³>→H*[RP²,ℤ₂] = DS-Ind-Prop.f _ _ _ _
    (λ _ → trunc _ _)
    refl
    (λ { zero x → cong (base zero) (retEq (H⁰[RP²,ℤ/2]≅ℤ/2 .fst) x)
       ; one x → cong (base one) (retEq (H¹[RP²,ℤ/2]≅ℤ/2 .fst) x)
       ; two x → cong (base two) (retEq (H²[RP²,ℤ/2]≅ℤ/2 .fst) x)
       ; (suc (suc (suc r))) x → cong (base (3 +ℕ r))
         (isContr→isProp (isContrH³⁺ⁿ[RP²,G] r ℤ/2) _ _)})
    λ {x} {y} p q
      → (IsRingHom.pres+ (ℤ₂[X]/<X³>→H*[RP²,ℤ₂] .snd) _ _ ∙ cong₂ _add_ p q)

  ℤ₂[X]/<X³>≅H*[RP²,ℤ₂] : RingEquiv (CommRing→Ring ℤ₂[X]/<X³>) (H*R ℤ/2Ring RP²)
  fst ℤ₂[X]/<X³>≅H*[RP²,ℤ₂] =
    isoToEquiv (iso (ℤ₂[X]/<X³>→H*[RP²,ℤ₂] .fst) H*[RP²,ℤ₂]→ℤ₂[X]/<X³>
                    H*[RP²,ℤ₂]→ℤ₂[X]/<X³>→H*[RP²,ℤ₂]
                    ℤ₂[X]/<X³>→H*[RP²,ℤ₂]→ℤ₂[X]/<X³>)
  snd ℤ₂[X]/<X³>≅H*[RP²,ℤ₂] = ℤ₂[X]/<X³>→H*[RP²,ℤ₂] .snd

  H*[RP²,ℤ₂]≅ℤ₂[X]/<X³> : RingEquiv (H*R ℤ/2Ring RP²) (CommRing→Ring ℤ₂[X]/<X³>)
  H*[RP²,ℤ₂]≅ℤ₂[X]/<X³> = RingEquivs.invRingEquiv ℤ₂[X]/<X³>≅H*[RP²,ℤ₂]
