{-# OPTIONS --safe --lossy-unification #-}

module Cubical.Cohomology.EilenbergMacLane.MayerVietoris where

open import Cubical.Homotopy.EilenbergMacLane.GroupStructure
open import Cubical.Homotopy.EilenbergMacLane.Base
open import Cubical.Homotopy.EilenbergMacLane.Properties

open import Cubical.Cohomology.EilenbergMacLane.Base

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat
open import Cubical.Data.Sigma

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup.Base

open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.Pushout

open IsGroupHom

module MV {ℓ ℓ' ℓ'' ℓ'''} (G : AbGroup ℓ''')
          (A : Type ℓ) (B : Type ℓ') (C : Type ℓ'')
          (f : C → A) (g : C → B) where
  -- Proof from Brunerie 2016.
  -- We first define the three morphisms involved: i, Δ and d.

  private
    ×coHomGr : (n : ℕ) → AbGroup _
    ×coHomGr n = dirProdAb (coHomGr n G A) (coHomGr n G B)

    i* : (n : ℕ) → coHom n G (Pushout f g) → coHom n G A × coHom n G B
    i* n = ST.rec (isSet× squash₂ squash₂)
            λ δ → ∣ (λ x → δ (inl x)) ∣₂ , ∣ (λ x → δ (inr x)) ∣₂

  i : (n : ℕ) → AbGroupHom (coHomGr n G (Pushout f g)) (×coHomGr n)
  fst (i n) = i* n
  snd (i n) =
    makeIsGroupHom
     (ST.elim2 (λ _ _ →
       isOfHLevelPath 2
        (isSet× isSetSetTrunc isSetSetTrunc) _ _)
        λ _ _ → refl)

  private
    distrLem : (n : ℕ) (x y z w : EM G n)
      → (x +[ n ]ₖ y) -[ n ]ₖ (z +[ n ]ₖ w)
       ≡ (x -[ n ]ₖ z) +[ n ]ₖ (y -[ n ]ₖ w)
    distrLem n x y z w = cong (λ z → (x +[ n ]ₖ y) +[ n ]ₖ z) (-distrₖ n z w)
                     ∙∙ sym (assocₖ n x y ((-[ n ]ₖ z) +[ n ]ₖ (-[ n ]ₖ w)))
                     ∙∙ cong (λ y → x +[ n ]ₖ y)
                         (commₖ n y ((-[ n ]ₖ z) +[ n ]ₖ (-[ n ]ₖ w))
                                    ∙ sym (assocₖ n _ _ _))
                     ∙∙ assocₖ n _ _ _
                     ∙∙ cong (λ y → (x -[ n ]ₖ z) +[ n ]ₖ y)
                             (commₖ n (-[ n ]ₖ w) y)

    Δ' : (n : ℕ) → ×coHomGr n .fst → coHom n G C
    Δ' n (α , β) = coHomFun n f α -[ n ]ₕ coHomFun n g β

  Δ : (n : ℕ) → AbGroupHom (×coHomGr n) (coHomGr n G C)
  fst (Δ n) = Δ' n
  snd (Δ n) =
    makeIsGroupHom (uncurry (ST.elim2 (λ _ _ → isSetΠ λ _ → isSetPathImplicit)
      λ a b → uncurry (ST.elim2 (λ _ _ → isSetPathImplicit)
        λ c d → cong ∣_∣₂ (funExt
         (λ x → distrLem n (a (f x)) (c (f x)) (b (g x)) (d (g x)))))))

  d-pre : (n : ℕ) → (C → EM G n) → Pushout f g → EM G (suc n)
  d-pre n γ (inl x) = 0ₖ (suc n)
  d-pre n γ (inr x) = 0ₖ (suc n)
  d-pre n γ (push a i) = EM→ΩEM+1 n (γ a) i

  dHomHelper : (n : ℕ) (h l : C → EM G n) (x : Pushout f g)
             → d-pre n (λ x → h x +[ n ]ₖ l x) x
              ≡ d-pre n h x +[ suc n ]ₖ d-pre n l x
  dHomHelper n h l (inl x) = sym (rUnitₖ (suc n) (0ₖ (suc n)))
  dHomHelper n h l (inr x) = sym (rUnitₖ (suc n) (0ₖ (suc n)))
  dHomHelper n h l (push a i) j = lem n h l j i
    where
    lem : (n : ℕ) (h l : C → EM G n)
      → Square (EM→ΩEM+1 n ((h a) +ₖ (l a)))
                (cong₂ _+ₖ_ (EM→ΩEM+1 n (h a)) (EM→ΩEM+1 n (l a)))
                (sym (rUnitₖ (suc n) (0ₖ (suc n))))
                (sym (rUnitₖ (suc n) (0ₖ (suc n))))
    lem zero h l = EM→ΩEM+1-hom zero (h a) (l a)
                 ∙ sym (cong₂+₁ (EM→ΩEM+1 zero (h a)) (EM→ΩEM+1 zero (l a)))
    lem (suc n) h l =
        EM→ΩEM+1-hom (suc n) (h a) (l a)
      ∙ sym (cong₂+₂ n (EM→ΩEM+1 (suc n) (h a)) (EM→ΩEM+1 (suc n) (l a)))

  d : (n : ℕ) → AbGroupHom (coHomGr n G C) (coHomGr (suc n) G (Pushout f g))
  fst (d n) = ST.rec isSetSetTrunc λ a → ∣ d-pre n a ∣₂
  snd (d n) = makeIsGroupHom (ST.elim2 (λ _ _ → isSetPathImplicit)
              λ a b → cong ∣_∣₂ (funExt (dHomHelper n a b)))

  -- The long exact sequence
  Im-d⊂Ker-i : (n : ℕ) (x : coHom (suc n) G (Pushout f g))
            → isInIm (d n) x
            → isInKer (i (suc n)) x
  Im-d⊂Ker-i n =
    ST.elim (λ _ → isSetΠ λ _ → isProp→isSet (isPropIsInKer _ _))
      λ a → PT.rec (isPropIsInKer _ _)
        (uncurry (ST.elim (λ _ → isSetΠ λ _ → isProp→isSet (isPropIsInKer _ _))
          λ δ b i → ST.rec (isSetΣ squash₂ (λ _ → squash₂))
            (λ δ → ∣ δ ∘ inl ∣₂ , ∣ δ ∘ inr ∣₂)
            (b (~ i))))

  Ker-i⊂Im-d : (n : ℕ) (x : coHom (suc n) G (Pushout f g))
             → isInKer (i (suc n)) x
             → isInIm (d n) x
  Ker-i⊂Im-d n =
    ST.elim (λ _ → isSetΠ λ _ → isProp→isSet (isPropIsInIm _ _))
      λ a p → PT.map2 (λ l r
               → ∣ F a (funExt⁻ l) (funExt⁻ r) ∣₂
                 , cong ∣_∣₂ (funExt (F-kill a (funExt⁻ l) (funExt⁻ r))))
                (Iso.fun PathIdTrunc₀Iso (cong fst p))
                (Iso.fun PathIdTrunc₀Iso (cong snd p))
    where
    module _ (a : Pushout f g → EM G (suc n))
             (l : (x : A) → a (inl x) ≡  0ₖ (suc n))
             (r : (x : B) → a (inr x) ≡ 0ₖ (suc n)) where
      F : C → EM G n
      F c = ΩEM+1→EM n (sym (l (f c))
                      ∙∙ cong a (push c)
                      ∙∙ r (g c))

      F-kill : (x : _) → d-pre n F x ≡ a x
      F-kill (inl x) = sym (l x)
      F-kill (inr x) = sym (r x)
      F-kill (push c j) k = help k j
        where
        help : Square (EM→ΩEM+1 n (F c)) (cong a (push c))
                      (sym (l (f c))) (sym (r (g c)))
        help = Iso.rightInv (Iso-EM-ΩEM+1 n) _
             ◁ symP (doubleCompPath-filler
                    (sym (l (f c))) (cong a (push c)) (r (g c)))

  Im-i⊂Ker-Δ : (n : ℕ) (x : ×coHomGr n .fst)
            → isInIm (i n) x
            → isInKer (Δ n) x
  Im-i⊂Ker-Δ n =
    uncurry (ST.elim2 (λ _ _ → isSetΠ λ _ → isSetPathImplicit)
     λ a b → PT.rec (squash₂ _ _)
       (uncurry (ST.elim (λ _ → isSetΠ λ _ → isSetPathImplicit)
         λ h p → cong (Δ' n) (sym p)
               ∙ cong ∣_∣₂ (funExt λ x
                 → cong (λ z → h z -ₖ h (inr (g x))) (push x)
                       ∙ rCancelₖ n (h (inr (g x)))))))

  Ker-Δ⊂Im-i : (n : ℕ) (a : ×coHomGr n .fst)
            → isInKer (Δ n) a
            → isInIm (i n) a
  Ker-Δ⊂Im-i n =
    uncurry (ST.elim2
      (λ _ _ → isSetΠ λ _ → isProp→isSet (isPropIsInIm _ _))
        λ a b p → PT.map (λ q → ∣ F a b (funExt⁻ q) ∣₂ , refl)
                                (Iso.fun PathIdTrunc₀Iso p))

    where
    module _ (a : A → EM G n) (b : B → EM G n)
             (q : (x : C) → a (f x) -ₖ b (g x) ≡ 0ₖ n) where
      qs : (x : C) → a (f x) ≡ b (g x)
      qs x = sym (rUnitₖ n (a (f x)))
          ∙∙ (cong (a (f x) +ₖ_) (sym (lCancelₖ n (b (g x))))
          ∙∙ (assocₖ n (a (f x)) (-ₖ b (g x)) (b (g x)))
          ∙∙ cong (λ z → z +ₖ b (g x)) (q x))
          ∙∙ lUnitₖ n (b (g x))

      F : Pushout f g → EM G n
      F (inl x) = a x
      F (inr x) = b x
      F (push c i) = qs c i

  private
    distrHelper : (n : ℕ) (p q : _)
      → ΩEM+1→EM n p +[ n ]ₖ (-[ n ]ₖ ΩEM+1→EM n q) ≡ ΩEM+1→EM n (p ∙ sym q)
    distrHelper n p q =
      cong (λ x → ΩEM+1→EM n p +[ n ]ₖ x) helper ∙ sym (ΩEM+1→EM-hom n _ _)
      where
      helper : -[ n ]ₖ ΩEM+1→EM n q ≡ ΩEM+1→EM n (sym q)
      helper =
           sym (rUnitₖ n _)
        ∙∙ cong (λ x → (-[ n ]ₖ (ΩEM+1→EM n q)) +[ n ]ₖ x) (sym helper2)
        ∙∙ (assocₖ n _ _ _
        ∙∙ cong (λ x → x +[ n ]ₖ (ΩEM+1→EM n (sym q))) (lCancelₖ n _)
        ∙∙ lUnitₖ n _)
        where
        helper2 : ΩEM+1→EM n q +[ n ]ₖ (ΩEM+1→EM n (sym q)) ≡ 0ₖ n
        helper2 = sym (ΩEM+1→EM-hom n q (sym q))
               ∙∙ cong (ΩEM+1→EM {G = G} n) (rCancel q)
               ∙∙ ΩEM+1→EM-refl n

  Ker-d⊂Im-Δ : (n : ℕ) (a : coHom n G C)
             → isInKer (d n) a
             → isInIm (Δ n) a
  Ker-d⊂Im-Δ n =
    ST.elim (λ _ → isSetΠ λ _ → isProp→isSet (isPropIsInIm _ _))
      λ h p → PT.map
               (λ p → (∣ (λ a → ΩEM+1→EM n (cong (λ f → f (inl a)) p)) ∣₂
                      , ∣ (λ a → ΩEM+1→EM n (cong (λ f → f (inr a)) p)) ∣₂)
             , cong ∣_∣₂ (funExt λ c → distrHelper n (λ i₁ → p i₁ (inl (f c)))
                                                     (λ i₁ → p i₁ (inr (g c)))
                                    ∙ cong (ΩEM+1→EM n) (help h p c)
                                    ∙ Iso.leftInv (Iso-EM-ΩEM+1 n) (h c)))
               (Iso.fun (PathIdTrunc₀Iso) p)
    where
    help : (h : _) (p : d-pre n h ≡ (λ _ → 0ₖ (suc n))) (c : C)
       → funExt⁻ p (inl (f c))
        ∙ sym (funExt⁻ p (inr (g c)))
        ≡ EM→ΩEM+1 n (h c)
    help h p c i j =
      hcomp (λ k → λ {(i = i1) → p (~ k) (push c j)
                     ; (j = i0) → p (~ k ∧ i) (inl (f c))
                     ; (j = i1) → p (~ k) (push c j)})
            (p (i ∨ j) (inl (f c)))


  Im-Δ⊂Ker-d : (n : ℕ) (a : coHom n G C)
             → isInIm (Δ n) a
             → isInKer (d n) a
  Im-Δ⊂Ker-d n =
    ST.elim (λ _ → isOfHLevelΠ 2 λ _ → isSetPathImplicit)
          λ a → PT.rec (isPropIsInKer _ _)
            (uncurry (uncurry (ST.elim2
              (λ _ _ → isOfHLevelΠ 2 λ _ → isSetPathImplicit)
              λ F G p → PT.rec (isPropIsInKer (d n) ∣ a ∣₂)
                         (λ q → cong ∣_∣₂ (cong (d-pre n) (sym q))
                          ∙ (cong ∣_∣₂ (funExt
                             λ { (inl x) → EM→ΩEM+1 n (F x)
                               ; (inr x) → EM→ΩEM+1 n (G x)
                               ; (push a j) i → help (F (f a)) (G (g a)) i j})))
                         (Iso.fun (PathIdTrunc₀Iso) p))))
    where
    help : (x y : EM G n) → Square (EM→ΩEM+1 n (x -ₖ y)) refl
                                    (EM→ΩEM+1 n x) (EM→ΩEM+1 n y)
    help x y = (EM→ΩEM+1-hom n x (-ₖ y)
             ∙∙ cong (EM→ΩEM+1 n x ∙_) (EM→ΩEM+1-sym n y)
             ∙∙ λ i → (λ j → EM→ΩEM+1 n x (j ∧ i))
                    ∙∙ (λ j → EM→ΩEM+1 n x (j ∨ i))
                    ∙∙ sym (EM→ΩEM+1 n y) )
             ◁ λ i j → doubleCompPath-filler
                         (EM→ΩEM+1 n x) refl (sym (EM→ΩEM+1 n y)) (~ i) j
