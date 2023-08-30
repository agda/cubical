{-
Module in which the Grothendieck Group ("Groupification") of a commutative monoid is defined.
-}
{-# OPTIONS --safe #-}
module Cubical.Algebra.CommMonoid.GrothendieckGroup where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Algebra.Monoid
open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.CommMonoid.CommMonoidProd
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.AbGroup

open import Cubical.HITs.SetQuotients.Base
open import Cubical.HITs.SetQuotients.Properties

open import Cubical.Relation.Binary.Base


private
  variable
    ℓ ℓ' : Level


module _ (M : CommMonoid ℓ) where
  open BinaryRelation

  M² : CommMonoid _
  M² = CommMonoidProd M M

  open CommMonoidStr ⦃...⦄
  private
    instance
      _ = snd M
      _ = snd M²

  R : ⟨ M² ⟩  → ⟨ M² ⟩ → Type _
  R (a₁ , b₁) (a₂ , b₂) =  Σ[ k ∈ ⟨ M ⟩ ] k · (a₁ · b₂) ≡ k · (b₁ · a₂)

  M²/R : Type _
  M²/R = ⟨ M² ⟩ / R

  0/R : M²/R
  0/R = [ ε , ε ]

  private
    _+/_ : M²/R → M²/R → M²/R
    x +/ y = setQuotBinOp isReflR isReflR _·_ isCongR x y
      where
      isReflR : isRefl R
      isReflR (a , b) = ε , cong (ε ·_) (·Comm a b)

      isCongR : ∀ u u' v v' → R u u' → R v v' → R (u · v) (u' · v')
      isCongR (a₁ , b₁) (a₂ , b₂) (a₃ , b₃) (a₄ , b₄) (k , p) (s , q) = k · s , proof
        where
        proof =
          (k · s) · ((a₁ · a₃) · (b₂ · b₄)) ≡⟨ lemma ⟩
          (k · (a₁ · b₂)) · (s · (a₃ · b₄)) ≡⟨ cong₂ _·_ p q ⟩
          (k · (b₁ · a₂)) · (s · (b₃ · a₄)) ≡⟨ sym lemma ⟩
          (k · s) · ((b₁ · b₃) · (a₂ · a₄)) ∎
            where
            rExp : ∀ {x y z} → x ≡ y → x · z ≡ y · z
            rExp r = cong₂ _·_ r refl

            lExp : ∀ {x y z} → x ≡ y → z · x ≡ z · y
            lExp r = cong₂ _·_ refl r

            -- remove proof when MonoidSolver is done
            lemma : ∀ {k s a b c d} → (k · s) · ((a · b) · (c · d)) ≡ (k · (a · c)) · (s · (b · d))
            lemma = sym (·Assoc _ _ _) ∙ lExp (
                                   (·Assoc _ _ _) ∙ (·Assoc _ _ _) ∙ rExp (
                                       ·Comm _ _ ∙ (·Assoc _ _ _) ∙ (·Assoc _ _ _) ∙ rExp (
                                            ·Comm _ _ ∙ (·Assoc _ _ _)
                                       ) ∙ sym (·Assoc _ _ _)
                                   ) ∙ sym (·Assoc _ _ _) ∙ lExp (sym (·Assoc _ _ _))
                              ) ∙ (·Assoc _ _ _)

    -/_ : M²/R → M²/R
    -/_ = setQuotUnaryOp swap h
      where
      swap : ⟨ M² ⟩  → ⟨ M² ⟩
      swap = λ (a , b) → b , a

      h : ∀ u v → R u v → R (swap u) (swap v)
      h _ _ (k , p) = k , sym p

    assoc/R : (x y z : M²/R) → x +/ ( y +/ z) ≡ (x +/ y) +/ z
    assoc/R = elimProp3 (λ x y z → squash/ _ _) (λ u v w → cong [_] (·Assoc _ _ _))

    rid/R : (x : M²/R) → x +/ 0/R ≡ x
    rid/R = elimProp (λ x → squash/ _ _) (λ u → cong [_] (·IdR u))

    rinv/R : (x : M²/R) → x +/ (-/ x) ≡ 0/R
    rinv/R = elimProp (λ x → squash/ _ _)
                      (λ (a , b) →  eq/ _ _ (ε , cong (λ x → ε · (x · ε)) (·Comm _ _)))

    comm/R : (x y : M²/R) → x +/ y ≡ y +/ x
    comm/R = elimProp2 (λ x y → squash/ _ _) (λ u v → cong [_] (·Comm _ _))

  asAbGroup : AbGroup ℓ
  asAbGroup = makeAbGroup 0/R _+/_ -/_ squash/ assoc/R rid/R rinv/R comm/R

Groupification : CommMonoid ℓ → AbGroup ℓ
Groupification M = asAbGroup M


module UniversalProperty (M : CommMonoid ℓ) where
  open IsMonoidHom
  open CommMonoidStr ⦃...⦄

  private
    instance
      _ = snd M

{-
The "groupification" of a monoid comes with a universal morphism and a universal property:

            M ----- ∀φ -----> A
             \               Λ
              \             /
       universalHom    ∃! inducedHom
                \         /
                 V       /
             Groupification M
-}

  universalHom : CommMonoidHom M (AbGroup→CommMonoid (Groupification M))
  fst universalHom = λ m → [ m , ε ]
  pres· (snd universalHom) =
    λ _ _ → eq/ _ _ (ε , cong (ε ·_) (·Comm _ _ ∙ cong₂ _·_ (·IdR ε) refl))
  presε (snd universalHom) = refl

  private
    i = fst universalHom

  module _ {A : AbGroup ℓ} (φ : CommMonoidHom M (AbGroup→CommMonoid A)) where
    open IsGroupHom

    open GroupTheory (AbGroup→Group A)

    open AbGroupStr ⦃...⦄ using (-_; _-_; _+_; +InvR; +InvL)
    private
      instance
        AAsGroup  = snd A
        MAsGroup  = snd (Groupification M)
        AAsMonoid = snd (AbGroup→CommMonoid A)

    private
      module φ = IsMonoidHom (snd φ)
      f = fst φ

    inducedHom : AbGroupHom (Groupification M) A
    fst inducedHom = elim (λ x → is-set) g proof
        where
        g = λ (a , b) → f a - f b
        proof : (u v : ⟨ M² M ⟩) (r : R M u v) → g u ≡ g v
        proof _ _ (k , p) = lemma (lemma₂ p)
            where
            lemma₂ : ∀ {k a b c d} → k · (a · d) ≡ k · (b · c) → f a + f d ≡ f b + f c
            lemma₂ {k} {a} {b} {c} {d} p =
              f a + f d   ≡⟨ sym (φ.pres· _ _) ⟩
              f (a · d)   ≡⟨ ·CancelL _ (sym (φ.pres· _ _) ∙ (cong f p) ∙ φ.pres· _ _) ⟩
              f (b · c)   ≡⟨ φ.pres· _ _ ⟩
              f b + f c   ∎

            lemma : ∀ {a b c d} → f a + f d ≡ f b + f c → f a - f b ≡ f c - f d
            lemma {a} {b} {c} {d} p =
              f a - f b
                ≡⟨ cong (λ x → x - f b) (sym (·IdR _)) ⟩
              f a + ε - f b
                ≡⟨ cong (λ x → f a + x - f b) (sym (+InvR _)) ⟩
              f a + (f d - f d) - f b
                ≡⟨ cong (λ x → x - f b) (·Assoc _ _ _) ⟩
              f a + f d - f d - f b
                ≡⟨ cong (λ x → x - f d - f b) p ⟩
              f b + f c - f d - f b
                ≡⟨ ·Comm _ _ ∙ ·Assoc _ _ _ ⟩
              (- f b + (f b + f c)) - f d
                ≡⟨ cong (λ x → x - f d) (·Assoc _ _ _) ⟩
              ((- f b + f b) + f c) - f d
                ≡⟨ cong (λ x → (x + f c) - f d) (+InvL _) ∙ sym (·Assoc _ _ _) ∙ ·IdL _ ⟩
              f c - f d
                ∎

    pres· (snd inducedHom) = elimProp2 (λ _ _ → is-set _ _) proof
      where
        rExp : ∀ {x y z} → x ≡ y → x + z ≡ y + z
        rExp r = cong₂ _+_ r refl

        lExp : ∀ {x y z} → x ≡ y → z + x ≡ z + y
        lExp r = cong₂ _+_ refl r

        proof : ((a , b) (c , d) : ⟨ M² M ⟩) → (f (a · c)) - (f (b · d)) ≡ (f a - f b) + (f c - f d)
        proof (a , b) (c , d) =
          f (a · c) - f (b · d)     ≡⟨ cong₂ _-_ (φ.pres· _ _) (φ.pres· _ _) ⟩
          (f a + f c) - (f b + f d) ≡⟨ lExp (invDistr _ _ ∙ ·Comm _ _) ∙ ·Assoc _ _ _ ⟩
          ((f a + f c) - f b) - f d ≡⟨ lemma ⟩
          (f a - f b) + (f c - f d) ∎
          where
            lemma = rExp (sym (·Assoc _ _ _) ∙ lExp (·Comm _ _) ∙ ·Assoc _ _ _) ∙ sym (·Assoc _ _ _)

    pres1 (snd inducedHom)   = +InvR _
    presinv (snd inducedHom) = elimProp (λ _ → is-set _ _)
                                        (λ _ → sym (invDistr _ _ ∙ cong₂ _-_ (invInv _) refl))

    solution : (m : ⟨ M ⟩) → (fst inducedHom) (i m) ≡ f m
    solution m = cong ((f m)+_) ((cong (-_) φ.presε) ∙ inv1g) ∙ ·IdR _

    unique : (ψ : AbGroupHom (Groupification M) A)
             → (ψIsSolution : (m : ⟨ M ⟩) → ψ .fst (i m) ≡ f m)
             → (u : ⟨ M² M ⟩) → ψ .fst [ u ] ≡ inducedHom .fst [ u ]
    unique ψ ψIsSolution (a , b) =
       ψ .fst [ a , b ]                    ≡⟨ lemma ⟩
       ψ .fst ([ a , ε ] - [ b , ε ])      ≡⟨ (snd ψ).pres· _ _ ∙ cong₂ _+_ refl ((snd ψ).presinv _) ⟩
       ψ .fst [ a , ε ] - ψ .fst [ b , ε ] ≡⟨ cong₂ _-_ (ψIsSolution a) (ψIsSolution b) ⟩
       f a - f b                           ∎
       where
         lemma = cong (ψ .fst) (eq/ _ _ (ε , cong (ε ·_) (·Assoc _ _ _ ∙ ·Comm _ _)))
