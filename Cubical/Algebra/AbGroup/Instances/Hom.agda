-- Given two abelian groups A, B
--   the set of all group homomorphisms from A to B
-- is itself an abelian group.
-- In other words, Ab is cartesian closed.
-- This is needed to show Ab is an abelian category.

{-# OPTIONS --safe #-}

module Cubical.Algebra.AbGroup.Instances.Hom where

open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Properties
open import Cubical.Foundations.Prelude

private
  variable
    ℓ ℓ' : Level

module _ (A : AbGroup ℓ) (B : AbGroup ℓ') where

  -- These names are useful for the proofs
  private
    open IsGroupHom
    open AbGroupStr (A .snd) using () renaming (0g to 0A; _+_ to _⋆_; -_ to inv)
    open AbGroupStr (B .snd) using (_+_; -_; comm; assoc; identity; inverse)
                             renaming (0g to 0B)
    open GroupTheory (AbGroup→Group B) using (invDistr) renaming (inv1g to inv0B)

    -- Some lemmas
    idrB : (b : B .fst) → b + 0B ≡ b
    idrB b = identity b .fst

    invrB : (b : B .fst) → b + (- b) ≡ 0B
    invrB b = inverse b .fst

    hom0AB : (f : AbGroupHom A B) → f .fst 0A ≡ 0B
    hom0AB f = hom1g (AbGroupStr→GroupStr (A .snd)) (f .fst)
                     (AbGroupStr→GroupStr (B .snd)) (f .snd .pres·)

    homInvAB : (f : AbGroupHom A B) → (a : A .fst) → f .fst (inv a) ≡ (- f .fst a)
    homInvAB f a = homInv (AbGroupStr→GroupStr (A .snd)) (f .fst)
                          (AbGroupStr→GroupStr (B .snd)) (f .snd .pres·) a


  -- Zero morphism
  zero : AbGroupHom A B
  zero .fst a = 0B
  zero .snd .pres· a a' = sym (idrB _)
  zero .snd .pres1 = refl
  zero .snd .presinv a = sym (inv0B)


  -- Pointwise addition of morphisms
  module _ (f* g* : AbGroupHom A B) where
    private
      f = f* .fst
      g = g* .fst

    HomAdd : AbGroupHom A B
    HomAdd .fst = λ a → f a + g a

    HomAdd .snd .pres· a a' =
        f (a ⋆ a') + g (a ⋆ a')           ≡⟨ cong (_+ g(a ⋆ a')) (f* .snd .pres· _ _) ⟩
        (f a + f a') + g (a ⋆ a')         ≡⟨ cong ((f a + f a') +_) (g* .snd .pres· _ _) ⟩
        (f a + f a') + (g a + g a')       ≡⟨ sym (assoc _ _ _) ⟩
        f a + (f a' + (g a + g a'))       ≡⟨ cong (f a +_) (assoc _ _ _) ⟩
        f a + ((f a' + g a) + g a')       ≡⟨ cong (λ b → (f a + b + g a')) (comm _ _) ⟩
        f a + ((g a + f a') + g a')       ≡⟨ cong (f a +_) (sym (assoc _ _ _)) ⟩
        f a + (g a + (f a' + g a'))       ≡⟨ assoc _ _ _ ⟩
        (f a + g a) + (f a' + g a')       ∎

    HomAdd .snd .pres1 =
        f 0A + g 0A       ≡⟨ cong (_+ g 0A) (hom0AB f*) ⟩
        0B + g 0A         ≡⟨ cong (0B +_) (hom0AB g*) ⟩
        0B + 0B           ≡⟨ idrB _ ⟩
        0B                ∎

    HomAdd .snd .presinv a =
        f (inv a) + g (inv a)     ≡⟨ cong (_+ g (inv a)) (homInvAB f* _) ⟩
        (- f a) + g (inv a)       ≡⟨ cong ((- f a) +_) (homInvAB g* _) ⟩
        (- f a) + (- g a)         ≡⟨ comm _ _ ⟩
        (- g a) + (- f a)         ≡⟨ sym (invDistr _ _) ⟩
        - (f a + g a)             ∎


  -- Pointwise inverse of morphism
  module _ (f* : AbGroupHom A B) where
    private
      f = f* .fst

    HomInv : AbGroupHom A B
    HomInv .fst = λ a → - f a

    HomInv .snd .pres· a a' =
        - f (a ⋆ a')            ≡⟨ cong -_ (f* .snd .pres· _ _) ⟩
        - (f a + f a')          ≡⟨ invDistr _ _ ⟩
        (- f a') + (- f a)      ≡⟨ comm _ _ ⟩
        (- f a) + (- f a')      ∎

    HomInv .snd .pres1 =
        - (f 0A)      ≡⟨ cong -_ (f* .snd .pres1) ⟩
        - 0B          ≡⟨ inv0B ⟩
        0B            ∎

    HomInv .snd .presinv a =
        - f (inv a)     ≡⟨ cong -_ (homInvAB f* _) ⟩
        - (- f a)       ∎


  -- Group laws for morphisms
  private
    0ₕ = zero
    _+ₕ_ = HomAdd
    -ₕ_ = HomInv

  -- Morphism addition is associative
  HomAdd-assoc : (f g h : AbGroupHom A B) → (f +ₕ (g +ₕ h)) ≡ ((f +ₕ g) +ₕ h)
  HomAdd-assoc f g h = GroupHom≡ (funExt λ a → assoc _ _ _)

  -- Morphism addition is commutative
  HomAdd-comm : (f g : AbGroupHom A B) → (f +ₕ g) ≡ (g +ₕ f)
  HomAdd-comm f g = GroupHom≡ (funExt λ a → comm _ _)

  -- zero is right identity
  HomAdd-zero : (f : AbGroupHom A B) → (f +ₕ zero) ≡ f
  HomAdd-zero f = GroupHom≡ (funExt λ a → idrB _)

  -- -ₕ is right inverse
  HomInv-invr : (f : AbGroupHom A B) → (f +ₕ (-ₕ f)) ≡ zero
  HomInv-invr f = GroupHom≡ (funExt λ a → invrB _)


-- Abelian group structure on AbGroupHom A B
open AbGroupStr
HomAbGroupStr : (A : AbGroup ℓ) → (B : AbGroup ℓ') → AbGroupStr (AbGroupHom A B)
HomAbGroupStr A B .0g        = zero A B
HomAbGroupStr A B ._+_       = HomAdd A B
HomAbGroupStr A B .-_        = HomInv A B
HomAbGroupStr A B .isAbGroup = makeIsAbGroup isSetGroupHom
    (HomAdd-assoc A B) (HomAdd-zero A B) (HomInv-invr A B) (HomAdd-comm A B)

HomAbGroup : (A : AbGroup ℓ) → (B : AbGroup ℓ') → AbGroup (ℓ-max ℓ ℓ')
HomAbGroup A B = AbGroupHom A B , HomAbGroupStr A B
