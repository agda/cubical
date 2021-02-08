{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Displayed.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence using (pathToEquiv)

open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Sigma

open import Cubical.Relation.Binary
open BinaryRelation

open import Cubical.Displayed.Base

private
  variable
    ℓ ℓA ℓA' ℓP ℓ≅A ℓ≅A' ℓB ℓB' ℓ≅B ℓ≅B' ℓC ℓ≅C : Level

-- UARel on Σ-type

module _ {A : Type ℓA} {ℓ≅A : Level} {𝒮-A : UARel A ℓ≅A}
  {B : A → Type ℓB} {ℓ≅B : Level}
  (𝒮ᴰ-B : DUARel 𝒮-A B ℓ≅B)
  where

  open UARel 𝒮-A
  open DUARel 𝒮ᴰ-B

  ∫ : UARel (Σ A B) (ℓ-max ℓ≅A ℓ≅B)
  UARel._≅_ ∫ (a , b) (a' , b') = Σ[ p ∈ a ≅ a' ] (b ≅ᴰ⟨ p ⟩ b')
  UARel.ua ∫ (a , b) (a' , b') =
    compEquiv
      (Σ-cong-equiv (ua a a') (λ p → uaᴰ b p b'))
      ΣPath≃PathΣ

-- UARel on Π-type

module _ {A : Type ℓA} (𝒮-A : UARel A ℓ≅A) {B : A → Type ℓB} (𝒮ᴰ-B : DUARel 𝒮-A B ℓ≅B) where

  open UARel 𝒮-A
  open DUARel 𝒮ᴰ-B

  𝒮ᴰ→𝒮-Π : UARel ((a : A) → B a) (ℓ-max ℓA ℓ≅B)
  UARel._≅_ 𝒮ᴰ→𝒮-Π f f' = ∀ a → f a ≅ᴰ⟨ ρ a ⟩ f' a
  UARel.ua 𝒮ᴰ→𝒮-Π f f' =
    compEquiv
      (equivΠCod λ a → uaᴰρ (f a) (f' a))
      funExtEquiv


-- induction principles

module _ {A : Type ℓA} {ℓ≅A : Level} (𝒮-A : UARel A ℓ≅A) where
  open UARel 𝒮-A
  𝒮-J : {a : A}
        (P : (a' : A) → (p : a ≡ a') → Type ℓ)
        (d : P a refl)
        {a' : A}
        (p : a ≅ a')
        → P a' (≅→≡ p)
  𝒮-J {a} P d {a'} p
    = J (λ y q → P y q)
        d
        (≅→≡ p)

  𝒮-J-2 : {a : A}
            (P : (a' : A) → (p : a ≅ a') → Type ℓ)
            (d : P a (ρ a))
            {a' : A}
            (p : a ≅ a')
            → P a' p
  𝒮-J-2 {a = a} P d {a'} p
    = subst (λ r → P a' r) (Iso.leftInv (uaIso a a') p) g
    where
      g : P a' (≡→≅ (≅→≡ p))
      g = J (λ y q → P y (≡→≅ q)) d (≅→≡ p)


-- constructors

module _ {A : Type ℓA} {𝒮-A : UARel A ℓ≅A}
  {B : A → Type ℓB}
  (_≅ᴰ⟨_⟩_ : {a a' : A} → B a → UARel._≅_ 𝒮-A a a' → B a' → Type ℓ≅B)
  where

    open UARel 𝒮-A

    -- constructor that reduces ua to the case where p = ρ a by induction on p
    private
      𝒮ᴰ-make-aux : (uni : {a : A} (b b' : B a) → b ≅ᴰ⟨ ρ a ⟩ b' ≃ (b ≡ b'))
                    → ({a a' : A} (b : B a) (p : a ≅ a') (b' : B a') → (b ≅ᴰ⟨ p ⟩ b') ≃ PathP (λ i → B (≅→≡ p i)) b b')
      𝒮ᴰ-make-aux uni {a} {a'} b p
        = 𝒮-J-2 𝒮-A
                    (λ y q → (b' : B y) → (b ≅ᴰ⟨ q ⟩ b') ≃ PathP (λ i → B (≅→≡ q i)) b b')
                    (λ b' → uni' b')
                    p
        where
          g : (b' : B a) → (b ≡ b') ≡ PathP (λ i → B (≅→≡ (ρ a) i)) b b'
          g b' = subst (λ r → (b ≡ b') ≡ PathP (λ i → B (r i)) b b')
                       (sym (Iso.rightInv (uaIso a a) refl))
                       refl
          uni' : (b' : B a) → b ≅ᴰ⟨ ρ a ⟩ b' ≃ PathP (λ i → B (≅→≡ (ρ a) i)) b b'
          uni' b' = compEquiv (uni b b') (pathToEquiv (g b'))

    𝒮ᴰ-make-1 : (uni : {a : A} (b b' : B a) → b ≅ᴰ⟨ ρ a ⟩ b' ≃ (b ≡ b'))
                → DUARel 𝒮-A B ℓ≅B
    DUARel._≅ᴰ⟨_⟩_ (𝒮ᴰ-make-1 uni) = _≅ᴰ⟨_⟩_
    DUARel.uaᴰ (𝒮ᴰ-make-1 uni) = 𝒮ᴰ-make-aux uni

    -- constructor that reduces univalence further to contractibility of relational singletons

    𝒮ᴰ-make-2 : (ρᴰ : {a : A} → isRefl _≅ᴰ⟨ ρ a ⟩_)
                (contrTotal : (a : A) → contrRelSingl _≅ᴰ⟨ UARel.ρ 𝒮-A a ⟩_)
                → DUARel 𝒮-A B ℓ≅B
    DUARel._≅ᴰ⟨_⟩_ (𝒮ᴰ-make-2 ρᴰ contrTotal) = _≅ᴰ⟨_⟩_
    DUARel.uaᴰ (𝒮ᴰ-make-2 ρᴰ contrTotal)
      = 𝒮ᴰ-make-aux (contrRelSingl→isUnivalent _ ρᴰ (contrTotal _))


-- lifts

module _ {A : Type ℓA} (𝒮-A : UARel A ℓ≅A)
  {B : A → Type ℓB}
  {ℓ≅B : Level}
  (𝒮ᴰ-B : DUARel 𝒮-A B ℓ≅B)
  {C : A → Type ℓC}
  (𝒮ᴰ-C : DUARel 𝒮-A C ℓ≅C)
  where

  open DUARel 𝒮ᴰ-B

  Lift-𝒮ᴰ : DUARel (∫ 𝒮ᴰ-C) (λ (a , _) → B a) ℓ≅B
  DUARel._≅ᴰ⟨_⟩_ Lift-𝒮ᴰ b p b' = b ≅ᴰ⟨ p .fst ⟩ b'
  DUARel.uaᴰ Lift-𝒮ᴰ b p b' = uaᴰ b (p .fst) b'


-- associativity

module _ {A : Type ℓA} (𝒮-A : UARel A ℓ≅A)
  {B : A → Type ℓB} {ℓ≅B : Level} (𝒮ᴰ-B : DUARel 𝒮-A B ℓ≅B)
  {C : Σ A B → Type ℓC} {ℓ≅C : Level} (𝒮ᴰ-C : DUARel (∫ 𝒮ᴰ-B) C ℓ≅C)
  where

  open UARel 𝒮-A
  open DUARel 𝒮ᴰ-B renaming (_≅ᴰ⟨_⟩_ to _≅B⟨_⟩_ ; uaᴰ to uaB)
  open DUARel 𝒮ᴰ-C renaming (_≅ᴰ⟨_⟩_ to _≅C⟨_⟩_ ; uaᴰ to uaC)

  splitTotal-𝒮ᴰ : DUARel 𝒮-A (λ a → Σ[ b ∈ B a ] C (a , b)) (ℓ-max ℓ≅B ℓ≅C)
  DUARel._≅ᴰ⟨_⟩_ splitTotal-𝒮ᴰ (b , c) p (b' , c') =
    Σ[ q ∈ b ≅B⟨ p ⟩ b' ]  (c ≅C⟨ p , q ⟩ c')
  DUARel.uaᴰ splitTotal-𝒮ᴰ (b ,  c) p (b' , c') =
    compEquiv
      (Σ-cong-equiv (uaB b p b') (λ q → uaC c (p , q) c'))
      ΣPath≃PathΣ

-- combination

module _ {A : Type ℓA} {𝒮-A : UARel A ℓ≅A}
  {B : A → Type ℓB} {ℓ≅B : Level} (𝒮ᴰ-B : DUARel 𝒮-A B ℓ≅B)
  {C : A → Type ℓC} {ℓ≅C : Level} (𝒮ᴰ-C : DUARel 𝒮-A C ℓ≅C)
  where

  _×𝒮ᴰ_ : DUARel 𝒮-A (λ a → B a × C a) (ℓ-max ℓ≅B ℓ≅C)
  _×𝒮ᴰ_ = splitTotal-𝒮ᴰ 𝒮-A 𝒮ᴰ-B (Lift-𝒮ᴰ 𝒮-A 𝒮ᴰ-C 𝒮ᴰ-B)

-- constant displayed structure

module _ {A : Type ℓA} (𝒮-A : UARel A ℓ≅A)
  {B : Type ℓB} (𝒮-B : UARel B ℓ≅B)  where

  open UARel 𝒮-B
  open DUARel

  𝒮ᴰ-const : DUARel 𝒮-A (λ _ → B) ℓ≅B
  𝒮ᴰ-const ._≅ᴰ⟨_⟩_ b _ b' = b ≅ b'
  𝒮ᴰ-const .uaᴰ b p b' = ua b b'

  -- UARel product

  _×𝒮_ : UARel (A × B) (ℓ-max ℓ≅A ℓ≅B)
  _×𝒮_ = ∫ 𝒮ᴰ-const

-- relational isomorphisms

𝒮-iso→iso : {A : Type ℓA} (𝒮-A : UARel A ℓ≅A)
               {B : Type ℓB} (𝒮-B : UARel B ℓ≅B)
               (F : RelIso (UARel._≅_ 𝒮-A) (UARel._≅_ 𝒮-B))
               → Iso A B
𝒮-iso→iso 𝒮-A 𝒮-B F
  = RelIso→Iso (UARel._≅_ 𝒮-A)
               (UARel._≅_ 𝒮-B)
               (UARel.≅→≡ 𝒮-A)
               (UARel.≅→≡ 𝒮-B)
               F

-- fiberwise relational isomorphisms

module _ {A : Type ℓA} {𝒮-A : UARel A ℓ≅A}
  {A' : Type ℓA'} {𝒮-A' : UARel A' ℓ≅A'}
  (F : Iso A A')
  {B : A → Type ℓB} (𝒮ᴰ-B : DUARel 𝒮-A B ℓ≅B)
  {B' : A' → Type ℓB'} (𝒮ᴰ-B' : DUARel 𝒮-A' B' ℓ≅B') where

  open UARel 𝒮-A
  open DUARel 𝒮ᴰ-B renaming (_≅ᴰ⟨_⟩_ to _≅B⟨_⟩_
                            ; uaᴰ to uaB
                            ; fiberRel to fiberRelB
                            ; uaᴰρ to uaᴰρB)
  open DUARel 𝒮ᴰ-B' renaming (_≅ᴰ⟨_⟩_ to _≅B'⟨_⟩_
                             ; uaᴰ to uaB'
                             ; fiberRel to fiberRelB'
                             ; uaᴰρ to uaᴰρB')

  private
    f = Iso.fun F

    -- the following can of course be done slightly more generally
    -- for fiberwise binary relations

    F*fiberRelB' : (a : A) → Rel (B' (f a)) (B' (f a)) ℓ≅B'
    F*fiberRelB' a = fiberRelB' (f a)

  module _ (G : (a : A) → RelIso (fiberRelB a) (F*fiberRelB' a)) where
    private
      fiberIsoOver : (a : A) → Iso (B a) (B' (f a))
      fiberIsoOver a
        = RelIso→Iso (fiberRelB a)
                     (F*fiberRelB' a)
                     (equivFun (uaᴰρB _ _))
                     (equivFun (uaᴰρB' _ _))
                     (G a)

    -- DUARelFiberIsoOver→TotalIso produces an isomorphism of total spaces
    -- from a relational isomorphism between B a and (F * B) a
    𝒮ᴰ-fiberIsoOver→totalIso : Iso (Σ A B) (Σ A' B')
    𝒮ᴰ-fiberIsoOver→totalIso = Σ-cong-iso F fiberIsoOver


-- Special cases:
-- Subtypes
𝒮-type : (A : Type ℓ) → UARel A ℓ
UARel._≅_ (𝒮-type A) = _≡_
UARel.ua (𝒮-type A) a a' = idEquiv (a ≡ a')

module _ {A : Type ℓA} (𝒮-A : UARel A ℓ≅A) where
  𝒮ᴰ-subtype : (P : A → hProp ℓP) → DUARel 𝒮-A (λ a → P a .fst) ℓ-zero
  𝒮ᴰ-subtype P
    = 𝒮ᴰ-make-2 (λ _ _ _ → Unit)
                (λ _ → tt)
                λ a p → isOfHLevelRespectEquiv 0
                                               (invEquiv (Σ-contractSnd (λ _ → isContrUnit)))
                                               (inhProp→isContr p (P a .snd))
