module Cubical.Algebra.Algebra.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma

open import Cubical.Reflection.RecordEquiv

open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Module


open Iso

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level

record IsAlgebra (R : Ring ℓ) {A : Type ℓ'}
                 (0a 1a : A) (_+_ _·_ : A → A → A) (-_ : A → A)
                 (_⋆_ : ⟨ R ⟩ → A → A) : Type (ℓ-max ℓ ℓ') where

  no-eta-equality

  open RingStr (snd R) using (1r) renaming (_+_ to _+r_; _·_ to _·r_)

  field
    +IsLeftModule : IsLeftModule R 0a _+_ -_ _⋆_
    ·IsMonoid     : IsMonoid 1a _·_
    ·DistR+       : (x y z : A) → x · (y + z) ≡ (x · y) + (x · z)
    ·DistL+       : (x y z : A) → (x + y) · z ≡ (x · z) + (y · z)
    ⋆AssocR       : (r : ⟨ R ⟩) (x y : A) → r ⋆ (x · y) ≡ x · (r ⋆ y)
    ⋆AssocL       : (r : ⟨ R ⟩) (x y : A) → (r ⋆ x) · y ≡ r ⋆ (x · y)

  open IsLeftModule +IsLeftModule public

  isRing : IsRing _ _ _ _ _
  isRing = isring (IsLeftModule.+IsAbGroup +IsLeftModule) ·IsMonoid ·DistR+ ·DistL+
  open IsRing isRing public
    hiding (_-_; +Assoc; +IdL; +InvL; +IdR; +InvR; +Comm; ·DistR+; ·DistL+; is-set)

unquoteDecl IsAlgebraIsoΣ = declareRecordIsoΣ IsAlgebraIsoΣ (quote IsAlgebra)

record AlgebraStr (R : Ring ℓ) (A : Type ℓ') : Type (ℓ-max ℓ ℓ') where

  field
    0a             : A
    1a             : A
    _+_            : A → A → A
    _·_            : A → A → A
    -_             : A → A
    _⋆_            : ⟨ R ⟩ → A → A
    isAlgebra      : IsAlgebra R 0a 1a _+_ _·_ -_ _⋆_

  open IsAlgebra isAlgebra public

unquoteDecl AlgebraStrIsoΣ = declareRecordIsoΣ AlgebraStrIsoΣ (quote AlgebraStr)

Algebra : (R : Ring ℓ) → ∀ ℓ' → Type (ℓ-max ℓ (ℓ-suc ℓ'))
Algebra R ℓ' = Σ[ A ∈ Type ℓ' ] AlgebraStr R A

module commonExtractors {R : Ring ℓ} where

  module _ where
    open IsAlgebra
    open RingStr
    open LeftModuleStr

    Algebra→Module : (A : Algebra R ℓ') → LeftModule R ℓ'
    Algebra→Module A .fst = A .fst
    Algebra→Module A .snd .0m = _
    Algebra→Module A .snd ._+_ = _
    Algebra→Module A .snd .-_ = _
    Algebra→Module A .snd ._⋆_ = _
    Algebra→Module A .snd .isLeftModule = (A .snd .AlgebraStr.isAlgebra) .+IsLeftModule

    Algebra→Ring : (A : Algebra R ℓ') → Ring ℓ'
    Algebra→Ring A .fst = A .fst
    Algebra→Ring A .snd .0r = _
    Algebra→Ring A .snd .1r = _
    Algebra→Ring A .snd ._+_ = _
    Algebra→Ring A .snd ._·_ = _
    Algebra→Ring A .snd .-_  = _
    Algebra→Ring A .snd .RingStr.isRing = IsAlgebra.isRing (A .snd .AlgebraStr.isAlgebra)

  Algebra→AbGroup : (A : Algebra R ℓ') → AbGroup ℓ'
  Algebra→AbGroup A = LeftModule→AbGroup (Algebra→Module A)

  Algebra→Group : (A : Algebra R ℓ') → Group ℓ'
  Algebra→Group A = Ring→Group (Algebra→Ring A)

  Algebra→AddMonoid : (A : Algebra R ℓ') → Monoid ℓ'
  Algebra→AddMonoid A = Group→Monoid (Algebra→Group A)

  Algebra→MultMonoid : (A : Algebra R ℓ') → Monoid ℓ'
  Algebra→MultMonoid A = Ring→MultMonoid (Algebra→Ring A)

  open RingStr (snd R) using (1r; ·DistL+) renaming (_+_ to _+r_; _·_ to _·s_)

  module _ {A : Type ℓ'} {0a 1a : A}
                (isSet-A : isSet A)
                {_+_ _·_ : A → A → A} { -_ : A → A} {_⋆_ : ⟨ R ⟩ → A → A}
                (+Assoc  :  (x y z : A) → x + (y + z) ≡ (x + y) + z)
                (+IdR    : (x : A) → x + 0a ≡ x)
                (+InvR   : (x : A) → x + (- x) ≡ 0a)
                (+Comm   : (x y : A) → x + y ≡ y + x)
                (·Assoc  :  (x y z : A) → x · (y · z) ≡ (x · y) · z)
                (·IdR    : (x : A) → x · 1a ≡ x)
                (·IdL    : (x : A) → 1a · x ≡ x)
                (·DistR+ : (x y z : A) → x · (y + z) ≡ (x · y) + (x · z))
                (·DistL+ : (x y z : A) → (x + y) · z ≡ (x · z) + (y · z))
                (⋆Assoc  : (r s : ⟨ R ⟩) (x : A) → (r ·s s) ⋆ x ≡ r ⋆ (s ⋆ x))
                (⋆DistR+ : (r : ⟨ R ⟩) (x y : A) → r ⋆ (x + y) ≡ (r ⋆ x) + (r ⋆ y))
                (⋆DistL+ : (r s : ⟨ R ⟩) (x : A) → (r +r s) ⋆ x ≡ (r ⋆ x) + (s ⋆ x))
                (⋆IdL    : (x : A) → 1r ⋆ x ≡ x)
                (⋆AssocR : (r : ⟨ R ⟩) (x y : A) → r ⋆ (x · y) ≡ x · (r ⋆ y))
                (⋆AssocL : (r : ⟨ R ⟩) (x y : A) → (r ⋆ x) · y ≡ r ⋆ (x · y))
    where
    makeIsAlgebra : IsAlgebra R 0a 1a _+_ _·_ -_ _⋆_
    makeIsAlgebra .IsAlgebra.+IsLeftModule = makeIsLeftModule
                                            isSet-A
                                            +Assoc +IdR +InvR +Comm
                                            ⋆Assoc ⋆DistR+ ⋆DistL+ ⋆IdL
    makeIsAlgebra .IsAlgebra.·IsMonoid = makeIsMonoid isSet-A ·Assoc ·IdR ·IdL
    makeIsAlgebra .IsAlgebra.·DistR+ = ·DistR+
    makeIsAlgebra .IsAlgebra.·DistL+ = ·DistL+
    makeIsAlgebra .IsAlgebra.⋆AssocR = ⋆AssocR
    makeIsAlgebra .IsAlgebra.⋆AssocL = ⋆AssocL

open commonExtractors public

record IsAlgebraHom {R : Ring ℓ} {A : Type ℓ'} {B : Type ℓ''}
  (M : AlgebraStr R A) (f : A → B) (N : AlgebraStr R B)
  : Type (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
  where

  -- Shorter qualified names
  private
    module M = AlgebraStr M
    module N = AlgebraStr N

  field
    pres0 : f M.0a ≡ N.0a
    pres1 : f M.1a ≡ N.1a
    pres+ : (x y : A) → f (x M.+ y) ≡ f x N.+ f y
    pres· : (x y : A) → f (x M.· y) ≡ f x N.· f y
    pres- : (x : A) → f (M.- x) ≡ N.- (f x)
    pres⋆ : (r : ⟨ R ⟩) (y : A) → f (r M.⋆ y) ≡ r N.⋆ f y

unquoteDecl IsAlgebraHomIsoΣ = declareRecordIsoΣ IsAlgebraHomIsoΣ (quote IsAlgebraHom)
open IsAlgebraHom

private
  variable
    R : Ring ℓ
    A B : Algebra R ℓ

AlgebraHom : (M : Algebra R ℓ') (N : Algebra R ℓ'') → Type _
AlgebraHom M N = Σ[ f ∈ (⟨ M ⟩ → ⟨ N ⟩) ] IsAlgebraHom (M .snd) f (N .snd)

IsAlgebraEquiv : {A : Type ℓ'} {B : Type ℓ''}
  (M : AlgebraStr R A) (e : A ≃ B) (N : AlgebraStr R B)
  → Type _
IsAlgebraEquiv M e N = IsAlgebraHom M (e .fst) N

AlgebraEquiv : (M : Algebra R ℓ') (N : Algebra R ℓ'') → Type _
AlgebraEquiv M N = Σ[ e ∈ ⟨ M ⟩ ≃ ⟨ N ⟩ ] IsAlgebraEquiv (M .snd) e (N .snd)

_$a_ : AlgebraHom A B → ⟨ A ⟩ → ⟨ B ⟩
f $a x = fst f x

AlgebraEquiv→AlgebraHom : AlgebraEquiv A B → AlgebraHom A B
AlgebraEquiv→AlgebraHom (e , eIsHom) = e .fst , eIsHom

isPropIsAlgebra : (R : Ring ℓ) {A : Type ℓ'}
  (0a 1a : A)
  (_+_ _·_ : A → A → A)
  (-_ : A → A)
  (_⋆_ : ⟨ R ⟩ → A → A)
  → isProp (IsAlgebra R 0a 1a _+_ _·_ -_ _⋆_)
isPropIsAlgebra R _ _ _ _ _ _ = let open IsLeftModule in
  isOfHLevelRetractFromIso 1 IsAlgebraIsoΣ
    (isPropΣ
      (isPropIsLeftModule _ _ _ _ _)
      (λ mo → isProp×4 (isPropIsMonoid _ _)
                       (isPropΠ3 λ _ _ _ → mo .is-set _ _)
                       (isPropΠ3 λ _ _ _ → mo .is-set _ _)
                       (isPropΠ3 λ _ _ _ → mo .is-set _ _)
                       (isPropΠ3 λ _ _ _ → mo .is-set _ _) ))


isPropIsAlgebraHom : (R : Ring ℓ) {A : Type ℓ'} {B : Type ℓ''}
                     (AS : AlgebraStr R A) (f : A → B) (BS : AlgebraStr R B)
                   → isProp (IsAlgebraHom AS f BS)
isPropIsAlgebraHom R AS f BS =
  isOfHLevelRetractFromIso 1
    IsAlgebraHomIsoΣ
    (isProp×5 (is-set _ _)
              (is-set _ _)
              (isPropΠ2 λ _ _ → is-set _ _)
              (isPropΠ2 λ _ _ → is-set _ _)
              (isPropΠ λ _ → is-set _ _)
              (isPropΠ2 λ _ _ → is-set _ _))
  where
  open AlgebraStr BS

isSetAlgebraHom : (M : Algebra R ℓ') (N : Algebra R ℓ'')
                → isSet (AlgebraHom M N)
isSetAlgebraHom _ N = isSetΣ (isSetΠ (λ _ → is-set))
                        λ _ → isProp→isSet (isPropIsAlgebraHom _ _ _ _)
  where
  open AlgebraStr (str N)


isSetAlgebraEquiv : (M : Algebra R ℓ') (N : Algebra R ℓ'')
                  → isSet (AlgebraEquiv M N)
isSetAlgebraEquiv M N = isSetΣ (isOfHLevel≃ 2 M.is-set N.is-set)
                          λ _ → isProp→isSet (isPropIsAlgebraHom _ _ _ _)
  where
  module M = AlgebraStr (str M)
  module N = AlgebraStr (str N)

AlgebraHom≡ : {φ ψ : AlgebraHom A B} → fst φ ≡ fst ψ → φ ≡ ψ
AlgebraHom≡ = Σ≡Prop λ f → isPropIsAlgebraHom _ _ f _

-- Smart constructor for algebra homomorphisms
-- that infers the other equations from pres1, pres+, pres·, and pres⋆

module _
  -- Variable generalization would fail below without the module parameters A and B.
  {A : Algebra R ℓ}
  {B : Algebra R ℓ'}
  {f : ⟨ A ⟩ → ⟨ B ⟩}
  where

  private
    module A = AlgebraStr (A .snd)
    module B = AlgebraStr (B .snd)

  module _
    (p1 : f A.1a ≡ B.1a)
    (p+ : (x y : ⟨ A ⟩) → f (x A.+ y) ≡ f x B.+ f y)
    (p· : (x y : ⟨ A ⟩) → f (x A.· y) ≡ f x B.· f y)
    (p⋆ : (r : ⟨ R ⟩) (x : ⟨ A ⟩) → f (r A.⋆ x) ≡ r B.⋆ f x)
    where

    open IsAlgebraHom
    private
      isGHom : IsGroupHom (Algebra→Group A .snd) f (Algebra→Group B .snd)
      isGHom = makeIsGroupHom p+

    makeIsAlgebraHom : IsAlgebraHom (A .snd) f (B .snd)
    makeIsAlgebraHom .pres0 = isGHom .IsGroupHom.pres1
    makeIsAlgebraHom .pres1 = p1
    makeIsAlgebraHom .pres+ = p+
    makeIsAlgebraHom .pres· = p·
    makeIsAlgebraHom .pres- = isGHom .IsGroupHom.presinv
    makeIsAlgebraHom .pres⋆ = p⋆
