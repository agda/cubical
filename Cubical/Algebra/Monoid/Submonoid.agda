open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma

open import Cubical.Algebra.Monoid

module Cubical.Algebra.Monoid.Submonoid {ℓ : Level} (M : Monoid ℓ) where
open MonoidStr (str M)

record isSubmonoid (S : ℙ ⟨ M ⟩) : Type ℓ where
  field
    ε-closed : ε ∈ S
    ·-closed : {x y : ⟨ M ⟩} → (x ∈ S) → (y ∈ S) → (x · y) ∈ S

Submonoid : Type (ℓ-suc ℓ)
Submonoid = Σ[ S ∈ ℙ ⟨ M ⟩ ] isSubmonoid S

Submonoid→Monoid : Submonoid → Monoid ℓ
Submonoid→Monoid ( S , isSubmonoid ) =
  let
    open isSubmonoid isSubmonoid
    ε' = ε , ε-closed
    _·'_ = λ where (m , m∈) (n , n∈) → m · n , ·-closed m∈ n∈
    is-setM' = isSetΣSndProp is-set (∈-isProp S)
    ·Assoc' = λ x y z → Σ≡Prop (∈-isProp S) (·Assoc (fst x) (fst y) (fst z))
    ·IdR' = λ x → Σ≡Prop (∈-isProp S) (·IdR (fst x))
    ·IdL' = λ x → Σ≡Prop (∈-isProp S) (·IdL (fst x))
  in makeMonoid ε' _·'_ is-setM' ·Assoc' ·IdR' ·IdL'

module _ where
  open IsMonoidHom

  Submonoid→MonoidHom : (S : Submonoid) → MonoidHom (Submonoid→Monoid S) M
  Submonoid→MonoidHom _ .fst = fst
  Submonoid→MonoidHom _ .snd .presε = refl
  Submonoid→MonoidHom _ .snd .pres· x y = refl
