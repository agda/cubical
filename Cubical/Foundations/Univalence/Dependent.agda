{-

Dependent Version of Univalence

The univalence corresponds to the dependent equivalences/isomorphisms,
c.f. `Cubical.Foundations.Equiv.Dependent`.

-}
module Cubical.Foundations.Univalence.Dependent where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Univalence

private
  variable
    ℓ ℓ' : Level


-- Dependent Univalence
--
-- Given families `P` and `Q` over base types `A` and `B`
-- respectively, and given
--  * an equivalence of base types `e : A ≃ B`,
--  * and and a pointwise equivalence of the families,
-- construct a dependent path over `ua e` between the families.
module _
  {A B : Type ℓ} {P : A → Type ℓ'} {Q : B → Type ℓ'}
  (e : A ≃ B) (F : mapOver (e .fst) P Q)
  (equiv : isEquivOver {P = P} {Q = Q} F)
  where
  private
    -- Bundle `F` and `equiv` into a pointwise equivalence of `P` and `Q`:
    Γ : (a : A) → P a ≃ Q (equivFun e a)
    Γ a = F a , equiv a

    -- A quick proof provided by @ecavallo.
    -- Unfortunately it gives a larger term overall.
    _ : PathP (λ i → ua e i → Type ℓ') P Q
    _ = ua→ (λ a → ua (Γ a))

  uaOver : PathP (λ i → ua e i → Type ℓ') P Q
  uaOver i x = Glue Base {φ} equiv-boundary where
    -- Like `ua`, `uaOver` is obtained from a line of
    -- Glue-types, except that they are glued
    -- over a line dependent on `ua e : A ≡ B`.

    -- `x` is a point along the path `A ≡ B` obtained
    -- from univalence, i.e. glueing over `B`:
    --
    --  A = = (ua e) = = B
    --  |                |
    -- (e)          (idEquiv B)
    --  |                |
    --  v                v
    --  B =====(B)====== B
    _ : Glue B {φ = i ∨ ~ i} (λ { (i = i0) → A , e ; (i = i1) → B , idEquiv B })
    _ = x

    -- We can therefore `unglue` it to obtain a term in the base line of `ua e`,
    -- i.e. term of type `B`:
    φ = i ∨ ~ i
    b : B
    b = unglue φ x

    -- This gives us a line `(i : I) ⊢ Base` in the universe of types,
    -- along which we can glue the equivalences `Γ x` and `idEquiv (Q x)`:
    --
    -- P (e x) = = = = = = Q x
    --    |                |
    --  (Γ x)        (idEquiv (Q x))
    --    |                |
    --    v                v
    --   Q x ===(Base)=== Q x
    Base : Type ℓ'
    Base = Q b

    equiv-boundary : Partial φ (Σ[ T ∈ Type ℓ' ] T ≃ Base)
    equiv-boundary (i = i0) = P x , Γ x
    equiv-boundary (i = i1) = Q x , idEquiv (Q x)

    -- Note that above `(i = i0) ⊢ x : A` and `(i = i1) ⊢ x : B`,
    -- thus `P x` and `Q x` are well-typed.
    _ : Partial i B
    _ = λ { (i = i1) → x }

    _ : Partial (~ i) A
    _ = λ { (i = i0) → x }

-- Dependent `isoToPath`

open isHAEquiv

isoToPathOver :
  {A B : Type ℓ} {P : A → Type ℓ'} {Q : B → Type ℓ'}
  (f : A → B) (hae : isHAEquiv f)
  (isom : IsoOver (isHAEquiv→Iso hae) P Q)
  → PathP (λ i → ua (_ , isHAEquiv→isEquiv hae) i → Type ℓ') P Q
isoToPathOver f hae isom = uaOver _ _ (isoToEquivOver f hae isom)
