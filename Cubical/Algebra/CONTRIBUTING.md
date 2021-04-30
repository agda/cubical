CONTRIBUTING
============

# General

- We divide the definition of an algebraic structure into four parts:

  1. Carrier: This is often `Type`, but might be for example `Type × Type`.
  2. Properties of the carrier: this is usually `isSet`.
  3. Operations: Non-propositional operations on the carrier, such as the multiplication and unit for a monoid.
  4. Properties of the operations: for example, the associativity and unit laws for a monoid.

  We separate (ii) and (iv) because it makes it easier to avoid redundant assumptions of `isSet` in complex
  algebraic structures or to drop this assumption when it is not needed. As an example illustrating our naming
  conventions, we would give the following definitions building up the universe of monoids.

  ```
  RawMonoidStr : Type ℓ → Type ℓ
  RawMonoidStr = {! unit and multiplication operators !}

  IsMonoidStr : (A : Type ℓ) → RawMonoidStr A → Type ℓ
  IsMonoidStr = (⋯ associativity and unit laws ⋯)

  MonoidStr : Type ℓ → Type ℓ
  MonoidStr A = Σ[ R ∈ RawMonoidStr A ] (IsMonoidStr R)

  Monoid : Type (ℓ-suc ℓ)
  Monoid = Σ[ A ∈ Type ℓ ] (isSet A × MonoidStr A)
  ```

  _Is this definition of `Monoid` best, or should it be rearranged to `Σ[ A ∈ hSet ℓ ] MonoidStr (A .fst)`?
  Should we use a record instead of this four-part `Σ`-type? I'd guess we want sub-groupings of these often
  enough that a `Σ`-type is preferable._

- We define more complicated instances of (i-iv) by nesting simpler instances. For example, the definition of
  `RawRingStr` structure would be a record or `Σ`-type containing `RawMonoidStr` and `RawAbGroupStr` as
  fields, and `IsRingStr` would likewise use `IsMonoidStr` and `IsAbGroupStr`.

- We prefer records over nested `Σ`-types for efficiency and readability. For example, the definition of
  `IsRingStr` could be a record with first `IsMonoidStr` and `IsAbGroupStr` fields and then fields for the
  laws concerning both the monoid and group operations. Reflection
  ([`Cubical.Reflection.RecordEquiv`](https://github.com/agda/cubical/blob/master/Cubical/Reflection/RecordEquiv.agda))
  can be used to derive an equivalent `Σ`-type representation when this is more convenient, for example to
  prove that some record type is propositional.

- When defining an instance of an algebraic structure, use copattern matching rather than a record
  constructor, and try to avoid relying on helper functions that take many arguments---this is for efficiency
  reasons. Because of the heavily nested nature of algebraic structures, it can be more readable to separate
  out components into separate definitions (local or otherwise), for example defining the group component of a
  given ring structure separately.

- It is preferred to include redundant structure and properties if there are often more direct proofs in
  specific instances or if there is no canonical choice of minimal axioms. Helper functions can then be
  defined to generate the full structure from a subset. For example, the definition of groups includes both a
  left inverse and right inverse law although this is not strictly necessary. Use your judgment.

- _Where should instances of structure be located?_

- _When should instance arguments be used?_

# Morphisms and equivalences

- The definitions of structured functions and equivalences should be broken into parts following the structure
  format. Structured equivalences should be defined as equivalences whose underlying functions are structured.
  For example:

  ```
  IsRawMonoidHom : {A₀ : Type ℓ} {A₁ : Type ℓ'}
    (S₀ : RawMonoidStr A₀) (f : A₀ → A₁) (S₁ : RawMonoidStr A₁) → Type (ℓ-max ℓ ℓ')
  IsRawMonoidHom (S₀ , _) f (S₁ , _) = {! probably a record !}

  IsMonoidHom : {A₀ : Type ℓ} {A₁ : Type ℓ'}
    (S₀ : MonoidStr A₀) (f : A₀ → A₁) (S₁ : MonoidStr A₁) → Type (ℓ-max ℓ ℓ')
  IsMonoidHom (S₀ , _) f (S₁ , _) = IsRawMonoidHom S₀ f S₁

  IsMonoidEquiv : {A₀ : Type ℓ} {A₁ : Type ℓ'}
    (S₀ : MonoidStr A₀) (e : A₀ ≃ A₁) (S₁ : MonoidStr A₁) → Type (ℓ-max ℓ ℓ')
  IsMonoidEquiv (S₀ , _) e (S₁ , _) = IsRawMonoidHom S₀ (e .fst) S₁

  MonoidHom : Monoid ℓ → Monoid ℓ' → Type (ℓ-max ℓ ℓ')
  MonoidHom (M₀ , _ , S₀) (M₁ , _ S₁) = Σ[ f ∈ (M₀ → M₁) ] IsMonoidHom S₀ f S₁

  MonoidEquiv : Monoid ℓ → Monoid ℓ' → Type (ℓ-max ℓ ℓ')
  MonoidEquiv = {! as with MonoidHom !}
  ```
  _These definitions aren't set up the right way for the current SIP setup, but are correct for the DUARel
  setup we're ready to replace it with._

- The definition of morphism (and thus equivalence) should include a preservation law for every operation of
  the structure, even if these are redundant. In other words, the division between "operation" and "property"
  in the morphism definitions should match that of the structure definitions.
