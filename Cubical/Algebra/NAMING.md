NAMING
======

This file provides a guide for naming definitions in the Algebra folder.

* To name a property of an operation, write the name of the operation
  first, then the property. For example, `+Comm` or `·Assoc`.

* Use the following names and abbreviations for common properties.
  For laws that have left and right versions, use a suffix `L` or `R`.
  Check below to see which version is `L` and which is `R`.
  - `Assoc` = associativity

    ```
    ·Assoc : x · (y · z) ≡ (x · y) · z
    ```

  - `Comm` = commutativity

    ```
    ·Comm : x · y ≡ y · x
    ·CommL : x · (y · z) ≡ y · (x · z)
    ·CommR : (x · y) · z ≡ (x · z) · y
    ```

  - `Dist` = distributivity. The name should show first the operation
    that is distributed, whether it is distributing over the left or
    right, and then the operation that is distributed over.

    ```
    x · (y + z) ≡ (x · y) + (x · z)
    ```

  - `Id` = unit laws

    ```
    ·IdL : 1 · x ≡ x
    -Id : (- 0) ≡ 0
    ```

  - `Inv` = inverse laws

    ```
    +InvL : (- x) + x ≡ 0
    ```

  - `Absorb` = absorption. The name should show first the outer
    operation, whether it is absorbed on the left, then the inner
    operation.

    ```
    ∧AbsorbL∨ : x ∧ (x ∨ y) ≡ x
    ```

  - `Invol` = involution

    ```
    -Invol : - (- x) ≡ x
    ```

  - `Cancel` = cancellation

    ```
    ·CancelL : x · a ≡ x · b → a ≡ b
    ```

  - `Annihil` = annihilation

    ```
    ·AnnihilL : 0 · x ≡ 0
    ```

  - `Idem` = idempotency

    ```
    ∧Idem : x ∧ x ≡ x
    ```

* The fact that a homomorphism preserves a specific operation
  should be named `pres·` where `·` is the operation.

* An instance of an algebraic structure should include the
  name of the structure. For example `UnitGroup` and `ℤGroup`.
