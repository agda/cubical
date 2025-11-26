{-

This module contains a set of test cases designed to ensure the robustness of the `NSolver` module. The multitude of test cases is motivated by the necessity to cover various aspects that impact the solver's correctness.

### Aspects Covered

- **Dimensionality**:
  - Goals of more than 2 dimensions are treated slightly diferent in some situations, also some edgecases can
    apear only in higher dimensions.
- **Functoriality of Congruence**:
  - Verifies that solving paths may require applying functoriality of congruence.
- **Path Definition Scope**:
  - Tests paths defined as free variables, higher constructors, and abstract definitions.
- **Degenerated Interval Expressions**:
  - Verifies handling of degenerated interval expressions present in paths.

### Importance of Coverage

Covering these aspects in different combinations is crucial for maintaining the solver's code. Experience during development has shown that some errors can be specific to arbitrary combinations of the above aspects. Having the ability to quickly receive feedback about the precise combination of factors triggering an error is indispensable when introducing optimizations and heuristics in the solver.

### Test Modules

- **Const.agda**:
  - Tests solver on basic properties of constant paths.
- **GroupoidLaws.agda**:
  - Checks the solver against groupoid laws.
- **Cong.agda**:
  - Verifies that the solver correctly handles congruence properties.
- **Coherence.agda**:
  - Tests sollver on coherence of its own solutions.

-}

{-# OPTIONS --safe -v 0 #-}

module Cubical.Tactics.PathSolver.NSolver.Tests where


import Cubical.Tactics.PathSolver.NSolver.Tests.Const
import Cubical.Tactics.PathSolver.NSolver.Tests.GroupoidLaws
import Cubical.Tactics.PathSolver.NSolver.Tests.Cong
import Cubical.Tactics.PathSolver.NSolver.Tests.Coherence

