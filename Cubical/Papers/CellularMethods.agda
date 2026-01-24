{-

Please do not move this file. Changes should only be made if necessary.

This file contains pointers to the code examples and main results from
the paper:

Cellular Methods in Homotopy Type Theory

-}

module Cubical.Papers.CellularMethods where
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat

{- Cubical.CW.Base contains the definition of
   - CW structures (CWskel)
   - Finite CW structures (finCWskel)
   - The colimit of a CW structure (realise)
   - The category of CW complexes (CW , _→ᶜʷ_)
   - The category of finite CW complexes (finCW , _→ᶜʷ_) -}
open import Cubical.CW.Base

{- Cubical.CW.Properties contains the proof of
   - Lemma 12 from the paper (isConnected-CW↪)
   - Lemma 13 from the paper (isConnected-CW↪∞) -}
open import Cubical.CW.Properties

{- Cubical.HITs.SphereBouquet.Base contains the definition of sphere bouquets -}
open import Cubical.HITs.SphereBouquet.Base

{- Cubical.HITs.SphereBouquet.Degree contains the definition/proof of
   - The degree of a sphere bouquet (bouquetDegree)
   - Proposition 29 from the paper (bouquetDegreeSusp, bouquetDegreeComp) -}
open import Cubical.HITs.SphereBouquet.Degree

{- Cubical.CW.ChainComplex contains the definition of
   - The augmented chain complex associated to a CW structure (CW-AugChainComplex)
   - The reduced cellular homology groups of a CW structure (H̃ˢᵏᵉˡ) -}
open import Cubical.CW.ChainComplex

{- Cubical.CW.Map contains the definition/proof of
   - Cellular maps (cellMap)
   - Finite cellular maps (finCellMap)
   - The colimit of a cellular map (realiseCellMap)
   - The identity and composition of cellular maps (idCellMap, composeCellMap)
   - The functor from finite CW complexes to finite chains (finCellMap→finChainComplexMap)
   - The functoriality of cellular homology (finCellMap→HomologyMap) -}
open import Cubical.CW.Map

{- Cubical.CW.Homotopy contains the definition/proof of
   - Cellular homotopies (cellHom)
   - Finite cellular homotopies (finCellHom)
   - Finite cellular homotopies induce finite chain homotopies (cellHom-to-ChainHomotopy) -}
open import Cubical.CW.Homotopy

{- Cubical.CW.Approximation contains the proof of
   - The first cellular approximation theorem (CWmap→finCellMap)
   - The second cellular approximation theorem (pathToCellularHomotopy) -}
open import Cubical.CW.Approximation

{- Cubical.CW.Homology contains the definition/proof of
   - The functoriality of cellular homology for CW structures (H̃ˢᵏᵉˡ→-pre)
   - The definition of cellular homology groups for CW complexes (H̃ᶜʷ)
   - The functoriality of cellular homology for CW complexes (H̃ᶜʷ→ , H̃ᶜʷ→id , H̃ᶜʷ→comp) -}

open import Cubical.CW.Homology.Base

{- Cubical.CW.Connected contains the proof of the Hurewicz approximation theorem (makeConnectedCW) -}
open import Cubical.CW.Connected

{- Cubical.CW.HurewiczTheorem contains the proof of the Hurewicz theorem (HurewiczTheorem) -}
open import Cubical.CW.HurewiczTheorem
