{-

Normalize Integer Matrices

-}
{-# OPTIONS --safe #-}

module Cubical.Experiments.IntegerMatrix where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat
open import Cubical.Data.Int
open import Cubical.Data.FinData
open import Cubical.Data.List

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Int

open import Cubical.Algebra.Matrix
open import Cubical.Algebra.Matrix.CommRingCoefficient
open import Cubical.Algebra.IntegerMatrix.Smith
open import Cubical.Algebra.IntegerMatrix.Diagonalization

private
  variable
    m n : ℕ

open Coefficient ℤCommRing

-- Get divisors directly

open isSmithNormal
open Smith
open isDiagonal
open Diag

getElemDiv : Mat m n → List ℤ
getElemDiv M = smith M .isnormal .divs .fst

getDiagDiv : Mat m n → List ℤ
getDiagDiv M = diagonalize M .isdiag .divs .fst

-- Constructing matrices

makeMat2×2 : ℤ → ℤ → ℤ → ℤ → Mat 2 2
makeMat2×2 a00 _ _ _ zero zero = a00
makeMat2×2 _ a01 _ _ zero one  = a01
makeMat2×2 _ _ a10 _ one  zero = a10
makeMat2×2 _ _ _ a11 one  one  = a11

makeMat3×3 : ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → Mat 3 3
makeMat3×3 a00 _ _ _ _ _ _ _ _ zero zero = a00
makeMat3×3 _ a01 _ _ _ _ _ _ _ zero one  = a01
makeMat3×3 _ _ a02 _ _ _ _ _ _ zero two  = a02
makeMat3×3 _ _ _ a10 _ _ _ _ _ one  zero = a10
makeMat3×3 _ _ _ _ a11 _ _ _ _ one  one  = a11
makeMat3×3 _ _ _ _ _ a12 _ _ _ one  two  = a12
makeMat3×3 _ _ _ _ _ _ a20 _ _ two  zero = a20
makeMat3×3 _ _ _ _ _ _ _ a21 _ two  one  = a21
makeMat3×3 _ _ _ _ _ _ _ _ a22 two  two  = a22

-- The Tests

-- One can add flag "-vprofile.interactive:10" to this file,
-- then C-c C-n to run these tests and also get the time.

-- It turns out that, "smith" is much slower than "diagonalize"
-- and it doesn't work even for simple 3×3-matrices.
-- The "diagonalize" works only for very simple 3×3-matrices.
-- One subtle point is, if one only do one-step in Smith normalization
-- and simply add the time cost in each steps,
-- the result is far less than running the whole function "smith".
-- So the recursive procedure slows down the procedure
-- for some reasons I don't fully understand.
-- Also, the performance of "smith" is very bad at certain trivial cases,
-- much worse than some non-trivial cases.

mat1 = makeMat2×2
   1  0
   0  1
-- Time: 528ms
test1  = getElemDiv mat1
-- Time: 51ms
test1' = getDiagDiv mat1

mat2 = makeMat2×2
   2  0
   0  1
-- Time: 89,437ms
-- Why so slow?
test2  = getElemDiv mat2
-- Time: 51ms
test2' = getDiagDiv mat2

mat3 = makeMat2×2
   2  1
   3  5
-- Time: 3,308ms
test3  = getElemDiv mat3
-- Time: 1,887ms
test3' = getDiagDiv mat3

mat4 = makeMat2×2
   4  2
   2  4
-- Time: 3,284ms
test4  = getElemDiv mat4
-- Time: 1,942ms
test4' = getDiagDiv mat4

mat5 = makeMat3×3
   1  0  0
   0  0  0
   0  0  0
-- Time: 9,400ms
test5  = getElemDiv mat5
-- Time: 337ms
test5' = getDiagDiv mat5

mat6 = makeMat3×3
   1  0  0
   0  1  0
   0  0  1
-- Time: ???
-- It doesn't work out already.
test6  = getElemDiv mat6
-- Time: 8,598ms
test6' = getDiagDiv mat6

mat7 = makeMat3×3
   1  1  0
   3  2  1
   2  0  1
-- Time: ???
test7  = getElemDiv mat7
-- Time: 14,149ms
test7' = getDiagDiv mat7

mat8 = makeMat3×3
   2  3  1
   2  2  3
   1  1  0
-- Time: ???
test8  = getElemDiv mat8
-- Time: ???
-- Not working either.
test8' = getDiagDiv mat8
