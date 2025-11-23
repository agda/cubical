{-# OPTIONS --safe #-}
module Cubical.HITs.CauchyReals.Lems where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure


open import Cubical.Data.List
open import Cubical.Data.Nat using (ℕ)

import Cubical.Algebra.CommRing as CR

open import Cubical.Tactics.CommRingSolver



module Lems (R : CR.CommRing ℓ-zero) where
 open CR.CommRingStr (snd R)

 [_]r : ℕ → fst R
 [ ℕ.zero ]r = 0r
 [ ℕ.suc (ℕ.zero) ]r = 1r
 [ ℕ.suc x@(ℕ.suc _) ]r = 1r + [ x ]r

 lem-01 : ∀ ε δ η η' a →
       (ε - (δ + η)) +
       ((a + δ) + (η' - a))
      ≡ (ε + η') - η
 lem-01 ε δ η η' a = solve! R

 lem-02 : ∀ ε δ η η' → (ε - (δ + η)) + (δ + η')
           ≡ ((ε + η') - η)
 lem-02 ε δ η η' = solve! R

 lem-03 : ∀ ε η₁ δ η δ* η* →
            (ε - (δ +  η)) +
       ((η* + δ) + (η₁ - (δ* +  η*)))
        ≡ (ε + η₁) - (δ* + η)
 lem-03 ε η₁ δ η δ* η* = solve! R

 lem-04 : ∀ ε η₁ δ η δ* η* →
            (ε - (δ +  η)) +
       ((η* + η) + (η₁ - (δ* +  η*)))
        ≡ (ε + η₁) - (δ* + δ)
 lem-04 ε η₁ δ η δ* η* = solve! R

 lem-05 : ∀ x y → x + (y - (x + x)) ≡ y - x
 lem-05 x y = solve! R

 +AssocCommR : ∀ x y z → (x + y) + z ≡ (x + z) + y
 +AssocCommR x y z = solve! R

 private
  variable
   ε δ q q' a'' 𝕢 r η σ* δ* η₁ η* η'' η' x y x' y' a a' b b' c c' θ L : fst R

 lem--00 : (ε - δ) + δ ≡ ε
 lem--00 = solve! R

 lem--01 : (- (ε - δ)) + (- δ) ≡ (- ε)
 lem--01 = solve! R

 lem--02 : ε + q + (ε - q) ≡ ε + ε
 lem--02 = solve! R

 lem--03 : (- ε) + δ ≡ (- (ε - δ))
 lem--03 = solve! R

 lem--04 : (- ε) + (ε + q) ≡ q
 lem--04 = solve! R

 lem--05 : δ + (q - δ) ≡ q
 lem--05 = solve! R

 lem--06 : (ε - q) + (q - δ) ≡ (ε - δ)
 lem--06 = solve! R

 lem--07 : ε + (- q') + (- a'') + q' ≡ (ε - a'')
 lem--07 = solve! R

 lem--08 : δ + (ε - (δ + δ)) ≡ (ε - δ)
 lem--08 = solve! R

 lem--09 : (q - r) + (𝕢 - q) ≡ (𝕢 - r)
 lem--09 = solve! R

 lem--010 : (- (q - r)) + (𝕢 - r) ≡ (𝕢 - q)
 lem--010 = solve! R

 lem--012 : (- (- ε)) + η ≡ ε + η
 lem--012 = solve! R

 lem--013 : η + (ε - δ) ≡ (ε + η) - δ
 lem--013 = solve! R

 lem--014 : ((ε - δ) + η) ≡ (ε + η) - δ
 lem--014 = solve! R

 lem--015 : (ε - δ) + ((σ* + δ) + ((η - σ*) )) ≡ ε + η
 lem--015 = solve! R

 lem--016 : (η₁ - (δ* + η*)) + (ε - (δ + η)) + (δ + η*) ≡ (ε + η₁) - (δ* + η)
 lem--016 = solve! R

 lem--017 : (η₁ - (δ* + η*)) + (ε - (δ + η)) + (η + η*) ≡ (ε + η₁) - (δ* + δ)
 lem--017 = solve! R

 lem--018 : (ε - δ) + (η - δ*) ≡ (ε + η) - (δ* + δ)
 lem--018 = solve! R

 lem--019 : (ε - δ) + ((η* + δ) + (η - (δ* + η*))) ≡ (ε + η) - δ*
 lem--019 = solve! R

 lem--020 : (ε - δ) + ((η* + δ) + (η - (δ* + η*))) ≡ (ε + η) - δ*
 lem--020 = solve! R

 lem--021 : (ε - δ) + (η - δ*) ≡ (ε + η) - (δ* + δ)
 lem--021 = solve! R

 lem--022 : (ε - δ) + η ≡ (ε + η) - δ
 lem--022 = solve! R

 lem--023 : (((ε - δ)) + ((δ + δ*) + ((η - δ*)))) ≡ (ε + η)
 lem--023 = solve! R

 lem--024 : (ε - δ) + (η* - δ*) ≡ (ε + η*) - (δ + δ*)
 lem--024 = solve! R

 lem--025 : (ε - δ) + ((δ* + δ) + ((η'' - (δ* + η*)))) ≡ (ε + η'') - η*
 lem--025 = solve! R

 lem--026 : (((ε - δ)) + ((δ + δ*) + ((η' - δ*)))) ≡ (ε + η')
 lem--026 = solve! R

 lem--027 : (ε - δ) + η' ≡ (ε + η') - δ
 lem--027 = solve! R

 lem--028 : (ε - δ) + ((δ* + δ) + (η' - (δ* + η*))) ≡ (ε + η') - η*
 lem--028 = solve! R

 lem--029 : (ε - δ) + (η' - δ*) ≡ (ε + η') - (δ + δ*)
 lem--029 = solve! R

 lem--030 : (ε - (δ + η)) + ((δ* + δ) + (η' - δ*)) ≡ (ε + η') - η
 lem--030 = solve! R

 lem--031 : (ε - (δ + η)) + ((δ*  + η) + (η' - δ*)) ≡ (ε + η') - δ
 lem--031 = solve! R

 lem--032 : (ε - (δ + η)) + ((δ* + δ) + ((η₁ - (δ* + η*)))) ≡ (ε + η₁) - (η + η*)
 lem--032 = solve! R

 lem--033 : (ε - (δ + η₁)) + ((δ* + η₁) + ((η - (δ* + η*)))) ≡ (ε + η) - (δ + η*)
 lem--033 = solve! R

 lem--034 : ε ≡ ((ε + δ) - δ)
 lem--034 = solve! R

 lem--035 : ε ≡ ((ε - δ) + δ)
 lem--035 = solve! R

 lem--036 : (ε - η) ≡
             ((ε + δ) - (η +  δ))
 lem--036 = solve! R

 lem--037 : (ε - η) ≡
             ((δ + ε) - (δ + η))
 lem--037 = solve! R

 lem--038 : (ε - η) · (ε + η) ≡
             (ε · ε) - (η · η)
 lem--038 = solve! R

 lem--039 : (x' - x) · (y' - y) + (x' · y + x · (y' - y))
            ≡ x' · y'
 lem--039 = solve! R

 lem--040 : (x' + x) · (x' - x)
            ≡ x' · x' - x · x
 lem--040 = solve! R

 lem--041 : (x' + x) - (y' + y)
            ≡ (x' - y') + (x - y)
 lem--041 = solve! R

 lem--042 : (a ·  b' ·  c' + c · ( a' ·  b')) ·  c' ≡
           (a ·  c' + c ·  a') · ( b' ·  c')
 lem--042 = solve! R

 lem--043 : (b ·  a' ·  c' + c · ( a' ·  b')) ·  c' ≡
            (b ·  c' + c ·  b') · ( a' ·  c')
 lem--043 = solve! R

 lem--044 : (θ +  θ) + ( θ) +
      ( ε - ( ( θ +  θ) +  ( θ +  θ)))
      ≡ ( (ε + δ) - ( ( θ) +  δ))
 lem--044 = solve! R

 lem--045 : (x' + x) + (y' + y)
            ≡ (x' + y') + (x + y)
 lem--045 = solve! R

 lem--046 : L · (ε + (- δ)) ≡
    L · ε + (- (L · δ))
 lem--046 = solve! R

 lem--047 : L · (ε - (δ + η)) ≡
    ((L · ε) - ((L · δ) + (L · η)))
 lem--047 = solve! R

 lem--048 : ((x + (y - x) · a) + (y - x) · a) + (y - x) · a ≡ x + (a + a + a) · (y - x)
 lem--048 = solve! R

 lem--049 : ((ε · x) · y) + ((η · x) · y) ≡ (((ε + η) · x) · y)
 lem--049 = solve! R

 lem--050 : (- ε) ≡ (x - (x + ε))
 lem--050 = solve! R

 lem--051 :  y + ((- y) - ε) ≡ (- ((x + ε) - x))
 lem--051 = solve! R

 lem--052 : ε + x + (- y - ε) ≡ x - y
 lem--052 = solve! R

 lem--053 : y + (- (- ε)) - y  ≡ (x + ε) - x
 lem--053 = solve! R

 lem--054 : (((ε - θ) - η) + (θ + η)) ≡ ε
 lem--054 = solve! R

 lem--055 : θ + (ε - (θ + θ + θ)) ≡ (ε - (θ + θ))
 lem--055 = solve! R

 lem--056 : (ε - θ) ≡ (ε - (θ + θ)) + θ
 lem--056 = solve! R

 lem--057 : (x · y) + ((x · y) + (x · y)) ≡  (x + (x + x)) · y
 lem--057 = solve! R

 lem--058 : (r · q) + (r · q) ≡
      ((r + q) · (r + q) + - (r · r + q · q))
 lem--058 = solve! R

 lem--059 : (x' - q) + (y' + q)
            ≡ x' + y'
 lem--059 = solve! R

 lem--060 : (x' - q) + (q - y')
            ≡ x' - y'
 lem--060 = solve! R

 lem--061 : (q - y) + (x - q) ≡ (x - y)
 lem--061 = solve! R

 lem--062 : (q - x) - (q - y) ≡ y - x
 lem--062 = solve! R

 lem--063 : (ε + δ) - ε ≡ δ
 lem--063 = solve! R

 lem--064 : (x · (ε · x')) + (y · (ε · y'))
               ≡ ((x · x') + (y · y')) · ε
 lem--064 = solve! R

 lem--065 : (x' · y') - (x · y)
              ≡ y · (x' - x) + x' · (y' - y)
 lem--065 = solve! R

 lem--066 : (x' - y') + (x - y)
              ≡ (x' - y) + (x - y')
 lem--066 = solve! R

 lem--067 : (x' - y') - (y - x)
              ≡ (x' - y) + (x - y')
 lem--067 = solve! R

 lem--068 : (x' - y') - (y - x)
              ≡ (x' - y) - (y' - x)
 lem--068 = solve! R

 lem--069 : (((a · ((q + q') - δ)) - (a · (x - δ))) + y)
             - (((a · (q - δ)) - (a · (x' - δ))) + y') ≡
                (a · (q' - (x - x')) + (y - y'))
 lem--069 = solve! R

 lem--070 : - (a · b) ≡ a · (- b)
 lem--070 = solve! R

 lem--071 : x' - (y - ((x + y) - x)) ≡ x'
 lem--071 = solve! R

 lem--072 : x - (x + y) ≡ - y
 lem--072 = solve! R

 lem--073 : (x - y) · (x - y) ≡ (x · x + y · y) - (( x · y ) + ( x · y ))
 lem--073 = solve! R

 lem--074 : (x - y) + (y + x') ≡ x + x'
 lem--074 = solve! R

 lem--075 : (y + x') - (x + x')  ≡ y - x
 lem--075 = solve! R

 lem--076 : x - y + (x - y) - (x' - y) ≡ x + x - x' - y
 lem--076 = solve! R

 lem--077 : x - y ≡ (x' - y) + (x - x')
 lem--077 = solve! R

 lem--078 : y - x' ≡ (y + (y' - x')) - y'
 lem--078 = solve! R

 lem--079 : y - (y - x) ≡ x
 lem--079 = solve! R

 lem--080 : (ε + x) + ((- y) + ε) ≡ (ε + ε) + (x - y)
 lem--080 = solve! R

 lem--081 : (q + x) - (q + y) ≡ x - y
 lem--081 = solve! R

 lem--082 : (((ε - θ) - η) + (θ + η')) ≡ ε + (η' - η)
 lem--082 = solve! R

 lem--083 : x - y ≡ (- y) - (- x)
 lem--083 = solve! R

 lem--084 : δ - ε ≡ (- (ε - δ))
 lem--084 = solve! R

 lem--085 : (((x - 1r) · (x - 1r)) · ([ 2 ]r · x - 1r)) ≡ (x · ((([ 2 ]r) · (x - 1r)) · (x - 1r)
           - (x - 1r) + 1r)) - 1r
 lem--085 = solve! R

 lem--086 : (x · y) · (x' · y') ≡ (x · x') · (y · y')
 lem--086 = solve! R

 lem--087 : x + y + (x' + y') ≡ x + x' + (y + y')
 lem--087 = solve! R

 lem--088 : (x + y) - (x + y') ≡ (y - y')
 lem--088 = solve! R

 lem--089 : y - (y' + x) ≡ (y - y') - x
 lem--089 = solve! R

 lem--090 : (η · (y · y')) · (x · η') ≡ (((x · y) · y') · η) · η'
 lem--090 = solve! R

 lem--091 : ∀ {f'x fx fy gx g'x gy} →
       (f'x · gx + g'x · fx) · ε
         - (fy · gy - fx · gx)
      ≡
      gx · (f'x · ε - (fy - fx)) +
      fy · (g'x · ε - (gy - gx))
      + ε · (g'x · (fx - fy))
 lem--091 =
   solve! R

 lem--092 : (x · x) + (x' · x') + ((y · y) + (y' · y'))
      -
      (x' · y' - x · - y + (x' · y' - x · - y))
      ≡ (((x - y) · (x - y)) +  ((x' - y') · (x' - y')) )

 lem--092 = solve! R

open import Cubical.Data.Rationals as ℚ

module _ where
 open CR.CommRingStr

 ℚCommRing : CR.CommRing ℓ-zero
 ℚCommRing .fst = ℚ.ℚ
 ℚCommRing .snd .0r = 0
 ℚCommRing .snd .1r = 1
 ℚCommRing .snd .CR.CommRingStr._+_ = ℚ._+_
 ℚCommRing .snd .CR.CommRingStr._·_ = ℚ._·_
 ℚCommRing .snd .CR.CommRingStr.-_ = ℚ.-_
 ℚCommRing .snd .isCommRing = isCommRingℚ
   where
   abstract
     isCommRingℚ : CR.IsCommRing 0 1 ℚ._+_ ℚ._·_ (ℚ.-_)
     isCommRingℚ = CR.makeIsCommRing
       ℚ.isSetℚ ℚ.+Assoc ℚ.+IdR
       ℚ.+InvR ℚ.+Comm ℚ.·Assoc
       ℚ.·IdR (λ x y z → ℚ.·DistL+ x y z) ℚ.·Comm


open Lems ℚCommRing public
