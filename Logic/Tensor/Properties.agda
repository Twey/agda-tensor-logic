{-# OPTIONS --copatterns #-}

module Logic.Tensor.Properties where

open import Logic.Tensor.Syntax
open import Logic.Tensor.Semantics

import Semantics.Game as G
import Semantics.Game.Strategy as S
import Semantics.Game.Strategy.Strategies as S

open import Data.Unit hiding (⊤)
open import Data.Sum
open import Data.Product

⊤-defn : Provable ⊤
⊤-defn = S.⊤

⊤-id-right : ∀ {A} → Provable A → Provable (A ⊗ ⊤)
⊤-id-right s = s S.⊗ ⊤-defn

⊤-id-left : ∀ {A} → Provable A → Provable (⊤ ⊗ A)
⊤-id-left s = ⊤-defn S.⊗ s

⊥-defn : Disprovable ⊥
⊥-defn = S.⊥

¬-defn : {A : Formula} → Disprovable A → Provable (¬ A)
¬-defn = S.¬_

⊗-defn : ∀ {A B} → Provable A × Provable B → Provable (A ⊗ B)
⊗-defn (sA , sB) = sA S.⊗ sB

⊗-commute : ∀ {A B} → Provable (A ⊗ B) → Provable (B ⊗ A)
⊗-commute = S.swap
