{-# OPTIONS --copatterns #-}

module Semantics.Game.Strategy where

open import Semantics.Game renaming (_⊗_ to _⊗ₗ_)

record Strategy  (g : Game) : Set
record Strategy′ (g : Game) : Set

record Strategy g where
  coinductive
  constructor strat
  open Game g
  field
    react : (m : move) → Strategy′ (play m)

record Strategy′ g where
  coinductive
  constructor strat′
  open Game g
  field
    response : move
    followup : Strategy (play response)

open Strategy  public
open Strategy′ public

open import Data.Sum using (inj₁; inj₂)

_⊗_ : ∀ {A B} → Strategy A → Strategy B → Strategy (A ⊗ₗ B)
react (sA ⊗ sB) (inj₁ a)
  = strat′ (response (react sA a)) (followup (react sA a) ⊗ sB)
react (sA ⊗ sB) (inj₂ b)
  = strat′ (response (react sB b)) (sA ⊗ followup (react sB b))
