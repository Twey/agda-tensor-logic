{-# OPTIONS --copatterns #-}

module Semantics.Game.Strategy where

open import Semantics.Game

record Strategy  (g : Game) : Set
record Strategy′ (g : Game) : Set

record Strategy g where
  coinductive
  constructor strat
  field
    react : (m : move g) → Strategy′ (play g m)

record Strategy′ g where
  coinductive
  constructor strat′
  field
    response : move g
    followup : Strategy (play g response)

open Strategy  public
open Strategy′ public

