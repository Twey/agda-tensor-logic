module Logic.Tensor.Syntax where

infixl 5 _⊗_
data Formula : Set where
  ⊤   : Formula
  ¬_  : Formula → Formula
  _⊗_ : Formula → Formula → Formula

⊥ = ¬ ⊤
_⇒_ : Formula → Formula → Formula
A ⇒ B = ¬ (A ⊗ ¬ B)

