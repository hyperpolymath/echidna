-- Type error: claims A → B from no premise.
module Broken where

bogus : (A : Set) -> (B : Set) -> A -> B
bogus A B x = x
