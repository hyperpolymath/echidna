module MulZero
open FStar.Mul
val mul_zero : x:int -> Lemma (x * 0 == 0)
let mul_zero _ = ()
