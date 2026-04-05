module NonNeg
val abs_nonneg : x:int -> Lemma (if x >= 0 then x >= 0 else -x >= 0)
let abs_nonneg _ = ()
