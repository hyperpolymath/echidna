(* Type error: claims `True -> False` and proves with `exact I`. *)
Theorem broken : True -> False.
Proof. intro H. exact I. Qed.
