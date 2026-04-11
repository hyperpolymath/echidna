-- Minimal Lean example for ECHIDNA MVP
-- Use 'variable' instead of 'axiom' to avoid introducing a global axiom
-- into the Lean kernel. A variable is universally quantified in each
-- definition that uses it, which is sound and does not pollute the
-- environment.
variable (A : Prop)
