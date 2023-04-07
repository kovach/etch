# Verification of Semantics of Indexed Streams

In this folder, we verify the semantics of indexed streams. The folder is organized as follows:

    - `skip_stream.lean`: This is the file which contains the main definitions of (skippable) indexed streams.
    - `skip_add.lean`: Defines the sum of indexed streams; proves that addition is sound (i.e. `(a + b).eval = a.eval + b.eval`)
    - `skip_mul.lean`: Defines the product of indexed streams; prove that multiplication is sound (i.e. `(a * b).eval = a.eval * b.eval`)
    - `skip_contract.lean`: Defines the contraction of indexed streams; proves soundness (i.e. `s.contract.eval = sum of values of s.eval`, where "sum of values" is `finsupp.sum_range` defined in finsupp_lemmas)
    - `skip_replicate.lean`: Defines replication of indexed streams; proves soundness (i.e. (replicate n v).eval is the constant function which always returns v)

These files are all used together in `nested_eval.lean`, which defines nested stream evaluation inductively on the depth of the nesting. We define the typeclass `LawfulEval`. An instance of `LawfulEval s f` indicates that evaluation is an addition and multiplication preserving map from `s` to `f`. We inductively give an instance for 
`LawfulEval (ι ⟶ₛ α) (ι →₀ β)` given an instance `LawfulEval α β`. Thus, we get the indexed stream correctness theorem, which states that evaluation is a homomorphism on strictly monotonic lawful streams.

The figures from the paper are generated in `examples.lean`.
