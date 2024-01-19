# Verification of Semantics of Indexed Streams

In this folder, we verify the semantics of indexed streams. There are two key claims in the paper: that the evaluation of indexed streams to functions is a homomorphism; and the operations on strictly monotonic indexed streams form strictly monotonic indexed streams.

Both of these claims are proved in `nested_eval.lean`, which defines nested stream evaluation inductively on the depth of the nesting using typeclasses. We define the type of strictly monotonic lawful streams `ι ⟶ₛ α` and prove that the sum, product etc. of strictly lawful streams is strictly lawful. This is implicit in the type signatures of the operators e.g. `+ : (ι ⟶ₛ α) → (ι ⟶ₛ α) → (ι ⟶ₛ α)` produces a strictly lawful stream as output.

We then define the typeclass `LawfulEval`, where `LawfulEval s f` indicates that evaluation is an addition and multiplication preserving map from `s` to `f`. We inductively give an instance for `LawfulEval (ι ⟶ₛ α) (ι →₀ β)` given an instance `LawfulEval α β`. We also prove correctness for `contract` and `replicate` (expand). Thus, we get the indexed stream correctness theorem (theorem 6.1 from the paper), which states that evaluation is a homomorphism on strictly monotonic lawful streams.


The folder is organized as follows:

 - `skip_stream.lean`: This is the file which contains the main definitions of (skippable) indexed streams.
 - `add.lean`: Defines the sum of indexed streams; proves that addition is sound (i.e. `(a + b).eval = a.eval + b.eval`)
 - `mul.lean`: Defines the product of indexed streams; prove that multiplication is sound (i.e. `(a * b).eval = a.eval * b.eval`)
 - `contract.lean`: Defines the contraction of indexed streams; proves soundness (i.e. `s.contract.eval = sum of values of s.eval`, where "sum of values" is `finsupp.sum_range` defined in finsupp_lemmas)
 - `replicate.lean`: Defines replication of indexed streams; proves soundness (i.e. `(replicate n v).eval` is the constant function which always returns `v`)
 - `nested_eval.lean`: Defines nested evaluation of streams, and puts together the results from the above files to prove that evaluation is a homomorphism.

The figures from the paper are generated in `examples.lean`.
