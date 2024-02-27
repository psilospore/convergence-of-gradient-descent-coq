Require Import Reals.


Module Main.

(**
We are attempting to prove convergence of gradient descent in coq and see how far we get.
Reference: https://www.stat.cmu.edu/~ryantibs/convexopt-F13/scribes/lec6.pdf
*)

(*TODO We can take this as an assumption*)
Definition lipschitz (L: R) (f: list R -> R) : Prop.
Admitted.

Definition convex (f: list R -> R) : Prop.
Admitted.

Definition differentiable (f: list R -> R) : Prop.
Admitted.
(**
Theorem 6.1 Suppose the function f : Rn → R is convex and differentiable, and that its gradient is
Lipschitz continuous with constant L > 0, i.e. we have that ‖∇f (x) − ∇f (y)‖2 ≤ L‖x − y‖2 for any x, y.
Then if we run gradient descent for k iterations with a fixed step size t ≤ 1/L, it will yield a solution f (k)
which satisfies
          f (x(k)) − f (x∗) ≤ ‖x(0) − x∗‖2
2
2tk , (6.1)
where f (x∗) is the optimal value. Intuitively, this means that gradient descent is guaranteed to converge
and that it converges with rate O(1/k).
*)
Theorem convergence : forall f : list R -> R,  exists L : R,
  lipschitz L f ->
  convex f ->
  differentiable f ->
  True. (* Fill in the rest *)
