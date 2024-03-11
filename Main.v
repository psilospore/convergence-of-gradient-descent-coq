Require Import Reals.
Require Import Vector.
Open Scope R_scope.

Module Main.

(**
We are attempting to prove convergence of gradient descent in coq and see how far we get.
Reference: https://www.stat.cmu.edu/~ryantibs/convexopt-F13/scribes/lec6.pdf
*)

(*TODO We can take this as an assumption*)
Definition lipschitz {n: nat} (L: R) (f: Vector.t R n -> R) : Prop.
Admitted.

Definition convex {n: nat} (f: Vector.t R n -> R) : Prop.
Admitted.

Definition differentiable {n: nat} (f: Vector.t R n -> R) : Prop.
Admitted.


Definition L2norm {n: nat} (x : Vector.t R n) : R.
Admitted.

Definition vector_subtract {n:nat} (v1 v2: Vector.t R n) : Vector.t R n :=
  map2 (fun x y => x - y) v1 v2.

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
Theorem convergence : forall {n: nat} (k: nat)(t: R) (x_0: Vector.t R n) (x_k : Vector.t R n) (x_star: Vector.t R n) (f : Vector.t R n -> R), 
  exists L : R,   
  L > 0 ->
  lipschitz L f ->
  convex f ->
  differentiable f ->
  f x_k - f x_star <= (L2norm(vector_subtract x_0 x_star) * L2norm(vector_subtract x_0 x_star)) / (2 * t * (INR k)). (* Fill in the rest *)

Proof. 
  intros k t x_0 x_k x_star f. 
