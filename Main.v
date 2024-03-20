Require Import Reals.
Require Import Vector.
Open Scope R_scope.

Module Main.

(*Alias for real numbered vector of size n*)
Notation Vec n := (Vector.t R n).

Notation CostFunction n := (Vector.t R n -> R).

Notation GradientFunction n := (Vector.t R n -> Vector.t R n).

(**
We are attempting to prove convergence of gradient descent in coq and see how far we get.
Reference: https://www.stat.cmu.edu/~ryantibs/convexopt-F13/scribes/lec6.pdf
*)

(* BEGIN Utilities *)
Definition L2norm {n: nat} (x : Vec n) : R.
Admitted.

Definition vector_subtract {n:nat} (v1 v2: Vec n) : Vec n :=
  map2 (fun x y => x - y) v1 v2.

(* distance for real numbers*)
Definition dist_R (x y : R) : R := Rabs (x - y).

Definition square (x : R) : R := x * x.

(* transpose v1 then multiply with v2 *)
Definition transpose_mult {n: nat} (v1 v2: Vec n) : R.
Admitted.

(*BEGIN Supporting Lemmas and Definations*)

Definition lipschitz {n: nat} (L: R) (f: CostFunction n) : Prop :=
  forall x1 x2 : Vec n,
  dist_R (f x1) (f x2) <= L * (L2norm (vector_subtract x1 x2)).

(* Could make this more polymorphic but also could make a thereom lipschitz imply this too*)
Definition lipschitz_gradient {n: nat} (L: R) (f: GradientFunction n) : Prop :=
  forall x1 x2 : Vec n,
  L2norm (vector_subtract (f x1) (f x2)) <= L * (L2norm (vector_subtract x1 x2)).

(* x_star is the optimal point in f
TODO so we just need state it's the lowest value?
 *)
Definition optimal {n: nat} (x_star: Vec n) (f: CostFunction n) : Prop :=
  forall x : Vec n, f x_star <= f x.

(*TODO write a defination*)
Definition convex {n: nat} (f: CostFunction n) : Prop.
Admitted.

(*TODO write a defination*)
Definition differentiable {n: nat} (f: Vec n -> R) : Prop.
Admitted.

(* TODO see wikipedia gradients for details*)
Definition grad {n: nat} (f : CostFunction n ) : GradientFunction n.
Admitted.

(* TODO I forgot which one this was and if we needed it *)
(* Lemma lipschitz_implies_gradient_bound : lipschitz L f -> grad f -> True. *)

(**
Our assumption that ∇f is Lipschitz continuous with constant L implies that ∇2f (x) LI, or
equivalently that ∇2f (x) − LI is a negative semidefinite matrix. Using this fact we can perform a quadratic
expansion of f around f (x) and obtain the following inequality
f (y) ≤ f (x) + ∇f (x)T (y − x) + 1
2 ∇2f (x)‖y − x‖2
2
≤ f (x) + ∇f (x)T (y − x) + 1
2 L‖y − x‖2
2
*)
Lemma lipschitz_implies_inequality : forall {n: nat} (x y : Vec n) (f: CostFunction n),
  exists L : R,
  L > 0 ->
  (* I think we need to make lipschitz handle R^n as a function output*)
  lipschitz_gradient L (grad f) -> 
  f y <= f x + transpose_mult ((grad f) x) (vector_subtract y x) + (1%R/2%R) * L * square (L2norm (vector_subtract y x)).
Admitted.

(*BEGIN Convergence Theorem*)

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
Theorem convergence : forall {n: nat} (k: nat) (t: R) (x_0: Vec n) (x_k : Vec n) (x_star: Vec n) (f : CostFunction n), 
  exists L : R,   
  L > 0 ->
  lipschitz L f ->
  convex f ->
  differentiable f ->
  optimal x_star f ->
  f x_k - f x_star <= (square (L2norm (vector_subtract x_0 x_star))) / (2 * t * (INR k)).
Admitted.

End Main.

