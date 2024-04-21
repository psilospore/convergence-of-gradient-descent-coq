Require Import Reals.
Require Import Vector.
Open Scope R_scope.

Module Main.

(*Alias for real numbered vector of size n*)
Notation Vec n := (Vector.t R n).

Notation CostFunction n := (Vector.t R n -> R).

Notation GradientFunction n := (Vector.t R n -> Vector.t R n).

(*All the x points from x_1 to x_k where x in Real ^ n for some arbitrary n dimensions *)
Notation X_Points k n := (Vector.t (Vec n) k).

(**
We are attempting to prove convergence of gradient descent in coq and see how far we get.
Reference: https://www.stat.cmu.edu/~ryantibs/convexopt-F13/scribes/lec6.pdf
Comments are occasionally from the reference.
*)

(* BEGIN Utilities *)
Definition L2norm {n: nat} (x : Vec n) : R.
Admitted.

(* Not sure why some of the vector functions are not in the stdlib or maybe I'm missing them.*)
(* Might be nice to make some notation with these *)
Definition vector_subtract {n:nat} (v1 v2: Vec n) : Vec n :=
  map2 (fun x y => x - y) v1 v2.


Definition scalar_mult {n: nat} (s: R) (v: Vec n) : Vec n.
Admitted.

(* distance for real numbers*)
Definition dist_R (x y : R) : R := Rabs (x - y).


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
Definition differentiable {n: nat} (f: CostFunction n) : Prop.
Admitted.

(* TODO see wikipedia gradients for details*)
Definition grad {n: nat} (f : CostFunction n ) : GradientFunction n.
Admitted.

(* Gradient decent after k steps *)
Fixpoint gradient_descent {n: nat} (k : nat) (x : Vec n) (f : CostFunction n) (learningRate: R) : Vec n :=
  match k with
  | O => x (*Last step return the optimized weights*)
  | S k' => 
    let gradient := grad f x in
    let step := scalar_mult learningRate gradient in
    (* Next weights *)
    let x_i_plus_1 := vector_subtract x step in
    gradient_descent k' x_i_plus_1 f learningRate
  end.

(* TODO consider making this it's own function so we can do 6.2*)
(* Definition update_weights *)

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
  lipschitz_gradient L (grad f) -> 
  f y <= f x + transpose_mult ((grad f) x) (vector_subtract y x) + (1/2) * L * (L2norm (vector_subtract y x) ^ 2).
Admitted.

(* Minor Lemmas*)


(* Using t ≤ 1/L, we know that −(1 − 1/2 Lt) = 1/2 Lt − 1 ≤ 1/2 L(1/L) − 1 = 1/2 − 1 = − 1 / 2 *)
(* TODO see https://www.cs.princeton.edu/courses/archive/fall07/cos595/stdlib/html/Coq.Reals.Raxioms.html*)
(* We should do this proof first because it's the easiest*)
Lemma t_less_than_one_over_L_implies : forall (L t : R),
  L > 0 ->
  t <= 1 / L ->
  - (1 - 1/2 * L * t) <= -1/2.
Proof.
  intros L t H_L_less_than_0 H_t_less_than_eq_1_div_L.
  unfold Rdiv in H_t_less_than_eq_1_div_L.
  rewrite Rmult_1_l in H_t_less_than_eq_1_div_L.
Admitted.

(*6.2 *)
(**
Now let’s plug in the gradient descent update by letting y = x+ = x − t∇f (x). We then get:
f (x+) ≤ f (x) + ∇f (x)T (x+ − x) + 1/2 * L‖x+ − x‖_2^2
= ... # Some algebra 
= f (x) − (1 − 1/2 * L* t) t‖∇f (x)‖_2^2
# And then use t_less_than_one_over_L_implies to get 
= f (x) − 1/2 t‖∇f (x)‖_2^2
*)
Lemma f_x_plus_less_than : forall {n : nat} (x : Vec n) (f : CostFunction n) (L t : R),
  (* x+ = x − t∇f (x) *)
  let x_plus := vector_subtract x (scalar_mult t (grad f x)) in
  f x_plus <= f x - 1/2 * t * ((L2norm (grad f x)) ^ 2).
Admitted.

(* TODO apply t_less_than_one_over_L_implies*)

Search (fold_left).

(*6.6 The total difference of the cost at each iteration and the optimum cost is bounded
by some factor initial x subtracted by the x at the optimum and learning rate.

After each iteration taking the distance of how far it is 
from the optimum value and then sum all those values.
Those sum of iterations should be **bounded** by some factor 
of the initial x subtracted by the x at the optimum and learning rate.

  ∑ f (x(i) − f (x∗) ≤ 1 / 2t ( ‖x(0) − x∗‖^2_2

  x_1_to_k : List R Represents x^1 to x^k for the k number of iterations

*)
Lemma bounded_sum_of_costs: forall {n: nat} {k: nat} (t: R) (x_0: Vec n) (x_star: Vec n) (X: X_Points k n) (f : CostFunction n),
  let sums_of_iterations := fold_left (fun (acc : R) (x_i : Vec n) => acc + (f x_i) - (f x_star)) 0 X in
  sums_of_iterations <= (L2norm (vector_subtract x_0 x_star)) ^ 2 / (2 * t).
Admitted.

(*TODO add hypothesis that f is decreasing *)
Lemma r1_lt_r2: forall {n: nat} {k: nat} (t: R) (x_0: Vec n) (x_k : Vec n) (x_star: Vec n) (X: X_Points k n) (f : CostFunction n),
  let sums_of_iterations := fold_left (fun (acc : R) (x_i : Vec n) => acc + (f x_i) - (f x_star)) 0 X in
  f x_k - f x_star <= sums_of_iterations / (INR k). (*TODO add k and inequality*)
Admitted.

Lemma r2_lt_r3: forall {n: nat} {k: nat} (t: R) (x_0: Vec n) (x_k : Vec n) (x_star: Vec n) (X: X_Points k n) (f : CostFunction n),
  let sums_of_iterations := fold_left (fun (acc : R) (x_i : Vec n) => acc + (f x_i) - (f x_star)) 0 X in
  sums_of_iterations / (INR k) <= (L2norm (vector_subtract x_0 x_star)) ^ 2 / (2 * t * (INR k)).  (*TODO add k and inequality*)
Admitted.

(*We esentially want to squish Rlt_le_trans_middle :e. This sorta helps us do that.
 *)
Lemma Rlt_le_trans_middle : forall r1 r2 r3, r1 <= r2 -> r2 <= r3 -> (r1 <= r3) = (r1 <= r2).
Admitted.

Lemma six_to_seven: forall {n: nat} {k: nat} (t: R) (x_0: Vec n) (x_star: Vec n) (X: X_Points k n) (f : CostFunction n) (x_k : Vec n),
  let sums_of_iterations := fold_left (fun (acc : R) (x_i : Vec n) => acc + (f x_i) - (f x_star)) 0 X in
  sums_of_iterations <= (L2norm (vector_subtract x_0 x_star)) ^ 2 / (2 * t) ->
  f x_k - f x_star <=
  fold_left (fun (acc : R) (x_i : Vec n) => acc + f x_i - f x_star)
    0 X / INR k.
Admitted.


(* 6.5 -> 6.6 A *)
Lemma six_five_implies_six_six_A: forall {n: nat} {k: nat} (t: R) (x_0: Vec n) (x_star: Vec n) (X: X_Points k n) (f: CostFunction n),
    (forall (i: nat) (Hi: Nat.lt i k) (HSi: Nat.lt (S i) k) (Hi_minus_one: Nat.lt (i-1) k),
        let xi_minus_one := nth X (Fin.of_nat_lt Hi_minus_one) in
        let xi := nth X (Fin.of_nat_lt Hi) in
        let xi_plus_one := nth X (Fin.of_nat_lt HSi) in
        let f_x_star := f x_star in
        let f_xi_plus_one := f xi_plus_one in
        let right_hand := 1 / (2 * t) * (L2norm (vector_subtract xi x_star)^2 - L2norm(vector_subtract xi_plus_one x_star)^2) in
        f_xi_plus_one - f_x_star <= right_hand ->
        fold_left (fun (acc : R) (x_i : Vec n) => acc + f x_i - f x_star) 0 X
                  <= 1 / (2*t) * (L2norm (vector_subtract xi_minus_one x_star)^2 - L2norm(vector_subtract xi x_star)^2)).

(* 6.6 A -> 6.6 C *)
Lemma six_six_A_implies_six_six_C: forall {n: nat} {k: nat} (t: R) (x_0: Vec n) (x_star: Vec n) (X: X_Points),
  (* 6.6 A *)
  (* TODO *)
  fold_left (fun (acc : R) (x_i : Vec n) => acc + f x_i - f x_star) 0 X
      <= (* TODO righthand inequality in statement 6.6 A *)

  ->
  (* 6.6 C *)
  fold_left (fun (acc : R) (x_i : Vec n) => acc + f x_i - f x_star)
    0 x_1st_to_kth <=
  L2norm (vector_subtract x_0 x_star) ^ 2 / (2 * t).



(*Bridge from 6.6 to 6.7*)
(**
Theorem 6.1 Suppose the function f : Rn → R is convex and differentiable, and that its gradient is
Lipschitz continuous with constant L > 0, i.e. we have that ‖∇f (x) − ∇f (y)‖2 ≤ L‖x − y‖2 for any x, y.
Then if we run gradient descent for k iterations with a fixed step size t ≤ 1/L, it will yield a solution f (k)
which satisfies
          f (x(k)) − f (x∗) ≤ ‖x(0) − x∗‖2
where f (x∗) is the optimal value. Intuitively, this means that gradient descent is guaranteed to converge
and that it converges with rate O(1/k).
*)
Theorem convergence : forall {n: nat} {k: nat} (t: R) (x_0: Vec n) (x_k : Vec n) (X: X_Points) (f : CostFunction n) (L : R),
  L > 0 ->
  lipschitz L f ->
  convex f ->
  differentiable f ->
  optimal x_star f ->
  f x_k - f x_star <= (L2norm (vector_subtract x_0 x_star)) ^ 2 / (2 * t * (INR k)).
Proof.
  intros.
  try  (rewrite (Rlt_le_trans_middle _ _ _ r1_lt_r2 r2_lt_r3)). (*Was hoping this would work*)
  (* Well what if we specify everiy argument? *)
  rewrite (Rlt_le_trans_middle _ _ _ (@r1_lt_r2 n k t x_0 x_k x_star x_1st_to_kth f) (@r2_lt_r3 n k t x_0 x_k x_star x_1st_to_kth f)).
  apply (six_to_seven t x_0).
  rewrite (Rlt_le_trans_middle _ _ _ (@r1_lt_r2 n k t x_0 x_k x_star x_1st_to_kth f) (@r2_lt_r3 n k t x_0 x_k x_star x_1st_to_kth f)).



End Main.

