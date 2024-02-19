(** It includes a number of examples of terms to be reduced, including examples
    from a family of terms that show that the number of exponential steps can be
    exponential in the number of multiplicative steps. *) 

open Format

(** Fresh and reset are used to generate fresh variable indexes and to reset
    the counter to 1. They are useful to generate examples algorithmically. *)

let fresh, reset =
  let i = ref 0 in
  ( (function
    | () ->
        incr i;
        !i),
    function () -> i := 0 )

(** The next set of six functions encode the examples that shows that the
    number of exponential steps can be exponential in the number of multiplicative
    steps. *)

(** [pi f k] returns [[f?_]...[f?_][f?e]e] where [k] derelictions are used *)
let rec pi f k =
  if k = 1 then
    let var = fresh () in
    sprintf "[e%d?e%d]e%d" f var var
  else if k > 1 then sprintf "[e%d?e%d]%s" f (fresh ()) (pi f (k - 1))
  else assert false

  (** [test_k_h k h] returns [[!pi f₁ k-f₂]pi f₂ h] that reduces to [pi f₁ (k*h)]
   using exponential steps only *)
let test_k_h k h =
  assert (k > 0 && h > 0);
  let f1 = fresh () in
  let f2 = fresh () in
  sprintf "[!%s-e%d]%s" (pi f1 k) f2 (pi f2 h)

(** [delta_n f n] returns [[!pi f₁ 2-f₂]...[!piSk f_(n-1) 2-fₙ]pi fₙ 2] that
    reduces to [pi f₁ 2ⁿ] in [Ω(2ⁿ)] exponential steps only *)
let rec delta_n f n =
  if n = 1 then pi f 2
  else if n > 1 then
    let var = fresh () in
    sprintf "[!%s-e%d]%s" (pi f 2) var (delta_n var (n - 1))
  else assert false

(** exploding n returns [[!!λm₁m₁-f₁]delta_n f₁ n] that reduces to the identity
    function in [Ω(2ⁿ)] exponential steps only *)
let exploding n =
  let var = fresh () in
  sprintf "[!!\\m1m1-e%d]%s" var (delta_n var n)

(** Tests a number of simple examples, followed by instances of the
    previous exploding families *)
let all () =
  let open REPL in
  fprintf std_formatter "Examples of term evaluation:@.@.";
  test "[m1-m2]m2";
  test "[m1-m2][m2-m3]m3";
  test "[m1-m2]!\\m3m2";
  test "[m1-m2]!\\e1m2";
  test "[\\m1m1-m2][m2>m3,m4][m3>m4,m5]m5";
  test "[\\m2m2-m3][m3>m1,m4]m4";
  test "[\\m4m4-m5][e2?e7][m5>m3,m6][e7?e8]\\e1m6";
  test "[!m1-e2][e2-e3][e3?m4]!m4";
  test "[!m1-e2][e2-e3]e3";
  test "[m2-m3][m3>m1,m4]m4";
  test "[!m2-e1][e1?e2]e2";
  test "[!\\m1m1-e1][e1?m2][e1?m3][m2>m3,m4]m4";
  test "[!\\m1[m1-m2]m2-e3][e3?m4][e3?m5][m4>m5,m6]m6";
  test "[\\m1m1-m2][\\m3m3-m4][m2>m4,m5]m5";
  test "[m1-m2][![!m2-e1]e1-e2][e2?e3]e3";
  test "[m1>m1,m2]m2";
  test (test_k_h 3 4); reset ();
  test (delta_n (fresh ()) 3); reset ();
  test (exploding 3); reset ()
