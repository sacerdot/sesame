(** It implements the SESAME machine reduction rules, the main reduction loop and the Garbage Collection
    functions.
    
    All functions in this module are O(1), unless stated otherwise.
*)

open Format
open TermGraphs

(** [reset] and [fresh] are used to generate fresh variable names (i.e. the
    pedixes used to distinguish the variables). Reset resets the internal
    counter by setting the index of the variable already used that has the
    largest index.  [fresh] increments the counter.   *)

let reset, fresh =
  let name = ref 0 in
  ( (fun ?(last_var = 0) () -> name := last_var),
    fun () ->
      incr name;
      !name )

(** Returns [true] if the value in input is exponential *)
let is_exp : value -> bool = function
  | Var v -> v.kind = Exp
  | Abs _ -> false
  | Bang _ -> true

(** Auxiliary function used during a [-o] step.
    [enter_bo bo ptr x t], where [bo] is
    an abstraction body [[...]...[...]v]
    pointed by [ptr], turns the graph pointed by
    [ptr] in place to [[...]...[...][v-x]t]
    The function takes O(n) time where n is the
    length of the context [[...]...[...]].  *)
let rec enter_bo : term -> ptr -> var -> term -> term =
 fun bo ptr var t ->
  match bo with
  | Val v ->
      var.is <- Some (Cut { v; ptr = Some ptr });
      let res = Bind { var; t } in
      assign ptr res;
      res
  | Bind { t = t'; _ } ->
      let _ = enter_bo t' (InsideBind bo) var t in
      bo

(** The following set of functions are used to copy in linear time
    a subgraph. They are called by the [alpha] function that is used
    in the [-o] step. Some of them take in input the optional pointer
    to the subgraph to be copied, in order to create the backpointers
    during the copy. *)

let rec copy_value : value -> value = function
  | Var var -> Var var.copy
  | Abs { var; bo } -> (
      let res = Abs { var = copy_var None var; bo (*dummy*) } in
      let bo = copy_term (Some (InsideAbs res)) bo in
      match res with
      | Abs r ->
          r.bo <- bo;
          res
      | _ -> assert false)
  | Bang { bo } -> (
      let res = Bang { bo (*dummy*) } in
      let bo = copy_term (Some (InsideBang res)) bo in
      match res with
      | Bang r ->
          r.bo <- bo;
          res
      | _ -> assert false)

and copy_term : ptr option -> term -> term =
 fun ptr t ->
  match t with
  | Val v -> Val (copy_value v)
  | Bind { var; t } -> (
      let res = Bind { var = copy_var ptr var; t (*dummy*) } in
      let t = copy_term (Some (InsideBind res)) t in
      match res with
      | Bind r ->
          r.t <- t;
          res
      | _ -> assert false)

and copy_var : ptr option -> var -> var =
 fun ptr ({ is; kind; _ } as r) ->
  let is =
    match (is, ptr) with
    | None, _ -> None
    | Some is, Some ptr -> Some (copy_bvar ptr is)
    | _, _ -> assert false
  in
  let rec copy = { is; kind; copy; name = fresh () } in
  r.copy <- copy;
  copy

and copy_bvar : ptr -> bvar -> bvar =
 fun ptr bvar ->
  match bvar with
  | Cut { v; _ } -> Cut { v = copy_value v; ptr = Some ptr }
  | MElim { var; v } -> MElim { var = var.copy; v = copy_value v }
  | EElim { var } -> EElim { var = var.copy }

(** [alpha bo ptr x t]
    implements at once alpha-conversion, i.e. subgraph copy, and
    subgraph alteration as needed to implement the -o rule.
    [bo] must be a term [...]...[...]v that is the context of an exponential box,
    and [ptr] a pointer to it. The function builds a renaming/copy
    [[...]'...[...]'v'] of [[...]...[...]v] and it returns
    [[...]'...[...]'[v'-x]t]. The function takes linear time in the size of
    [[...]...[...]v] *)
let rec alpha : term -> ptr -> var -> term -> term =
 fun bo ptr var t ->
  match bo with
  | Val v ->
      let v = copy_value v in
      var.is <- Some (Cut { v; ptr = Some ptr });
      Bind { var; t }
  | Bind { var = x; t = t' } -> (
      let res = Bind { var = copy_var (Some ptr) x; t = t' (* dummy *) } in
      let t' = alpha t' (InsideBind res) var t in
      match res with
      | Bind r ->
          r.t <- t';
          res
      | _ -> assert false)

(** [drop_multiplicative_cut ptr p] (drops) a multiplicative cut, i.e. changes
    the subgraph [[v-m]t] pointed by [ptr] into [t].
    The function also maps the additional pointer [p], that could point to [t]
    inside [[v-m]t],
    to reflect the cancellation of the cut.
   - the first pointer must point to a [Bind] binding a multiplicative
     cut to be dropped
   - the return pointer is meant to be identical to the second pointer;
     however, if the second pointer was pointing inside the [Bind]
     pointed by the first pointer, than the return pointer is updated
     to be the first pointer *)
let drop_multiplicative_cut : ptr -> ptr -> ptr =
 fun ptr p ->
  match deref ptr with
  | Val _ -> assert false
  | Bind { t; _ } as tt ->
      (*fprintf err_formatter "Dropping: %a => %a@." (Pp.pr_ptr []) ptr (Pp.pr_term []) tt;*)
      assign ptr t;
      (match t with
      | Bind { var = { is = Some (Cut r); _ }; _ } -> r.ptr <- Some ptr
      | _ -> ());
      if match p with InsideBind b -> b == tt | _ -> false then ptr else p


(** Clash is raised at run time by the SESAME when there is a clash during
    reduction (e.g. a multiplicative value is found when an exponential value
    was expected) *)
exception Clash

(** Implements a single SESAME machine step by acting on the first job of the pool
    in input. It modifies in place the term graph and it returns the new pool and
    the name of the reduction rule used (e.g. "axm₂").
    
    The computational cost of each step is either constant or linear in the size of
    unevaluted copies of values that occur in the initial term.  *)
let step : pool -> string * pool = function
  | [] -> assert false
  | p :: pool -> (
      match deref p with
      | Bind { var = { is = Some (Cut r); _ }; _ } as bind ->
          (* sea1 *)
          r.ptr <- Some p;
          ("sea₁", InsideBind bind :: pool)
      | Bind { var = { is = Some (MElim { var = { is = None | Some (MElim _ | EElim _); kind; _ }; _; } as bvar); _; }; _; } as bind ->
          (* sea2 *)
          if kind = Exp then raise Clash;
          ("sea₂", InsideMElim bvar :: InsideBind bind :: pool)
      | Bind { var = { is = Some (EElim { var = { is = None | Some (MElim _ | EElim _); kind; _ }; _; }); _; }; _; } as bind ->
          (* sea3 *)
          if kind = Mul then raise Clash;
          ("sea₃", InsideBind bind :: pool)
      | Val (Abs _ as v) ->
          (* sea4 *)
          ("sea₄", InsideAbs v :: pool)
      | Val (Bang _ as v) ->
          (* sea5 *)
          ("sea₅", InsideBang v :: pool)
      | Val (Var { is = None | Some (MElim _ | EElim _); _ }) ->
          (* sea6 *)
          ("sea₆", pool)
      | Bind { var = { is = Some (MElim ({ var = { is = Some (Cut { v = Var var; ptr = Some ptr }); kind; _; }; _; } as r)); _; }; _; } ->
          (* axm2 *)
          if kind = Exp || var.kind = Exp then raise Clash;
          r.var <- var;
          let p = drop_multiplicative_cut ptr p in
          ("axm₂", p :: pool)
      | Bind { var = { is = Some (MElim { var = { is = Some (Cut { v = Abs { var = absvar; bo }; ptr = Some ptr; }); kind; _; }; v; }); _; } as var; t; } ->
          (* -o *)
          if kind = Exp then raise Clash;
          absvar.is <- Some (Cut { v; ptr = Some p });
          let res = Bind { var = absvar; t = Val (Var var) (* dummy *) } in
          let bo' = enter_bo bo (InsideBind res) var t in
          (match res with Bind r -> r.t <- bo' | _ -> assert false);
          assign p res;
          let p = drop_multiplicative_cut ptr p in
          ("-o  ", p :: pool)
      | Bind { var = { is = Some (EElim ({ var = { is = Some (Cut { v = Var var; _ }); kind; _ }; _; } as r)); _; }; _; } ->
          (* axe2 *)
          if kind = Mul || var.kind = Mul then raise Clash;
          r.var <- var;
          ("axe₂", p :: pool)
      | Bind { var = { is = Some (EElim { var = { is = Some (Cut { v = Bang { bo }; _ }); kind; _ }; _; }); _; } as x; t; } ->
          (* ! *)
          let res = alpha bo p x t in
          if kind = Mul then raise Clash;
          assign p res;
          ("!   ", p :: pool)
      | Val (Var { is = Some (Cut { v; ptr = Some ptr }); kind = Mul; _ }) ->
          (* axm1 *)
          if is_exp v then raise Clash;
          assign p (Val v);
          let p = drop_multiplicative_cut ptr p in
          ("axm₁", p :: pool)
      | Val (Var { is = Some (Cut { v; _ }); kind = Exp; _ }) ->
          (* axe1 *)
          if not (is_exp v) then raise Clash;
          assign p (Val v);
          ("axe₁", p :: pool)
      | Bind { var = { is = Some (MElim { var = { is = Some (Cut { v = Bang _; _ }); _ }; _ }); _; }; _; }
      | Bind { var = { is = Some (EElim { var = { is = Some (Cut { v = Abs _; _ }); _ }; _ }); _; }; _; } ->
          (* clash *)
          raise Clash
      | Val (Var { is = Some (Cut { ptr = None; _ }); _ })
      | Bind { var = { is = None; _ }; _ }
      | Bind { var = { is = Some (MElim { var = { is = Some (Cut { ptr = None; _ }); _ }; _ }); _; }; _; } ->
          (* impossible cases due to implementation invariants *)
          assert false)

(** Main SESAME loop: it repeats single steps until the empty pool is reached.
    It takes in input a pretty printing function to print the new machine state
    after each step. The pretty printing function takes in input the name of the
    rule used and the new pool. *)
let rec steps : pp:(string -> pool -> unit) -> pool -> unit =
 fun ~pp pool ->
  let stepname, pool = step pool in
  pp stepname pool;
  if pool <> [] then steps ~pp pool

(** The next two functions implement garbage collection over normal forms by
    rewriting the term graph in place. They run in time linear in the size of
    the input. [gc_term] also takes in input the pointer to the term to be
    garbage collected. *)

let rec gc_value : value -> unit = function
  | Var _ -> ()
  | Abs { bo; _ } as t -> gc_term (InsideAbs t) bo
  | Bang { bo } as t -> gc_term (InsideBang t) bo

and gc_term : ptr -> term -> unit =
 fun ptr t' ->
  match t' with
  | Val v -> gc_value v
  | Bind { var = { is = Some (Cut _); _ }; t } ->
      assign ptr t;
      gc_term ptr t
  | Bind { var = { is = Some (MElim { v; _ }); _ }; t } ->
      gc_value v;
      gc_term (InsideBind t') t
  | Bind { t; _ } -> gc_term (InsideBind t') t

(** Entry point for term evaluation. It takes in input a term, it builds
    the initial SESAME state, it calls the main SESAME loop, followed by
    garbage collection. The final garbage free normal form is returned. *)
let eval : term -> term = function
  | t ->
      let r = ref t in
      let pool = [ Initial r ] in
      let pp name pool =
        fprintf std_formatter "->@<4>%s %a@." name (Pp.pr_term pool) !r
      in
      fprintf std_formatter "       %a@." (Pp.pr_term pool) !r;
      (match steps ~pp pool with
      | () ->
          gc_term (Initial r) !r;
          pp "*GC " []
      | exception Clash -> pp "CLASH" []);
      !r
