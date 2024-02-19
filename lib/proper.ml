(** It implements the check that a given term is proper, i.e. all multiplicative
    variables occur linearly and no multiplicative variable occurs free in an
    exponential box *)

open Format
open TermGraphs

(** Raised when the term is detected to be non proper. *)
exception NotProper of string

(** The following auxiliary functions check if the input is proper
   and also return the multiset of free multiplicative variable
   occurrences used in the input. The exception [NotProper] is
   raised when the input is not proper. *)

let rec is_proper_value : value -> var list = function
  | Var var -> if var.kind = Mul then [ var ] else []
  | Abs { var; bo } as v ->
      let vars = is_proper_term bo in
      if var.kind = Mul then
        let eq, diff = List.partition (fun var' -> var == var') vars in
        if List.length eq != 1 then
          raise
            (NotProper
               (asprintf "Multiplicative variable %a not used linearly in %a"
                  Pp.pr_var_occ var (Pp.pr_value []) v))
        else diff
      else vars
  | Bang { bo } as v -> (
      match is_proper_term bo with
      | [] -> []
      | _ :: tl as vl ->
          raise
            (NotProper
               (asprintf
                  "Free occurrences of the multiplicative %s %a in the \
                   exponential box %a"
                  (if tl = [] then "variable" else "variables")
                  (pp_print_list
                     ~pp_sep:(fun ppf () -> fprintf ppf ",")
                     Pp.pr_var_occ)
                  vl (Pp.pr_value []) v)))

and is_proper_bvar : bvar -> var list = function
  | Cut { v; _ } -> is_proper_value v
  | MElim { var; v } ->
      if var.kind = Mul then var :: is_proper_value v else is_proper_value v
  | EElim { var } -> if var.kind = Mul then [ var ] else []

and is_proper_term : term -> var list = function
  | Val v -> is_proper_value v
  | Bind { var; t } as term -> (
      match var.is with
      | None -> assert false
      | Some is ->
          let vars = is_proper_term t in
          let vars =
            if var.kind = Mul then
              let eq, diff = List.partition (fun var' -> var == var') vars in
              if List.length eq != 1 then
                raise
                  (NotProper
                     (asprintf
                        "Multiplicative variable %a not used linearly in %a"
                        Pp.pr_var_occ var (Pp.pr_term []) term))
              else diff
            else vars
          in
          is_proper_bvar is @ vars)

(** Given an accumulator and a list, it returns its list of duplicates that are
    not already in the accumulator *)
let rec duplicates dups = function
  | [] -> dups
  | var :: vars ->
      if List.memq var vars && not (List.memq var dups) then
        duplicates (var :: dups) vars
      else duplicates dups vars

(** Main entry point of the module. It checks if a term is proper or not. *)
let is_proper : term -> bool =
 fun t ->
  try
    let vars = is_proper_term t in
    let dups = duplicates [] vars in
    match dups with
    | [] ->
        fprintf std_formatter "The term is proper.@.";
        true
    | _ :: _ ->
        raise
          (NotProper
             (asprintf
                "The following multiplicative variables occur free not \
                 linearly in the term: %a"
                (pp_print_list
                   ~pp_sep:(fun ppf () -> fprintf ppf ",")
                   Pp.pr_var_occ)
                dups))
  with NotProper msg ->
    fprintf err_formatter "Error: the term is not proper.@.";
    fprintf err_formatter "%s@." msg;
    false
