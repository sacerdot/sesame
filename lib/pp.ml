(** Functions to pretty print the terms and other data structures used by the SESAME machine. *)

open Format
open TermGraphs

(** Finds the index of the first element of a list that satisfies a certain predicate *)
let find_index p l =
  let rec aux n = function
    | [] -> None
    | hd :: tl -> if p hd then Some n else aux (n + 1) tl
  in
  aux 1 l

(** Encodes a positive integer as a string made of UNICODE pedixes (e.g. "₃₁"). *)
let rec pr_subscript = function
  | 0 -> "₀"
  | 1 -> "₁"
  | 2 -> "₂"
  | 3 -> "₃"
  | 4 -> "₄"
  | 5 -> "₅"
  | 6 -> "₆"
  | 7 -> "₇"
  | 8 -> "₈"
  | 9 -> "₉"
  | n -> pr_subscript (n / 10) ^ pr_subscript (n mod 10)

(** The following set of functions are formatters to be used according to the
    Format module of the OCaml standard lib. They are used to print the various
    kind of nodes that constitute a term graph, as well as pointers. They take
    in input a pool in order to mark in the output the unevaluated subterms
    using angle brackets and a subscript which is the position of the job in
    the pool (e.g. [!<m₁>₂] is a value whose approximant is [!<>₂] and such that
    the job number 2 required to reduce [m₁]; equivalently it is a term graph
    whose pool contains in second position a pointer to the occurrence of [m₁]
    inside the value) *)

let rec pr_value (pool:pool) ppf v =
  let in_pool =
    find_index
      (function
        | InsideMElim _ as ptr -> (
            match deref ptr with Val v' -> v' == v | _ -> false)
        | _ -> false)
      pool
  in
  Option.iter (fun _ -> fprintf ppf "@[<") in_pool;
  (match v with
  | Var var -> fprintf ppf "%a" pr_var_occ var
  | Abs { var; bo } ->
      fprintf ppf "@[λ%a%a@]" pr_var_occ var (pr_term pool) bo
  | Bang { bo } -> fprintf ppf "@[!%a@]" (pr_term pool) bo);
  Option.iter (fun n -> fprintf ppf ">%s@]" (pr_subscript n)) in_pool

and pr_var pool ppf ({ is; _ } as var) =
  fprintf ppf "%a" (pr_bvar pool var)
    (match is with None -> assert false | Some is -> is)

and pr_var_occ ppf { kind; name; _ } =
  fprintf ppf "%s%s" (if kind = Mul then "m" else "e") (pr_subscript name)

and pr_bvar pool x ppf = function
  | Cut { v; ptr = _ } ->
      fprintf ppf "@[[%a→%a]@]" (pr_value pool) v pr_var_occ x
  | MElim { var; v } ->
      fprintf ppf "@[[%a⊳%a,%a]@]" pr_var_occ var (pr_value pool) v pr_var_occ
        x
  | EElim { var } -> fprintf ppf "@[[%a?%a]@]" pr_var_occ var pr_var_occ x

and pr_term pool ppf t =
  let in_pool = find_index (fun ptr -> deref ptr == t) pool in
  Option.iter (fun _ -> fprintf ppf "@[<") in_pool;
  (match t with
  | Val v -> fprintf ppf "%a" (pr_value pool) v
  | Bind { var; t } ->
      fprintf ppf "@[<hov 1>%a@,%a@]" (pr_var pool) var (pr_term pool) t);
  Option.iter (fun n -> fprintf ppf ">%s@]" (pr_subscript n)) in_pool

let pr_ptr pool ppf = function
  | Initial topterm -> fprintf ppf "INITIAL: %a" (pr_term pool) !topterm
  | InsideBang v -> fprintf ppf "INSIDEBANG: %a" (pr_value pool) v
  | InsideAbs v -> fprintf ppf "INSIDEABS: %a" (pr_value pool) v
  | InsideBind t -> fprintf ppf "INSIDEBIND: %a" (pr_term pool) t
  | InsideMElim bv ->
      let rec dummy = { is = None; kind = Mul; copy = dummy; name = 999 } in
      fprintf ppf "INSIDEMELim: %a" (pr_bvar pool dummy) bv
