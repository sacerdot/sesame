(** It implements a parser for terms written in ASCII art.

    The parser accepts the following grammar.

    {[
    Term ::= [EVar?Var] | [MVar>Value,Var] | [Value-Var] | Value
    Value ::= Var | \VarValue | !VarValue
    Var ::= MVar | EVar
    MVar ::= m1 | m2 | ...
    EVar ::= e1 | e2 | ...
    ]}

   All terms must follow the Barendregt's convention, i.e. all variable cannot be used both free and bound and cannot be bound twice.
*)

open Format
open TermGraphs

(** Raised when a parsing error is found *)
exception ParsingError of string

(** The type of lexers.
    - next reads the next character, if any
    - undo undoes the last next action
    - index returns the current position inside the input string
 *)
type lexer = < next : char option ; undo : unit ; index : int >

(** The parser status.
    - lexer is the lexer status
    - vars is an associative list that maps variable kind and name to variable nodes
      in the graph
    - vars_out_of_scope lists the variable that are now out of scope and therefore not usable
      because of the Barendregt's convention
    - last_var is the index of the used variable that has the highest index so far *)
type status = {
  lexer : lexer;
  mutable vars : ((me * int) * var) list;
  mutable vars_out_of_scope : var list;
  mutable last_var : int;
}

(** Builds a lexer from a string *)
let lexer_of_string : string -> lexer = function
  | s ->
      object
        val mutable i = 0
        val len = String.length s

        method next =
          if i < len then (
            let c = s.[i] in
            i <- i + 1;
            Some c)
          else None

        method undo = i <- max 0 (i - 1)
        method index = i
      end

(** Undoes the last lexer next action and raises a ParsingError exception *)
let fail status msg =
  status.lexer#undo;
  raise (ParsingError msg)

(** It parses an integer or returns None *)
let int : status -> int = function
  | status ->
      let rec aux acc =
        match status.lexer#next with
        | Some c when '0' <= c && c <= '9' ->
            if c = '0' && acc = None then
              fail status "Variable numbers cannot start with 0"
            else
              let acc = match acc with None -> 0 | Some acc -> 10 * acc in
              aux (Some (acc + int_of_string (String.make 1 c)))
        | oc -> (
            match acc with
            | Some n ->
                if oc != None then status.lexer#undo;
                n
            | None -> fail status "Not a number")
      in
      aux None

(** It parses a variable or returns None *)
let var : status -> var option = function
  | status ->
      let varname =
        match status.lexer#next with
        | Some 'm' -> Some (Mul, int status)
        | Some 'e' -> Some (Exp, int status)
        | _ ->
            status.lexer#undo;
            None
      in
      Option.map
        (fun ((kind, name) as varname) ->
          match List.assoc_opt varname status.vars with
          | Some v ->
              if List.memq v status.vars_out_of_scope then
                fail status "Barendregt's convention not respected"
              else v
          | None ->
              let rec var = { kind; name; copy = var; is = None } in
              status.vars <- (varname, var) :: status.vars;
              status.last_var <- max name status.last_var;
              var)
        varname

(** It parses a value or raises ParsingError *)
let rec value : status -> value = function
  | status -> (
      match var status with
      | Some var -> Var var
      | None -> (
          match status.lexer#next with
          | Some '!' -> Bang { bo = term status }
          | Some '\\' -> (
              let vars = status.vars in
              match var status with
              | None -> fail status "Variable expected after \\"
              | Some var ->
                  if List.exists (fun (_, varx) -> var == varx) vars then
                    fail status "Barendregt's convention not respected";
                  let bo = term status in
                  status.vars_out_of_scope <- var :: status.vars_out_of_scope;
                  Abs { var; bo })
          | _ -> fail status "Syntax error"))

(** It parses a term or raises ParsingError *)
and term : status -> term = function
  | status -> (
      match status.lexer#next with
      | Some '[' -> (
          let binder =
            let v = value status in
            match (status.lexer#next, v) with
            | Some '?', Var var1 when var1.kind = Exp -> EElim { var = var1 }
            | Some '?', _ ->
                fail status "Expected exponential variable before '?'"
            | Some '-', _ -> Cut { v; ptr = None }
            | Some '>', Var var1 when var1.kind = Mul -> (
                let v = value status in
                match status.lexer#next with
                | Some ',' -> MElim { var = var1; v }
                | _ -> fail status "',' expected after ..>..")
            | Some '>', _ ->
                fail status "Expected multiplicative variable before '>'"
            | _ -> fail status "Binder not recognized"
          in
          let vars = status.vars in
          match var status with
          | None -> fail status "Var expected after '-'"
          | Some var2 -> (
              if List.exists (fun (_, varx) -> var2 == varx) vars then
                fail status "Barendregt's convention not respected";
              match status.lexer#next with
              | Some ']' ->
                  assert (var2.is = None);
                  var2.is <- Some binder;
                  let t = term status in
                  status.vars_out_of_scope <- var2 :: status.vars_out_of_scope;
                  Bind { var = var2; t }
              | _ -> fail status "Missing ']'"))
      | _ ->
          status.lexer#undo;
          Val (value status))

(** Main entry point of the parser: given a string, it parses a term or returns None *)
let parse : string -> term option =
 fun s ->
  let status =
    {
      lexer = lexer_of_string s;
      vars = [];
      vars_out_of_scope = [];
      last_var = 0;
    }
  in
  try
    fprintf std_formatter "Input: %s@." s;
    let t = term status in
    Option.iter (fun _ -> fail status "Syntax error") status.lexer#next ;
    fprintf std_formatter "Parsed: %a@." (Pp.pr_term []) t;
    Reduction.reset ~last_var:status.last_var ();
    Some t
  with ParsingError err ->
    fprintf err_formatter "Error: %s in@." err;
    fprintf err_formatter "  %s@." s;
    fprintf err_formatter "  %s@." (String.make status.lexer#index ' ' ^ "^");
    None
