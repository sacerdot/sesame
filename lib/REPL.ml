(** It implements a REPL loop: the user is asked to enter a term that is
    parsed, checked to be proper and evaluated, until the user quits the
    REPL loop. *)

open Format

(** Given a string s, it parses the string, checks that the parsed term
    is proper and then evaluates it, throwing away the computed normal
    form. *)
let test s =
  Option.iter
    (fun t -> if Proper.is_proper t then ignore (Reduction.eval t))
    (Parser.parse s);
  fprintf std_formatter "@.@.";
  Reduction.reset ()

(** Main loop of the REPL. *)
let main () =
  fprintf std_formatter "Input syntax of terms (in ASCII art):@.";
  fprintf std_formatter
    "  Term ::= [EVar?Var] | [MVar>Value,Var] | [Value-Var] | Value@.";
  fprintf std_formatter "  Value ::= Var | \\VarValue | !VarValue@.";
  fprintf std_formatter "  Var ::= MVar | EVar@.";
  fprintf std_formatter "  MVar ::= m1 | m2 | ...@.";
  fprintf std_formatter "  EVar ::= e1 | e2 | ...@.@.";
  fprintf std_formatter "All terms must follow the Barendregt's convention,@.";
  fprintf std_formatter
    "i.e. all variable cannot be used both free and bound and cannot be bound \
     twice.@.";
  try
    while true do
      fprintf std_formatter
        "@.Enter the next term to evaluate (Ctr-D to exit):@.";
      let s = read_line () in
      if s <> "" then test s
    done
  with End_of_file -> ()
