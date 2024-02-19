(** Data types used to represent terms and states of the SESAME machine. 

    A term graph is essentially a DAG that captures the syntactic structure of
    a term, augmented with a few backpointers from cut variables to the terms
    that surround the cuts. These backpointers are used to consume the cut
    during multiplicative steps.
    
    In a term graph all occurrences of a variable are shared, i.e. they are all
    pointers to the same node in memory. If the variable is bound by a cut or
    a subtraction or a dereliction, then its node points to the cut value or to
    the arguments of the subtraction/dereliction. For example, if [x] is
    bound by the cut [[v-x]], then the node for [x] points to [v] and it
    remembers that it is a cut. A term which is not a value (e.g. [[v-x]t])
    is represented by a node that points both to the subterm [t] and to the
    bound variable [x] which, in turn, will point to the subterms of the binder
    ([v] in this case).


    The pool of the machine is a list of jobs where each job is implemented
    simply as a pointer inside the term graph that points to the term that
    needs to be reduced. For example, a machine state [!λm<>ₐ, <t>ₐ::ϵ]
    of the paper is implemented as the pair made by the term graph for [!λmt]
    and a singleton list made of a pointer to the root of the subgraph that
    encodes [t].  *)

(** Used to differentiate between multiplicative and exponential variables *)
type me = Mul | Exp

(** A value is either a variable occurrence, an abstraction or an exponential box *)
type value =
  | Var of var
  | Abs of { var : var; mutable bo : term }
  | Bang of { mutable bo : term }

(** A [var] is the unique node in memory associated to a variable. Variable
    occurrences and binders point to this node.
   
    The is field is [None] for free variable and variables bound by
    abstractions.  Otherwise it points the node holding the information about
    the binder.

    The kind field distinguish multiplicative from exponential variables.

    The name field is the positive integer used to differentiate variables.
    A variable is identified both by its kind and name so that [m₁]
    (a variable of kind [Mult] and name [1]) is different from [e₁]
    (a variable of kind [Exp] and name [1]).

    The copy field is used during alpha-renaming (i.e. subgraph copying) to
    preserve sharing. When a variable is copied to a new one, it points to
    the new one. Variables that have never been copied point to themselves. *)
and var = {
  mutable is : bvar option;
  kind : me;
  name : int;
  mutable copy : var;
}

(** A [bvar] represents a cut or a subtraction or a dereliction, that are all
    binders. The node points to the variables or values used in the binder.

    Cuts also hold an optional pointer to the [Bind] term that binds the
    variable. The pointer is used during reduction to consume multiplicative
    cuts. To simplify the parser, it can be [None] in initial terms, but it
    must be set in approximants.  *)
and bvar =
  (* ptr must point to the surrounding Bind; it can be None in initial terms *)
  | Cut of { v : value; mutable ptr : ptr option }
  | MElim of { mutable var : var; mutable v : value }
  | EElim of { mutable var : var }

(** A [term] is either a (node pointing to a) value or a binder pointing to
    the bound variable and the remaining term.  *)
and term =
  | Val of value
  | Bind of { var : var; mutable t : term } (* var must have is != None *)

(** [topterm] is the root of the term graph. Initially it represents the
    term to be reduced.  When the machine stops, it contains the normal form. *)
and topterm = term ref

(** In OCaml it is not possible to take the address of a record field to
    mutate it. One needs to have a reference to the whole record instead.
    The [ptr] datatype represents a pointer inside the term graph by listing
    all the constructors (i.e. labelled records) that have fields that are
    subterms different from variables (i.e. all the positions where an hole
    can occur in an approximant). *)
and ptr =
  | Initial of topterm (** points to the [topterm] *)
  | InsideBang of value (** [value] must be a [Bang] *)
  | InsideAbs of value (** [value] must be an [Abs] *)
  | InsideBind of term (** [value] must be a [Bind] *)
  | InsideMElim of bvar (** [bvar] must be an [MElim] *)

(** A pool is a list of pointers [ptr] to the maximal subterms that are
    still to be evaluated.  Equivalently, it is a list of pointers to the
    subterms that have been replaced by holes in an approximant. *)
type pool = ptr list

(** [deref ptr] returns the subterm pointed by [ptr] *)
let deref : ptr -> term = function
  | Initial r -> !r
  | InsideBang (Bang { bo }) -> bo
  | InsideAbs (Abs { bo; _ }) -> bo
  | InsideBind (Bind { t; _ }) -> t
  | InsideMElim (MElim { v; _ }) -> Val v
  | InsideBang (Var _ | Abs _)
  | InsideAbs (Var _ | Bang _)
  | InsideMElim (Cut _ | EElim _)
  | InsideBind (Val _) ->
      assert false

(** [assign ptr t] mutates the term graph in place by assigning [t] to the
    pointer [ptr] *)
let assign : ptr -> term -> unit =
 fun p t ->
  match p with
  | Initial r -> r := t
  | InsideBang (Bang r) -> r.bo <- t
  | InsideAbs (Abs r) -> r.bo <- t
  | InsideBind (Bind r) -> r.t <- t
  | InsideMElim (MElim r) -> (
      match t with Val v -> r.v <- v | Bind _ -> assert false)
  | InsideBang (Var _ | Abs _)
  | InsideAbs (Var _ | Bang _)
  | InsideMElim (Cut _ | EElim _)
  | InsideBind (Val _) ->
      assert false
