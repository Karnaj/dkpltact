type name = string * string
type variable = string 

type element = 
  | ElementCst of name
  | FunctionCall of name * element list

type proposition =
  | True
  | False
  | PropositionCst of variable
  | GlobalProposition of name (* If someone declare an axiom (for instance I: True) and want to prove True using I... *)
  | Forall of predicate
  | Exists of predicate
  | Implication of proposition * proposition
  | Conjonction of proposition * proposition
  | Disjonction of proposition * proposition
  | Negation of proposition
  | Equality of name * element * element
  | PredicateCall of name * element list

and predicate = name * variable * proposition (*x: set, (P x) = (set, x, P)*)

type rule =  (* Some rules keep the hypothesis names avoiding the generation of fresh names. *)
  | T
  | FalseElim of proposition
  | Assumption of variable
  | GlobalAssumption of name (* To distinguish theorem and context hypothesis *)
  | AndIntro of proposition * proposition * proof * proof
  | AndElim of variable * proposition * variable * proposition * proof * proposition * proof
  | OrIntroL of proposition * proposition * proof
  | OrIntroR of proposition * proposition * proof
  | OrElim of variable * proposition * variable * proposition * proposition * variable * proof * variable * proof * proof 
  | ExIntro of predicate * element * proof 
  | ExElim of predicate * proposition * proof * variable * variable * proof
  | ForallIntro of predicate * proof
  | ForallElim of predicate * proof * element
  | ImplIntro of proposition * proof * proof 
  | ImplElim of variable * proposition * proof * proof (* (H, A, Pimp, PA) Show A => B as H, and show A.*)
  | Apply of name * term list (* Use another theorem, replace it by ImplElim and ForallElim. *)
  | Cut of proposition * proof * variable * proof
  | NNPP of proposition * proof
  | EqElim of predicate * element * element * proof * proof
  | EqElimR of predicate * element * element * proof * proof
  | EqSym of predicate * element * element * proof * proof
  | EqRefl of predicate * element * element * proof * proof 
  | EqTrans of predicate * element * element * element * proof * proof * proof   

and proof = rule (* proposition * rule *)

and term = 
  | Element of element 
  | Proof of proof
(*| Proposition of proposition *)

type declaration = 
  | SetDecl of string
  | ElementDecl of string * name
  | FunctionDecl of string * name list * name
  | PredicateDecl of string * name list
  | AxiomDecl of string * proposition
  | PredicateDef of string * (variable * name) list * proposition (* TODO *)
  | FunctionDef of string * (variable * name) list * name * element (* TODO *)
  | TheoremDef of string * proposition * proof



type entry =
  | Set
  | Element of name
  | PredicateSymbol of name list
  | Predicate of (variable * name) list * proposition
  | FunctionSymbol of name list * name
  | Function of (variable * name) list * name * element
  | Axiom of proposition
  | Theorem of proposition * proof 

type declarations = string * string * entry