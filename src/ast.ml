type name = string * string
type variable = string

type element =
  | ElementCst of variable
  | GlobalElementCst of name
  | FunctionCall of name * element list

type proposition =
  | True
  | False
  | PropositionCst of variable
  | GlobalProposition of name
    (* If someone declare an axiom (for instance I: True) and want to prove True using I... *)
  | Forall of predicate
  | Exists of predicate
  | Implication of proposition * proposition
  | Conjonction of proposition * proposition
  | Disjonction of proposition * proposition
  | Negation of proposition
  | Equality of name * element * element
  | NotEquality of name * element * element
  | PredicateCall of name * element list

and predicate = name * variable * proposition (*x: set, (P x) = (set, x, P)*)

type rule =
  (* Some rules keep the hypothesis names avoiding the generation of fresh names. *)
  | T
  | FalseElim of proof
  | Assumption of variable
  | GlobalAssumption of name (* To distinguish theorem and context hypothesis *)
  | AndIntro of proposition * proposition * proof * proof
  | AndInd of
      variable
      * proposition
      * variable
      * proposition
      * proof
      * proposition
      * proof
  | AndIndRight of
      proposition * variable * proposition * proof * proposition * proof
  | AndIndLeft of
      variable * proposition * proposition * proof * proposition * proof
  | AndElimRight of proposition * proposition * proof
  | AndElimLeft of proposition * proposition * proof
  | OrIntroL of proposition * proposition * proof
  | OrIntroR of proposition * proposition * proof
  | OrInd of
      proposition
      * proposition
      * proposition
      * variable
      * proof
      * variable
      * proof
      * proof
  | ExIntro of predicate * element * proof
  | ExInd of predicate * proposition * proof * variable * variable * proof
  | ForallIntro of predicate * proof
  | ForallElim of predicate * proof * element
  | ImplIntro of variable * proposition * proof
  | ImplElim of variable * proposition * proof * proof
    (* (H, A, Pimp, PA) Show A => B as H, and show A.*)
  | Cut of proposition * proof * variable * proof
  | NNPP of proposition * proof
  | EqElim of predicate * element * element * proof * proof
  | EqElimR of predicate * element * element * proof * proof
  | EqSym of name * element * element * proof
  | EqRefl of name * element
  | EqTrans of name * element * element * element * proof * proof
  | Apply of variable * term list
    (* Use another theorem, replace it by ImplElim and ForallElim. *)
  | ApplyTheorem of name * term list

and proof = rule (* proposition * rule *)
and term = TElement of element | TProof of proof
(* | Proposition of proposition *)

type declaration_old =
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

(*
type _type = 
  | Set
  | SetElement of name
  | Predicate of name list
  | Function of name list * name
  | Proposition of proposition

type declaration = name * _type * term option
type context = (name * _type) list *)

type _entry =
  | SetEntry
  | PredicateEntry of name list
  | FunctionEntry of name list * name
  | TheoremEntry of proposition
  | ElementEntry of name

type context_element =
  | SetC
  | HypothesisC of proposition
  | ElementC of name
  | FunctionC of name list * name
  | PredicateC of name list

type global_context = name * context_element list
type local_context = variable * context_element list
