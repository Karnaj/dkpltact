open Extras
open Kernel
open Parsers

val dep_of_entry : Basic.mident list -> Entry.entry -> StrSet.t
(** [dep_of_entry mds e] compute the direct dependencies of [e] which
    are not part of [mds]. *)

val deps_of_md : ?transitive:bool -> Basic.mident -> Basic.MidentSet.t
(** [deps_of_md ?transitive md] returns the set of modules id on
    which [md] depends. If [?transitive] is set to [true], the
    transitive closure is computed. *)
