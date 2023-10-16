open Extras
open Kernel
open Parsers

val dep_of_entry : Basic.mident list -> Entry.entry -> StrSet.t
(** [dep_of_entry mds e] compute the direct dependencies of [e] which
    are not part of [mds]. *)