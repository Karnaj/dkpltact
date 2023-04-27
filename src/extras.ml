(** Extensions to the standard library. *)

module StrSet = Set.Make (String)

(** Some handy Dedukti functions or aliases. *)
module DkTools = struct
  let is_static :
      Kernel.Signature.t -> Kernel.Basic.loc -> Kernel.Basic.name -> bool =
   fun sign l n ->
    Kernel.Signature.get_staticity sign l n = Kernel.Signature.Static
end

module Result = struct
  include Result

  module Monad = struct
    let ( let* ) = Result.bind
    let return = Result.ok
  end
end

type 'a printer = Format.formatter -> 'a -> unit
(** The type of printers of ['a]. *)
