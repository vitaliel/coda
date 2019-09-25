open Core_kernel

(* deriving version and bin_io both appear; OK outside functor body *)

module Stable = struct
  module V1 = struct
    module T = struct
      type t = int [@@deriving bin_io, version]
    end
  end
end
