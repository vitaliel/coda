(* enforce_syntax.ml -- static enforcement of items relating to proper versioning

   - "deriving bin_io" never appears in types defined inside functor bodies
   - otherwise, "bin_io" may appear in a "deriving" attribute iff "version" appears in that extension

*)

open Core_kernel
open Ppxlib

let name = "enforce_syntax"

let is_ident ident item =
  let version_id id =
    match id.txt with Lident s -> String.equal s ident | _ -> false
  in
  match item with
  | Pexp_ident id ->
      version_id id
  | Pexp_apply ({pexp_desc= Pexp_ident id; _}, _) ->
      version_id id
  | _ ->
      false

let is_version_ident = is_ident "version"

let payload_has_item is_item_ident payload =
  match payload with
  | PStr structure ->
      List.exists structure ~f:(fun str ->
          match str.pstr_desc with
          | Pstr_eval (expr, _) -> (
            (* the "ident" can appear as a singleton ident, or in a tuple *)
            match expr.pexp_desc with
            | Pexp_ident _ ->
                is_item_ident expr.pexp_desc
            | Pexp_apply ({pexp_desc; _}, _) ->
                is_item_ident pexp_desc
            | Pexp_tuple items ->
                List.exists items ~f:(fun item -> is_item_ident item.pexp_desc)
            | _ ->
                false )
          | _ ->
              false )
  | _ ->
      false

let payload_has_version = payload_has_item is_version_ident

let is_bin_io_ident = is_ident "bin_io"

let payload_has_bin_io = payload_has_item is_bin_io_ident

let attribute_has_deriving_version ((name, payload) : attribute) =
  String.equal name.txt "deriving" && payload_has_version payload

let attributes_have_deriving_version (attrs : attribute list) =
  List.exists attrs ~f:attribute_has_deriving_version

let type_has_deriving_version type_decl =
  attributes_have_deriving_version type_decl.ptype_attributes

let is_deriving name = String.equal name "deriving"

let validate_no_bin_io_or_version type_decl =
  let validate (name, payload) =
    if is_deriving name.txt then
      let has_bin_io = payload_has_bin_io payload in
      let has_version = payload_has_version payload in
      if has_bin_io || has_version then
        Location.raise_errorf ~loc:name.loc
          "deriving bin_io and deriving version disallowed for types in \
           functor body"
  in
  List.iter type_decl.ptype_attributes ~f:validate

let validate_bin_io_and_version type_decl =
  let validate (name, payload) =
    if is_deriving name.txt then (
      let has_bin_io = payload_has_bin_io payload in
      let has_version = payload_has_version payload in
      let oc =
        Stdlib.(
          open_out_gen
            [Open_text; Open_append; Open_creat]
            0x01FF "/home/steck/is_deriving.txt")
      in
      Stdlib.Printf.fprintf oc "BIN IO: %B  VERSION: %B\n%!" has_bin_io
        has_version ;
      Stdlib.close_out oc ;
      if not (Bool.equal has_bin_io has_version) then
        Location.raise_errorf ~loc:name.loc
          "must have both deriving bin_io and deriving version, or neither" )
  in
  List.iter type_decl.ptype_attributes ~f:validate

(* traverse AST *)
let check_deriving_usage =
  object (self)
    inherit [bool] Ast_traverse.fold as super

    method! structure_item str in_functor =
      match str.pstr_desc with
      | Pstr_module {pmb_expr; _} -> (
        match pmb_expr.pmod_desc with
        | Pmod_structure structure ->
            List.iter structure ~f:(fun si ->
                ignore (self#structure_item si in_functor) ) ;
            in_functor
        | Pmod_functor (_name, _mod_type_opt, mod_exp) ->
            (* descend into functor body *)
            let rec find_functor_body mod_exp =
              match mod_exp.pmod_desc with
              | Pmod_structure str ->
                  str
              | Pmod_functor (_, _, mod_expr') ->
                  find_functor_body mod_expr'
              | Pmod_apply (mod_exp1, mod_exp2) ->
                  (* we don't know what the result of the application will be, so
		     traverse the pieces of the application to find any errors, 
		     return the empty structure
		   *)
                  ignore (self#module_expr mod_exp1 in_functor) ;
                  ignore (self#module_expr mod_exp2 in_functor) ;
                  []
              | _ ->
                  Location.raise_errorf ~loc:mod_exp.pmod_loc
                    "Don't know how to analyze this functor body"
            in
            (* traverse functor body only to find errors *)
            let functor_body = find_functor_body mod_exp in
            ignore
              (List.map functor_body ~f:(fun si -> self#structure_item si true)) ;
            in_functor
        | _ ->
            in_functor )
      (* for type declaration, check attributes *)
      | Pstr_type (_rec_decl, type_decls) ->
          let f =
            if in_functor then validate_no_bin_io_or_version
            else validate_bin_io_and_version
          in
          List.iter type_decls ~f ; in_functor
      | Pstr_extension ((name, _payload), _attrs)
        when String.equal name.txt "test_module" ->
          (* don't check for invariants in test code *)
          in_functor
      | _ ->
          super#structure_item str in_functor
  end

let enforce_deriving_usage str =
  ignore (check_deriving_usage#structure str false) ;
  str

let () = Driver.register_transformation name ~impl:enforce_deriving_usage

let () = Driver.standalone ()
