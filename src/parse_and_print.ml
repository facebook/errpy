(*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

print_endline ("Running on OCaml version: " ^ Sys.ocaml_version)

let () =
  let print_recoverable_errors recoverable_errors =
    recoverable_errors |> List.map Ast.show_recoverableerrorwithlocation |> String.concat ", " |> Format.asprintf "[%s]"
  in
  match Parser.parse_module Sys.argv.(1) with
  | Ok(mod_, recoverable_errors)  -> Printf.printf "Parser produced AST:\n%s\nRecoverable Errors:\n%s\n" (Ast.show_mod_ mod_) (print_recoverable_errors recoverable_errors)
  | Error err -> Printf.eprintf "Parser error: %s\n" err
