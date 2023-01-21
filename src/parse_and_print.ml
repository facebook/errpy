(*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

print_endline ("Running on OCaml version: " ^ Sys.ocaml_version)

let () =
  match Parser.parse Sys.argv.(1) with
  | Ok mod_ -> Printf.printf "Parser produced AST:\n%s\n" (Ast.show_mod_ mod_)
  | Error err -> Printf.eprintf "Parser error: %s\n" err
