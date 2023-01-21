(*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open OUnit2

(*
  Simple tests to ensure we can invoke ERRPY via the FFI interface from OCaml
  and marshall the output ast to an OCaml datastructure and handle comments
  correctly
*)


let test_parser_ast input_code expected_ast =
  match Parser.parse input_code with
  | Ok mod_ -> assert_equal expected_ast mod_ ~printer:( Ast.show_mod_  )
  | Error err -> assert_failure err


let expected_output_simple = Ast.Module {
  body =
  [{ Ast.desc =
     Ast.Assign {
       targets =
       [{ Ast.desc = Ast.Name {id = "a"; ctx = Ast.Store}; lineno = 1;
          col_offset = 0; end_lineno = (Some 1); end_col_offset = (Some 1) }
         ];
       value =
       { Ast.desc =
         Ast.Constant {value = (Some (Ast.Num (Ast.Int 8))); kind = None};
         lineno = 1; col_offset = 2; end_lineno = (Some 1);
         end_col_offset = (Some 3) };
       type_comment = None};
     lineno = 1; col_offset = 0; end_lineno = (Some 1);
     end_col_offset = (Some 3) }
    ];
  type_ignores = []}

let () = test_parser_ast "a=8" expected_output_simple

let expected_output_comments = Ast.Module {
  body =
  [{ Ast.desc =
     Ast.FunctionDef {name = "foo";
       args =
       { Ast.posonlyargs = [];
         args =
         [{ Ast.arg = "a"; annotation = None; type_comment = None;
            lineno = 2; col_offset = 4; end_lineno = (Some 2);
            end_col_offset = (Some 5) };
           { Ast.arg = "skip_loads"; annotation = None; type_comment = None;
             lineno = 4; col_offset = 4; end_lineno = (Some 4);
             end_col_offset = (Some 14) }
           ];
         vararg = None; kwonlyargs = []; kw_defaults = []; kwarg = None;
         defaults =
         [{ Ast.desc =
            Ast.Constant {value = (Some (Ast.Num (Ast.Int 34))); kind = None};
            lineno = 2; col_offset = 6; end_lineno = (Some 2);
            end_col_offset = (Some 8) };
           { Ast.desc =
             Ast.Constant {value = (Some (Ast.Bool true)); kind = None};
             lineno = 4; col_offset = 15; end_lineno = (Some 4);
             end_col_offset = (Some 19) }
           ]
         };
       body =
       [{ Ast.desc = Ast.Pass; lineno = 6; col_offset = 4;
          end_lineno = (Some 6); end_col_offset = (Some 8) }
         ];
       decorator_list = []; returns = None; type_comment = None};
     lineno = 1; col_offset = 0; end_lineno = (Some 6);
     end_col_offset = (Some 8) }
    ];
  type_ignores = []}

let () = test_parser_ast "def foo(
    a=34,
    # a comment here
    skip_loads=True,
):
    pass" expected_output_comments
