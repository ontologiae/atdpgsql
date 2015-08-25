(* Helper classes *)

open Printf
open Atdj_env

let output_atdj env =
  let out = Atdj_trans.open_sql env "Atdj" in
  fprintf out "";
  close_out out


(*
let output_package_javadoc env (loc, annots) =
  let out = open_out (env.package_dir ^ "/" ^ "package.html") in
  output_string out "<body>\n";
  let from_doc_para acc para =
    List.fold_left
      (fun acc -> function
         | `Text text -> text :: acc
         | `Code _ -> failwith "Not yet implemented: code in javadoc comments"
      )
      acc
      para in
  let from_doc = function
    | `Text blocks ->
        List.fold_left
          (fun acc -> function
             | `Paragraph para -> from_doc_para acc para
             | `Pre _ ->
                 failwith "Not yet implemented: \
                           preformatted text in javadoc comments"
          )
          []
          blocks in
  (match Ag_doc.get_doc loc annots with
     | Some doc ->
         let str = String.concat "\n<p>\n" (List.rev (from_doc doc)) in
         output_string out str
     | _ -> ()
  );
  output_string out "\n</body>";
  close_out out
  *)
