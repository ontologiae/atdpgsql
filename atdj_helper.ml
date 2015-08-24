(* Helper classes *)

open Printf
open Atdj_env

let output_atdj env =
  let out = Atdj_trans.open_sql env "Atdj" in
  fprintf out "";
  close_out out


let ml_create_model isSave req params structAff =
        let name = if isSave then "save" else "create" in
        Printf.sprintf
      "let quote s = \"'\"^s^\"'\"

       let %s request_service newline =
        let req  = Printf.sprintf \"%s\" %s in
        let lines = request_service req [] in
        let line  = L.hd lines in
        { %s }" name req params structAff;;  


let output_util env =
  let out = Atdj_trans.open_sql env "Util" in
  fprintf out "\
class Util {
  // Extract the tag of sum-typed value
  static String extractTag(Object value) throws JSONException {
    if (value instanceof String)
      return (String)value;
    else if (value instanceof JSONArray)
      return ((JSONArray)value).getString(0);
    else throw new JSONException(\"Cannot extract type\");
  }

  // Is an option value a none?
  static boolean isNone(Object value) throws JSONException {
    return (value instanceof String) && (((String)value).equals(\"None\"));
  }

  // Is an option value a Some?
  static boolean isSome(Object value) throws JSONException {
    return (value instanceof JSONArray)
      && ((JSONArray)value).getString(0).equals(\"Some\");
  }

";
  close_out out

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
