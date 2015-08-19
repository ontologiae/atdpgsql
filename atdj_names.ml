(* Names *)

open Atdj_env

let to_camel_case s =
  let res    = String.copy s in
  let offset = ref 0 in
  let upper  = ref true in
  let f = function
    | '_' ->
        upper := true;
    | ('0'|'1'|'2'|'3'|'4'|'5'|'6'|'7'|'8'|'9') as x ->
        upper := true;
        res.[!offset] <- x;
        incr offset
    | _ as x ->
        if !upper then (
          res.[!offset] <- Char.uppercase x;
          upper := false
        ) else
          res.[!offset] <- x;
        incr offset in
  String.iter f s;
  String.sub res 0 !offset

(* Translate type names into idiomatic Java class names.  We special case
 * `string', `int' and `bool'  (see code).  For the remainder, we remove
 * underscores and capitalise any character that is immediately following
 * an underscore or digit.  We also capitalise the initial character
 * e.g. "foo_bar42baz" becomes "FooBar42Baz". *)
let to_class_name str =
  match str with
    | "string" -> "String"
    | "int"    -> "Integer"
    | "bool"   -> "Boolean"
    | "float"  -> "Double"
    | _ -> to_camel_case str

let pgsql_keywords = [
  "boolean";
  "byte";
  "case";
  "catch";
  "char";
  "class";
  "const";
  "continue";
  "default";
  "do";
  "double";
  "else";
  "enum";
  "extends";
  "final";
  "finally";
  "real";
  "for";
  "if";
  "int";
  "integer";
  "bigin";
  "package";
  "private";
  "protected";
  "public";
  "returning";
  "short";
  "super";
  "switch";
  "transient";
  "try";
  "when";
  "while";
]

let is_pgsql_keyword =
  let tbl = Hashtbl.create 200 in
  List.iter (fun k -> Hashtbl.add tbl k ()) pgsql_keywords;
  fun k -> Hashtbl.mem tbl k

(*
   Automatically append an underscore to a field name if it is a Java keyword.
   Use the alternative provided as <pgsql name ="..."> if available.

   ATD field                           Java name

   not_a_keyword                       not_a_keyword
   class                               class_
   class <pgsql name="class_name">      class_name
   not_a_keyword <pgsql name="class">   class

*)
let get_pgsql_field_name field_name annot =
  let field_name =
    if is_pgsql_keyword field_name then
      field_name ^ "_"
    else
      field_name
  in
  Atd_annot.get_field (fun s -> Some s) field_name ["pgsql"] "name" annot

let get_pgsql_variant_names field_name annot =
  let lower_field_name = String.lowercase field_name in
  let field_name =
    if is_pgsql_keyword lower_field_name then
      field_name ^ "_"
    else
      field_name
  in
  let field_name =
    Atd_annot.get_field (fun s -> Some s) field_name ["pgsql"] "name" annot
  in
  let func_name = to_camel_case field_name in
  let enum_name = String.uppercase field_name in
  let private_field_name = String.lowercase field_name in
  func_name, enum_name, private_field_name

let get_json_field_name field_name annot =
  Atd_annot.get_field (fun s -> Some s) field_name ["json"] "name" annot

let get_json_variant_name field_name annot =
  Atd_annot.get_field (fun s -> Some s) field_name ["json"] "name" annot
