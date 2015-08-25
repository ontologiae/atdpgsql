open Printf
open Atdj_names
open Atdj_env
open Atdj_util


module L = BatList

module S = BatString

(* Calculate the JSON representation of an ATD type.
 *
 * Values of sum types t are encoded as either Strings or two-element
 * JSONArrays, depending upon the arity of the particular constructor.
 * A nullary constructor C is denoted by the String "C", whilst
 * an application of a unary constructor C to an ATD value v is denoted by the
 * JSONArray ["C", <v>], where <v> is the JSON representation of v.
 *
 * Option types other than in optional fields (e.g. '?foo: int option')
 * are not supported.
 *)
let json_of_atd env atd_ty =
  let atd_ty = norm_ty ~unwrap_option:true env atd_ty in
  match atd_ty with
    | `Sum    _ -> "" (* Either a String or a two element JSONArray *)
    | `Record _ -> "JSONObject"
    | `List   _ -> "[]"
    | `Name (_, (_, ty, _), _) ->
        (match ty with
           | "bool"   -> "Boolean"
           | "int"    -> "Bigint"
           | "float"  -> "Double precision"
           | "string" -> "Text"
           | _        -> assert false
        )
    | x -> type_not_supported x

(* Calculate the method name required to extract the JSON representation of an
 * ATD value from either a JSONObject or a JSONArray ("get", "opt",
 * "getInt", "optInt", ...)
 *)
let get env atd_ty opt =
  let atd_ty = norm_ty ~unwrap_option:true env atd_ty in
  let prefix = if opt then "opt" else "get" in
  let suffix =
    match atd_ty with
      | `Sum _ -> ""
      | _ -> String.capitalize (json_of_atd env atd_ty) in
  prefix ^ suffix

let extract_from_edgy_brackets s =
  Str.global_replace
    (Str.regexp "^[^<]*<\\|>[^>]*$") "" s
(*
extract_from_edgy_brackets "ab<cd<e>>f";;
- : string = "cd<e>"
*)

(* Assignment with translation.  Suppose that atd_ty is an ATD type, with
 * corresponding Java and (Javafied) JSON types pgsql_ty and json_ty. Then this
 * function assigns to a variable `dst' of type pgsql_ty from a variable `src' of
 * type `json_ty'.
 *)
let rec assign env opt_dst src pgsql_ty atd_ty indent =
  let atd_ty = norm_ty env atd_ty in
  match opt_dst with
  | None ->
      (match atd_ty with
       | `Sum _ ->
           sprintf "new %s(%s)" pgsql_ty src
       | `Record _ ->
           sprintf "new %s(%s)" pgsql_ty src
       | `Name (_, (_, ty, _), _) ->
           (match ty with
            | "bool" | "int" | "float" | "string" -> src
            | _  -> assert false
           )
       | x -> type_not_supported x
      )
  | Some dst ->
      (match atd_ty with
       | `Sum _ ->
           sprintf "%s%s = new %s(%s);\n" indent dst pgsql_ty src
       | `Record _ ->
           sprintf "%s%s = new %s(%s);\n" indent dst pgsql_ty src
       | `List (_, sub_ty, _) ->
           let pgsql_sub_ty = (*ahem*) extract_from_edgy_brackets pgsql_ty in
           let sub_expr = assign env None "_tmp" pgsql_sub_ty sub_ty "" in

           sprintf "%s%s = new %s();\n" indent dst pgsql_ty
           ^ sprintf "%sfor (int _i = 0; _i < %s.length(); ++_i) {\n" indent src

           ^ sprintf "%s  %s _tmp = %s.%s(_i);\n" indent
             (json_of_atd env sub_ty) src (get env sub_ty false)

           ^ sprintf "%s  %s.add(%s);\n" indent
             dst sub_expr
           ^ sprintf "%s}\n" indent

       | `Name (_, (_, ty, _), _) ->
           (match ty with
            | "bool" | "int" | "float" | "string" ->
                sprintf "%s%s = %s;\n" indent dst src
            | _  -> assert false
           )
       | x -> type_not_supported x
      )

(* Assign from an object field, with support for optional fields.  The are two
 * kinds of optional fields: `With_default (~) and `Optional (?).  For both
 * kinds, we return the following values if the field is absent:
 *
 *   bool   -> false
 *   int    -> 0
 *   float  -> 0.0
 *   string -> ""
 *   list   -> []
 *   option -> None
 *
 * Optional fields of record and sum types are not supported. They are
 * treated as required fields.
 *
 * Fields of the `Optional kind extend this behaviour by automatically lifting
 * values of type t to option t by wrapping within a `Some'.
 * Hence `Optional may only be applied to fields of type option t.
 * Note that absent fields are still
 * assigned `None', as before.
 *
 * For `With_default fields, of types bool, int, float, string and list, we use
 * the org.json opt methods to extract the field.  These methods already return
 * the appropriate defaults if field is absent.  For option types, we manually
 * check for the field and manually create a default.  If the field is present,
 * then we wrap its values as necessary.
 *)
let assign_field env
    (`Field (loc, (atd_field_name, kind, annots), atd_ty)) pgsql_ty =
  let json_field_name = get_json_field_name atd_field_name annots in
  let field_name = get_pgsql_field_name atd_field_name annots in
  (* Check whether the field is optional *)
  let is_opt =
    match kind with
      | `Optional | `With_default -> true
      | `Required -> false in
  let src = sprintf "jo.%s(\"%s\")" (get env atd_ty is_opt) json_field_name in
  if not is_opt then
    assign env (Some field_name) src pgsql_ty atd_ty "    "
  else
    let mk_else = function
      | Some default ->
          sprintf "    } else {\n      %s = %s;\n    }\n"
            field_name default
      | None ->
          "    }\n"
    in
    let opt_set_default =
      match kind with
      | `With_default ->
          (match norm_ty ~unwrap_option:true env atd_ty with
           | `Name (_, (_, name, _), _) ->
               (match name with
                | "bool" -> mk_else (Some "false")
                | "int" -> mk_else (Some "0")
                | "float" -> mk_else (Some "0.0")
                | "string" -> mk_else (Some "\"\"")
                | _ -> mk_else None (* TODO: fail if no default is provided *)
               )
           | `List _ ->
               (* pgsql_ty is supposed to be of the form "ArrayList<...>" *)
               mk_else (Some (sprintf "new %s()" pgsql_ty))
           | _ ->
               mk_else None (* TODO: fail if no default is provided *)
          )
      | _ ->
          mk_else None
    in
    let atd_ty = norm_ty ~unwrap_option:true env atd_ty in
    sprintf "    if (jo.has(\"%s\")) {\n" json_field_name
    ^ assign env (Some field_name) src pgsql_ty atd_ty "      "
    ^ opt_set_default


(* Generate a toJsonBuffer command *)
let rec to_string env id atd_ty indent =
  let atd_ty = norm_ty env atd_ty in
  match atd_ty with
    | `List (_, atd_sub_ty, _) ->
          sprintf "%s_out.append(\"[\");\n" indent
        ^ sprintf "%sfor (int i = 0; i < %s.size(); ++i) {\n" indent id
        ^ to_string env (id ^ ".get(i)") atd_sub_ty (indent ^ "  ")
        ^ sprintf "%s  if (i < %s.size() - 1)\n" indent id
        ^ sprintf "%s    _out.append(\",\");\n" indent
        ^ sprintf "%s}\n" indent
        ^ sprintf "%s_out.append(\"]\");\n" indent
    | `Name (_, (_, "string", _), _) ->
        (* TODO Check that this is the correct behaviour *)
        sprintf
          "%sUtil.writeJsonString(_out, %s);\n"
          indent id
    | `Name _ ->
        sprintf "%s_out.append(String.valueOf(%s));\n" indent id
    | _ ->
        sprintf "%s%s.toJsonBuffer(_out);\n" indent id

(* Generate a toJsonBuffer command for a record field. *)
let to_string_field env = function
  | (`Field (loc, (atd_field_name, kind, annots), atd_ty)) ->
      let json_field_name = get_json_field_name atd_field_name annots in
      let field_name = get_pgsql_field_name atd_field_name annots in
      let atd_ty = norm_ty ~unwrap_option:true env atd_ty in
      (* In the case of an optional field, create a predicate to test whether
       * the field has its default value. *)
      let if_part =
        sprintf "
    if (%s != null) {
      if (_isFirst)
        _isFirst = false;
      else
        _out.append(\",\");
      _out.append(\"\\\"%s\\\":\");
%s    }
"
          field_name
          json_field_name
          (to_string env field_name atd_ty "      ")
      in
      let else_part =
        let is_opt =
          match kind with
            | `Optional | `With_default -> true
            | `Required -> false in
        if is_opt then
          ""
        else
          sprintf "    \
    else
      throw new JSONException(\"Uninitialized field %s\");
"
            field_name
      in
      if_part ^ else_part

(* Generate a pgsqldoc comment *)
let pgsqldoc loc annots indent =
  let from_inline_text text = indent ^ " * " ^ text ^ "\n" in
  (* Assume that code is the name of a field that is defined
     in the same class *)
  let from_inline_code code = indent ^ " * {@link #" ^ code ^ "}\n" in
  let from_doc_para acc para =
    L.fold_left
      (fun acc -> function
         | `Text text -> (from_inline_text text) :: acc
         | `Code code -> (from_inline_code code) :: acc
      )
      acc
      para in
  let from_doc = function
    | `Text blocks ->
        L.fold_left
          (fun acc -> function
             | `Paragraph para -> from_doc_para acc para
             | `Pre _ -> failwith "Preformatted doc blocks are not supported"
          )
          []
          blocks in
  (match Ag_doc.get_doc loc annots with
     | Some doc ->
         let header = indent ^ "/**\n" in
         let footer = indent ^ " */\n" in
         let body   =
           String.concat "" (List.rev (from_doc doc)) in
         header ^ body ^ footer
     | None     -> ""
  )


(* ------------------------------------------------------------------------- *)
(* Translation of ATD types into Java types *)

(* For option, sum and record types, we generate a Java class.  Each such class
 * implements the following interface:
 *
 *  interface Atdj {
 *    String toJson() throws JSONException;
 *    void toJsonBuffer(StringBuilder out) throws JSONException;
 *  }
 *
 * The toJson() method outputs a JSON representation of the
 * associated value.
 *
 * Each class also has a String constructor for a JSON string as well as a
 * constructor from the corresponding org.json type (see json_of_atd, above).
 *
 * We do not generate classes for types bool, int, float, string and list;
 * instead we `inline' these types directly into the class in which they
 * occur.  We do this so that the Java programmer can access such values
 * directly, thereby avoiding the overhead of having to manually unbox each such
 * value upon access.
 *)

let open_sql env cname =
  let out = open_out (env.package_dir ^ "/" ^ cname ^ ".sql") in
  fprintf out "\
// Entête génération SQL
";
  out

let open_ml env cname =
  let out = open_out (env.package_dir ^ "/" ^ cname ^ ".ml") in
  fprintf out "\
// Entête génération SQL
";
  out


type depending_pass = {
                recs : string list;
                sums : (string * Atd_ast.variant list) list;
}

type fromWhat =
        | FromNothing
        | FromList
        | FromOption


type simplifiedType =
        | String
        | Int
        | Float
        | Char
        | Bool
        | Date
        | TimeStamp
        | DefinedType of string
        | Option of simplifiedType
        | List   of simplifiedType

let dep_dict = ref {recs = [] ; sums = []};;

let rec trans_module env items =
        let _ = dep_dict :=  (List.fold_left depending_pass_op (!dep_dict) items)  in 
      (*  let _ = L.length dep_dict.recs |> string_of_int |> prerr_endline in
        let _ = L.iter prerr_endline dep_dict.recs in*)
        L.fold_left trans_outer env items
        (*
 * TODO : Ici, ajouter un depending pass, qui va nous informer :
         * Des types sommes à transformer en définition de type, pour le moment
         * Des types record, dont il faut noter le nom pour chacun d'entre eux afin de créer les id adéquats
                * Le depending pass créer une liste de type record
                * Le depending pass créer une liste de type somme, en embarquant leur def      
         * A l'avenir, lorsqu'on aura un type somme utilisé dans un record, il faudra gérer la conversion
         * A l'avenir, gérer l'option permettant d'utiliser un type somme comme table
 * *)

and depending_pass_op   dep_struct  (`Type (_, (name, _, _), atd_ty)) =
        match unwrap atd_ty with
        | `Sum (_, vl, _) ->  { dep_struct with sums = (Atdj_names.to_sql_name name,vl)::dep_struct.sums; }
        | `Record _   ->  { dep_struct with recs = (Atdj_names.to_sql_name name)::dep_struct.recs; }
        | `Name (_, (_, name, _), _) -> dep_struct
        | x -> type_not_supported x



and trans_outer env (`Type (_, (name, _, _), atd_ty)) =
  match unwrap atd_ty with
    | `Sum _ as s ->
        trans_sum name env s
    | `Record _ as r -> let _ = trans_record_sql name env r in
                        trans_record_ml name env r
    | `Name (_, (_, name, _), _) ->
        (* Don't translate primitive types at the top-level 
         * Donc inclus les types date*)
        env
    | x -> type_not_supported x

(* Translation of sum types.  For a sum type
 *
 *   type ty = Foo | Bar of whatever
 *
 * we generate a class Ty implemented in Ty.pgsql and an enum TyEnum defined
 * in a separate file TyTag.pgsql.
 *)
and trans_sum my_name env (`Sum (loc, vars, annots)) =
  let class_name = Atdj_names.to_sql_name my_name in

  let cases = L.map (function
    | `Variant (_, (atd_name, an), opt_ty) ->
        let json_name = get_json_variant_name atd_name an in
        let func_name, enum_name, field_name =
          get_pgsql_variant_names atd_name an in
        let opt_pgsql_ty =
          match opt_ty with
          | None -> None
          | Some ty ->
              let (pgsql_ty, env) = trans_inner env (unwrap_option env ty) in
              Some (ty, pgsql_ty)
        in
        (json_name, func_name, enum_name, field_name, opt_pgsql_ty)
    | `Inherit _ -> assert false
  ) vars
  in

  let tags = L.map (fun (_, _, enum_name, _, _) -> enum_name) cases in

  let out = open_sql env class_name in

  fprintf out "\
/**
 * Construct objects of type %s.
 */

public class %s {
  Tag t = null;

  public %s() {
  }

  public Tag tag() {
    return t;
  }
"
    my_name
    class_name
    class_name;

  fprintf out "
  /**
   * Define tags for sum type %s.
   */
  public enum Tag {
    %s
  }
"
    my_name
    (String.concat ", " tags);

  fprintf out "
  public %s(Object o) throws JSONException {
    String tag = Util.extractTag(o);
   %a
      throw new JSONException(\"Invalid tag: \" + tag);
  }
"
    class_name
    (fun out l ->
       L.iter (fun (json_name, func_name, enum_name, field_name, opt_ty) ->
         match opt_ty with
         | None ->
             fprintf out " \
    if (tag.equals(\"%s\"))
      t = Tag.%s;
    else"
               json_name (* TODO: pgsql-string-escape this *)
               enum_name

         | Some (atd_ty, pgsql_ty) ->
             let src = sprintf "((JSONArray)o).%s(1)" (get env atd_ty false) in
             let set_value =
               assign env
                 (Some ("field_" ^ field_name)) src
                 pgsql_ty atd_ty "      "
             in
             fprintf out " \
    if (tag.equals(\"%s\")) {
%s
      t = Tag.%s;
    }
    else"
               json_name (* TODO: pgsql-string-escape this *)
               set_value
               enum_name
       ) l
  ) cases;

  L.iter (fun (_, func_name, enum_name, field_name, opt_ty) ->
    match opt_ty with
    | None ->
        fprintf out "
  public void set%s() {
    /* TODO: clear previously-set field and avoid memory leak */
    t = Tag.%s;
  }
"
          func_name
          enum_name;
    | Some (atd_ty, pgsql_ty) ->
        fprintf out "
  %s field_%s = null;
  public void set%s(%s x) {
    /* TODO: clear previously-set field in order to avoid memory leak */
    t = Tag.%s;
    field_%s = x;
  }
  public %s get%s() {
    if (t == Tag.%s)
      return field_%s;
    else
      return null;
  }
"
          pgsql_ty field_name
          func_name pgsql_ty
          enum_name
          field_name
          pgsql_ty func_name
          enum_name
          field_name;
  ) cases;

  fprintf out "
  public void toJsonBuffer(StringBuilder _out) throws JSONException {
    if (t == null)
      throw new JSONException(\"Uninitialized %s\");
    else {
      switch(t) {%a
      default:
        break; /* unused; keeps compiler happy */
      }
    }
  }

  public String toJson() throws JSONException {
    StringBuilder out = new StringBuilder(128);
    toJsonBuffer(out);
    return out.toString();
  }
"
    class_name
    (fun out l ->
       L.iter (fun (json_name, func_name, enum_name, field_name, opt_ty) ->
         match opt_ty with
         | None ->
             fprintf out "
      case %s:
        _out.append(\"\\\"%s\\\"\");
        break;"
               enum_name
               json_name (* TODO: pgsql-string-escape *)

         | Some (atd_ty, _) ->
             fprintf out "
      case %s:
         _out.append(\"[\\\"%s\\\",\");
%s         _out.append(\"]\");
         break;"
             enum_name
             json_name
             (to_string env ("field_" ^ field_name) atd_ty "         ")
       ) l
    ) cases;

  fprintf out "}\n";
  close_out out;
  env




(* Translate a record into a pgsql definition file AND a ml file to create, save, get .  Each record field becomes a field
 * within the class.
 *)
and trans_record_ml my_name env (`Record (loc, fields, annots)) = 
        (* TODO
         * INSERT INTO %s(%s) VALUES ( %s ) RETURNING %s, %s;
         * 1. Liste des noms de champs SQL, 2 fois
         * 2. Liste des champs, à partir du newline, converti en chaines, en fonction du type, la conversion est différente
         *  String : quote
         *  Date   : idem
         *  Array  : genre '{{1,2,3},{4,5,6},{7,8,9}}'
         *  Option : Null si None
         *  Tuple  : '{1,2,3}'
         *  id = L.hd line |> int_of_string; label = L.at line 1
         *
         *  Faire une fonction séparée, pour pouvoir choisir
         *  Faire un type FromNothing | FromList | FromOption pour pouvoir faire une seule fonction qui traite tous les cas
         *
         *
         * type table3 = {
	l3 : string;
	d  : date;
	t  : timestamp;
	n3 : int;
	f3 : float;
	b3 : bool;
	fk : table2 list ;
        fk2 : table1 list;
}
         *
         *  DANS LE INSERT VALUES:
                 *  quote newline.l3, quote newline.date, quote newline.t, string_of_int n3, string_of_float f3, string_of_bool b3, L.map (fun t -> t.idTable2) fk), fk.idTable1
         *
         * DANS l'hydratation de la structure en retour
         * { idTable3 = L.hd line |> int_of_string ; l3 = L.at line 1 ; d =  L.at line 2 |> float_of_string ; t =  L.at line 3 |> float_of_string ; 
         *   n3 = d =  L.at line 4 |> int_of_string ; f3 = L.at line 5 |> float_of_string ; b3 = L.at line 6 |> bool_of_string ;
         *   Et là ? : on créé un env ? }
         * *)
  let fields = L.map (function
          | `Field _ as f -> f
          | `Inherit _ -> assert false
                           )
  fields in
  let rec find_type  ty =
          match  ty with
                | `Name (_, (_, name1, _), _) -> ( 
                        match name1 with
                        | "bool"    -> Bool
                        | "int"     -> Int
                        | "float"   -> Float
                        | "string"  -> String
                        | "date"    -> Date
                        | "timestamp" -> TimeStamp
                        | "char"    -> Char
                        | x         -> if L.exists (fun (n,_) -> n=x)  env.module_items then DefinedType x else "cas non géré : "^x |> failwith 
                        )
                | `List (loc, sub_atd_ty, _)  -> List (find_type sub_atd_ty)
                | `Option (_, atd_ty, _)      -> Option (find_type atd_ty)
                | `Record (_,_,_) -> failwith "Cas Record non géré : record dans une table : on fabrique un type ?"
                | `Tuple  (_,_,_) -> failwith "Cas Tuple non géré : Tuple dans une table, inliner ?"
                | _ -> failwith "name_a_type_for_sql : cas non géré" in

  let field_to_string_for_ml (`Field (_, (field_name, _, annots), atd_ty)) =
       field_name, find_type atd_ty
  in
  let upletList = L.map field_to_string_for_ml fields  in
  let makeValues (f,t) =
          match t with
          | Float         -> "string_of_float line."^f
          | Int           -> "string_of_int line."^f
          | String        ->  "\"'\"^line."^f^"^\"'\""
          | Date | TimeStamp     -> "\"'\"^(string_of_float line."^f^")^\"'\""
          | Char          -> "String.make 1 line."^f
          | Bool          -> "string_of_bool line."^f
          | DefinedType s -> "string_of_int line."^f^".id"^s
          (* Cas à la con*)
          | List (DefinedType s) -> "\"'{\"^ (L.map (fun i -> i.id"^s^" |> string_of_int) line."^f^" |> String.concat \",\" )^\"}'\""
          | Option s      -> "match line."^f^" with | None -> \"NULL\" | Some s -> s"
          | List   s      -> failwith "Gestion des listes de type builtin" in
  let makeGetters cpt (f,t) =
          match t with
          | Float         -> "List.nth line."^f^" "^(string_of_int cpt)^" |> float_of_string"
          | Int           -> "List.nth line."^f^" "^(string_of_int cpt)^" |> float_of_string"
          | String        -> "List.nth line."^f^" "^(string_of_int cpt)^" |> float_of_string"
          | Date          -> "List.nth line."^f^" "^(string_of_int cpt)^" |> float_of_string"
          | TimeStamp     -> "List.nth line."^f^" "^(string_of_int cpt)^" |> float_of_string"
          | Char          -> "String.get (List.nth line."^f^" "^(string_of_int cpt)^") 0"
          | Bool          -> "List.nth line."^f^" "^(string_of_int cpt)^" |> float_of_string"
          | DefinedType s -> "Bon là falloir chercher dans env..."
          (* Cas à la con*)
          | List (DefinedType s) -> "Bon là falloir chercher dans env..."
          | Option s      -> "Some line."^f (*TODO : écrire un test*)
          | List   s      -> failwith "Gestion des listes de type builtin" in
  let valuesStr         = L.map  makeValues upletList |> S.concat "^\", \"^ " in
  let valuesGetters     = L.mapi makeGetters upletList |> S.concat ", " in
  let names             = L.map (fun (f,t) -> f) upletList |> S.concat ", "  in
  let req = Printf.sprintf "\"INSERT INTO %s(%s) VALUES (\"^ %s ^\" ) RETURNING %s;\"" my_name names valuesStr names  in (*TODO : gérer les quotes*)
  let _ = prerr_endline req in
  let _ = prerr_endline valuesGetters; prerr_endline "" in
  env
and trans_record_sql my_name env (`Record (loc, fields, annots)) =
         (* Construction des liste de champs
         * Remove `Inherit values *)
        (*let _ =  L.length !dep_dict.recs |> string_of_int |> prerr_endline in *)
        let fields = L.map (function
                                | `Field _ as f -> f
                                | `Inherit _ -> assert false
                           )
                     fields in
        (* Translate field types : préparation des nom, pour n'avoir ensuite qu'à les inliner*)

        let name_a_list_type_for_sql ty =
                match ty with
                | `Name (_, (_, name2, _), _) ->  
                                (match name2 with
                                | "bool" | "int" | "float" | "string" | "abstract" -> name2
                                | _ -> (try
                                        let x = List.assoc name2 env.module_items in
                                        (*Type existant défini dans le fichier*)
                                        "Integer[]"
                                with Not_found ->
                                        Atd_ast.error_at loc ("Warning: unknown type "^name2^" %s\n%!")
                                        )
                                )
                | _ -> failwith "liste de autre chose qu'un type" in

        let rec name_a_type_for_sql ty =
               match  ty with
                | `Name (_, (_, name1, _), _) ->
                                (* It's a primitive type e.g. int *)
                                   Atdj_names.to_sql_name name1
                | `List (loc, sub_atd_ty, _)  -> (* Est-ce une liste d'un type builtin, ou une liste d'un type défini dans le fichier ATD ?*)
                                name_a_list_type_for_sql sub_atd_ty
                | `Option (_, atd_ty, _) -> name_a_type_for_sql atd_ty
                | `Record (_,_,_) -> failwith "Cas Record non géré : record dans une table : on fabrique un type ?"
                | `Tuple  (_,_,_) -> failwith "Cas Tuple non géré : Tuple dans une table, inliner ?"
                | _ -> failwith "name_a_type_for_sql : cas non géré" in


            (* Output sql and ML file *)
        let sql_name = Atdj_names.to_sql_name my_name in
        let sqlout = open_sql env sql_name in
        let mlout  = open_ml  env sql_name in

        let field_to_string_for_sql fin (`Field (_, (field_name, _, annots), atd_ty)) = 
                let field_name = get_pgsql_field_name field_name annots in
                let pgsql_ty   =  name_a_type_for_sql atd_ty in
                let virgule    = if fin then "" else "," in
                (*let _ = L.iter prerr_endline !dep_dict.recs in 
                let _ = prerr_endline pgsql_ty in *)
                match L.exists (S.starts_with pgsql_ty) !dep_dict.recs with
                | false -> fprintf sqlout ("\t%s %s%s\n") field_name pgsql_ty virgule
                | true  -> fprintf sqlout ("\t%s %s%s--foreign key %s\n") field_name "Integer" virgule pgsql_ty in

        (*GÉNÉRATION*)
        let _ = output_string sqlout (pgsqldoc loc annots "") in
        let _ = fprintf sqlout 
        "Create Table %s (\n\tid%s Serial Primary Key,\n" sql_name sql_name in


        let _ = L.take ((L.length fields ) -1) fields |> L.iter (field_to_string_for_sql false) in
        let _ = L.last fields |> field_to_string_for_sql true in
        let _ = fprintf sqlout "\n}\n" in
                close_out sqlout;
                env


                (* Translate an `inner' type i.e. a type that occurs within a record or sum *)
and trans_inner env atd_ty =
                match atd_ty with
                | `Name (_, (_, name1, _), _) ->
                                (match norm_ty env atd_ty with
                                | `Name (_, (_, name2, _), _) ->
                                                (* It's a primitive type e.g. int *)
                                                (Atdj_names.to_sql_name name2, env)
                                | `List (_, sub_atd_ty, _)  ->
                                                let (ty', env) = trans_inner env sub_atd_ty in
                                                ( ty' ^ "[]", env)
                                | _ ->
                                                (Atdj_names.to_sql_name name1, env)
                                )

  | x -> type_not_supported x
