open Printf
open Atdj_names
open Atdj_env
open Atdj_util

module L = BatList

module S = BatString

module O = BatOption


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
-- Entête génération SQL
";
  out

let open_ml env cname =
  let out = open_out (env.package_dir ^ "/" ^ cname ^ ".ml") in
  fprintf out "\
(* Entête génération ML *)
type date = float;;
type timestamp = float
let quote s = \"'\"^s^\"'\";;

";
  out

let reopen_file env cname ext =
  open_out_gen [Open_wronly; Open_append] 0o600 (env.package_dir ^ "/" ^ cname ^ "." ^ ext)


let ml_create_model isUpd nom req params structAff =
        let name, idp = 
                match String.uppercase isUpd with
                | "U" -> "saveOne"^nom, "line"
                | "C" -> "createOne"^nom, "line"
                | "R" -> "find"^nom^"ById", "id" in
        Printf.sprintf
        "let %s (request_service : string -> string list -> string list list) %s =
        let req  = Printf.sprintf \"%s\" %s in
        let lines = request_service req [] in
        try 
                let ret = List.hd lines in
                Some { %s } 
        with e -> None \n" name idp req params structAff;;  

let ml_model_new_one nom structAff =
        Printf.sprintf 
        "let new%s () = 
                { %s }\n" nom structAff 

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



type generated = {
        ty              : simplifiedType;
        parentTyp       : string;
        fieldName       : string;
        fieldNameWCast  : string;
        valueUpdate     : string;
        valueInsert     : string;
        valueGetter     : string;
        getterId        : string;
};;



let rec trans_module env items =
        (* Création des fichiers de génération*)
        let file_prefix =  Filename.chop_suffix (O.get env.input_file |>  Filename.basename) ".atd" in
        let outml,outsql = open_ml env file_prefix, open_sql env file_prefix in
        let _ = close_out outml; close_out outsql in
        L.fold_left trans_outer  env items
     

and trans_outer  env (`Type (_, (name, _, _), atd_ty)) =
  match unwrap atd_ty with
    | `Sum _ as s ->
        trans_sum name env s
    | `Record _ as r -> let _ = trans_record_sql  name env r in
                        trans_record_ml  name env r
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
  env




(* Translate a record into a pgsql definition file AND a ml file to create, save, get .  Each record field becomes a field
 * within the class.
 *)
and  find_type env ty =
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
                | `List (loc, sub_atd_ty, _)  -> List (find_type env sub_atd_ty)
                | `Option (_, atd_ty, _)      -> Option (find_type env atd_ty)
                | `Record (_,_,_) -> failwith "Cas Record non géré : record dans une table : on fabrique un type ?"
                | `Tuple  (_,_,_) -> failwith "Cas Tuple non géré : Tuple dans une table, inliner ?"
                | _ -> failwith "name_a_type_for_sql : cas non géré" 


and trans_record_ml  my_name env (`Record (loc, fields, annots)) = 
        (*TODO : cette fonction doit être capable d'aller chercher ça dans le env, à partir du nom, comme ça on pourra ressortir d'autres infos d'autres types*)
        let file_prefix =  Filename.chop_suffix (O.get env.input_file |>  Filename.basename) ".atd" in
        let mlout = reopen_file env file_prefix "ml" in
        let fields = L.map (function
                | `Field _ as f -> f
                | `Inherit _ -> assert false
        )
        fields in
        let field_to_string_for_ml (`Field (_, (field_name, _, annots), atd_ty)) =
                field_name, find_type env atd_ty
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
                | List (DefinedType s) -> "\"'{\"^ (List.map (fun i -> i.id"^s^" |> string_of_int) line."^f^" |> String.concat \",\" )^\"}'\""
                | Option Float | Option Date | Option TimeStamp
                -> "match line."^f^" with | None -> \"NULL\" | Some s -> string_of_float s"
                | Option String  -> "match line."^f^" with | None -> \"NULL\" | Some s -> s"
                | Option Int     -> "match line."^f^" with | None -> \"NULL\" | Some s -> string_of_int s"
                | Option Bool    -> "match line."^f^" with | None -> \"NULL\" | Some s -> string_of_bool s"
                | Option Char    -> "match line."^f^" with | None -> \"NULL\" | Some s -> String.make 1 s"
                | List String    -> "\"'{\"^(  line."^f^" |> String.concat \",\" )^\"}'\""

                | List Int       -> "\"'{\"^ (List.map  string_of_int  line."^f^" |> String.concat \",\" )^\"}'\""
                | List Bool      -> "\"'{\"^ (List.map  string_of_bool line."^f^" |> String.concat \",\" )^\"}'\""
                | List Char      -> "\"'{\"^ (List.map (String.make 1) line."^f^" |> String.concat \",\" )^\"}'\""
                | List Float | List Date | List TimeStamp -> "\"'{\"^ (List.map  string_of_float line."^f^" |> String.concat \",\" )^\"}'\""
                | List s ->  failwith "TODO : Gestion des listes de type autre que builtin => Reprendre le cas List (DefinedType s) " in
        let makeGetters cpt (f,t) =
                match t with
                | Float         -> "List.nth ret "^(string_of_int cpt)^" |> float_of_string"
                | Int           -> "List.nth ret "^(string_of_int cpt)^" |> int_of_string"
                | String        -> "List.nth ret "^(string_of_int cpt)^" "
                | Date          -> "List.nth ret "^(string_of_int cpt)^" |> float_of_string"
                | TimeStamp     -> "List.nth ret "^(string_of_int cpt)^" |> float_of_string"
                | Char          -> "String.get (List.nth ret "^(string_of_int cpt)^") 0"
                | Bool          -> "if List.nth ret "^(string_of_int cpt)^" = \"t\" then true else false"
                | DefinedType s -> "line."^f
                (* Cas à la con*)
                | List (DefinedType s) -> "line."^f
                | Option String | Option Date | Option TimeStamp | Option (DefinedType _) -> "let s = List.nth ret "^(string_of_int cpt)^" in if s = \"\" then None else Some s" (*TODO : gérer les cas non string*)
                | Option s      -> failwith "Cas option non géré" (*TODO : gérer les qq cas*)
                | List   s      -> failwith "Gestion des listes de type builtin" in
        let makeInitField (f,t) =
                match t with
                | Float         -> f^" = 0.0"
                | Int           -> f^" = 0"
                | String        -> f^" = \"\" "
                | Date | TimeStamp     -> f^" = 0.0 "
                | Char          -> f^" = 'a' "
                | Bool          -> f^" = false "
                | DefinedType s -> f^" = {} (*TODO*)"
                (* Cas à la con*)
          | List (DefinedType s) -> f^" = "
          | Option _      -> f^" = None"
          | List _        -> f^" = []" in

(*
type generated = {
        ty              : simplifiedType;
        parentTyp       : name;
        fieldName       : string;
        fieldNameWCast  : string;
        valueUpdate     : string;
        valueInsert     : string;
        valueGetter     : string;
        getterId        : string;
};;*)


  let valuesStr         = L.map  makeValues upletList |> S.concat "^\", \"^ " in
  let valuesGetters  d  = let decal = if d then 1 else 0 in L.mapi (fun i -> (fun (f,t) -> f^" = "^( makeGetters (i+decal) (f,t)))) upletList |> S.concat "; " in
  let valuesGettersCrea = "  id"^my_name^" = "^(makeGetters  0 ("id"^(Atdj_names.to_sql_type_name my_name),Int))^" ; "^(valuesGetters true) in
  let valuesUpdate      = L.map  (fun (f,t) -> "\""^f^" = \"^"^(makeValues (f,t))) upletList |> S.concat "^\", \"^ " in
  let valuesGettersUpd  = "line with "^(valuesGetters false) in
  let names             = 
          let find_dates (f,t) = match t with | Date | TimeStamp -> "EXTRACT(EPOCH FROM  "^f^")" | _ -> f in
          L.map find_dates upletList |> S.concat ", " in

  let reqInser = Printf.sprintf "INSERT INTO %s(%s) VALUES (\"^ %s ^\" ) RETURNING id%s,%s;" my_name names valuesStr my_name names  in 
  let reqUpdat = Printf.sprintf "UPDATE %s SET \"^ %s  ^\" WHERE id%s = \"^%s^\" RETURNING %s;" my_name valuesUpdate my_name ("string_of_int line.id"^my_name) names in
  let reqSelec = Printf.sprintf "SELECT id%s, %s FROM %s WHERE id%s = %%d" my_name names my_name my_name  in
  (*TODO : problème des tables en plus à gérer, lié avec le TODO du env
   * On va tout mettre dans une grosse structure, générer toutes les structures, qui contiendront aussi fields
   * A la fin, le code est généré*)
  let codeCrea = ml_create_model "C" (Atdj_names.to_camel_case my_name) reqInser "" valuesGettersCrea in
  let codeUpda = ml_create_model "U" (Atdj_names.to_camel_case my_name) reqUpdat "" valuesGettersUpd in 
  let codeSel  = ml_create_model "R" (S.capitalize my_name) reqSelec "id" valuesGettersCrea in
  let newOneLi = ("id"^my_name^" = -1")::(L.map makeInitField upletList) |> S.concat "; " in
  let codeNew  = ml_model_new_one my_name newOneLi in

  (*TODO : génération des types AVEC IDs*)
  let entet             = "type "^my_name^" = {" in
  let rec typename  t   = match  t with
          | Float         -> "float"
          | Int           -> "int"
          | String        -> "string"
          | Date          -> "date"
          | TimeStamp     -> "timestamp"
          | Char          -> "char"
          | Bool          -> "bool"
          | DefinedType s -> s
          | List  s       -> (typename s)^" list"
          | Option s      -> (typename s)^" option" in
  let typId             = "id"^my_name^" : int;" in
  let contentTyp        = L.map (fun (f,t) -> "\t"^f^" : "^(typename t)^";") upletList in
  let defTypeStr        = S.concat "\n" contentTyp in
  let _ = fprintf mlout "%s\n\t%s\n%s\n}\n"  entet typId defTypeStr in
  let _ = fprintf mlout "%s\n\n" codeCrea in
  let _ = fprintf mlout "%s\n\n" codeUpda  in
  let _ = fprintf mlout "%s\n\n" codeSel   in
  let _ = fprintf mlout "%s\n\n\n" codeNew in
  close_out mlout;
  env
and trans_record_sql  my_name env (`Record (loc, fields, annots)) =
         (* Construction des liste de champs
         * Remove `Inherit values *)
        (*let _ =  L.length !dep_dict.recs |> string_of_int |> prerr_endline in *)
        let file_prefix =  Filename.chop_suffix (O.get env.input_file |>  Filename.basename) ".atd" in
        let sqlout = reopen_file env file_prefix "sql" in
        let fields = L.map (function
                                | `Field _ as f -> f
                                | `Inherit _ -> assert false
                           )
                     fields in
        let field_to_string_type (`Field (_, (field_name, _, annots), atd_ty)) =
                field_name, find_type env atd_ty in
        let fields = L.map field_to_string_type fields in

        (* Translate field types : préparation des nom, pour n'avoir ensuite qu'à les inliner*)

        let rec name_a_type_for_sql ty ishadBeenAnOption =
                let notnull = " NOT NULL" in
                let rec internRec ty ishadBeenAnOption =
                        match ty with
                        | Float         -> "Double Precision",(if ishadBeenAnOption then "" else  notnull)
                        | Int           -> "Integer",(if ishadBeenAnOption then "" else  notnull)
                        | String        -> "Text",(if ishadBeenAnOption then "" else  notnull)
                        | Date          -> "Date",(if ishadBeenAnOption then "" else  notnull)
                        | TimeStamp     -> "TimeStamp",(if ishadBeenAnOption then "" else  notnull)
                        | Char          -> "Character",(if ishadBeenAnOption then "" else  notnull)
                        | Bool          -> "Boolean",(if ishadBeenAnOption then "" else  notnull)
                        | DefinedType s -> "Integer",(if ishadBeenAnOption then "" else  notnull)
                        | List (DefinedType s) -> "Integer[]",(if ishadBeenAnOption then "" else  notnull)
                        | Option s      -> let t,_ = internRec s true  in t,""
                        | List   s      -> let t,_ = internRec s true  in t^"[]",(if ishadBeenAnOption then "" else  notnull) in
                let typName, notNullOption = internRec ty false in
                typName^notNullOption in
                                     (*   let x = List.assoc name2 env.module_items in
                                                                        with Not_found ->
                                        Atd_ast.error_at loc ("Warning: unknown type "^name2^" %s\n%!")
                                                                         Atdj_names.to_sql_name name1
               *)


            (* Output sql and ML file *)
        let sql_name = Atdj_names.to_sql_type_name my_name in

        let field_to_string_for_sql fin field_name atd_ty = 
                let field_name = get_pgsql_field_name field_name annots in
                let pgsql_ty   =  name_a_type_for_sql atd_ty false in
                let virgule    = if fin then "" else "," in
                (*let _ = L.iter prerr_endline !dep_dict.recs in 
                let _ = prerr_endline pgsql_ty in *)
                match L.exists (S.starts_with pgsql_ty) !dep_dict.recs with
                | false -> fprintf sqlout ("\t%s %s%s\n") field_name pgsql_ty virgule
                | true  -> fprintf sqlout ("\t%s %s%s--foreign key %s\n") field_name "Integer" virgule pgsql_ty in

        (*GÉNÉRATION*)
        let _ = output_string sqlout "" in
        let _ = fprintf sqlout 
        "Create Table %s (\n\tid%s Serial Primary Key,\n" sql_name sql_name in


        let _ = L.take ((L.length fields ) -1) fields |> L.iter (fun (f,t) -> field_to_string_for_sql false f t) in
        let _ = L.last fields |> (fun (f,t) -> field_to_string_for_sql true f t) in
        let _ = fprintf sqlout "\n)\n" in
                close_out sqlout;
                env


                (* Translate an `inner' type i.e. a type that occurs within a record or sum *)
and trans_inner env atd_ty =
                match atd_ty with
                | `Name (_, (_, name1, _), _) ->
                                (match norm_ty env atd_ty with
                                | `Name (_, (_, name2, _), _) ->
                                                (* It's a primitive type e.g. int *)
                                                (Atdj_names.to_sql_type_name name2, env)
                                | `List (_, sub_atd_ty, _)  ->
                                                let (ty', env) = trans_inner env sub_atd_ty in
                                                ( ty' ^ "[]", env)
                                | _ ->
                                                (Atdj_names.to_sql_type_name name1, env)
                                )

  | x -> type_not_supported x
