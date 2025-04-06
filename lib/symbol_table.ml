open Ast
open Errors

let type_symbol_table :
    (perkident, perktype * string option * perkident list) Hashtbl.t =
  Hashtbl.create 10

let lookup_type (id : perkident) : perktype option =
  if Hashtbl.mem type_symbol_table id then
    let t, _code, _deps = Hashtbl.find type_symbol_table id in
    Some t
  else None

let resolve_type (typ : perktype) : perktype =
  let rec resolve_type_aux (typ : perktype) (lst : perktype list) :
      perktype * perktype list =
    say_here (Printf.sprintf "resolve_type: %s" (show_perktype typ));
    if List.mem typ lst then (typ, lst)
    else
      let a, typ', q = typ in
      match typ' with
      | Basetype t ->
          ( ( a,
              (match lookup_type t with None -> typ' | Some (_, t, _) -> t),
              q ),
            typ :: lst )
      | Pointertype t ->
          let lst = typ :: lst in
          let res_t, res_l = resolve_type_aux t lst in
          ((a, Pointertype res_t, q), res_l)
      | Funtype (params, ret) ->
          let lst = typ :: lst in
          let params_t, params_l =
            List.fold_right
              (fun param (acc, lst) ->
                let res_t, res_l = resolve_type_aux param lst in
                (res_t :: acc, res_l))
              params ([], lst)
          in
          let ret_t, ret_l = resolve_type_aux ret params_l in
          ((a, Funtype (params_t, ret_t), q), ret_l)
      | Arraytype (t, n) ->
          let lst = typ :: lst in
          let ret_t, ret_l = resolve_type_aux t lst in
          ((a, Arraytype (ret_t, n), q), ret_l)
      | Structtype _t -> (typ, lst)
      | ArcheType (name, decls) ->
          let lst = typ :: lst in
          let decls_t, decls_l =
            List.fold_right
              (fun (param, ide) (acc, lst) ->
                let res_t, res_l = resolve_type_aux param lst in
                ((res_t, ide) :: acc, res_l))
              decls ([], lst)
          in
          ((a, ArcheType (name, decls_t), q), decls_l)
      | ArchetypeSum ts ->
          let lst = typ :: lst in
          let ts_t, ts_l =
            List.fold_right
              (fun param (acc, lst) ->
                let res_t, res_l = resolve_type_aux param lst in
                (res_t :: acc, res_l))
              ts ([], lst)
          in
          ((a, ArchetypeSum ts_t, q), ts_l)
      | Modeltype (name, archetypes, decls, constr_params) ->
          let lst = typ :: lst in
          let decls_t, decls_l =
            List.fold_right
              (fun (param, ide) (acc, lst) ->
                let res_t, res_l = resolve_type_aux param lst in
                ((res_t, ide) :: acc, res_l))
              decls ([], lst)
          in
          ((a, Modeltype (name, archetypes, decls_t, constr_params), q), decls_l)
      | Optiontype t ->
          let lst = typ :: lst in
          let ret_t, ret_l = resolve_type_aux t lst in
          ((a, Optiontype ret_t, q), ret_l)
      | Tupletype ts ->
          let lst = typ :: lst in
          let ts_t, ts_l =
            List.fold_right
              (fun param (acc, lst) ->
                let res_t, res_l = resolve_type_aux param lst in
                (res_t :: acc, res_l))
              ts ([], lst)
          in
          ((a, Tupletype ts_t, q), ts_l)
      | Vararg -> ((a, Vararg, q), lst)
      | Infer -> ((a, Infer, q), lst)
    (* | Structtype t -> (
          match lookup_type t with None -> typ' | Some (_, t, _) -> t) *)
  in
  fst (resolve_type_aux typ [])

let rec type_descriptor_of_perktype (t : perktype) : string =
  let _, t, _ = t in
  match t with
  | Basetype s -> s
  | Structtype s -> s
  | Funtype (args, ret) ->
      let args_str =
        String.concat "__" (List.map type_descriptor_of_perktype args)
      in
      Printf.sprintf "l_%s_to_%s_r" args_str (type_descriptor_of_perktype ret)
  | Pointertype t -> Printf.sprintf "%s_ptr" (type_descriptor_of_perktype t)
  | Arraytype (t, _) -> Printf.sprintf "%s_arr" (type_descriptor_of_perktype t)
  | Vararg ->
      "vararg"
      (* This is probably problematic, cannot define function pointers with ... . Nvm, apparently you can 😕*)
  | ArcheType (name, _decls) -> name
  | ArchetypeSum archs ->
      "Sum" ^ String.concat "Plus" (List.map type_descriptor_of_perktype archs)
  | Modeltype (name, _archs, _decls, _constr_params) -> name
  | Optiontype t -> Printf.sprintf "%s_opt" (type_descriptor_of_perktype t)
  | Infer -> failwith "Impossible: type has not been inferred"
  | Tupletype ts ->
      Printf.sprintf "tup_%s_le"
        (String.concat "__" (List.map type_descriptor_of_perktype ts))

let print_type_symbol_table () =
  Printf.printf "Type Symbol Table:\n";
  Hashtbl.iter
    (fun id (typ, _code, deps) ->
      Printf.printf "Identifier: %s, Type: %s, Dependencies: [%s]\n" id
        (type_descriptor_of_perktype typ)
        (String.concat ", " deps))
    type_symbol_table

let rec bind_type (id : perkident) (t : perktype) =
  say_here (Printf.sprintf "bind_type: %s" (show_perktype t));
  if not (Hashtbl.mem type_symbol_table id) then
    Hashtbl.add type_symbol_table id (t, None, dependencies_of_type t)

and rebind_type (id : perkident) (t : perktype) =
  if Hashtbl.mem type_symbol_table id then
    Hashtbl.replace type_symbol_table id (t, None, dependencies_of_type t)
  else raise (Undeclared ("Type not found in symbol table: " ^ id))

and dependencies_of_type (typ : perktype) : perkident list =
  let typ = resolve_type typ in
  let rec dependencies_of_type_aux (typ : perktype) (lst : perktype list) :
      perkident list * perktype list =
    say_here (Printf.sprintf "dependencies_of_type: %s\n\n" (show_perktype typ));
    if List.mem typ lst then
      ( (match typ with
        | _, Basetype _, _ -> []
        | _ -> [ type_descriptor_of_perktype typ ]),
        lst )
    else
      let _, typ', _ = typ in
      match typ' with
      | Basetype _ -> ([], typ :: lst)
      | Pointertype t -> dependencies_of_type_aux t (typ :: lst)
      | Funtype (params, ret) ->
          let lst = typ :: lst in
          let params_t, params_l =
            List.fold_right
              (fun param (acc, lst) ->
                let res_t, res_l = dependencies_of_type_aux param lst in
                (res_t @ acc, res_l))
              params ([], lst)
          in
          let ret_t, ret_l = dependencies_of_type_aux ret (ret :: params_l) in
          ((type_descriptor_of_perktype typ :: params_t) @ ret_t, ret_l)
      | Arraytype (t, _) -> dependencies_of_type_aux t (typ :: lst)
      | Structtype _t -> ([], lst)
      | ArcheType (name, decls) ->
          let lst = typ :: lst in
          let decls_t, decls_l =
            List.fold_right
              (fun (param, _ide) (acc, lst) ->
                let res_t, res_l = dependencies_of_type_aux param lst in
                (res_t @ acc, res_l))
              decls ([], lst)
          in
          (name :: decls_t, decls_l)
      | ArchetypeSum ts ->
          let lst = typ :: lst in
          List.fold_left
            (fun (acc, lst) param ->
              let res_t, res_l = dependencies_of_type_aux param lst in
              (res_t @ acc, res_l))
            ([], lst) ts
      | Modeltype (name, archetypes, decls, constr_params) ->
          let lst = typ :: lst in
          let decls =
            List.map
              (fun (typ, id) ->
                match typ with
                | a, Funtype (params, ret), d ->
                    ( ( a,
                        Funtype
                          ( ([], Pointertype ([], Basetype name, []), [])
                            :: params,
                            ret ),
                        d ),
                      id )
                | _ -> (typ, id))
              decls
          in
          let decls_t, lst =
            List.fold_right
              (fun (param, _ide) (acc, lst) ->
                let res_t, res_l = dependencies_of_type_aux param lst in
                (res_t @ acc, res_l))
              decls ([], lst)
          in
          let constructor_params_t, constr_params_l =
            List.fold_left
              (fun (acc, lst) param ->
                let res_t, res_l = dependencies_of_type_aux param lst in
                (res_t @ acc, res_l))
              ([], lst) constr_params
          in
          ( (name :: archetypes) @ decls_t @ constructor_params_t,
            constr_params_l )
      | Optiontype t -> dependencies_of_type_aux t (typ :: lst)
      | Tupletype ts ->
          let lst = typ :: lst in
          List.fold_left
            (fun (acc, lst) param ->
              let res_t, res_l = dependencies_of_type_aux param lst in
              (res_t @ acc, res_l))
            ([], lst) ts
      | Vararg -> ([], lst)
      | Infer -> ([], lst)
  in
  fst (dependencies_of_type_aux typ [])
  |> List.sort_uniq String.compare
  |> List.filter (fun s -> s <> type_descriptor_of_perktype typ)

let rec bind_type_if_needed (typ : perktype) =
  say_here (Printf.sprintf "bind_type_if_needed: %s" (show_perktype typ));
  let typ' = resolve_type typ in
  match typ' with
  | _, Basetype _t, _ -> ()
  | _, Pointertype t, _ -> bind_type_if_needed t
  | _, Funtype (_params, _ret), _ ->
      bind_type (type_descriptor_of_perktype typ') typ'
  (* List.iter bind_type_if_needed _params;
      bind_type_if_needed _ret *)
  | _, Arraytype (t, _), _ -> bind_type_if_needed t
  | _, Structtype _, _ -> ()
  | _, ArcheType (name, _decls), _ ->
      bind_type name typ'
      (* ;List.iter (fun (typ, _id) -> bind_type_if_needed typ) _decls *)
  | _, ArchetypeSum _ts, _ -> bind_type (type_descriptor_of_perktype typ') typ'
  (* List.iter bind_type_if_needed _ts *)
  | _, Modeltype (name, _archetypes, _decls, _constr_params), _ ->
      bind_type name typ'
      (* ; List.iter (fun (typ, _id) -> bind_type_if_needed typ) decls;
      List.iter (fun typ -> bind_type_if_needed typ) constr_params *)
  | _, Optiontype _t, _ -> bind_type (type_descriptor_of_perktype typ') typ'
  (* bind_type_if_needed t *)
  | _, Tupletype _ts, _ -> bind_type (type_descriptor_of_perktype typ') typ'
  (* List.iter bind_type_if_needed ts *)
  | _, Vararg, _ -> ()
  | _, Infer, _ -> ()
