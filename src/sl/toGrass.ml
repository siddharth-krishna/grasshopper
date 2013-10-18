(* Translate SL formulas to GRASS formulas *)

open Sl
open Symbols
open SlUtil


let one_and_rest lst =
  let rec process acc1 acc2 lst = 
    match lst with
    | x :: xs -> process ((x, acc2 @ xs) :: acc1) (x :: acc2) xs
    | [] -> acc1
  in
  process [] [] lst

let fresh_existentials f =
  let fct id t =
    if fst id = "_" 
    then FormUtil.mk_var ?srt:(FormUtil.sort_of t) (FormUtil.fresh_ident "?_")
    else t
  in
 subst_consts_fun fct f

(* translation that keeps the heap separated from the pointer structure *)
let to_form pred_to_form set_fct domain f =
  let fresh_dom d = FormUtil.fresh_ident ("?" ^ fst d) in
  let rec process_sep pol d f = 
    match f with
    | Pure p -> 
        ([p, FormUtil.mk_empty (Some (Form.Set Form.Loc))], FormUtil.mk_true)
    | Atom (Emp, _) ->
        [FormUtil.mk_true, FormUtil.mk_empty (Some (Form.Set Form.Loc))], FormUtil.mk_true
    | Atom (Region, [t]) ->
        let domain = fresh_dom d in
        [FormUtil.mk_true, mk_loc_set_var domain], 
        FormUtil.mk_eq (mk_loc_set_var domain) t
    | Atom (Pred p, args) -> 
        let domain = mk_loc_set_var (fresh_dom d) in
        let structure, footprint = pred_to_form p args domain in
        [structure, domain], footprint
    | (SepStar forms as f)
    | (SepPlus forms as f) ->
        (*let ds = List.map (fun _ -> fd "sep" domain) forms in*)
        let translated = List.map (process_sep pol (FormUtil.fresh_ident (fst d))) forms in
        let translated_1, translated_2 = List.split translated in
        let translated_product = 
          match translated_1 with
          | [] -> []
          | ts :: tss ->
              List.fold_left 
                (fun acc ts1  -> Util.flat_map (fun ts2 ->  List.map (fun t -> t :: ts2) ts1) acc)
                (List.map (fun t -> [t]) ts) tss
        in
        let process (otranslated_1, translated_2) translated =
          let domain = fresh_dom d in
          let translated_1, dsc = List.split translated in
          (*let dsc = List.map mk_loc_set ds in*)
          let separation1 = FormUtil.mk_eq (mk_loc_set_var domain) (FormUtil.mk_union dsc) in
          let separation2 =
            let rec pw_disj acc = function
              | _ :: [] 
              | [] -> acc
              | d1 :: dcs -> 
                 (*pw_disj (empty_t (FormUtil.mk_inter [d1; FormUtil.mk_union dcs]) :: acc) dcs *)
                 pw_disj (List.map (fun d2 -> empty_t (FormUtil.mk_inter [d2; d1])) dcs @ acc) dcs
            in pw_disj [] dsc
          in
          let heap_part = separation1 :: translated_2 in
          let struct_part = 
            match f with
            | SepStar _ -> FormUtil.smk_and (separation2 @ translated_1) 
            | SepPlus _ -> FormUtil.smk_and translated_1
            | _ -> failwith "impossible"
          in
          ((struct_part, mk_loc_set_var domain) :: otranslated_1, heap_part)
        in 
        let struct_part, heap_part = List.fold_left process ([], translated_2) translated_product in
        struct_part, FormUtil.smk_and heap_part
    | Or forms ->
        let translated_1, translated_2 = List.split (List.map (process_sep pol d) forms) in
        List.concat translated_1, FormUtil.smk_and translated_2
    | other -> failwith ("process_sep does not expect " ^ (string_of_form other))
  in

  let rec process_bool pol f = match f with
    | And forms ->
      let translated = List.map (process_bool pol) forms in
      let (translated_1, translated_2) = List.split translated in
        (FormUtil.smk_and translated_1, FormUtil.smk_and translated_2)
    | Or forms ->
      let translated = List.map (process_bool pol) forms in
      let (translated_1, translated_2) = List.split translated in
        (FormUtil.smk_or translated_1, FormUtil.smk_and translated_2)
    | Not form ->
      let (structure, heap) = process_bool (not pol) form in
        (FormUtil.mk_not structure, heap)
    | sep ->
      let d' = FormUtil.fresh_ident "X" in
      let struct_part, heap_part = process_sep pol d' sep in
      let process (str, d) = FormUtil.mk_and [str; set_fct d domain]
      in
      FormUtil.smk_or (List.map process struct_part), heap_part
  in
  process_bool true (fresh_existentials f)

let post_process f =
  let _ = if !Debug.verbose then
    begin
      print_endline "Sl.to_grass(raw): ";
      Form.print_form stdout f;
      print_newline ()
    end
  in
  let aux_sets = List.map (fun v -> (v, Form.Set Form.Loc)) (IdSet.elements (FormUtil.fv f)) in
  FormUtil.mk_exists aux_sets (FormUtil.nnf f)

let to_grass pred_to_form domain f =
  let (pointers, separations) = to_form pred_to_form FormUtil.mk_eq domain f in
    post_process (FormUtil.smk_and [pointers; separations])

let to_grass_contained pred_to_form domain f = (* same structure and footprint not larger *)
  let (pointers, separations) = to_form pred_to_form FormUtil.mk_subseteq domain f in
    post_process (FormUtil.smk_and [pointers; separations])

let to_grass_not_contained pred_to_form domain f = (* different structure or larger footprint *)
  let (pointers, separations) = to_form pred_to_form FormUtil.mk_subseteq domain (mk_not f) in
    post_process (FormUtil.smk_and [pointers; separations])

let to_grass_negated pred_to_form domain f =
  let (pointers, separations) = to_form pred_to_form FormUtil.mk_eq domain (mk_not f) in
    post_process (FormUtil.smk_and [pointers; separations])
