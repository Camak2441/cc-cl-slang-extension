open Past 

let complain = Errors.complain

let internal_error msg = complain ("INTERNAL ERROR: " ^ msg) 

let report_expecting e msg t = 
    let loc = loc_of_expr e in 
    let loc_str = string_of_loc loc in 
    let e_str = string_of_expr e in 
    let t_str = string_of_type t in 
    complain ("ERROR at location " ^ 
	      loc_str ^ "\nExpression " ^ e_str ^ 
	      "\nhas type " ^ t_str ^ ", but expecting " ^ msg) 

let report_types_not_equal loc t1 t2 = 
    let loc_str = string_of_loc loc in 
    let t1_str = string_of_type t1 in 
    let t2_str = string_of_type t2 in 
    complain ("Error near location " ^ loc_str ^ 
              "\nExpecting type " ^ t1_str ^ " to be equal to type " ^ t2_str)

let report_type_mismatch (e1, t1) (e2, t2) = 
    let loc1 = loc_of_expr e1 in 
    let loc2 = loc_of_expr e2 in 
    let loc1_str = string_of_loc loc1 in 
    let loc2_str = string_of_loc loc2 in 
    let e1_str = string_of_expr e1 in 
    let e2_str = string_of_expr e2 in 
    let t1_str = string_of_type t1 in 
    let t2_str = string_of_type t2 in 
    complain ("ERROR, Type Mismatch: expecting equal types, however\n" ^ 
	      "at location " ^ loc1_str ^ "\nexpression " ^ e1_str ^ "\nhas type " ^ t1_str ^ 
	      " and at location " ^ loc2_str ^ "\nexpression " ^ e2_str ^ "\nhas type " ^ t2_str)

let rec find loc x = function 
  | [] -> complain (x ^ " is not defined at " ^ (string_of_loc loc)) 
  | (y, v) :: rest -> if x = y then v else find loc x rest


(* may want to make this more interesting someday ... *) 
let match_types (t1, t2) = (t1 = t2) 

let strict loc t1 (e2, t2) = match t2 with
    | TEthunk t2' -> if match_types (t1, t2') then Strict(loc, e2) else report_types_not_equal loc t1 t2'
    | _   -> if match_types (t1, t2) then e2 else report_types_not_equal loc t1 t2

let contain loc t1 (e2, t2) = match (t1, t2) with
    | TEthunk t1', TEthunk t2' -> 
        if match_types (t1', t2') 
        then e2
        else report_types_not_equal loc t1 t2
    | TEthunk t1', _ -> 
        if match_types (t1', t2) 
        then StrictThunk(loc, e2)
        else report_types_not_equal loc t1' t2
    | _, TEthunk t2' -> 
        if match_types (t1, t2') 
        then Strict(loc, e2)
        else report_types_not_equal loc t1 t2'
    | _, _ -> 
        if match_types (t1, t2) 
        then e2
        else report_types_not_equal loc t1 t2

let infer_contain loc t1 (e2, t2) = match (t1, t2) with
| TEthunk t1', TEthunk t2' -> 
    if match_types (t1', t2') 
    then (e2, t1)
    else report_types_not_equal loc t1 t2
| TEthunk t1', _ -> 
    if match_types (t1', t2) 
    then (StrictThunk(loc, e2), t1)
    else report_types_not_equal loc t1' t2
| _, TEthunk t2' -> 
    if match_types (t1, t2') 
    then (Strict(loc, e2), t1)
    else report_types_not_equal loc t1 t2'
| _, _ -> 
    if match_types (t1, t2) 
    then (e2, t1)
    else report_types_not_equal loc t1 t2
    
let make_strict loc (e, t) = match t with
    | TEthunk t' -> (Strict(loc, e), t')
    | _ -> (e, t)

let make_uop loc uop (e, t) = 
    match uop, t with 
    | NEG, TEint  -> (UnaryOp(loc, uop, e), t) 
    | NEG, TEthunk TEint -> (UnaryOp(loc, uop, Strict(loc, e)), t) 
    | NEG, _      -> report_expecting e "integer" t
    | NOT, TEbool -> (UnaryOp(loc, uop, e), t) 
    | NOT, TEthunk TEbool -> (UnaryOp(loc, uop, Strict(loc, e)), t)  
    | NOT, _      -> report_expecting e "boolean" t

    | HEAD, TEthunk (TElist (t', _)) -> (UnaryOp(loc, uop, Strict(loc, e)), t')
    | HEAD, TElist (t', _) -> (UnaryOp(loc, uop, e), t')
    | HEAD, _ -> report_expecting e "list" t

    | TAIL, TElist (t', true) -> (UnaryOp(loc, uop, e), TEthunk (TElist (t', true)))
    | TAIL, TElist (t', false) -> (UnaryOp(loc, uop, e), (TElist (t', false)))
    | TAIL, TEthunk (TElist (t', true)) -> (UnaryOp(loc, uop, Strict(loc, e)), TEthunk (TElist (t', true)))
    | TAIL, TEthunk (TElist (t', false)) -> (UnaryOp(loc, uop, Strict(loc, e)), (TElist (t', false)))
    | TAIL, _ -> report_expecting e "list" t

let rec make_bop loc bop (e1, t1) (e2, t2) = 
    match bop, t1, t2 with 
    | LT,  TEthunk TEint, t   -> make_bop loc bop (make_strict loc (e1, t1)) (e2, t2)
    | LT,  t, TEthunk TEint   -> make_bop loc bop (e1, t1) (make_strict loc (e2, t2))
    | LT,  TEint,  TEint  -> (Op(loc, e1, bop, e2), TEbool)
    | LT,  TEint,  t      -> report_expecting e2 "integer" t
    | LT,  t,      _      -> report_expecting e1 "integer" t
    | ADD, TEthunk TEint, t   -> make_bop loc bop (make_strict loc (e1, t1)) (e2, t2)
    | ADD, t, TEthunk TEint   -> make_bop loc bop (e1, t1) (make_strict loc (e2, t2))
    | ADD, TEint,  TEint  -> (Op(loc, e1, bop, e2), t1) 
    | ADD, TEint,  t      -> report_expecting e2 "integer" t
    | ADD, t,      _      -> report_expecting e1 "integer" t
    | SUB, TEthunk TEint, t   -> make_bop loc bop (make_strict loc (e1, t1)) (e2, t2)
    | SUB, t, TEthunk TEint   -> make_bop loc bop (e1, t1) (make_strict loc (e2, t2))
    | SUB, TEint,  TEint  -> (Op(loc, e1, bop, e2), t1) 
    | SUB, TEint,  t      -> report_expecting e2 "integer" t
    | SUB, t,      _      -> report_expecting e1 "integer" t
    | MUL, TEthunk TEint, t   -> make_bop loc bop (make_strict loc (e1, t1)) (e2, t2)
    | MUL, t, TEthunk TEint   -> make_bop loc bop (e1, t1) (make_strict loc (e2, t2))
    | MUL, TEint,  TEint  -> (Op(loc, e1, bop, e2), t1) 
    | MUL, TEint,  t      -> report_expecting e2 "integer" t
    | MUL, t,      _      -> report_expecting e1 "integer" t
    | DIV, TEthunk TEint, t   -> make_bop loc bop (make_strict loc (e1, t1)) (e2, t2)
    | DIV, t, TEthunk TEint   -> make_bop loc bop (e1, t1) (make_strict loc (e2, t2))
    | DIV, TEint,  TEint  -> (Op(loc, e1, bop, e2), t1) 
    | DIV, TEint,  t      -> report_expecting e2 "integer" t
    | DIV, t,      _      -> report_expecting e1 "integer" t
    | OR,  TEthunk TEbool, t   -> make_bop loc bop (make_strict loc (e1, t1)) (e2, t2)
    | OR,  t, TEthunk TEbool   -> make_bop loc bop (e1, t1) (make_strict loc (e2, t2))
    | OR,  TEbool, TEbool -> (Op(loc, e1, bop, e2), t1) 
    | OR,  TEbool,  t     -> report_expecting e2 "boolean" t
    | OR,  t,      _      -> report_expecting e1 "boolean" t
    | AND, TEthunk TEbool, t   -> make_bop loc bop (make_strict loc (e1, t1)) (e2, t2)
    | AND, t, TEthunk TEbool   -> make_bop loc bop (e1, t1) (make_strict loc (e2, t2))
    | AND, TEbool, TEbool -> (Op(loc, e1, bop, e2), t1) 
    | AND, TEbool,  t     -> report_expecting e2 "boolean" t
    | AND, t,      _      -> report_expecting e1 "boolean" t
    | CONS, t1', TEthunk (TElist (t2', false)) -> (Op(loc, contain loc t2' (e1, t1), bop, Strict(loc, e2)), TElist (t2', false))
    | CONS, t1', TEthunk (TElist (t2', true)) -> (Op(loc, contain loc t2' (e1, t1), bop, e2), TElist (t2', true))
    | CONS, t1', TEthunk (TEempty) -> (Op(loc, e1, bop, e2), TElist (t1, true))
    | CONS, t1', (TElist (t2', false)) -> (Op(loc, contain loc t2' (e1, t1), bop, e2), TElist (t2', false))
    | CONS, t1', (TElist (t2', true)) -> (Op(loc, contain loc t2' (e1, t1), bop, StrictThunk(loc, e2)), TElist (t2', true))
    | CONS, t1', (TEempty) -> (Op(loc, e1, bop, e2), TElist (t1, false))
    | CONS, _, _ -> report_expecting e2 "list or empty" t2
    | EQ,  TEthunk _, t   -> make_bop loc bop (make_strict loc (e1, t1)) (e2, t2)
    | EQ,  t, TEthunk _   -> make_bop loc bop (e1, t1) (make_strict loc (e2, t2))
    | EQ,  TEbool, TEbool -> (Op(loc, e1, EQB, e2), t1) 
    | EQ,  TEint,  TEint  -> (Op(loc, e1, EQI, e2), TEbool)  
    | EQ,  _,      _      -> report_type_mismatch (e1, t1) (e2, t2) 
    | EQI, _, _           -> internal_error "EQI found in parsed AST"
    | EQB, _, _           -> internal_error "EQB found in parsed AST"

let make_lazy loc (e, t) = match t with
    | TEthunk _ -> (e, t) 
    | _ -> (Lazy(loc, e), TEthunk t)

let make_pair loc (e1, t1) (e2, t2)  = (Pair(loc, e1, e2), TEproduct(t1, t2))
let make_inl loc t2 (e, t1)          = (Inl(loc, t2, e), TEunion(t1, t2))
let make_inr loc t1 (e, t2)          = (Inr(loc, t1, e), TEunion(t1, t2))
let make_lambda loc x t1 (e, t2)     = (Lambda(loc, (x, t1, e)), TEarrow(t1, t2))
let make_ref loc (e, t)              = (Ref(loc, e), TEref t)
let make_letfun loc f x t1 (body, t2) t2' (e, t)    = (LetFun(loc, f, (x, t1, contain loc t2' (body, t2)), t2, e), t)
let make_letrecfun loc f x t1 (body, t2) t2' (e, t) = (LetRecFun(loc, f, (x, t1, contain loc t2' (body, t2)), t2, e), t)

let make_let loc x t (e1, t1) (e2, t2)  = (Let(loc, x, t, contain loc t (e1, t1), e2), t2)

let make_if loc (e1, t1) (e2, t2) (e3, t3) = match t2, t3 with
    | TEthunk t2', TEthunk t3' -> if (match_types (t2', t3')) then
        (If(loc, strict loc TEbool (e1, t1), e2, e3), t2)
        else report_type_mismatch (e2, t2) (e3, t3) 
    | TEthunk t2', t3' -> if (match_types (t2', t3')) then
        (If(loc, strict loc TEbool (e1, t1), e2, StrictThunk(loc, e3)), t2)
        else report_type_mismatch (e2, t2) (e3, t3) 
    | t2', TEthunk t3' -> if (match_types (t2', t3')) then
        (If(loc, strict loc TEbool (e1, t1), StrictThunk(loc, e2), e3), t3)
        else report_type_mismatch (e2, t2) (e3, t3) 
    | t2', t3' -> if (match_types (t2', t3')) then
        (If(loc, strict loc TEbool (e1, t1), e2, e3), t2)
        else report_type_mismatch (e2, t2) (e3, t3) 

let make_fst loc = function 
  | (e, TEproduct(t, _)) -> (Fst(loc, e), t) 
  | (e, t) -> report_expecting e "product" t

let make_snd loc = function 
  | (e, TEproduct(_, t)) -> (Snd(loc, e), t) 
  | (e, t) -> report_expecting e "product" t

let make_deref loc (e, t) = 
    match t with 
    | TEref t' -> (Deref(loc, e), t') 
    | TEthunk (TEref t')-> (Deref(loc, Strict(loc, e)), t')
    | _ -> report_expecting e "ref type" t

let make_app loc (e1, t1) (e2, t2) = 
    match t1 with 
    | TEarrow(t3, t4) -> (App(loc, e1, contain loc t3 (e2, t2)), t4)
    | TEthunk (TEarrow(t3, t4)) -> (App(loc, Strict(loc, e1), contain loc t3 (e2, t2)), t4)
    | _ -> report_expecting e1 "function type" t1

let make_while loc (e1, t1) (e2, t2) = if t2 = TEunit
    then (While(loc, strict loc TEbool (e1, t1), e2), TEunit)
    else report_expecting e2 "unit type" t2

let rec make_assign loc (e1, t1) (e2, t2) = match t1 with
    | TEref t -> (Assign(loc, e1, contain loc t (e2, t2)), TEunit)
    | TEthunk TEref t -> make_assign loc (make_strict loc (e1, t1)) (e2, t2)
    | t -> report_expecting e1 "ref type" t 

let rec make_case loc left right x1 x2 (e1, t1) (e2, t2) (e3, t3) = 
    match t1 with 
    | TEunion(left', right') -> 
      if match_types(left, left') 
      then if match_types(right, right')
           then if match_types(t3, t2)
                then (Case(loc, e1, (x1, left, e2), (x2, right, e3)), t2)
                else report_type_mismatch (e2, t2) (e3, t3)
           else report_types_not_equal loc right right'
      else report_types_not_equal loc left left' 
    | TEthunk (TEunion _) -> make_case loc left right x1 x2 (make_strict loc (e1, t1)) (e2, t2) (e3, t3)
    | t -> report_expecting e1 "disjoint union" t

let rec type_of_param_list l t = match l with
    | [] -> t
    | (_, tx) :: l -> TEarrow (tx, type_of_param_list l t)

let rec infer env e = 
    match e with 
    | Unit _               -> (e, TEunit)
    | What _               -> (e, TEint) 
    | Empty _              -> (e, TEempty)
    | Integer _            -> (e, TEint) 
    | Boolean _            -> (e, TEbool)
    | Var(loc, x)         -> (e, find loc x env)
    | Seq(loc, el)         -> infer_seq loc env el 
    | While(loc, e1, e2)   -> make_while loc (infer_tar env e1 TEbool) (infer_tar env e2 TEunit) 
    | Ref(loc, e)          -> make_ref loc (infer env e) 
    | Deref(loc, e)        -> make_deref loc (infer env e) 
    | Assign(loc, e1, e2)  -> make_assign loc (infer env e1) (infer env e2) 
    | UnaryOp(loc, uop, e) -> (match uop with 
    | NEG -> make_uop loc uop (infer_tar env e TEint)
    | NOT -> make_uop loc uop (infer_tar env e TEbool)
    | _ -> make_uop loc uop (infer env e))
    | Op(loc, e1, bop, e2) -> (match bop with
        | ADD -> make_bop loc bop (infer_tar env e1 TEint) (infer_tar env e2 TEint)
        | SUB -> make_bop loc bop (infer_tar env e1 TEint) (infer_tar env e2 TEint)
        | MUL -> make_bop loc bop (infer_tar env e1 TEint) (infer_tar env e2 TEint)
        | DIV -> make_bop loc bop (infer_tar env e1 TEint) (infer_tar env e2 TEint)
        | LT -> make_bop loc bop (infer_tar env e1 TEint) (infer_tar env e2 TEint)
        | EQ -> (try make_bop loc bop (infer_tar env e1 TEint) (infer_tar env e2 TEint)
            with _ -> make_bop loc bop (infer_tar env e1 TEbool) (infer_tar env e2 TEbool))
        | OR -> make_bop loc bop (infer_tar env e1 TEbool) (infer_tar env e2 TEbool)
        | AND -> make_bop loc bop (infer_tar env e1 TEbool) (infer_tar env e2 TEbool)
        | _ -> make_bop loc bop (infer env e1) (infer env e2))
    | If(loc, e1, e2, e3)  -> make_if loc (infer_tar env e1 TEbool) (infer env e2) (infer env e3)          
    | Pair(loc, e1, e2)    -> make_pair loc (infer env e1) (infer env e2) 
    | Fst(loc, e)          -> make_fst loc (infer env e)
    | Snd (loc, e)         -> make_snd loc (infer env e)
    | Inl (loc, t, e)      -> make_inl loc t (infer env e)
    | Inr (loc, t, e)      -> make_inr loc t (infer env e) 
    | Case(loc, e, (x1, t1, e1), (x2, t2, e2)) ->  
            make_case loc t1 t2 x1 x2 (infer env e) (infer ((x1, t1) :: env) e1) (infer ((x2, t2) :: env) e2)
    | Lambda (loc, (x, t, e)) -> make_lambda loc x t (infer ((x, t) :: env) e)
    | MultiLambda (loc, ((x, t) :: l, e)) -> make_lambda loc x t (infer ((x, t) :: env) (MultiLambda (loc, (l, e))))
    | MultiLambda (loc, ([], e)) -> infer env e
    | App(loc, e1, e2)        -> make_app loc (infer env e1) (infer env e2)
    | Let(loc, x, t, e1, e2)  -> make_let loc x t (infer_tar env e1 t) (infer ((x, t) :: env) e2) 
    | LetFun(loc, f, (x, t1, body), t2, e) -> 
      let env1 = (f, TEarrow(t1, t2)) :: env in 
      let p = infer env1 e in 
      let env2 = (x, t1) :: env in 
         (try make_letfun loc f x t1 (infer_tar env2 body t2) t2 p 
          with _ -> let env3 = (f, TEarrow(t1, t2)) :: env2 in 
                        make_letrecfun loc f x t1 (infer_tar env3 body t2) t2 p 
         )
    | LetMultiFun(loc, f, ((x, t1) :: l, body), tb, e) -> 
      let t2 =  type_of_param_list l tb in
      let env1 = (f, TEarrow(t1, t2)) :: env in 
      let p = infer env1 e in 
      let env2 = (x, t1) :: env in 
         (try make_letfun loc f x t1 (infer_tar env2 (MultiLambda (loc, (l, body))) t2) t2 p 
         with _ -> let env3 = (f, TEarrow(t1, t2)) :: env2 in 
                        make_letrecfun loc f x t1 (infer_tar env3 (MultiLambda (loc, (l, body))) t2) t2 p 
         )
    | LetMultiFun(_, _, ([], _), _, _) -> internal_error "Argumentless LetMultiFun"
    | LetRecFun(_, _, _, _, _)  -> internal_error "LetRecFun found in parsed AST" 
    | Lazy(loc, e) -> make_lazy loc (infer env e)
    | Strict(loc, e) -> make_strict loc (infer env e)
    | StrictThunk(loc, e) -> internal_error "StrictThunk found in parsed AST" 
      
and infer_seq loc env el = 
    let rec aux carry = function 
      | []        -> internal_error "empty sequence found in parsed AST" 
      | [e]       -> let (e', t) = infer env e in (Seq(loc, List.rev (e' :: carry )), t)
      | e :: rest -> let (e', _) = infer env e in aux (e' :: carry) rest 
    in aux [] el 
      
and infer_seq_tar loc env el tar = 
    let rec aux carry = function 
      | []        -> internal_error "empty sequence found in parsed AST" 
      | [e]       -> let (e', t) = infer_tar env e tar in (Seq(loc, List.rev (e' :: carry )), tar)
      | e :: rest -> let (e', _) = infer env e in aux (e' :: carry) rest 
    in aux [] el 

and infer_tar env e tar = 
    match e with
    | Unit loc             -> infer_contain loc tar (e, TEunit)
    | What loc             -> infer_contain loc tar (e, TEint)
    | Empty loc            -> infer_contain loc tar (e, TEempty)
    | Integer (loc, _)     -> infer_contain loc tar (e, TEint)
    | Boolean (loc, _)     -> infer_contain loc tar (e, TEbool)
    | Var (loc, x)         -> infer_contain loc tar (e, find loc x env)
    | Seq(loc, el)         -> infer_seq_tar loc env el tar
    | While(loc, e1, e2)   -> infer_contain loc tar (make_while loc (infer_tar env e1 TEbool) (infer_tar env e2 TEunit))
    | Ref(loc, e)          -> infer_contain loc tar (match tar with 
                                | TEref t -> infer_contain loc tar (make_ref loc (infer_tar env e t))
                                | TEthunk (TEref t) -> infer_contain loc tar (make_ref loc (infer_tar env e t))
                                | t -> report_expecting e "reference" t)
    | Deref(loc, e)        -> infer_contain loc tar (match tar with
                                | TEthunk t -> (try make_deref loc (infer_tar env e (TEref tar))
                                    with _ -> infer_contain loc tar (make_deref loc (infer_tar env e (TEref t))))
                                | t -> (try make_deref loc (infer_tar env e (TEref tar))
                                    with _ -> infer_contain loc tar (make_deref loc (infer_tar env e (TEref (TEthunk t))))))
    | Assign(loc, e1, e2)  -> let (e1', t1) = infer env e1 in
        (match t1 with
            | TEref(t1') -> infer_contain loc tar (make_assign loc (e1', t1) (infer_tar env e2 t1'))
            | TEthunk(TEref(t1')) -> infer_contain loc tar (make_assign loc (Strict(loc, e1'), TEref(t1')) (infer_tar env e2 t1'))
            | _ -> report_expecting e1 "reference" t1)
    | UnaryOp(loc, uop, e) -> (match uop with 
        | NEG -> infer_contain loc tar (make_uop loc uop (infer_tar env e TEint))
        | NOT -> infer_contain loc tar (make_uop loc uop (infer_tar env e TEbool))
        | _ -> infer_contain loc tar (make_uop loc uop (infer env e)))
    | Op(loc, e1, bop, e2) -> (match bop with
        | ADD -> infer_contain loc tar (make_bop loc bop (infer_tar env e1 TEint) (infer_tar env e2 TEint))
        | SUB -> infer_contain loc tar (make_bop loc bop (infer_tar env e1 TEint) (infer_tar env e2 TEint))
        | MUL -> infer_contain loc tar (make_bop loc bop (infer_tar env e1 TEint) (infer_tar env e2 TEint))
        | DIV -> infer_contain loc tar (make_bop loc bop (infer_tar env e1 TEint) (infer_tar env e2 TEint))
        | LT -> infer_contain loc tar (make_bop loc bop (infer_tar env e1 TEint) (infer_tar env e2 TEint))
        | EQ -> (try infer_contain loc tar (make_bop loc bop (infer_tar env e1 TEint) (infer_tar env e2 TEint))
            with _ -> infer_contain loc tar (make_bop loc bop (infer_tar env e1 TEbool) (infer_tar env e2 TEbool)))
        | OR -> infer_contain loc tar (make_bop loc bop (infer_tar env e1 TEbool) (infer_tar env e2 TEbool))
        | AND -> infer_contain loc tar (make_bop loc bop (infer_tar env e1 TEbool) (infer_tar env e2 TEbool))
        | _ -> make_bop loc bop (infer env e1) (infer env e2))
    | If(loc, e1, e2, e3)  -> make_if loc (infer_tar env e1 TEbool) (infer_tar env e2 tar) (infer_tar env e3 tar)          
    | Pair(loc, e1, e2)    -> (match tar with 
        | TEproduct(t1, t2) -> make_pair loc (infer_tar env e1 t1) (infer_tar env e2 t2)
        | TEthunk(TEproduct(t1, t2)) -> infer_contain loc tar (make_pair loc (infer_tar env e1 t1) (infer_tar env e2 t2))
        | _ -> report_expecting e1 "product" tar) (* Currently not generating nice error messages *)
    | Fst(loc, e)          -> infer_contain loc tar (make_fst loc (infer env e))
    | Snd (loc, e)         -> infer_contain loc tar (make_snd loc (infer env e))
    | Inl (loc, t, e)      -> infer_contain loc tar (make_inl loc t (infer env e))
    | Inr (loc, t, e)      -> infer_contain loc tar (make_inr loc t (infer env e))
    | Case(loc, e, (x1, t1, e1), (x2, t2, e2)) ->  
            make_case loc t1 t2 x1 x2 (infer env e) (infer ((x1, t1) :: env) e1) (infer ((x2, t2) :: env) e2)
    | Lambda (loc, (x, t, e)) -> (match tar with
        | TEarrow (t1, t2) -> if match_types(t, t1) 
            then infer_contain loc tar (make_lambda loc x t (infer_tar ((x, t) :: env) e t2))
            else report_expecting e "lambda argument" t
        | TEthunk (TEarrow (t1, t2)) -> if match_types(t, t1) 
            then infer_contain loc tar (make_lambda loc x t (infer_tar ((x, t) :: env) e t2))
            else report_expecting e "lambda argument" t
        | _ -> report_expecting e "lambda" t)
    | MultiLambda (loc, ((x, t) :: l, e)) -> (match tar with
        | TEarrow (t1, t2) -> if match_types(t, t1) 
            then infer_contain loc tar (make_lambda loc x t (infer_tar ((x, t) :: env) (MultiLambda (loc, (l, e))) t2))
            else report_expecting e "lambda argument" t
        | TEthunk (TEarrow (t1, t2)) -> if match_types(t, t1) 
            then infer_contain loc tar (make_lambda loc x t (infer_tar ((x, t) :: env) (MultiLambda (loc, (l, e))) t2))
            else report_expecting e "lambda argument" t
        | _ -> report_expecting e "lambda" t)
    | MultiLambda (loc, ([], e)) -> infer_tar env e tar
    | App(loc, e1, e2)        -> 
      let (f, tf) = infer env e1 in
      (match tf with
        | TEarrow (t1, t2) -> infer_contain loc tar (make_app loc (f, tf) (infer_tar env e2 t1))
        | TEthunk (TEarrow (t1, t2)) -> infer_contain loc tar (make_app loc (f, tf) (infer_tar env e2 t1))
        | _ -> report_expecting e "function" tf)
    | Let(loc, x, t, e1, e2)  -> make_let loc x t (infer_tar env e1 t) (infer_tar ((x, t) :: env) e2 tar) 
    | LetFun(loc, f, (x, t1, body), t2, e) -> 
      let env1 = (f, TEarrow(t1, t2)) :: env in 
      let p = infer_tar env1 e tar in 
      let env2 = (x, t1) :: env in 
         (try make_letfun loc f x t1 (infer_tar env2 body t2) t2 p 
          with _ -> let env3 = (f, TEarrow(t1, t2)) :: env2 in 
                        make_letrecfun loc f x t1 (infer_tar env3 body t2) t2 p 
         )
    | LetMultiFun(loc, f, ((x, t1) :: l, body), tb, e) ->
      let t2 =  type_of_param_list l tb in
      let env1 = (f, TEarrow(t1, t2)) :: env in 
      let p = infer_tar env1 e tar in 
      let env2 = (x, t1) :: env in 
         (try make_letfun loc f x t1 (infer_tar env2 (MultiLambda (loc, (l, body))) t2) t2 p 
          with _ -> let env3 = (f, TEarrow(t1, t2)) :: env2 in 
                        make_letrecfun loc f x t1 (infer_tar env3 (MultiLambda (loc, (l, body))) t2) t2 p 
         )
    | LetMultiFun(_, _, ([], _), _, _) -> internal_error "Argumentless LetMultiFun"
    | LetRecFun(_, _, _, _, _)  -> internal_error "LetRecFun found in parsed AST" 
    | Lazy(loc, e) -> (match tar with 
                        | TEthunk t -> make_lazy loc (infer_tar env e t)
                        | t -> infer_tar env e t)
    | Strict(loc, e) -> make_strict loc (infer env e)
    | StrictThunk(loc, e) -> internal_error "StrictThunk found in parsed AST" 

let env_init = [] 

let check e = 
    let (e', _) = infer env_init e 
    in e' 

