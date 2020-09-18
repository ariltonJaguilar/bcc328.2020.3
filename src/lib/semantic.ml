(* semantic.ml *)

module A = Absyn
module S = Symbol
module T = Type

type entry = [%import: Env.entry]
type env = [%import: Env.env]

(* Obtain the location of an ast *)

let loc = Location.loc

(* Reporting errors *)

let undefined loc category id =
  Error.error loc "undefined %s %s" category (S.name id)

let misdefined loc category id =
  Error.error loc "%s is not a %s" (S.name id) category

let type_mismatch loc expected found =
  Error.error loc "type mismatch: expected %s, found %s" (T.show_ty expected) (T.show_ty found)

(* Searhing in symbol tables *)

let look env category id pos =
  match S.look id env with
  | Some x -> x
  | None -> undefined pos category id

let tylook tenv id pos =
  look tenv "type" id pos

let varlook venv id pos =
  match look venv "variable" id pos with
  | VarEntry t -> t
  | FunEntry _ -> misdefined pos "variable" id

let funlook venv id pos =
  match look venv "function" id pos with
  | VarEntry _ -> misdefined pos "function" id
  | FunEntry (params, result) -> (params, result)

(* Type compatibility *)

let compatible ty1 ty2 pos =
  if not (T.coerceable ty1 ty2) then
    type_mismatch pos ty2 ty1

(* Set the value in a reference of optional *)

let set reference value =
  reference := Some value;
  value

(* Checking expressions *)

let rec check_exp env (pos, (exp, tref)) =
  match exp with
  | A.BoolExp _ -> set tref T.BOOL
  | A.IntExp  _ -> set tref T.INT
  | A.RealExp _ -> set tref T.REAL
  | A.StringExp _ -> set tref T.STRING
  | A.LetExp (decs, body) -> check_exp_let env pos tref decs body
  | A.BinaryExp (leftexp, opr, rightexp) -> check_exp_bin env pos tref leftexp opr rightexp
  | A.NegativeExp (exp) -> check_exp_negation env pos tref exp
  | A.ExpSeq seqexp -> check_exp_sequence env pos tref seqexp
  | A.IfExp (cond, ex, oth) -> check_exp_conditional env pos tref cond ex oth
  | A.WhileExp (cond, ex) -> check_exp_while env pos tref cond ex
  | A.BreakExp -> check_exp_break env pos tref 
  | _ -> Error.fatal "unimplemented"

(* Checking break condition *)

and check_exp_break env pos tref =
  match env.inloop with 
    | true -> set tref T.VOID  
    | _ -> Error.error pos "breaking outside a conditional loop"

(* Checking loop expressions *)

and check_exp_while env pos tref cond exec =
  let env' = {env with inloop = true} in
  ignore(check_exp env' cond); ignore(check_exp env' exec); set tref T.VOID

(* Checking conditional expressions *)

and check_exp_conditional env pos tref cond exec oth =
  let cond' = check_exp env cond in
    match cond' with
      | T.BOOL -> let exec' = check_exp env exec in
        match oth with 
          | Some lexp -> let oth' = check_exp env lexp in
            compatible exec' oth' pos ; 
            set tref exec'
          | None -> set tref T.VOID
      | _ -> type_mismatch pos T.BOOL cond'



(* Checking sequence expressions *)

and check_exp_sequence env pos tref seqexp =
  let seqexp' = breakexp_loop env seqexp in set tref seqexp'

and breakexp_loop env seqexp =
  match seqexp with
    | []   -> T.VOID
    | [exp]  -> check_exp env exp
    | first::second -> ignore(check_exp env first); breakexp_loop env second 

(* Checking negation operators *)

and check_exp_negation env pos tref exp = 
  let exp' = check_exp env exp in
    match exp' with
      | T.INT | T.REAL -> set tref exp'
      | _ -> type_mismatch pos T.REAL exp'

(* Checking binary operators *)

and check_exp_bin env pos tref leftexp opr rightexp =
  let leftexp' = check_exp env leftexp in
  let rightexp' = check_exp env rightexp in
    match opr with
      | A.Plus | A.Minus | A.Div | A.Times | A.Mod | A.Power ->
        begin match leftexp', rightexp' with
          | T.INT, T.REAL | T.REAL, T.INT | T.REAL, T.REAL  -> set tref  T.REAL
          | T.INT, T.INT                                    -> set tref T.INT
          | _                                               -> type_mismatch pos leftexp' rightexp'
        end 
      (* equality operators *)
      | A.Equal | A.NotEqual -> compatible leftexp' rightexp' pos; set tref T.BOOL
      (* relational operators *)
      | A.GreaterThan | A.LowerThan | A.GreaterEqual | A.LowerEqual ->
        begin match leftexp' with
          | T.INT    -> (match rightexp' with T.INT    -> set tref T.BOOL | _ -> type_mismatch pos T.INT rightexp')
          | T.REAL   -> (match rightexp' with T.REAL   -> set tref T.BOOL | _ -> type_mismatch pos T.REAL rightexp')
          | T.STRING -> (match rightexp' with T.STRING -> set tref T.BOOL | _ -> type_mismatch pos T.STRING rightexp')
        end 
      (* logical operators *)
      | A.And | A.Or ->
        begin match leftexp', rightexp' with
          | T.BOOL, T.BOOL -> set tref T.BOOL
          | _ -> (match leftexp' with  T.BOOL -> type_mismatch pos T.BOOL rightexp' | _ -> type_mismatch pos T.BOOL leftexp')
        end
      | _ -> Error.fatal "unimplemented"

and check_exp_let env pos tref decs body =
  let env' = List.fold_left check_dec env decs in
  let tbody = check_exp env' body in
  set tref tbody

(* Checking declarations *)

and check_dec_var env pos ((name, type_opt, init), tref) =
  let tinit = check_exp env init in
  let tvar =
    match type_opt with
    | Some tname ->
       let t = tylook env.tenv tname pos in
       compatible tinit t (loc init);
       t
    | None -> tinit
  in
  ignore (set tref tvar);
  let venv' = S.enter name (VarEntry tvar) env.venv in
  {env with venv = venv'}

and check_dec env (pos, dec) =
  match dec with
  | A.VarDec x -> check_dec_var env pos x
  | _ -> Error.fatal "unimplemented"

let semantic program =
  check_exp Env.initial program
