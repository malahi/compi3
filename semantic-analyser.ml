(* tag-parser.ml
 * A compiler from Scheme to CISC
 *
 * Programmer: Mayer Goldberg, 2018
 *)

#use "tag-parser.ml";;

type var = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | Const' of constant
  | Var' of var
  | Box' of var
  | BoxGet' of var
  | BoxSet' of var * expr'
  | If' of expr' * expr' * expr'
  | Seq' of expr' list
  | Set' of expr' * expr'
  | Def' of expr' * expr'
  | Or' of expr' list
  | LambdaSimple' of string list * expr'
  | LambdaOpt' of string list * string * expr'
  | Applic' of expr' * (expr' list)
  | ApplicTP' of expr' * (expr' list);;

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | Const' Void, Const' Void -> true
  | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
  | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
  | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                            (expr'_eq th1 th2) &&
                                              (expr'_eq el1 el2)
  | (Seq'(l1), Seq'(l2)
  | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
  | (Set'(var1, val1), Set'(var2, val2)
  | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq var1 var2) &&
                                             (expr'_eq val1 val2)
  | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr'_eq body1 body2)
  | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr'_eq body1 body2)
  | Applic'(e1, args1), Applic'(e2, args2)
  | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
	 (expr'_eq e1 e2) &&
	   (List.for_all2 expr'_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;

(* module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
end;;

module Semantics : SEMANTICS = struct *)

let rec find_element x l =
  match l with
  | [] -> -1
  | h :: t -> if x = h then 0 else 1 + find_element x t;;

let param_bound_index param_l p =
  match List.filter (fun x -> List.length (List.filter (fun y -> y = p) x) > 0) param_l with
  | [] -> (-1 , -1)
  | l ->  ((find_element (List.hd l) param_l) - 1 ,  find_element p (List.hd l))

let rec sem_helper param_l expr = 
  let nested = fun () ->
  try sem_const expr
  with X_syntax_error -> try sem_var param_l expr 
  with X_syntax_error -> raise X_syntax_error in
  nested ()

and sem_const = function
  | Const (x) -> Const' (x)
  | _ -> raise X_syntax_error

and sem_var param_l expr =
  match expr with
  | Var(x) -> (match (param_bound_index param_l x) with
              | (-1  , -1)  -> Var'(VarFree(x))
              | (-1  , p_i) -> Var'(VarParam(x , p_i))
              | (b_i , p_i) -> Var'(VarBound(x , b_i , p_i)))
 
  | _ -> raise X_syntax_error

and sem_if param_l = function
  | If(test , dit , dif) -> If'((sem_helper param_l test) , (sem_helper param_l dit) , (sem_helper param_l dif))
  | _ -> raise X_syntax_error

and sem_seq param_l = function
  | Seq(expr_l) -> Seq'(List.map (sem_helper param_l) expr_l)
  | _ -> raise X_syntax_error
  
and sem_lambda param_l = function
  | LambdaSimple(p_l , body) -> LambdaSimple'(p_l , (sem_helper (p_l :: param_l) body))
  | _ -> raise X_syntax_error

and sem_set param_l = function
  | Set(var , expr) -> Set'((sem_helper param_l var) , (sem_helper param_l expr))
  | _ -> raise X_syntax_error
  
and sem_def param_l = function
  | Def(var , expr) -> Def'((sem_helper param_l var) , (sem_helper param_l expr))
  | _ -> raise X_syntax_error
  
and sem_or param_l = function
  | Or(expr_l) -> Or'(List.map (sem_helper param_l) expr_l)
  | _ -> raise X_syntax_error

and sem_lambdaopt param_l = function
  | LambdaOpt(p_l , p_last , body) -> LambdaOpt'(p_l , p_last , (sem_helper ((List.append p_l [p_last]) :: param_l) body))
  | _ -> raise X_syntax_error

and sem_applic param_l = function
  | Applic(proc , p_l) -> Applic'((sem_helper param_l proc) , (List.map (sem_helper param_l) p_l))
  | _ -> raise X_syntax_error;;

let annotate_lexical_addresses e = raise X_not_yet_implemented;;

let annotate_tail_calls e = raise X_not_yet_implemented;;

let box_set e = raise X_not_yet_implemented;;

let run_semantics expr =
  box_set
    (annotate_tail_calls
       (annotate_lexical_addresses expr));;
  
(* end;;  *)
(* struct Semantics *)
