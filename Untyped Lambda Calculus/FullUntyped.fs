module FullUntyped.Main

(* ------------------------   EVALUATION  ------------------------ *)

exception NoRuleApplies

let rec isnumericval ctx = function
    | TmZero(_) -> true
    | TmSucc(_,t1) -> isnumericval ctx t1
    | _ -> false

/// Returns whether the val is in context.
let rec isval ctx = function
    | TmTrue(_)  -> true
    | TmFalse(_) -> true
    | TmFloat _  -> true
    | TmString _  -> true
    | t when isnumericval ctx t  -> true
    | TmAbs(_,_,_) -> true
    | TmRecord(_,fields) -> List.forall (fun (l,ti) -> isval ctx ti) fields
    | _ -> false

let rec eval1 ctx = function
    | TmIf(_,TmTrue(_),t2,t3) -> t2
    | TmIf(_,TmFalse(_),t2,t3) -> t3
    | TmIf(fi,t1,t2,t3) ->
        let t1' = eval1 ctx t1
        TmIf(fi, t1', t2, t3)
    | TmVar(fi,n,_) ->
        match getbinding fi ctx n with
        | TmAbbBind(t) -> t 
        | _ -> raise NoRuleApplies
    | TmApp(fi,TmAbs(_,x,t12),v2) when isval ctx v2 ->
        termSubstTop v2 t12
    | TmApp(fi,v1,t2) when isval ctx v1 ->
        let t2' = eval1 ctx t2
        TmApp(fi, v1, t2')
    | TmApp(fi,t1,t2) ->
        let t1' = eval1 ctx t1
        TmApp(fi, t1', t2)
    | TmRecord(fi,fields) ->
        let rec evalafield = function
            | [] -> raise NoRuleApplies
            | (l,vi)::rest when isval ctx vi -> 
                let rest' = evalafield rest
                (l,vi)::rest'
            | (l,ti)::rest -> 
                let ti' = eval1 ctx ti
                (l, ti')::rest
        let fields' = evalafield fields
        TmRecord(fi, fields')
    | TmProj(fi, (TmRecord(_, fields) as v1), l) when isval ctx v1 ->
        match List.tryFind (fun x -> fst x = l) fields with
        | Some x -> snd x
        | None -> raise NoRuleApplies
    | TmProj(fi, t1, l) ->
        let t1' = eval1 ctx t1
        TmProj(fi, t1', l)
    | TmTimesfloat(fi,TmFloat(_,f1),TmFloat(_,f2)) ->
        TmFloat(fi, f1 * f2)
    | TmTimesfloat(fi,(TmFloat(_,f1) as t1),t2) ->
        let t2' = eval1 ctx t2
        TmTimesfloat(fi,t1,t2') 
    | TmTimesfloat(fi,t1,t2) ->
        let t1' = eval1 ctx t1
        TmTimesfloat(fi,t1',t2) 
    | TmSucc(fi,t1) ->
        let t1' = eval1 ctx t1
        TmSucc(fi, t1')
    | TmPred(_,TmZero(_)) ->
        TmZero(dummyinfo)
    | TmPred(_,TmSucc(_,nv1)) when isnumericval ctx nv1 ->
        nv1
    | TmPred(fi,t1) ->
        let t1' = eval1 ctx t1 in
        TmPred(fi, t1')
    | TmIsZero(_,TmZero(_)) ->
        TmTrue(dummyinfo)
    | TmIsZero(_,TmSucc(_,nv1)) when isnumericval ctx nv1 ->
        TmFalse(dummyinfo)
    | TmIsZero(fi,t1) ->
        let t1' = eval1 ctx t1 in
        TmIsZero(fi, t1')
    | TmLet(fi,x,v1,t2) when isval ctx v1 ->
        termSubstTop v1 t2 
    | TmLet(fi,x,t1,t2) ->
        let t1' = eval1 ctx t1 in
        TmLet(fi, x, t1', t2) 
    | _ -> 
        raise NoRuleApplies

let rec eval ctx t =
  try let t' = eval1 ctx t
      in eval ctx t'
  with NoRuleApplies -> t

let evalbinding ctx = function
    | TmAbbBind(t) ->
        let t' = eval ctx t
        TmAbbBind(t')
    | bind -> bind

let test = """/* Examples for testing */

true;
if false then true else false; 

x/;
x;

x = true;
x;
if x then false else x; 

lambda x. x;
(lambda x. x) (lambda x. x x); 

{x=lambda x.x, y=(lambda x.x)(lambda x.x)}; 
{x=lambda x.x, y=(lambda x.x)(lambda x.x)}.x; 

"hello";

timesfloat (timesfloat 2.0 3.0) (timesfloat 4.0 5.0);

0; 
succ (pred 0);
iszero (pred (succ (succ 0))); 

let x=true in x;"""