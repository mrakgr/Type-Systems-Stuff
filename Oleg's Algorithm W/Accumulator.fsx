﻿// Argument accumulator inspired by FParsec.Pipes
    
type Result<'a,'b> = Succ of 'b | Fail of 'a

let either f s = function
    | Succ x -> s x
    | Fail x -> f x

let (|?>) x f = either Fail f x

let a = Succ "asd"
let b = Succ 2
let c = Succ 'a'

let start a = 
    match a with
    | Succ a -> (fun k -> k a) |> Succ
    | Fail x -> Fail x

let next b a = 
    match a with
    | Succ a ->
        match b with
        | Succ b -> a |> (fun x k -> x k b) |> Succ
        | Fail x -> Fail x
    | Fail x -> Fail x

let fin k a =
    match a with
    | Succ a -> Succ <| a k
    | Fail x -> Fail x

let r: Result<string,_> = 
    start a |> next b |> next c
    |> fin (fun a b c -> c)
