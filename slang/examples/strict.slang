
(* test store, sequence, assignment *) 

let x : int ref = ref 777 in
let a : int thunk = '!x in
let b : int thunk = a in
let c : int thunk = $! a in
begin
x := $! 101;
b + c
end
