
(* test store, sequence, assignment *) 

let x : int ref = ref 777 in
let a : int thunk = !x in
let b : int thunk = '!x in
begin
x := 101;
a + b
end
