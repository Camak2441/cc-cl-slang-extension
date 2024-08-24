
(* test store, sequence, assignment *) 

let x : int ref = ref 777 in
let a : int = 101 in
let b : int thunk = 777 in
begin
x := 101;
a + b
end
