
(* test store, sequence, assignment *) 

let x : int ref = ref 0 in
let f (y: int): int = begin (x := !x + 1); y end in
let g (y: int thunk): int = begin (x := !x + 1); y end in
let a: int thunk = '!x in
begin
(f a) + (g a) + (f a)
end
