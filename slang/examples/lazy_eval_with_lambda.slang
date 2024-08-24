
(* test store, sequence, assignment *) 

let x : int ref = ref 0 in
let f: int -> int = (fun (y: int) -> begin (x := !x + 1); y end) in
let g: int thunk -> int = (fun (y: int thunk) -> begin (x := !x + 1); y end) in
let a: int thunk = '!x in
begin
(f a) + (g a) + (f a)
end
