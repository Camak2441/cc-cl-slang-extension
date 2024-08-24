
(* test store, sequence, assignment *) 

let x : int ref = ref 0 in
let incx (y: unit): unit = begin (x := !x + 1) end in
begin
incx (); incx (); incx (); !x
end
