
(* test store, sequence, assignment *) 

let x : int list = 1 :: 2 :: [] in
begin
hd tl x + hd x 
end
