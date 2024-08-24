
(* test store, sequence, assignment *) 

let f (x: int): int seq = 
  x :: '(f (x + 1))
in
let l : int seq = f 1 in begin
hd l + hd tl l
end
