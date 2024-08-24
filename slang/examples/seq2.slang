
(* test store, sequence, assignment *) 

let n (x: int): int seq = 
  x :: '(n (x + 1))
in
let sumfirst (x: int) (l: int seq thunk): int = 
  if 0 < x then 
    (hd l) + sumfirst (x - 1) (tl l)
  else 0
in
let l : int seq = n 1 in begin
sumfirst (?) l
end
