;; Some examples with integers

;; 1 is a subtype of int
;; Proof in proofs/leq-1-int.txt
(<=p *1* *int*)

;; [1, +inf[ + [1, +inf[ <= [1, +inf[
;; Proof in proofs/plus-succint-succint-leq-succint.txt
(<=p ((*plus* (*succ* *int*)) (*succ* *int*)) (*succ* *int*))

;; Proving the factorial function returns a successor
;; Proof in proofs/leq-fact-succint.int
(<=p ((*fact-factory* (FUN n *int* (*succ* *int*))) *int*) (*succ* *int*))

;; Proving the syracuse function always returns 1
;; Proof in proofs/syracuse-leq-1.txt
(<=p ((*syracuse-factory* (FUN n *int* *1*)) *int*) *1*)
