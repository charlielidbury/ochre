;; Some examples with unions

;; Both 1 and 2 are integers, so is the union
(<=p (OR *1* *2*) *int*)

;; Both 1 and 2 are either 1 or 2
(<=p *1* (OR *1* *2*))
(<=p *2* (OR *1* *2*))
