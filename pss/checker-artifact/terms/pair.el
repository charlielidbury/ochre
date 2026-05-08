;; Terms for pairs - Scott encoding (non-dependent)
;;
;; A pair (a, b) is encoded as a function that, given a single
;; eliminator/case `pair-case` of shape (FUN a A (FUN b B top)),
;; applies it to the two components: ('pair-case 'a 'b).
;;
;; This mirrors *list*/*int*'s Scott-encoded eliminator pattern, but
;; with a single constructor (no OR needed).

;; The pair type, parametric in A and B.
;; *pair* A B = { p | given (pair-case : a:A -> b:B -> top), p pair-case : top }
(define-term
 '*pair*
 '(FUN A top
       (FUN B top
            (FUN pair-case (FUN a 'A (FUN b 'B top))
                 (('pair-case top) top)))))

;; Pair constructor: cons-pair A B a b = λpair-case. pair-case a b
(define-term
 '*cons-pair*
 '(FUN A top
       (FUN B top
            (FUN a 'A
                 (FUN b 'B
                      (FUN pair-case (FUN a 'A (FUN b 'B top))
                           (('pair-case 'a) 'b)))))))

;; First projection: fst p = p (FUN a top (FUN b top a))
(define-term
 '*fst*
 '(FUN A top
       (FUN B top
            (FUN p ((*pair* 'A) 'B)
                 ('p (FUN a 'A (FUN b 'B 'a)))))))

;; Second projection: snd p = p (FUN a top (FUN b top b))
(define-term
 '*snd*
 '(FUN A top
       (FUN B top
            (FUN p ((*pair* 'A) 'B)
                 ('p (FUN a 'A (FUN b 'B 'b)))))))

;; Unit type and value (used by *array* for the empty case)
(define-term
 '*unit*
 '(FUN unit-case top
       'unit-case))

(define-term
 '*unit-val*
 '(FUN unit-case top
       'unit-case))
