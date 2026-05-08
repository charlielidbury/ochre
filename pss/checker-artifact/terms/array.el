;; Terms for length-indexed arrays - Scott encoding
;;
;; *array* n T computes a *type* that depends on n : *int*:
;;   *array* 0       T = *unit*
;;   *array* (S pred) T = *pair* T (*array* pred T)
;;
;; The Scott eliminator on *int* is two-argument: ((n zero-case) succ-case)
;; reduces to (OR 'zero-case ('succ-case <pred>)). The type therefore
;; computes through OR, and we recurse via the y-bound `self`.
;;
;; This mirrors the dependent-indexing pattern in *sorted-list* (terms/list.el),
;; but indexes by the length of the array rather than a lower bound.

(define-term
 '*array*
 '(y (FUN self top
          (FUN n *int*
               (FUN T top
                    (('n
                      ;; n == 0 -> *unit*
                      *unit*)
                     ;; n == S(pred) -> *pair* T (self pred T)
                     (FUN pred top
                          ((*pair* 'T) (('self 'pred) 'T)))))))))
