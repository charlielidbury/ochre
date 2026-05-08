;; Length-indexed array append - dependent typing demonstration
;;
;; *append-arrays* T n1 n2 a1 a2 produces an *array* of length (plus n1 n2):
;;   appendArrays 0       n2 ()       a2 = a2
;;   appendArrays (S pred) n2 (h, t)   a2 = (h, appendArrays pred n2 t a2)
;;
;; This file deliberately defines TWO versions: the correct one and a
;; deliberately-wrong one in which the result-length annotation says
;; (plus n1 n1) instead of (plus n1 n2). The intent is to demonstrate
;; that compilation produces *different* proof obligations -- the wrong
;; version requires obligations that cannot be discharged because
;; (plus n1 n1) and (plus n1 n2) are not equal for general n1, n2.
;;
;; The factory pattern is borrowed from *append-factory* / *plus-factory*
;; in list.el / int.el: we wrap the y-recursion in a "FUN obj top" to
;; carry the recursive type ascription for `self`, and then apply the
;; factory at the call site to fix that ascription.
;;
;; T is bound outside the y because it is fixed across the recursion;
;; the recursion is on n1 (and the y-recursion threads through self).
;; The Scott eliminator on *int* has no IH in the succ case, so the
;; recursion *must* go through self.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Correct version
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-term
 '*append-arrays-factory*
 '(FUN T top
       (FUN obj top
            (y (FUN self 'obj
                    (FUN n1 *int*
                         (FUN n2 *int*
                              (FUN a1 ((*array* 'n1) 'T)
                                   (FUN a2 ((*array* 'n2) 'T)
                                        (('n1
                                          ;; n1 == 0 -> a2
                                          'a2)
                                         ;; n1 == S(pred)
                                         (FUN pred *int*
                                              ((((*cons-pair* 'T)
                                                 ((*array* ((*plus* 'pred) 'n2)) 'T))
                                                (((*fst* 'T) ((*array* 'pred) 'T)) 'a1))
                                               (((('self 'pred) 'n2)
                                                 (((*snd* 'T) ((*array* 'pred) 'T)) 'a1))
                                                'a2)))))))))))))

(define-term
 '*append-arrays*
 '(FUN T top
       ((*append-arrays-factory* 'T)
        (FUN n1 *int*
             (FUN n2 *int*
                  (FUN a1 ((*array* 'n1) 'T)
                       (FUN a2 ((*array* 'n2) 'T)
                            ((*array* ((*plus* 'n1) 'n2)) 'T))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Wrong version: result-length annotation says (plus n1 n1) instead
;; of (plus n1 n2). Body is unchanged - we want to see how the type
;; annotation alone provokes different obligations.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-term
 '*append-arrays-wrong*
 '(FUN T top
       ((*append-arrays-factory* 'T)
        (FUN n1 *int*
             (FUN n2 *int*
                  (FUN a1 ((*array* 'n1) 'T)
                       (FUN a2 ((*array* 'n2) 'T)
                            ;; <<< deliberately wrong: n1 instead of n2 >>>
                            ((*array* ((*plus* 'n1) 'n1)) 'T))))))))
