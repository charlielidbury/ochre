


;; Some examples

;; ok
(<=p ((*cons* *1*) ((*cons* *2*) *nil*)) (*sorted-list* *0*))

;; cannot be proven
(<=p ((*cons* *2*) ((*cons* *1*) *nil*)) (*sorted-list* *0*))


;; Proving the merge sort

;; Merge of sorting list
(<=p (((*merge2* *merge2-objective*) (*sorted-list* *int*)) (*sorted-list* *int*)) (*sorted-list* *int*))







;; Goal:
;; ((((*merge* *list*) *true*) *list*) *true*)

;; Dans le goal:
;; (((*leq* 'head1) 'head2)
;;     ((*cons* 'head1) (('self 'tail1) 'lst2)))
;;     ;; head1 > head2 -> cons head2 (merge lst1 tail2)
;;     ((*cons* 'head2) (('self 'lst1) 'tail2))

;; Montrer
;; ((*all-above-threshold*
;;    ((*cons* 'head1) (('self 'tail1) 'lst2)) ; l'appel recursif
;;    'head1 ; jsp
