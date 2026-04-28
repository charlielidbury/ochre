;; Terms for lists - Scott encoding
;; Not tested

;; The list type
(define-term
 '*list*
 '(y (FUN self top
          (FUN nil-case top
               (FUN cons-case (FUN head top (FUN tail top top))
                    (OR 'nil-case (('cons-case top) 'self)))))))

;; Empty list
(define-term
 '*nil*
 '(FUN nil-case top
       (FUN cons-case (FUN head top (FUN tail top top))
            'nil-case)))

;; List constructor
(define-term
 '*cons*
 '(FUN elem top
       (FUN lst *list*
            (FUN nil-case top
                 (FUN cons-case (FUN head top (FUN tail top top))
                      (('cons-case 'elem) 'lst))))))

;;;;;;;;;;;;;;;;;;;;;;;;
;; Basic list operations

;; Head of a list
;; head lst
(define-term
 '*head*
 '(FUN lst *list*
       (('lst
         ;; nil case - return nil
         *nil*)
        ;; cons case - return head
        (FUN head top
             (FUN tail top
		  'head)))))

;; Tail of a list
;; tail lst
(define-term
 '*tail*
 '(FUN lst *list*
       (('lst
         ;; nil case - return nil
         *nil*)
        ;; cons case - return tail
        (FUN head top
             (FUN tail top
		  'tail)))))

;; List append - recursive implementation
;; append lst1 lst2
(define-term
 '*append-factory*
 '(FUN obj top
       (y (FUN self 'obj
               (FUN lst1 *list*
                    (FUN lst2 *list*
                         (('lst1
                           ;; lst1 is nil -> return lst2
                           'lst2)
                          ;; lst1 is cons -> cons head with (append tail lst2)
                          (FUN head top
                               (FUN tail top
                                    (*cons* 'head (('self 'tail) 'lst2)))))))))))

(define-term
 '*append*
 '(*append-factory* (FUN lst1 *list* (FUN lst2 *list* *list*))))

;; List length - recursive implementation
;; length lst
(define-term
 '*length-factory*
 '(FUN obj top
       (y (FUN self 'obj
               (FUN lst *list*
                    (('lst
                      ;; nil case -> 0
                      *0*)
                     ;; cons case -> 1 + length tail
                     (FUN head top
                          (FUN tail top
                               (*succ* ('self 'tail))))))))))

(define-term
 '*length*
 '(*length-factory*
   (FUN lst *list* *int*)))

;; List map - applies a function to each element
;; map f lst
(define-term
 '*map-factory*
 '(FUN obj top
       (y (FUN self 'obj
               (FUN f (FUN a top top)
                    (FUN lst *list*
                         ('lst
                          ;; nil case -> nil
                          *nil*
                          ;; cons case -> cons (f head) (map f tail)
                          (FUN head top
                               (FUN tail top
				    ((*cons* ('f 'head)) (('self 'f) 'tail)))))))))))

(define-term
 '*map*
 '(*map-factory* (FUN f (FUN a top top) (FUN lst *list* *list*))))

;; Fold right - applies a function to each element and accumulates a result
;; foldr f acc lst
(define-term
 '*foldr-factory*
 '(FUN obj top
       (y (FUN self 'obj
               (FUN f (FUN a top (FUN b top top))
                    (FUN acc top
                         (FUN lst *list*
                              (('lst
                                ;; nil case -> initial value
                                'acc)
                               ;; cons case -> f head (fold f tail)
                               (FUN head top
                                    (FUN tail top
					 (('f 'head) ((('self 'f) 'acc) 'tail))))))))))))

(define-term
 '*foldr*
 '(*foldr-factory*
   (FUN f (FUN a top (FUN b top top)) (FUN acc top (FUN lst *list* *b*)))))

;; Return a *bool* which indicates if a list is sorted
;; is-sorted lst
(define-term
 '*is-sorted*
 '(FUN lst *list*
       (((*foldr*
          *leq*)
         *true*)
        'lst)))

;; Return the maximum element of a list
;; max-list lst
(define-term
 '*max-list*
 '(FUN lst *list*
       (((*foldr*
          *max*)
         *0*)
        'lst)))

;; Aux if all element of a list are above a threshold
(define-term
 '*all-above-threshold-aux*
 '(FUN lst *list*
       (FUN threshold *int*
            ((*map*
              (FUN elem *int* ((*geq* 'elem) 'threshold))
              'lst)))))

;; Return if all element of a list are above a threshold
;; all-above-threshold lst threshold
(define-term
 '*all-above-threshold*
 '(FUN lst *list*
       (FUN threshold *int*
            (((*foldr*
               '*and*)
              *true*)
             ((*all-above-threshold-aux* 'lst) 'threshold)))))

;;;;;;;;;;;;;;;;;
;; Sorting a list

;; Merge sort
;; merge-sort lst
(define-term
 '*merge-sort*
 '(FUN obj top
       (y (FUN self 'obj
               (FUN lst *list*
                    (('lst
                      ;; lst == [] -> nil
                      *nil*)
                     ;; lst == head :: tail
                     (FUN head top
                          (FUN tail top
                               ((*merge2*
				 (('self (('split 'tail) *true*))))
				(('self (('split 'tail) *false*))))))))))))

;; Split a list into a halves, based on a *bool* -> we take either the even indexes, or the odds
;; split lst b
(define-term
 '*split*
 '(FUN obj top
       (y (FUN self 'obj
               (FUN lst *list*
                    (FUN b *bool*
                         (('lst
                           ;; lst == [] -> nil
                           *nil*)
                          ;; lst == head :: tail
                          (FUN head top
                               (FUN tail top
				    ((('b 'head)
                                      (('self 'tail) (*not* 'b)))
                                     (('self 'tail) (*not* 'b))))))))))))

;; correct merge function
(define-term
 '*merge2*
 '(FUN obj top
       (y (FUN self 'obj
               (FUN lst1 (*sorted-list* *int*)
                    (FUN lst2 (*sorted-list* *int*)
			 (('lst1
			   ;; lst1 == [] -> lst2
			   'lst2)
			  ;; lst1 == head1 :: tail1
			  (FUN head1 top
                               (FUN tail1 top
				    (('lst2
				      ;; lst2 == [] -> lst1
				      'lst1)
				     ;; lst2 == head2 :: tail2
				     (FUN head2 top
					  (FUN tail2 top
					       ;; head1 <= head2 -> cons head1 (merge tail1 lst2)
					       ((((*leq* 'head1) 'head2)
						 ((*cons* 'head1) (('self 'tail1) 'lst2)))
						;; head1 > head2 -> cons head2 (merge lst1 tail2)
						((*cons* 'head2) (('self 'lst1) 'tail2)))))))))))))))

;; objective function of merge2
(define-term
 '*merge2-objective*
 '(FUN a *sorted-list*
       (FUN b *sorted-list*
            (('a
              ;; a == []
              (('b
                ;; b == []
                (*sorted-list* *0*))
               ;; b == head2 :: tail2
               (FUN head2 top
                    (FUN tail2 top
                         (*sorted-list* 'head2)))))
             ;; a == head1 :: tail1
             (FUN head1 top
                  (FUN tail1 top
                       (('b
                         ;; b == []
                         (*sorted-list* 'head1))
                        ;; b == head2 :: tail2
                        (FUN head2 top
                             (FUN tail2 top
                                  ((((*leq* 'head1) 'head2)
                                    ;; head1 <= head2 -> all >= head1
                                    (*sorted-list* 'head1))
                                   ;; head1 > head2 -> all >= head2
                                   (*sorted-list* 'head2)))))))))))

(define-term
 '*sorted-list*
 '(y (FUN self top
	  (FUN n *int*
               (FUN nil-case top
		    (FUN cons-case (FUN head top (FUN tail top top))
			 (OR
			  'nil-case
			  ((FUN head top
				(('cons-case 'head) ('self (*plus* 'head *int*))))
			   'n)
			  )))))))
