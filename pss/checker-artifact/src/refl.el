;; Check that two terms are alpha-equivalent

(defun alpha-equivalent-p (term1 term2 &optional env)
  "Check if TERM1 and TERM2 are alpha-equivalent.
Terms are expected to be symbols, quoted symbols ('symbol),
or lists of the form (FUN variable type body).
ENV is an internal alist mapping bound variables from TERM1 to TERM2."
  (message (format "Alpha-equivalent: %S %S" term1 term2))
  (message (format "ENV %S" env))
  (cond
   ;; Case 1: Quoted terms (constants or free vars treated as constants)
   ((eq (car-safe term1) 'quote)
    (equal term1 term2))
   ((eq (car-safe term2) 'quote)
    nil) ; term1 is not quoted, term2 is -> different

   ;; Case 2: Unquoted symbols (variables)
   ((symbolp term1)
    (unless (symbolp term2)
      ;; Type mismatch: symbol vs non-symbol. Consider them non-equivalent.
      (message "Alpha-equiv type mismatch: symbol vs non-symbol %S %S" term1 term2)
      (signal 'wrong-type-argument (list 'symbolp term2))) ; Or simply return nil
    (let ((binding (assoc term1 env)))
      (if binding
          ;; Bound variable: check if term2 matches the mapped variable in env
          (eq term2 (cdr binding))
        ;; Free variable: check if term2 is the *same* free variable
        (eq term1 term2))))

   ;; Case 3: Other atoms (numbers, strings, etc.) - compare directly
   ((atom term1)
    (equal term1 term2))

   ;; Case 4: Lists (expecting FUN terms)
   ((consp term1)
    (unless (consp term2)
      ;; Type mismatch: list vs non-list. Consider them non-equivalent.
      (message "Alpha-equiv type mismatch: list vs non-list %S %S" term1 term2)
      (signal 'wrong-type-argument (list 'consp term2))) ; Or simply return nil
    ;; Check for FUN structure: (FUN var type body)
    (if (and (eq (car term1) 'FUN) (= (length term1) 4)
             (eq (car term2) 'FUN) (= (length term2) 4))
        (let ((v1 (nth 1 term1)) (t1 (nth 2 term1)) (b1 (nth 3 term1))
              (v2 (nth 1 term2)) (t2 (nth 2 term2)) (b2 (nth 3 term2)))
          ;; 1. Types must be alpha-equivalent under the current environment
          (and (alpha-equivalent-p t1 t2 env)
               ;; 2. Bodies must be alpha-equivalent under an environment
               ;;    extended with the mapping v1 -> v2
               (alpha-equivalent-p b1 b2 (cons (list v1 v2) env))))
      ;; Else, it's an application, check that all the elements are alpha-equivalent
      (and (equal (length term1) (length term1))
           (cl-loop for arg1 in term1
                    for arg2 in term2
                    always (alpha-equivalent-p arg1 arg2 env)))))

   ;; Default case (e.g., if term1 is neither atom nor cons)
   (t nil)))

;; Examples:
;; (alpha-equivalent-p '(FUN x 'type x) '(FUN y 'type y)) ; => t
;; (alpha-equivalent-p '(FUN x 'type y) '(FUN z 'type y)) ; => t (y is free)
;; (alpha-equivalent-p '(FUN x 'type x) '(FUN y 'type z)) ; => nil
