;; Compile a term - generate proof obligations that once satisfied ensures the term is wellformed and can be executed

;; PO = proof obligation
;; Takes a term, and generate a list of POs
(defun pss-compile-term (term &optional env)
  "Recursively compile a term and return a list of proof obligations, using an environment."
  ;; First expand any symbols in the term
  (let ((expanded-term (macro-expand-term term)))
    (cond
     ;; Special form: (y body) - Compile body only, ignore 'y' itself
     ((and (consp expanded-term) (eq (car expanded-term) 'y) (= (length expanded-term) 2))
      (pss-compile-term (nth 1 expanded-term) env))

     ;; Function definition: (FUN var type body)
     ((and (listp expanded-term) (eq (car expanded-term) 'FUN))
      ;; Check for valid FUN structure
      (unless (= (length expanded-term) 4)
        (error "Malformed FUN term: %S" expanded-term))
      (let* ((var (nth 1 expanded-term))
             (type (nth 2 expanded-term))
             (body (nth 3 expanded-term))
             (new-env (cons (list var type) env)))
        ;; Recursively check type and body, collect POs from them
        (append (pss-compile-term type new-env) (pss-compile-term body new-env))))

     ;; Quote of smth - it's a variable, always wellformed, return nil
     ((and (consp expanded-term) (eq (car expanded-term) 'quote))
      nil)

     ;; Top - always wellformed, return nil
     ((eq expanded-term 'top)
      nil)

     ((and (listp expanded-term) (eq (car expanded-term) 'OR))
      ;; Check for valid OR structure (at least one argument)
      (unless (>= (length expanded-term) 2)
        (error "Malformed OR term: %S" expanded-term))
      (when (> (length expanded-term) 4)
        (error "Unsupported OR term with more than 2 arguments: %S" expanded-term))
      (append (pss-compile-term (nth 1 expanded-term) env)
              (pss-compile-term (nth 2 expanded-term) env)))

     ;; Application: (f arg1 arg2 ...) -> treat as ((f arg1) arg2) ... (curried application)
     ((consp expanded-term)
      (let* ((op (car expanded-term))
             (args (cdr expanded-term))
             ;; Start with the initial operator
             (current-op op)
             ;; Accumulate POs from all parts
             (all-pos nil))

        ;; 1. Compile the initial operator recursively
        (setf all-pos (append all-pos (pss-compile-term current-op env)))

        ;; 2. Iterate through arguments, applying one by one
        (dolist (arg args)
          ;; 2a. Compile the current argument recursively
          (setf all-pos (append all-pos (pss-compile-term arg env)))

          ;; 2b. Expand the current operator (which might be the result of previous application)
          (let ((resolved-op (macro-expand-term current-op)))

            ;; 2c. Check the type of the resolved operator and process the application step
            (cond
             ;; Case: Operator is (FUN var type body)
             ((and (consp resolved-op) (eq (car resolved-op) 'FUN))
              ;; Check for valid FUN structure
              (unless (= (length resolved-op) 4)
                (error "Malformed FUN term encountered during expansion: %S" resolved-op))
              (let* ((expected-type (nth 2 resolved-op))
                     (body (nth 3 resolved-op))  ;; Updated to use nth for body
                     ;; Generate PO for this application step: (env . arg . type)
                     (po (list env arg expected-type)))
                ;; Add the new PO
                (setf all-pos (append all-pos (list po)))
                ;; The result of this application step is the function body,
                ;; which becomes the operator for the next argument.
                (setf current-op body)))

             ;; Case: Operator resolves to *top*
             ((eq resolved-op 'top)
              (error "Term is ill-formed: application of top in %S" expanded-term))

             ;; Case: Operator resolves to something else (Symbol, other list, atom)
             ;; This means we are trying to apply something that isn't a function according to the rules.
             (t
              (setf all-pos (append all-pos (list
					     '()
					     (list env resolved-op '(FUN x XXX top))
					     (list env arg 'XXX)
					     '()
					     ))))
             ))) ; End let resolved-op and cond
        all-pos)) ; Return accumulated POs from this application and sub-expressions

     ;; Default error for anything else (e.g., improper lists not caught above)
     (t (error "Malformed term structure: %S" expanded-term)))))
