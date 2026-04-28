;; Some utilities

(load "macroexpand.el")
;; Check if a term contains at least one OR expressions after macro expansion
(defun has-at-least-one-or-expression (term &optional already-expanded)
  "Check if TERM contains at least one OR expressions after macro expansion.
Returns t if at least one OR expression is found, nil otherwise."
  (let ((expanded-term (if already-expanded
                           term
                         (macro-expand-term term))))
    (cond
     ((null expanded-term) nil)
     ((atom expanded-term) nil)
     ((eq (car expanded-term) 'OR) t)
     (t (or (has-at-least-one-or-expression (car expanded-term) nil)
            (has-at-least-one-or-expression (cdr expanded-term) nil))))))

;; Check if a term contains multiple instances of the varaible variable, respecting shadowing
(defun has-multiple-variable-instances (term variable)
  "Check if TERM contains multiple instances of VARIABLE, respecting shadowing.
Returns t if VARIABLE appears multiple times in TERM, nil otherwise."
  (let ((count 0))
    (let ((count-variable (lambda (term)
                            (cond
                             ((null term) nil)
                             ((equal term variable)
                              (setq count (1+ count)))
                             ((atom term) nil)
                             ((eq (car term) 'FUN)
                              (let ((bound-var (nth 1 term))
                                    (body (nth 3 term)))
				(unless (equal bound-var variable) ; Shadowing
                                  (funcall count-variable body))))
                             (t
                              (funcall count-variable (car term))
                              (funcall count-variable (cdr term)))))))
      (funcall count-variable term)
      (> count 1))))

;; Returns t if the following term is a function definition with multiple instances of its variable in its body
;; First, it expands the term, then calls has-multiple-variable-instances
(load "macroexpand.el")
(defun multiple-variable-fun (term)
  "Check if TERM is a function definition with multiple instances of its variable in its body.
Returns t if TERM is a function definition and its body contains multiple instances of its bound variable."
  (let ((expanded-term (macro-expand-term term)))
    (when (and (listp expanded-term)
               (eq (car expanded-term) 'FUN))
      (let ((bound-var (cadr expanded-term))
            (body (cadddr expanded-term)))
        (has-multiple-variable-instances body (list 'quote bound-var))))))
