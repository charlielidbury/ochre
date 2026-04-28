;; Everything related to OR

;; Is an or expression at point
(defun is-or-expression-at-path (super-sexp path)
  "Check if the subexpression at PATH within SUPER-SEXP is an (OR a b ...) expression."
  (let ((term (get-subexpression-at-path super-sexp path)))
    (and (listp term) (eq (car term) 'OR) (>= (length term) 3))))

;; Utility
(defun split-or-at-path (super-sexp path n)
  "If the subexpression at PATH is an (OR a b ...) term, split it into two cases, substituting the nth alternative.
SUPER-SEXP is the full S-expression.
PATH is a list of indices locating the subexpression to replace.
N is the index of the alternative to substitute (0-based)."
  (unless (is-or-expression-at-path super-sexp path)
    (error "Expression at path %S in %S is not an (OR ...) form" path super-sexp))

  (let* ((term (get-subexpression-at-path super-sexp path))
         (alternatives (cdr term)))
    (when (>= n (length alternatives))
      (error "Index %d is out of bounds for alternatives %S" n alternatives))
    (let ((alt (nth n alternatives)))
      (replace-subexpression-at-path super-sexp path alt))))

;; The real function
(defun split-or-at-path-all (super-sexp path)
  "If the subexpression at PATH is an (OR a b ...) term, return a list of new super-sexps,
each substituting one of the alternatives for the OR expression.
SUPER-SEXP is the full S-expression.
PATH is a list of indices locating the subexpression."
  (unless (is-or-expression-at-path super-sexp path)
    (error "Expression at path %S in %S is not an (OR ...) form suitable for splitting" path super-sexp))

  (let* ((term (get-subexpression-at-path super-sexp path))
         (alternatives (cdr term))
         (num-alternatives (length alternatives)))
    ;; Use mapcar and number-sequence to iterate through each alternative index n
    (mapcar (lambda (n)
              ;; For each n, call split-or-at-path to get the super-sexp with the nth alternative substituted
              (split-or-at-path super-sexp path n))
            (number-sequence 0 (1- num-alternatives)))))