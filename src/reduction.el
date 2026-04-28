;; Everything related to beta substitution and reduction of terms

(load "utilities.el")

;; Perform beta substitution on the subexpression of SUPER-SEXP located by PATH.
(defun beta-substitute-at-path (super-sexp path)
  "Perform beta substitution on the subexpression of SUPER-SEXP located by PATH.
Returns the modified SUPER-SEXP if a reduction occurred, otherwise the original SUPER-SEXP.
Recognized reductions:
- (top body) -> top
- (y f) -> (f (y f))
- ((FUN var type body) arg) -> body[arg/var]

SUPER-SEXP is the full S-expression.
PATH is a list of indices locating the subexpression to reduce."
  (let ((term (get-subexpression-at-path super-sexp path)))
    (cond
     ;; Special case: (top body) -> top
     ((and (listp term) (= (length term) 2) (eq (car term) 'top))
      (let ((result 'top))
        (replace-subexpression-at-path super-sexp path result)))

     ;; Special case: (y f) -> (f (y f))
     ((and (listp term) (= (length term) 2) (eq (car term) 'y))
      (let* ((f (cadr term))
             ;; The result replaces the original (y f) term
             (result (list f term)))
        (replace-subexpression-at-path super-sexp path result)))

     ;; Standard beta substitution: ((FUN var type body) arg)
     ((and (listp term) (= (length term) 2)
           (listp (car term))
           (eq (caar term) 'FUN)
           (= (length (car term)) 4))
      (let* ((rator (car term))
             (rand (cadr term))
             (var (nth 1 rator))
             ;; (_type (nth 2 rator)) ; Type not needed for substitution
             (body (nth 3 rator))
             (arg rand)
             (result (substitute-in-term body var arg)))
        (replace-subexpression-at-path super-sexp path result)))

     ;; Not a recognized application form for substitution
     (t
      (progn
        (error "Invalid term for beta substitution: %S" term)
        ;; No reduction occurred, return the original expression unchanged.
        ;; Note: Returning the original structure is important.
        super-sexp)))))

;; Recursively perform all possible beta substitutions in TERM.
(defun beta-substitute-all-in-term (term)
  "Recursively perform all possible beta substitutions in TERM."
  (cond
   ;; Special case: (top body) -> top
   ((and (listp term) (= (length term) 2) (eq (car term) 'top))
    'top)
   ;; Standard beta: ((FUN var type body) arg)
   ((and (listp term) (= (length term) 2)
         (let ((rator (car term)))
           (and (listp rator) (eq (car rator) 'FUN) (= (length rator) 4))))
    (let* ((rator (car term))
           (var (nth 1 rator))
           (_type (nth 2 rator))
           (body (nth 3 rator))
           (arg (cadr term)))
      ;; Only perform beta substitution if the argument doesn't contain multiple OR expressions
      (if (and (has-at-least-one-or-expression arg) (multiple-variable-fun rator))
          (list
           (list 'FUN var _type (beta-substitute-all-in-term body))
           (beta-substitute-all-in-term arg))
        (let ((substituted (substitute-in-term body var arg)))
          (beta-substitute-all-in-term substituted)))))
   ;; Application or other list: recursively substitute in all subterms - include the (y f) case where we reduce only f
   ((listp term)
    (mapcar #'beta-substitute-all-in-term term))
   ;; Atom: return as is
   (t term)))

;; Recursively perform all possible beta substitutions in the subexpression of SUPER-SEXP located by PATH, until the subexpression no longer changes.
(defun beta-substitute-all-at-path (super-sexp path)
  "Recursively perform all possible beta substitutions in the subexpression of SUPER-SEXP located by PATH, until the subexpression no longer changes.
  Returns the modified SUPER-SEXP if a reduction occurred, otherwise the original SUPER-SEXP.

  SUPER-SEXP is the full S-expression.
  PATH is a list of indices locating the subexpression to fully reduce."
  ;; Assuming get-subexpression-at-path and replace-subexpression-at-path exist
  (let ((term (get-subexpression-at-path super-sexp path)))
    ;; Check if a valid term was retrieved at the path
    (if term
        (let ((original-term term) ; Store the original subexpression
              (result term)
              (next nil))
          ;; Perform the full reduction on the extracted term
          (while (progn
                   (setq next (beta-substitute-all-in-term result))
                   (not (equal next result)))
            (setq result next))

          ;; If the term changed after full reduction, replace it in the super-expression
          (if (equal original-term result)
              super-sexp ; No change occurred, return the original super-sexp
            (replace-subexpression-at-path super-sexp path result)))
      ;; If term is nil (e.g., invalid path), return the original super-sexp unchanged.
      super-sexp)))

;; Substitute ARG for occurrences of 'VAR in BODY, respecting shadowing.
(defun substitute-in-term (body var arg)
  "Substitute ARG for occurrences of 'VAR in BODY, respecting shadowing.
VAR is the unquoted symbol from FUN."
  ;; The variable occurrences in the body are quoted symbols, e.g., 'x
  (let ((quoted-var (list 'quote var)))
    (substitute-in-term-internal body var quoted-var arg)))

;; Internal substitution helper.
(defun substitute-in-term-internal (body fun-var quoted-var arg)
  "Internal substitution helper.
BODY is the term to substitute into.
FUN-VAR is the unquoted variable symbol being substituted (e.g., x).
QUOTED-VAR is the quoted variable symbol to look for (e.g., 'x).
ARG is the term to substitute."
  (cond
   ;; Base case: If the current term is the quoted variable we're looking for, replace it with arg.
   ((equal body quoted-var) arg)
   ;; Base case: Atoms (like 'top', other quoted variables, numbers, etc.) are returned as is.
   ((atom body) body)
   ;; Recursive case: List structure
   ((listp body)
    (let ((op (car body)))
      (cond
       ;; Function definition: (FUN v type b)
       ((and (eq op 'FUN) (= (length body) 4))
        (let ((inner-fun-var (nth 1 body))
              (inner-fun-type (nth 2 body))
              (inner-fun-body (nth 3 body)))
          ;; Check for shadowing: If the inner function binds the same variable name (fun-var),
          ;; then do not substitute inside the inner function's body.
          ;; Only substitute within the type annotation part.
          (if (equal inner-fun-var fun-var)
              `(FUN ,inner-fun-var ,(substitute-in-term-internal inner-fun-type fun-var quoted-var arg) ,inner-fun-body)
            ;; No shadowing, substitute in both type and body.
            `(FUN ,inner-fun-var ,(substitute-in-term-internal inner-fun-type fun-var quoted-var arg) ,(substitute-in-term-internal inner-fun-body fun-var quoted-var arg)))))
       ;; Application or other list structure: (a b ...)
       ;; Recursively substitute in each element of the list.
       (t (mapcar (lambda (subterm) (substitute-in-term-internal subterm fun-var quoted-var arg)) body)))))
   ;; Default case: Should not be reached for valid terms.
   (t body)))
