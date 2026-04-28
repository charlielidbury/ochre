;; Everything related to subtyping/promotions/...

;; Finds the value of the type binding for a quoted variable
(defun find-binding-type-in-sexp (var-symbol super-sexp path)
  "Search upwards from PATH within SUPER-SEXP for the innermost (FUN fun-var type body)
that binds VAR-SYMBOL. Return the TYPE or nil.
VAR-SYMBOL is the symbol itself (e.g., 'x), not the quoted form ('x)."
  (let ((current-path (butlast path))
        found-type) ; Initialize found-type to nil
    (while (and current-path (not found-type)) ; Loop while path exists and type not found
      (let ((parent-term (ignore-errors (get-subexpression-at-path super-sexp current-path)))) ; Use ignore-errors for robustness
        (when (and parent-term ; Check if parent-term is valid
                   (listp parent-term)
                   (eq (car parent-term) 'FUN)
                   (= (length parent-term) 4))
          (let ((fun-var (nth 1 parent-term))
                (fun-type (nth 2 parent-term)))
            ;; Compare the symbol name directly
            (when (eq fun-var var-symbol)
              (setq found-type fun-type))))) ; Set found-type
      ;; Move to the next parent path only if type not found
      (unless found-type
        (setq current-path (butlast current-path))))

    ;; If found-type was not set in the loop, check the root
    (unless found-type
      (when (and (null current-path) ; We reached the root without finding in parents
                 path ; Ensure the original path was not empty
                 (listp super-sexp)
                 (eq (car super-sexp) 'FUN)
                 (= (length super-sexp) 4))
        (let ((fun-var (nth 1 super-sexp))
              (fun-type (nth 2 super-sexp)))
          (when (eq fun-var var-symbol)
            (setq found-type fun-type))))) ; Set found-type if root matches

    found-type)) ; Return found-type (nil if not found anywhere)

;; Promote the subexpression of SUPER-SEXP located by PATH.
(defun promote-at-path (super-sexp path)
  "Promote the subexpression of SUPER-SEXP located by PATH.
Returns the modified SUPER-SEXP if a promotion occurred, otherwise signals an error or returns original SUPER-SEXP if no rule applies.
Rules:
1. 'var -> its type from the binding FUN. If free, -> top.
2. (FUN ...) -> top (unless path points to FUN keyword, var, or type).
3. (app ...) -> top.
4. top -> error.
5. Cannot promote FUN keyword, var binding, or type annotation within a FUN.

SUPER-SEXP is the full S-expression.
PATH is a list of indices locating the subexpression to promote."
  ;; Assume get-subexpression-at-path and replace-subexpression-at-path exist and work correctly.
  (let ((term (get-subexpression-at-path super-sexp path)))
    ;; --- Pre-check: Forbidden promotions within a FUN ---
    (when path ; Cannot check parent if path is empty (term is super-sexp)
      (let ((parent-path (butlast path)))
        (let ((parent-term (ignore-errors (get-subexpression-at-path super-sexp parent-path)))
              (index-in-parent (car (last path)))) ; Get the index of the current term within its parent
          ;; Check if the parent is a FUN expression
          (when (and parent-term
                     (listp parent-term)
                     (eq (car parent-term) 'FUN)
                     (= (length parent-term) 4))
            ;; If parent is FUN, check if the index is forbidden (0, 1, or 2)
            (when (member index-in-parent '(0 1 2))
              (error "Cannot promote %s within a FUN expression"
                     (cond ((= index-in-parent 0) "FUN keyword")
                           ((= index-in-parent 1) "variable binding")
                           ((= index-in-parent 2) "type annotation")
                           (t "unknown part")))))))) ; Should not happen

    ;; --- Promotion Logic ---
    (cond
     ;; Case 1: Term is 'top'. Cannot promote.
     ((equal term 'top)
      (error "Cannot promote top"))

     ;; Case 2: Term is a quoted variable (e.g., 'x).
     ((and (listp term) (= (length term) 2) (eq (car term) 'quote) (symbolp (cadr term)))
      (let* ((var-symbol (cadr term))
             ;; Search for the type binding within the data structure
             (type (find-binding-type-in-sexp var-symbol super-sexp path)))
        (if type
            ;; If type found, replace variable with type.
            (replace-subexpression-at-path super-sexp path type)
          ;; If no binding FUN found (free variable), replace with 'top'.
          (replace-subexpression-at-path super-sexp path 'top))))

     ;; Case 3: Any other valid term (FUN expression, application, other atoms).
     ;; The pre-check already handled errors for forbidden parts inside FUN.
     ;; All other cases promote to 'top'.
     ;; We assume 'term' is non-nil and valid based on get-subexpression-at-path success.
     (t
      (replace-subexpression-at-path super-sexp path 'top)))))
