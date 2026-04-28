;; Everything related to macro expand/collapse/list of symbols

;; This variable holds all term definitions.
(defvar *term-definitions* nil
  "Alist mapping unquoted symbols to their term definitions.")

;; Expand the symbol at PATH within SUPER-SEXP using definitions in *term-definitions*.
(defun macro-expand-at-path (super-sexp path)
  "Expand the symbol at PATH within SUPER-SEXP using definitions in *term-definitions*.
Returns the modified SUPER-SEXP if an expansion occurred, otherwise the original SUPER-SEXP.
Assumes the term at PATH is an unquoted symbol intended for expansion.

SUPER-SEXP is the full S-expression.
PATH is a list of indices locating the subexpression to potentially expand."
  ;; Assumes helper functions get-subexpression-at-path and replace-subexpression-at-path exist.
  (let ((term (get-subexpression-at-path super-sexp path)))
    ;; Check if a valid term was retrieved and if it's a symbol.
    ;; Note: This basic check doesn't verify if the symbol was originally quoted in the source.
    ;; The calling context (e.g., an interactive function) should ideally perform that check.
    (if (and term (symbolp term))
        ;; Look up the symbol in the definitions.
        (let ((definition (cdr (assoc term *term-definitions*))))
          (if definition
              ;; If found, replace the symbol with its definition.
              (replace-subexpression-at-path super-sexp path definition)
            ;; If definition not found, raise an error.
            (error "No definition found for term %S" term)))
      ;; If term is not a symbol, raise an error.
      (error "Term %S is not a symbol" term))))

;; Collapse the subexpression at PATH within SUPER-SEXP if it matches a known macro definition.
(defun macro-collapse-at-path (super-sexp path)
  "Collapse the subexpression at PATH within SUPER-SEXP if it matches a known macro definition.
Returns the modified SUPER-SEXP if a collapse occurred, otherwise the original SUPER-SEXP.

SUPER-SEXP is the full S-expression.
PATH is a list of indices locating the subexpression to potentially collapse."
  ;; Assumes helper functions get-subexpression-at-path and replace-subexpression-at-path exist.
  (let ((subexp (get-subexpression-at-path super-sexp path)))
    (if subexp
        (let ((found-match nil)
              (result super-sexp))
          ;; Iterate through definitions to find a match
          (dolist (pair *term-definitions* result)
            (when (equal subexp (cdr pair))
              ;; Found a match, replace subexpression with the macro name
              (setq result (replace-subexpression-at-path super-sexp path (car pair)))
              (message "Macro expanded: %S -> %S: %S" subexp (car pair) result)
              (setq found-match t)))
          ;; If no match was found after checking all definitions, return original
          (if found-match result super-sexp)))))

;; Define a term in our calculus
(defun define-term (name definition)
  "Define NAME as a term with the given DEFINITION.
Adds (NAME . DEFINITION) to *term-definitions*, replacing any existing entry for NAME."
  ;; Remove existing entry for this name, if any (using assq for symbol comparison)
  (setq *term-definitions* (assq-delete-all name *term-definitions*))
  ;; Add the new entry to the front
  (push (cons name definition) *term-definitions*)
  ;; Print a message indicating the addition/update
  (message "Defined term: %S" name)
  ;; Return the name, similar to defun/defmacro convention
  name)

;; Recursively expand the symbols of *term-definitions*
(defun macro-expand-term (term)
  "Recursively expands term if it is a symbol defined in *term-definitions*."
  (let ((visited nil) ; Prevent infinite loops for cyclic definitions
        (current-term term)
        (continue-loop t)) ; Control variable for the loop
    (while continue-loop ; Loop while continue-loop is true
      (let* ((is-symbol (symbolp current-term))
             (not-visited (not (member current-term visited)))
             (definition (and is-symbol not-visited (assoc current-term *term-definitions*))))
        (if definition
            (progn
              (push current-term visited)
              (setq current-term (cdr definition)))
          ;; No definition found or already visited or not a symbol, stop looping
          (setq continue-loop nil) ; Signal to exit the loop
          )))
    ;; Return the final state of current-term after the loop finishes
    current-term))
