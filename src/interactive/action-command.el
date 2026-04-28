;; Action commands

;; TODOS:

;; split the or doesnt check the current buffer we are in

(load "reduction.el")
(load "subtype.el")
(load "macroexpand.el")
(load "or-split.el")
(load "path-management.el")
(load "interactive/logging.el")

(defun perform-action-on-sexp-at-point (action-fn action-name message-prefix)
  "Perform an action on the S-expression at point.
Finds the outermost S-expression containing the point, determines the
path to the S-expression directly at point, performs the ACTION-FN
on that subexpression, replaces the outermost S-expression with
the result if a change occurred, logs the action using ACTION-NAME,
and displays messages using MESSAGE-PREFIX."
  (let* ((pos (point))
         (bounds (get-outermost-sexp-bounds-at-point pos))
         (super-sexp (parse-outermost-sexp-at-point pos))
         (path (sexp-path-at-point pos)))
    (if (and bounds super-sexp) ; Ensure path is also valid
        (let ((result (funcall action-fn super-sexp path)))
          (if (equal result super-sexp)
              (message "%s: No change." message-prefix)
            (progn
              (when (eq action-fn 'split-or-at-path-all)
                (setq result (car result)))
              (delete-region (car bounds) (cdr bounds))
              (goto-char (car bounds))
              (insert (format "%S" result))
              ;; Log the action to *Temp-Proof* buffer
              (let ((original-subexp (get-subexpression-at-path super-sexp path))
                    (result-subexp (get-subexpression-at-path result path)))
                (proof-log--log-action "*Temp-Proof*" action-name path
                                       (if (string-prefix-p "*Objective" (buffer-name)) t nil)
                                       (format "%s to replace %S by %S"
                                               message-prefix
                                               original-subexp
                                               result-subexp)))
              (message "%s performed." message-prefix))))
      (message "Could not find path (%S), bounds (%S), or outermost S-expression (%S) at point." path bounds super-sexp))))

(defun beta-substitute ()
  "Interactively perform beta substitution on the S-expression at point."
  (interactive)
  (perform-action-on-sexp-at-point #'beta-substitute-at-path 'beta-substitute "Beta substitute"))

(defun beta-substitute-all ()
  "Interactively perform all possible beta substitutions on the S-expression at point."
  (interactive)
  (perform-action-on-sexp-at-point #'beta-substitute-all-at-path 'beta-substitute-all "Beta substitute all"))

(defun macro-expand ()
  "Interactively perform macro expansion on the symbol at point."
  (interactive)
  (perform-action-on-sexp-at-point #'macro-expand-at-path 'macro-expand "Macro expand"))

(defun macro-collapse ()
  "Interactively perform macro collapse on the S-expression at point."
  (interactive)
  (perform-action-on-sexp-at-point #'macro-collapse-at-path 'macro-collapse "Macro collapse"))

(defun promote ()
  "Interactively perform promotion on the S-expression at point."
  (interactive)
  (perform-action-on-sexp-at-point #'promote-at-path 'promote "Promote"))

(defun split-or-all ()
  "Interactively perform promotion on the S-expression at point."
  (interactive)
  (perform-action-on-sexp-at-point #'split-or-at-path-all 'split-or-all "Split OR"))

(defun objective-or-split (n)
  "Interactively split an (OR ...) expression on the *Objective* buffer, depending on the choice of the user."
  (interactive)
  (perform-action-on-sexp-at-point
   (lambda (s-expr path) (split-or-at-path s-expr path n)) ; Lambda captures n
   (list 'objective-or-split n)                            ; Action name includes n
   (format "Objective OR split (%d)" n)))                  ; Message prefix includes n
