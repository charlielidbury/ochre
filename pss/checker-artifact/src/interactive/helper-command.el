;; Some other commands that do not have any effect on the proof, purely for utilities

;; Copy and paste below super sexp at point
(defun copy-super-sexp-at-point ()
  "Copy the outermost S-expression at point and insert it on the next line."
  (interactive)
  (let ((bounds (save-excursion
                  (ignore-errors
                    (while t (backward-up-list 1)))
                  (bounds-of-thing-at-point 'sexp))))
    (unless bounds (error "No S-expression found"))
    (let* ((start (car bounds))
           (end (cdr bounds))
           (sexp-str (buffer-substring-no-properties start end)))
      (goto-char end)
      (end-of-line)
      (newline)
      (newline)
      (insert sexp-str)
      (message "Super S-expression copied below."))))