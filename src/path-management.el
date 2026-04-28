;; Everything related to path management - extracting paths from s-sexpr, ...
;; First, some utilities, then the functions

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Utilites related to s expr path

;; Get the path of the s-expr at point
(defun sexp-path-at-point (&optional pos)
  "Return a list of zero-based indices for the nested S-expression path at POS.
If POS is nil, use the current point."
  (let ((pos (or pos (point)))
        path)
    (save-excursion
      (cl-block sexp-path
        (while t
          (let* ((ppss  (syntax-ppss pos))
                 (start (nth 1 ppss)))
            (if (null start)
                (cl-return-from sexp-path)
              ;; Move to the start of the containing list and compute index
              (goto-char start)
              (forward-char 1)
              (let ((idx
                     (cl-loop for i from 0
                              for ptr = (save-excursion
                                          (goto-char start)
                                          (forward-char 1)
                                          (cl-loop repeat i do (forward-sexp 1))
                                          (point))
                              for end-pos = (ignore-errors
                                              (save-excursion
                                                (goto-char ptr)
                                                (forward-sexp 1)
                                                (point)))
                              while end-pos
                              when (and (<= ptr pos) (< pos end-pos))
                              return i)))
                (push (or idx 0) path)
                (setq pos start))))))
      path)))

;; Get the bounds of the outermost s-expr containing the point
(defun get-outermost-sexp-bounds-at-point (&optional pos)
  "Return the (START . END) bounds of the outermost S-expression containing POS.
If POS is nil, use the current point."
  (let ((orig-point (or pos (point)))
        (start-bounds (bounds-of-thing-at-point 'sexp))) ; Default result if we don't find anything
    (save-excursion
      (goto-char orig-point)
      (condition-case nil
          (progn
            (beginning-of-defun)
            (let ((start (point)))
              (end-of-defun)
              (let ((end (point)))
                ;; Verify that the original point is actually within these bounds
                ;; and that we didn't just get the whole buffer trivially unless
                ;; the buffer contains only one sexp.
                (if (and (<= start orig-point) (<= orig-point end)
                         (or (/= start (point-min)) (/= end (point-max))
                             (and (= start (point-min)) (= end (point-max))
                                  ;; Check if buffer contains roughly one sexp
                                  (save-excursion
                                    (goto-char (point-min))
                                    (ignore-errors (forward-sexp 1) (eobp))))))
                    (cons start end)
                  start-bounds))))))))

;; Get the parsed object of the outermost s-expr containing the point
(defun parse-outermost-sexp-at-point (&optional pos)
  "Return the parsed object of the outermost S-expression containing POS.
If POS is nil, use the current point. Returns nil if no sexp found or parse error."
  (let ((bounds (get-outermost-sexp-bounds-at-point pos)))
    (when bounds
      (let* ((start (car bounds))
             (end (cdr bounds))
             (sexp-str (buffer-substring-no-properties start end)))
        (message "sexp-str: %s %s %s" sexp-str start end)
        (read sexp-str)))))

;; Get the bounds, string, and parsed object of the sexp at point
(defun proof-get--sexp-at-point ()
  "Get the bounds, string, and parsed object of the sexp at point.
Returns a list (START END SEXP-STRING SEXP-OBJECT) or nil if no sexp."
  (let ((bounds (bounds-of-thing-at-point 'sexp)))
    (when bounds
      (let* ((start (car bounds))
             (end (cdr bounds))
             (sexp-str (buffer-substring-no-properties start end)))
        (condition-case err
            (let ((sexp-obj (read sexp-str)))
              (list start end sexp-str sexp-obj))
          (error (message "Error parsing sexp at point: %s" (error-message-string err))
                 nil))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Takes a path as argument

;; Get the subexpression at a path
(defun get-subexpression-at-path (sexp path)
  "Return the subexpression of SEXP located by PATH.
PATH is a list of non-negative integer indices."
  (if (null path)
      sexp
    (let ((idx (car path))
          (rest-path (cdr path)))
      (unless (and (integerp idx) (>= idx 0))
        (error "Path component must be a non-negative integer: %S" idx))
      (if (and (listp sexp) (> (length sexp) idx))
          (get-subexpression-at-path (nth idx sexp) rest-path)
        (error "Invalid path %S for S-expression %S at index %d" path sexp idx)))))

;; Replace the subexpression at a path
(defun replace-subexpression-at-path (sexp path replacement)
  "Return a new S-expression based on SEXP, with the subexpression at PATH replaced by REPLACEMENT.
PATH is a list of non-negative integer indices."
  (if (null path)
      replacement
    (let ((idx (car path))
          (rest-path (cdr path)))
      (unless (and (integerp idx) (>= idx 0))
        (error "Path component must be a non-negative integer: %S" idx))
      (if (and (listp sexp) (> (length sexp) idx))
          ;; Create a mutable copy to modify
          (let ((new-list (copy-sequence sexp)))
            (setf (nth idx new-list)
                  (replace-subexpression-at-path (nth idx sexp) rest-path replacement))
            new-list)
        (error "Invalid path %S for S-expression %S at index %d" path sexp idx)))))