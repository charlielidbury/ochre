;; Everything that interact with the proof mode

;; TODO me:

;; Create a function for reset, as it also resets temp proof and proof and everything
;; and similarly a function to check if a proof is already in progress (and which returns what we want to prove?)

;; Check if *Term* or others are already initialized when we ask the user if they want to do this, make it a helper function

(load "replay.el")
(load "compile.el")

;; return if a proof is already in progress
(defun proof-in-progress-p ()
  "Check if any of the buffers *Proof*, *Temp-Proof*, or *Goal* exist.
Returns t if at least one exists, nil otherwise."
  (or (get-buffer "*Proof*")
      (get-buffer "*Temp-Proof*")
      (get-buffer "*Goal*")))

;; start proof mode
(defun proof-mode-start-subtype-proof ()
  "Start a subtype proof if point is on a (<=p a b) or (<=p-rec a b) s-expression.
For (<=p-rec a b), it's treated as (<=p (a b) b).
Creates and manages *Term*, *Goal*, *Proof*, and *Temp-Proof* buffers,
displaying them alongside the original buffer."
  (interactive)
  (when (proof-in-progress-p)
    (unless (yes-or-no-p "Proof mode is already in progress. Do you want to reset it?")
      (user-error "User do not want to reset the proof mode. Exiting.")))
  (save-excursion
    (let* ((sexpr (thing-at-point 'sexp t)))
      (unless (and sexpr (string-match-p "^\\s-*(<=p\\(?:-rec\\)?\\s-+" sexpr))
        (user-error "Cursor is not on a (<=p a b) or (<=p-rec a b) s-expression"))
      (let* ((parsed (ignore-errors (read sexpr)))) ; Use ignore-errors for robustness
        (unless (and (listp parsed)
                     (= (length parsed) 3)
                     (memq (car parsed) '(<=p <=p-rec)))
          (user-error "Not a valid (<=p a b) or (<=p-rec a b) s-expression"))
        (let* ((op (car parsed))
               (original-a (cadr parsed))
               (original-b (caddr parsed))
               ;; Determine the effective 'a' and 'b' based on the operator
               (effective-a (if (eq op '<=p)
                                original-a
                              ;; Case: <=p-rec a b becomes <=p (a b) b
                              (list original-a original-b)))
               (effective-b original-b)
               ;; Convert effective terms to strings for display
               (a-str (prin1-to-string effective-a))
               (b-str (prin1-to-string effective-b))
               (term-buffer (get-buffer-create "*Term-0*"))
               (objective-buffer (get-buffer-create "*Objective-0*"))
               (goal-buffer (get-buffer-create "*Goal*"))
               (proof-buffer (get-buffer-create "*Proof*"))
               (temp-proof-buffer (get-buffer-create "*Temp-Proof*")))
          ;; Handle *Term* buffer
          (with-current-buffer term-buffer
            (erase-buffer))
          ;; Handle *Objective* buffer
          (with-current-buffer objective-buffer
            (erase-buffer))
          ;; Handle *Goal* buffer
          (with-current-buffer goal-buffer
            (erase-buffer))
          ;; Handle *Proof* buffer
          (with-current-buffer proof-buffer
            (erase-buffer)
            (insert ";; The proof (at each commit) will be displayed in this buffer\n\n")
            (insert (format "(start-term %s)\n" a-str))
            (insert (format "(start-goal %s)\n" b-str)))
          ;; Handle *Temp-Proof* buffer
          (with-current-buffer temp-proof-buffer
            (erase-buffer)
            (insert ";; Temporary proof displayed in this buffer\n\n"))
          ;; LAYOUT:
          ;;      [*Term*]       |  [*Goal*]   | [*Temp-Proof*]
          ;;---------------------|-----------------------------
          ;;   [*Objective*]     | [Orig buff] |   [*Proof*]
          ;; Display the four new buffers alongside the original buffer - comments are outdated related to the new variable names we use now
          (let* ((win-left-up (selected-window))
                 (win-right-up (split-window-right))
                 (_ (select-window win-right-up))
                 (win-right-down (split-window-below))
                 (_ (select-window win-right-up))
                 (win-right-right-up (split-window-right))
                 (_ (select-window win-right-down))
                 (win-right-right-down (split-window-right))
                 (_ (select-window win-left-up))
                 (win-left-down (split-window-below)))

            ;; Assign buffers to the newly created windows
            (set-window-buffer win-left-up term-buffer)
            (set-window-buffer win-left-down objective-buffer)
            (set-window-buffer win-right-up goal-buffer)
            (set-window-buffer win-right-down (current-buffer))
            (set-window-buffer win-right-right-up temp-proof-buffer)
            (set-window-buffer win-right-right-down proof-buffer)

            ;; Optionally balance windows in the frame containing the new windows
            ;; This might affect the original window's size too.
            ;; (balance-windows (window-frame win-term))

            ;; Select the window displaying the *Term* buffer
            (select-window win-left-up)

            (message "Proof mode started successfully - to prove that %s is a subtype of %s"
                     a-str b-str)
            (proof-mode-replay-proof)
            ))))))

;; commit *temp-proof* to *proof*
(defun proof-mode-commit-temp-proof ()
  "Copy content from *Temp-Proof* (except first 2 lines) to *Proof*, add '(commit)', and reset *Temp-Proof*.
The content from *Temp-Proof* is appended to *Proof*, followed by
a newline (if necessary), the line '(commit)', and another newline."
  (interactive)
  (let ((temp-proof-buffer (get-buffer "*Temp-Proof*"))
        (proof-buffer (get-buffer "*Proof*")))
    (unless temp-proof-buffer
      (user-error "*Temp-Proof* buffer does not exist"))
    (unless proof-buffer
      (user-error "*Proof* buffer does not exist"))

    ;; Get content from *Temp-Proof* after the first two lines
    (let ((content-to-copy
           (with-current-buffer temp-proof-buffer
             (save-excursion
               (goto-char (point-min))
               ;; Check if buffer has at least 3 lines
               (if (>= (count-lines (point-min) (point-max)) 3)
                   (progn
                     (forward-line 2) ; Move past the first two lines
                     (buffer-substring-no-properties (point) (point-max)))
                 ;; If less than 3 lines, copy nothing
                 (user-error "Nothing to commit from *Temp-Proof* buffer - temporary proof is empty"))))))

      ;; Append content and "(commit)" line to *Proof*
      (with-current-buffer proof-buffer
        (goto-char (point-max))
        ;; Insert the content from *Temp-Proof*
        (insert content-to-copy)

        ;; Ensure the buffer ends with a newline before adding the commit line
        (goto-char (point-max))
        (unless (or (= (point-min) (point-max)) ; Handle empty buffer
                    (eq (char-before (point-max)) ?\n))
          (insert "\n"))

        ;; Add the commit line and the final newline
        (insert "(commit)\n\n"))

      ;; Reset *Temp-Proof* buffer
      (with-current-buffer temp-proof-buffer
        (erase-buffer)
        (insert ";; Temporary proof steps in this buffer when actions are made\n\n"))

      (message "Committed temporary proof steps to *Proof* buffer."))))

;; qed
(defun proof-mode-qed-and-close ()
  "Append '(qed)' to the *Temp-Proof* buffer and close the current buffer."
  (interactive)
  (let ((temp-proof-buffer (get-buffer "*Temp-Proof*"))
        ;;(buffer-to-kill-1 (get-buffer "*Term*"))
        ;; (buffer-to-kill-2 (get-buffer "*Objective*"))
        )
    (unless temp-proof-buffer
      (user-error "*Temp-Proof* buffer does not exist"))

    ;; Append '(qed)' to *Temp-Proof*
    (with-current-buffer temp-proof-buffer
      (goto-char (point-max))
      ;; Ensure there's a newline before '(qed)' if buffer not empty
      (unless (or (= (point-min) (point-max))
                  (eq (char-before (point-max)) ?\n))
        (insert "\n"))
      (insert "(qed)\n"))

    ;; Todo, advice on if we delete them or not
					; (let ((window (get-buffer-window buffer-to-kill-1)))
					;     (when window
					;         (delete-window window)))
					; (kill-buffer buffer-to-kill-2)
					;         (let ((window (get-buffer-window buffer-to-kill-1)))
					;     (when window
					;         (delete-window window)))
					; (kill-buffer buffer-to-kill-2)
    (message "Qed current subgoal. Use C-c m to commit and C-c r to replay to see the effect.")))



;; Helper function to read all sexps from a string
(defun read-all-sexps-from-string (str)
  "Read all s-expressions from a string STR and return them as a list."
  (condition-case err
      (with-temp-buffer
        (insert str)
        (goto-char (point-min))
        (forward-line 2)
        (let ((sexps '()))
          ;; Skip initial whitespace/comments
          (skip-chars-forward " \t\n\r;")
          (while (not (eobp))
            (let ((start-pos (point)))
              ;; Use ignore-errors with read to handle potential EOF gracefully
              ;; after the last valid sexp but before actual eobp due to whitespace/comments.
              (let ((next-sexp (ignore-errors (read (current-buffer)))))
                ;; Only add non-nil results (read returns nil at EOF)
                (when next-sexp
                  (push next-sexp sexps))
                ;; Check if read consumed any input, if not, break to avoid infinite loop
                (when (= start-pos (point))
                  (goto-char (point-max)))) ; Force exit if stuck
              ;; Skip whitespace and comments after reading
              (skip-chars-forward " \t\n\r;")))
          (nreverse sexps)))
    (error (error "Error parsing proof log: %s" (error-message-string err)))))

;; replay a proof
(defun proof-mode-replay-proof ()
  "Replay the proof steps from the *Proof* buffer.
Reads the actions, calls 'replay-log', and updates the *Term*,
*Objective*, and *Goal* buffers with the final state."
  (interactive)
  ;; Assuming replay-log is available (e.g., replay.el loaded)
  (let* ((proof-buffer (get-buffer "*Proof*"))
         (goal-buffer (get-buffer "*Goal*"))
         (proof-content nil)
         (actions nil)
         (replay-result nil)
         (start-term nil)
         (start-objective nil)
         (final-term nil)
         (final-objective nil))

    ;; Check if necessary buffers exist
    (unless proof-buffer (user-error "*Proof* buffer not found."))
    (unless goal-buffer (user-error "*Goal* buffer not found."))

    ;; Read and parse proof content
    (setq proof-content (with-current-buffer proof-buffer (buffer-string)))
    (setq actions (read-all-sexps-from-string proof-content)) ; Error handled within helper

    ;; Replay the actions
    (condition-case err
        (setq replay-result (replay-log actions))
      (error (user-error "Error during proof replay: %s" (error-message-string err))))

    ;; Check replay result format
    (unless (and (listp replay-result) (= (length replay-result) 4))
      (user-error "Replay function returned unexpected result: %S" replay-result))

    ;; Check if proof has ended
    (if (not (nth 2 replay-result))
        (progn
          (message "Proof ended (replay-result: %s)" replay-result)
          ;; Update term and objective buffers to show proof is done
          (let ((term-buffer (get-buffer-create "*Term-0*"))
                (objective-buffer (get-buffer-create "*Objective-0*")))
            (with-current-buffer term-buffer
              (erase-buffer)
              (insert "Proof done."))
            (with-current-buffer objective-buffer
              (erase-buffer)
              (insert "Proof done."))
            (with-current-buffer goal-buffer
              (erase-buffer)
              (insert "Proof done."))))
      (progn
        (setq start-term (nth 0 replay-result))
        (setq start-objective (nth 1 replay-result))
        (setq final-term-objective-list (nth 2 replay-result))
        (setq current-index (nth 3 replay-result))

        ;; Todo, kill all terms and objective buffers

        ;; Update the *Term* and *Objective* buffers
        (let ((idx 0))
          (dolist (subgoal final-term-objective-list)
            (let ((term (car subgoal))
                  (objective (cadr subgoal))
                  (term-buffer (get-buffer-create (format "*Term-%d*" idx)))
                  (objective-buffer (get-buffer-create (format "*Objective-%d*" idx))))
              ;; Populate the specific Term buffer
              (with-current-buffer term-buffer
                (erase-buffer)
                (insert (format "Term of goal %d:\n\n%s\n" idx (prin1-to-string term))))
              ;; Populate the specific Objective buffer
              (with-current-buffer objective-buffer
                (erase-buffer)
                (insert (format "Objective of goal %d:\n\n%s\n" idx (prin1-to-string objective))))
              (setq idx (1+ idx)))))
        ;; Pop the current-index term and objective buffers to the screen
        (pop-to-buffer (get-buffer-create (format "*Term-%d*" current-index)))
        (pop-to-buffer (get-buffer-create (format "*Objective-%d*" current-index)))
        (select-window (get-buffer-window (format "*Term-%d*" current-index)))

        ;; Update *Goal* buffer
        (setq final-term (car (nth current-index final-term-objective-list)))
        (setq final-objective (cadr (nth current-index final-term-objective-list)))
        (with-current-buffer goal-buffer
          (erase-buffer)
          (insert "Current proof state:\n\n")
          (insert (format "Start term: %s\n" (prin1-to-string start-term)))
          (insert (format "Start goal: %s\n\n" (prin1-to-string start-objective)))
          (insert (format "%s/%s subgoal\n---------------\n%s <= %s\n\n"
			  (1+ current-index)
			  (length final-term-objective-list)
			  (prin1-to-string final-term)
			  (prin1-to-string final-objective)))
          ;; Print the remaining subgoals (after the current one)
          (let ((idx 0))
            (dolist (subgoal final-term-objective-list)
              ;; Check if the current index in the loop is greater than the active subgoal index
              (when (not (eq idx current-index))
                (let ((term (car subgoal))
                      (objective (cadr subgoal)))
                  (insert (format "%s/%s subgoal\n---------------\n%s <= %s\n\n"
                                  (1+ idx)
                                  (length final-term-objective-list)
                                  (prin1-to-string term)
                                  (prin1-to-string objective)))))
              (setq idx (1+ idx))))))))

  (message "Proof replayed successfully. Buffers updated."))


;; start compilation

(defun proof-mode-compile ()
  "Compile the term under the cursor if it's in a (<=-compile term) form."
  (interactive)
  (save-excursion
    (let* ((sexpr-text (thing-at-point 'sexp t))
           (sexpr (when sexpr-text (ignore-errors (read sexpr-text)))))
      (if (and (consp sexpr)
               (eq (car sexpr) '<=-compile)
               (= (length sexpr) 2))
          (let ((term (cadr sexpr)))
            (pss-compile term)
            (message "Compilation done for term: %S" term))
        (user-error (format "Cursor is not on a valid (<=-compile term) s-expression (cursor is on %s)" sexpr-text))))))

(defun pss-compile (term)
  "Top-level function to compile a term and write them in the *Obligations* buffer."
  (let ((result (pss-compile-term term)))
    (with-current-buffer (get-buffer-create "*Obligations*")
      (erase-buffer)
      (insert (format ";; Proof Obligations to compile %s\n\n" term))
      (dolist (po result)
        (let ((vars (car po))
              (arg (cadr po))
              (type (caddr po)))
          ;; Body of the outer let starts here
          (let ((fun-a (cl-reduce (lambda (acc v) `(FUN ,(car v) ,(cadr v) ,acc)) (reverse vars) :initial-value arg))
                (fun-b (cl-reduce (lambda (acc v) `(FUN ,(car v) ,(cadr v) ,acc)) (reverse vars) :initial-value type)))
            ;; Body of the inner let
            (if (and arg type)
                (insert (format "(<=p %S %S)\n" fun-a fun-b))
              (insert "--\n")))))))
  (let ((my-win (selected-window))
        (new-win (split-window-below)))
    (set-window-buffer new-win (get-buffer-create "*Obligations*"))
    (select-window new-win))

  (message "Proof Obligations written to *Obligations* buffer."))
