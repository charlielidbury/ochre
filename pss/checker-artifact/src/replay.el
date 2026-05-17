;; Replay a proof

(load "reduction.el")
(load "subtype.el")
(load "macroexpand.el")
(load "or-split.el")
(load "refl.el")
(load "path-management.el")

;; Map of action symbols to their implementation functions
(defvar *action-function-map*
  '((beta-substitute . beta-substitute-at-path)
    (beta-substitute-all . beta-substitute-all-at-path)
    (macro-expand . macro-expand-at-path)
    (macro-collapse . macro-collapse-at-path)
    (promote . promote-at-path)
    (split-or-all . split-or-at-path-all)
    )
  "Alist mapping action symbols from logs to their implementation functions.")

;; Replay a proof log represented as a list of actions.
;; Maintains a current term and objective, updating them based on rewrite actions.
;; Returns a list containing the start term, start objective, and a list of final (term objective) pairs.
;; Format: (start-term start-objective ((final-term final-objective) ...))
(defun replay-log (actions)
  "Replays a proof log represented as a list of actions.
Maintains a current term and objective, updating them based on rewrite actions.
Returns a list containing the start term, start objective, and a list of final (term objective) pairs.
Format: (start-term start-objective ((final-term final-objective) ...))"
  (let ((start-term nil)
        (start-objective nil)
        (action-function-map *action-function-map*)
        (current-list nil)
        (current-index 0))

    (dolist (action actions (list start-term start-objective current-list current-index)) ; Return final state
      (if (not (consp action))
          (error "Invalid action message: %S" action)
        (let ((action-type (car action))
              (current-term (when current-list (nth 0 (nth current-index current-list))))
              (current-objective (when current-list (nth 1 (nth current-index current-list)))))
          (cond
           ((eq action-type 'start-term)
            (when start-term (error "Term already initialized to %s while executing %s" start-term action))
            (setq start-term (cadr action))
            (message "Start Term: %S" start-term)
            (when (and start-term start-objective) (setq current-list (list (list start-term start-objective)))))
           ((eq action-type 'start-goal)
            (when start-objective (error "Goal already initialized to %s while executing %s" start-objective action))
            (setq start-objective (cadr action))
            (message "Start Goal: %S" start-objective)
            (when (and start-term start-objective) (setq current-list (list (list start-term start-objective)))))
           ((eq action-type 'rewrite)
            (let* ((params (cdr action))
                   (action-spec (pop params)) ; Can be a symbol or a list like (objective-or-split index)
                   (plist params) ; Remaining elements form a plist
                   (on-objectives (plist-get plist :on-objectives))
                   (path (plist-get plist :path))
                   (desc (plist-get plist :desc)) ; Description for logging
                   (target-expr (nth (if on-objectives 1 0) (nth current-index current-list)))
                   (result-expr nil)
                   (action-fn nil))

              (unless target-expr
                (error "Cannot perform rewrite: Target expression (%s) is nil for action %S."
                       (if on-objectives "objective" "term") action))

              ;; Use %S for desc as it might not always be a string
              (message "Applying: %S  Desc: %S" action desc)

              (if (consp action-spec) ; Handle special cases like (objective-or-split index)
                  (let ((composite-action-type (car action-spec)))
                    (cond
                     ((eq composite-action-type 'objective-or-split)
                      (let ((index (cadr action-spec)))
                        (setq result-expr (split-or-at-path target-expr path index))))
                     (t (error "Unknown composite rewrite action: %S" action-spec))))
                ;; Handle standard actions
                (progn
                  (setq action-fn (cdr (assoc action-spec action-function-map)))
                  (message "Action function: %S %S" action-fn action-spec)
                  (if action-fn
                      (let ((result (funcall action-fn target-expr path)))
                        (if (eq action-spec 'split-or-all)
                            ;; Some action that causes a split
                            (progn
                              (message "  Split generated %d goals." (length result))
                              (message "  Result: %S" result)
                              (setq result-expr (car result))
                              ;; Insert the rest of the results after the current index
                              (when (cdr result) ; Only insert if there are more results
                                (setq current-list
                                      (append (cl-subseq current-list 0 (1+ current-index))
                                              (mapcar (lambda (new-term) (list new-term current-objective)) (cdr result))
                                              (cl-subseq current-list (1+ current-index))))
                                (message "  Split generated %d additional goals." (length (cdr result)))))
                          ;; A regular action
                          (setq result-expr result)))
                    (error "Unknown rewrite action symbol: %S" action-spec))))

              ;; Update the correct state variable
              (setf (nth (if on-objectives 1 0) (nth current-index current-list)) result-expr)
              (message "  New %s: %S" (if on-objectives "Objective" "Term") result-expr)))
           ((eq action-type 'qed)
            (message "QED reached.  Final Term: %S  Final Objective: %S" current-term current-objective)

            (if (alpha-equivalent-p current-term current-objective)
                (progn
                  (message "Verification successful: term %s is alpha-equivalent objective %s."
                           current-term current-objective)
                  ;; Remove the successfully verified pair from the list
                  (setq current-list (append (cl-subseq current-list 0 current-index)
                                             (cl-subseq current-list (1+ current-index))))
                  (if (null current-list)
                      (message "All proof goals discharged.")
                    (message "Proof goal at index %d closed. %d remaining."
                             current-index (length current-list))))
              (warn "Verification failed: Term %s is NOT alpha-equivalent to objective %s." current-term current-objective))
            )
           ((eq action-type 'commit)
            (message "Commit action encountered (ignored).")
            ;; Do nothing for commit
            )
           ((eq action-type 'focus)
            (setq current-index (cadr action))
            (message "Focus %d." current-index)
            (if (>= current-index (length current-list))
                (error "Focus index %d out of bounds for list of length %d." current-index (length current-list))
              (message "Current term: %S  Current objective: %S" (nth 0 (nth current-index current-list))
                       (nth 1 (nth current-index current-list)))))
           (t
            (warn "Unknown action type in log: %S" action-type))))))))
