;; Utilities related to logging actions in proof mode

;; Structured log
(defun proof-log--log-action (buffer type path where description)
  "Append a formatted log entry to the BUFFER.
BUFFER is the buffer object or name.
TYPE is a symbol indicating the action type (e.g., 'beta-substitute).
PATH is a list of integers representing the location.
WHERE is a boolean indicating if the action is on objectives.
DESCRIPTION is a string describing the action."
  (let ((log-buffer (if (bufferp buffer) buffer (get-buffer-create buffer))))
    (with-current-buffer log-buffer
      (goto-char (point-max))
      ;; Ensure newline before adding content if buffer not empty
      (unless (bolp)
        (insert "\n"))
      (let ((log-entry (list 'rewrite type
                             :on-objectives where
                             :path path
                             :desc description))
            (print-length nil) ; Avoid truncation for long lists/paths
            (print-level nil))
        (prin1 log-entry (current-buffer))
        (insert "\n")))))

;; Raw logging
(defun proof-log--log-raw (buffer raw-string)
  "Append a raw string directly to the BUFFER.
BUFFER is the buffer object or name.
RAW-STRING is the string to append."
  (let ((log-buffer (if (bufferp buffer) buffer (get-buffer-create buffer))))
    (with-current-buffer log-buffer
      (goto-char (point-max))
      ;; Ensure newline before adding content if buffer not empty and not already at beginning of line
      (unless (bolp)
        (insert "\n"))
      (insert raw-string)
      ;; Ensure there's a newline after the raw string
      (unless (string-suffix-p "\n" raw-string)
        (insert "\n")))))