;; All the bindings of function to emacs shortcuts

;; Action commands
(load "interactive/action-command.el")
(global-set-key (kbd "C-c b") #'beta-substitute)
(global-set-key (kbd "C-c B") #'beta-substitute-all)
(global-set-key (kbd "C-c e") #'macro-expand)
(global-set-key (kbd "C-c E") #'macro-collapse)
(global-set-key (kbd "C-c p") #'promote)
(global-set-key (kbd "C-c o") #'split-or-all)
(global-set-key (kbd "C-c C-o 0") (lambda () (interactive) (objective-or-split 0)))
(global-set-key (kbd "C-c C-o 1") (lambda () (interactive) (objective-or-split 1)))

;; Proof mode commands
(load "interactive/proof-mode-command.el")
(global-set-key (kbd "C-c s") #'proof-mode-start-subtype-proof)
(global-set-key (kbd "C-c m") #'proof-mode-commit-temp-proof)
(global-set-key (kbd "C-c q") #'proof-mode-qed-and-close)
(global-set-key (kbd "C-c r") #'proof-mode-replay-proof)
(global-set-key (kbd "C-c S") #'proof-mode-compile)

;; Helpers commands
(load "interactive/helper-command.el")
(global-set-key (kbd "C-c c") #'copy-super-sexp-at-point)
