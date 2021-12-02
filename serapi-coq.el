;;; serapi-coq.el --- Major mode for interacting with Coq proof assistant using SerAPI

;;; Commentary:

;;; Code:

;; hook for the mode

(defcustom serapi-coq-mode-hook nil
  "Hook run when entering serapi-coq-mode."
  :type 'hook
  :options '(turn-on-auto-fill flyspell-mode)
  :group 'text)


;; keymap for the mode

(defvar serapi-coq-mode-map
  (let ((map (make-keymap)))
    (define-key map (kbd "<C-return>") 'evaluate-until-point)
    map)
  "Keymap for serapi-coq major mode.")


;; syntax table for the mode

(defvar serapi-coq-mode-syntax-table
  (let ((syntable (make-syntax-table)))
    syntable)
  "Syntax table for serapi-coq-mode.")


(defun serapi-coq-mode ()
  "Major mode for interacting with Coq."
  (interactive)
  (kill-all-local-variables)
  (setq major-mode 'serapi-coq-mode)
  (setq mode-name "Serapi-Coq")
  (use-local-map serapi-coq-mode-map)
  (set-syntax-table serapi-coq-mode-syntax-table)
  (run-hooks 'serapi-coq-mode-hook))

(provide 'serapi-coq)

;;; serapi-coq.el ends here
