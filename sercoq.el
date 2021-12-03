;;; sercoq.el --- Major mode for interacting with Coq proof assistant using SerAPI

;;; Commentary:

;;; Code:

;; hook for the mode

(defcustom sercoq-mode-hook nil
  "Hook run when entering sercoq-mode."
  :type 'hook
  :options '(turn-on-auto-fill flyspell-mode)
  :group 'text)


;; keymap for the mode

(defvar sercoq-mode-map
  (let ((map (make-keymap)))
    (define-key map (kbd "<C-return>") 'evaluate-until-point)
    map)
  "Keymap for sercoq major mode.")


;; syntax table for the mode

(defvar sercoq-mode-syntax-table
  (let ((syntable (make-syntax-table)))
    syntable)
  "Syntax table for sercoq-mode.")


(defun sercoq-mode ()
  "Major mode for interacting with Coq."
  (interactive)
  (kill-all-local-variables)
  (setq major-mode 'sercoq-mode)
  (setq mode-name "Sercoq")
  (use-local-map sercoq-mode-map)
  (set-syntax-table sercoq-mode-syntax-table)
  (run-hooks 'sercoq-mode-hook))

(provide 'sercoq)

;;; sercoq.el ends here
