# Known issues that are being worked on

1. Programs with comments that have periods ('.') followed by whitespaces or newlines confuse the following functions:
  - `sercoq-exec-next-sentence` (bound to C-c C-n)
  - `sercoq-undo-previous-sentence` (bound to C-c C-u)
  
  However, note that the functions `sercoq-exec-buffer` (bound to C-c C-b), `sercoq-retract-buffer` (bound to C-c C-r), `sercoq-exec-region`, and `sercoq-cancel-statements-upto-point` work well and can be used as temporary workarounds until this issue is fixed.


2. Programs that are syntactially correct but have semantically incorrect show an error message but stil may get locked as read-only when executed, and may prevent the cancellation commands from working. 

This is because sercoq-mode locks the region if it parses successfully. A fix for this issue is in the works. For a temporary workaround, run `M-x` `sercoq-stop-sertop`, which will reset sercoq and switch to `fundamental-mode`. Then errors can be fixed and `sercoq-mode` can be enabled again. 
