;;; sercoq-queue.el -- A small library that implements a fifo queue

;;; Commentary:

;; The queue is implemented as a cons cell of two lists, a front and a back list.
;; For enqueueing, the element is consed to the front of the back list.
;; For dequeueing, the first element of the front list is popped.  If the front list is empty, the front list is set to reverse of the back list and the back list is set to empty.

;;; Code:

(defun sercoq-queue-create (&optional elements)
  "Create a queue, with contents from the list ELEMENTS, with the first element being the head of the queue and the last being the tail."
  (when (not (listp elements))
      (setq elements (list elements)))
  (cons elements nil))


(defun sercoq-queue-emptyp (queue)
  "Return t if QUEUE is empty and nil otherwise."
  (and (consp queue)
       (null (car queue))
       (null (cdr queue))))


(defun sercoq-queue-exchange (queue)
  "Return a queue with the front list as reverse of the back list and the back list nil if the front list of QUEUE is empty."
  (if (null (car queue))
      (cons (nreverse (cdr queue)) nil)
    queue))


(defun sercoq-queue-enqueue (element queue)
  "Enqueue ELEMENT into QUEUE."
  (if (consp queue)
      (progn (setcdr queue (cons element (cdr queue)))
	     queue)
    (error "Queue must be a cons cell")))


(defun sercoq-queue-dequeue (queue)
  "Return a cons cell whose car is a new queue with the front element removed from QUEUE and cdr is the removed element."
  (if (sercoq-queue-emptyp queue)
      (error "Attempt to dequeue empty queue")
    (let ((q (sercoq-queue-exchange queue)))
      (cons (cons (cdr (car q)) (cdr q)) ;; dequeued queue
	    (car (car q)))))) ;; dequeued element


(defun sercoq-queue-front (queue)
  "Return the front of QUEUE without removing it from the queue."
  (if (sercoq-queue-emptyp queue)
      nil
    (car (car (sercoq-queue-exchange queue)))))


(provide 'sercoq-queue)

;;; sercoq-queue.el ends here
