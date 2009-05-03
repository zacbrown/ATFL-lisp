;; our environment registers
(defvar *stack* nil)
(defvar *env* nil)
(defvar *cont* nil)
(defvar *dump* nil)

;; helper functions

(defun index (n s)
  (if (eql n 0)
      (car s)
      (index (- n 1) (cdr s))))

(defun locate (ind env)
  (let ((n (cdr ind))
        (b (car ind)))
    (index n (index b env))
    ))

;; op-code definitions
(defun op-LDC ()
  (push (pop *cont*) *stack*))

(defun op-ADD ()
  (push (+ (pop *stack*) (pop *stack*)) *stack*))

(defun op-SUB ()
  (push (- (pop *stack*) (pop *stack*)) *stack*))

(defun op-MUL ()
  (push (* (pop *stack*) (pop *stack*)) *stack*))

(defun op-DIV ()
  (push (/ (pop *stack*) (pop *stack*)) *stack*))

(defun op-REM ()
  (push (mod (pop *stack*) (pop *stack*)) *stack*))

(defun op-EQ ()
  (push (eql (pop *stack*) (pop *stack*)) *stack*))

(defun op-LEQ ()
  (push (<= (pop *stack*) (pop *stack*)) *stack*))

(defun op-CONS ()
  (push (cons (pop *stack*) (pop *stack*)) *stack*))

(defun op-CAR ()
  (push (car (pop *stack*)) *stack*))

(defun op-CDR ()
  (push (cdr (pop *stack*)) *stack*))

(defun op-ATOM ()
  (push (atom (pop *stack*)) *stack*))

(defun op-LD ()
  (let ((ind (pop *cont*)))
    (let ((x (locate ind *env*)))
      (push x *stack*))))

(defun op-SEL ()
  (let ((ct (pop *cont*))
        (cf (pop *cont*))
        (x (pop *stack*)))
    (push *cont* *dump*)
    (if x
        (setf *cont* ct)
        (setf *cont* cf))))

(defun op-JOIN ()
  (setf *cont* (pop *dump*)))

(defun op-LDF ()
  (let ((func (pop *cont*))
        (env (copy-list *env*)))
    (let ((func-closure (cons func (list env))))
      (push func-closure *stack*))))

(defun op-AP ()
  (let ((func-closure (pop *stack*))
        (args (pop *stack*)))
    (let ((new-cont (car func-closure))
          (new-env (cadr func-closure)))
      (push *cont* *dump*)
      (push *env* *dump*)
      (push *stack* *dump*)
      (setf *cont* new-cont)
      (setf *env* new-env)
      (setf *stack* nil)
      (push args *env*))))

(defun op-RTN ()
  (let ((old-stack (pop *dump*))
        (old-env (pop *dump*))
        (old-cont (pop *dump*))
        (ret-val (pop *stack*)))
    (setf *stack* old-stack)
    (setf *env* old-env)
    (setf *cont* old-cont)
    (push ret-val *stack*)))

(defun op-STOP ()
  (setf *cont* nil))

(defun op-DUM ()
  (cons (list nil) *env*))

(defun op-RAP ()
  (let ((func-closure (pop *stack*))
        (args (pop *stack*)))
    (let ((new-cont (car func-closure))
          (new-env (cadr func-closure)))
      (push *cont* *dump*)
      (push *env* *dump*)
      (push *stack* *dump*)
      (setf *cont* new-cont)
      (setf *stack* nil)
      (setf *env* (rplaca new-env args)))))

(defun op-PRINT ()
  (format t "~a" (pop *stack*)))

(defun op-PRINTLN ()
  (format t "~a~%" (pop *stack*)))

;; define our LispKit compiler and helpers

(defun location (x n)
  (if (find x (car n))
      (cons 0 (position x (car n)))
      (let ((z (location x (cdr n))))
        (cons (+ (car z) 1) (cdr z)))))

(defun vars (d)
  (if (eql d nil)
      nil
      (cons (caar d) (vars (cdr d)))))

(defun exprs (d)
  (if (eql d nil)
      nil
      (cons (cdar d) (exprs (cdr d)))))

(defun complis (expr env code)
  (if (eql expr nil)
      (cons 'LDC (cons 'NIL code))
      (complis (cdr expr) env (comp (car expr) env (cons 'CONS code)))))

(defun comp (expr env code)
  (cond
    ((atom expr) (cons 'LD (cons (location expr env) code)))
    ((eql (car expr) 'quote) (cons 'LDC (cons (cadr expr) code)))
    ((eql (car expr) 'add)
     (comp (cadr expr) env (comp (caddr expr) env (cons 'ADD code))))
    ((eql (car expr) 'sub)
     (comp (cadr expr) env (comp (caddr expr) env (cons 'SUB code))))
    ((eql (car expr) 'mul)
     (comp (cadr expr) env (comp (caddr expr) env (cons 'MUL code))))
    ((eql (car expr) 'div)
     (comp (cadr expr) env (comp (caddr expr) env (cons 'DIV code))))
    ((eql (car expr) 'rem)
     (comp (cadr expr) env (comp (caddr expr) env (cons 'REM code))))
    ((eql (car expr) 'eq)
     (comp (cadr expr) env (comp (caddr expr) env (cons 'EQ code))))
    ((eql (car expr) 'leq)
     (comp (cadr expr) env (comp (caddr expr) env (cons 'LEQ code))))
    ((eql (car expr) 'car)
     (comp (cadr expr) env (cons 'CAR code)))
    ((eql (car expr) 'cdr)
     (comp (cadr expr) env (cons 'CDR code)))
    ((eql (car expr) 'atom)
     (comp (cadr expr) env (cons 'ATOM code)))
    ((eql (car expr) 'cons)
     (comp (caddr expr) env (comp (cadr expr) env (cons 'CONS code))))
    ((eql (car expr) 'if)
     (let ((thenpt (comp (caddr expr) env '(JOIN)))
           (elsept (comp (cadddr expr) env '(JOIN))))
       (comp (caddr expr) env (cons 'SEL (cons thenpt (cons elsept code))))))
    ((eql (car expr) 'lambda)
     (let ((body (comp (caddr expr) (cons (cadr expr) env) '(RTN))))
       (cons 'LDF (cons body code))))
    ((eql (car expr) 'let)
     (let ((args (exprs (cddr expr)))
           (m (cons (vars (cddr expr)) env)))
       (let ((body (comp (cadr expr) m '(RTN))))
         (complis args env (cons 'LDF (cons body (cons 'AP code)))))))
    ((eql (car expr) 'letrec)
     (let ((m (cons (vars (cddr expr)) env))
           (args (exprs (cddr expr))))
       (let ((body (comp (cadr expr) m '(RTN))))
         (cons 'DUM
               (complis args m (cons 'LDF (cons body (cons 'RAP code))))))))
    )
  (complis (cdr expr) env (comp (car expr) env (cons 'AP code)))
  )
