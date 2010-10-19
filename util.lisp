;;; -*- Mode: Lisp; Syntax: Common-Lisp; -*-
;;; ---------------------------------------------------------------------------
;;; File:         util.lisp
;;; Description:  Generic Utility Functions
;;; Date:         5/07
;;; Package:      CL-USER
;;; ---------------------------------------------------------------------------
;; Util.lisp


#|
These functions exhibit mostly system (SBCL) dependent behavoir.  Written 
original for CMUCL in 2004 and since then ported to SBCL
|#

(in-package :cl-user)

;; Compose a function
(defmacro compose (&rest rest)
  (let ((fn (nreverse rest)))
    `(lambda (&rest args)
      (fold (lambda (fn arg) (funcall fn arg)) (apply ,(car fn) args) (list ,@(cdr fn))))))

(defmacro For-Each (p list)
  "Similar to foreach in scheme aka map nil"
  `(map nil ,p ,list))


(defmacro cut (fn &rest body)
  (let* ((fn-args '())
         (rest nil)
         (call
          (mapcar (lambda (item)
                    (cond ((eq item '<>) 
                           (car (push (gensym) fn-args)))
                          ((and (eq item '<...>) (null rest))
                           (car (push (gensym) rest)))
                          ((eq item '<...>)
                           (error "Only one rest paramters allowed per cut"))
                          (t item))) body))
         (fargs (nreverse 
                 (if (null rest) 
                     fn-args 
                   (list* (car rest) '&rest fn-args)))))
    `(lambda ,fargs (funcall ,fn ,@call))))

(defmacro cute (fn &rest body)
  (let* ((expr nil)
        (arg
         (mapcar (lambda (item)
               (if (listp item) 
                   (let ((sym (gensym)))
                     (push (list sym item) expr)
                     sym)
                 item)) body)))
    `(let* ,(nreverse expr)
       (cut ,fn ,@arg))))

(defmacro poll (time &rest body)
  "Every given seconds do body"
  (let ((t1 (gensym))
        (t2 (gensym))
        (t-final (gensym)))
    `(loop while t for ,t1 = (Get-Internal-Real-Time) do
      (progn
        ,@body
        (let* ((,t2 (Get-Internal-Real-Time))
               (,t-final 
                (- ,time
                   (/ (- ,t2 ,t1)
                      Internal-Time-Units-Per-Second))))
          (if (> ,t-final 0)
              (sleep ,t-final)))))))

;; ###########################################################################

;; Lambda Functions ##########################################################

(defmacro Make-Thunk (&rest body)
  "Make a thunk.  A lamba with no arguments"
  `(lambda () ,@body))

(defmacro Make-N-Thunk (&rest body)
  "Make N-arity thunk.  Make a thunk which accepts any arguements but
ignores them"
  (let ((arg (gensym)))
    `(lambda (&rest ,arg) 
      (declare (ignore ,arg)) ,@body)))

(defmacro Make-Hook (fun)
  "Make a hook;  A hook is a lambda wrapped around a function, any args passed
to the lambda will get passed to the function"
  `(lambda (&rest args) (apply #',fun args)))


;; Hashtable Functions #######################################################
(declaim (inline duplicate-hash-table))
(defun Duplicate-Hash-Table (table)
  (declare (optimize (safety 0) (debug 0)))
  "Make a shallow copy of the hashtable"
  (let ((newtable (Make-Hash-table)))
    (Maphash (lambda (k v)
               (setf (Gethash k newtable) v))
             table)
    newtable))
       
(declaim (inline print-hash-table))
(defun Print-Hash-Table (table &optional (stream t) (arrow "=>"))
  (declare (optimize (safety 0) (debug 0)))
  "Print a hashtable's contents non-readably to a stream (Useful for debugging)"
  (Maphash (cut #'format stream "~A~A~A~%" <> arrow <>) table)
  (values))


(declaim (inline assoc-to-hash-table))
(defun Assoc-To-Hash-Table (assoc &optional (hash (make-hash-table)))
  (declare (optimize (safety 0) (debug 0)))
  "Convert an associated list to a hashtable.  Key is car; Value is cdr."
  (For-Each (lambda (item)
              (setf (gethash (car item) hash) (cdr item))) 
            assoc)
  hash)

(declaim (inline hash-table-to-assoc))
(defun Hash-Table-To-Assoc (table)
  (declare (optimize (safety 0) (debug 0)))
  "Convert a hashtable to an associated list
  of ((KEY . VALUE)...) form"
  (let ((list nil))
    (Maphash (lambda (k v) (Push (cons k v) list)) table)
    list))





;; List Functions ############################################################

(defmacro push-when (test value list)
  "Push when test is true.  FYI, list is evaluted twice."
  `(if ,test
      (push ,value ,list)
      ,list))

(defmacro push-unless (test value list)
  "Push unless test is true.  FYI, list is evaluted twice."
  `(if ,test
      ,list
      (push ,value ,list)))

;;;; The following are lifted from SRFI-1 in scheme and also from SML/NJ
;;;; *Note*: this is not nearly complete, I add them as I need them -jb

;; this is actually adapted from SRFI-1 document by Olin Shiver's
(declaim (inline zip))
(defun Zip (list &rest lists)
  (apply #'mapcar #'list list lists))

(declaim (inline Unzip1))
(defun Unzip1 (list)
  (mapcar #'car list))

(declaim (inline Unzip2))
(defun Unzip2 (list)
  (let ((a '())
        (b '()))
    (for-each (lambda (i) (push (first i) a) (push (second i) b)) list)
    (values (nreverse a) (nreverse b))))

(declaim (inline count-occurances))
(defun count-occurances (p list)
  "Similar to COUNT in srfi-1, different from COUNT in ANSI CL"
  (loop for i in list
        with count = 0
        when (funcall p i)
        do
        (incf count)
        finally (return count)))

(declaim (inline Unzip3))
(defun Unzip3 (list)
  (let ((a '())
        (b '())
        (c '()))
    (for-each (lambda (i) 
                (push (first i) a) 
                (push (second i) b)
                (push (third i) c)) list)
    (values (nreverse a) (nreverse b) (nreverse c))))

(defmacro NConstruct (item list list-tail)
  ;;Bad macro but works
  "Destructively Construct a list append an item onto list-tail: Note this macro isn't well written and requires all variables as arguements"
  `(progn
    (setf (cdr ,item) nil)
    (if (null ,list)
        (progn
          (setf ,list ,item)
          (setf ,list-tail ,item))
        (progn
          (setf (cdr ,list-tail) ,item)
          (setf ,list-tail ,item)))))

(declaim (inline NPartition))
(defun NPartition (p list)
  "Destructively split a list into two parts (values), those that fulfill p and those that don't"
  (let ((members nil)
        (members-tl nil)
        (non-members nil)
        (non-members-tl nil))
    (do ((item list rest)
         (rest (cdr list) (cdr rest)))
        ((null item) (values members non-members))
      (if (funcall p (car item))
          (nconstruct item members members-tl)
          (nconstruct item non-members non-members-tl)))))


(declaim (inline Partition))
(defun Partition (p list)
  "Split a list into two parts (values), those that fulfill p and those that don't"
  (let ((members nil)
        (non-members nil))
    (for-each (lambda (i) 
                (if (funcall p i)
                    (push i members)
                    (push i non-members)))
              list)
    (values (nreverse members) (nreverse non-members))))

(declaim (inline NTake-while))
(defun NTake-While (p list)
  "Return the list ending when p is no longer true.  Destroys list"
  (let ((l nil)
        (end-of-list nil))
    (for-each (lambda (i) (if (funcall p i) (nconstruct i l end-of-list)))
              list)))
  

(declaim (inline Take-while))
(defun Take-while (p list)
  "Return the list ending when p is no longer true"
  (loop for item in list
        while (funcall p item)
        collect item))

(declaim (inline Take))
(defun Take (l n)
  "Return a list ending at the nth element"
  (loop for item in l
        for i from n downto 1
        collect item))
         

(declaim (inline Drop-while))
(defun Drop-While (p list)
  "Return the list starting from when p isn't true"
  (do ((result list (cdr result))
       (item (car list) (car result)))
      ((not (funcall p item)) result)))
    


(declaim (inline Drop))
(defun Drop (l n)
  "Return a list starting at the nth element"
  (loop for item on l
        for i from n downto 1
        finally (return item)))

(declaim (inline Span))
(defun Span (p list)
  "Break a list in two parts, when p stops being true"
  (do ((item (car list) (car rest))
       (rest (cdr list) (cdr rest))
       (buffer nil))
      ((not (funcall p item)) (values (nreverse buffer) rest))
    (push item buffer)))

(declaim (inline NSpan))
(defun NSpan (p list)
  "Break list into two parts when p stops being true.  Will destroy list"
  (do ((item list rest)
       (rest (cdr list) (cdr rest))
       (buffer nil)
       (end-of-buffer nil))
      ((not (funcall p (car item))) (values buffer item))
    (nconstruct item buffer end-of-buffer)))


(declaim (inline Break-list))
(defun Break-List (p list)
  "Break a list in two parts, when p starts being true"
  (do ((item (car list) (car rest))
       (rest (cdr list) (cdr rest))
       (buffer nil))
      ((funcall p item) (values (nreverse buffer) rest))
    (push item buffer)))

(declaim (inline NBreak-list))
(defun NBreak-List (p list)
  "Break list into two parts, when p starts being true.  Will destroy list"
  (do ((item list rest)
       (rest (cdr list) (cdr rest))
       (buffer nil)
       (end-of-buffer nil))
      ((funcall p (car item)) (values buffer item))
    (nconstruct item buffer end-of-buffer)))


(defun Fold (f default list)
  "Fold left"
  (if (null list)
      default
    (reduce f list :initial-value default)))
;;      (fold f (funcall f (car list) default) (cdr list))))

(defun Fold-right (f default list)
  "Fold right"
    (reduce f list :from-end t :initial-value default))
;;  (fold f default (reverse list)))

(declaim (inline filter))
(defun Filter (p list)
  (declare 
   (type function p)
   (type list list)
   (optimize (speed 3) (safety 0) (debug 0)))
  "SML like filter function; collects member of the list that satisfy a predicate"
  (loop for x in list when (funcall p x) collect x))
 
(declaim (inline nfilter))
(defun NFilter (p list)
  "SML like filter function, *DESTRUCTIVELY* collects member of the list that satisfy a predicate."
  (let ((l '())
        (end '()))
    (do ((i list rest)
         (rest (cdr list) (cdr rest)))
        ((null rest) l)
      (when (funcall p (car i))
        (nconstruct i l end)))))

(declaim (inline list-tabulate))
(defun list-tabulate (n p)
  (loop for i from 0 upto (- n 1)
        collect
        (funcall p i)))

;;;; end of SRFI-1 like functions

;;;;; plist functions

(declaim (inline for-each-plist))
(defun for-each-plist (fn list)
  "Map plist"
  (loop for list on list by #'cddr
        for property = (First list) 
        for value = (Second list) 
        do (funcall fn property value)))


(declaim (inline map-plist))
(defun map-plist (fn list)
  "Map plist"
  (loop for list on list by #'cddr
        for property = (First list) 
        for value = (Second list) 
        collect (funcall fn property value)))

;; String Functions ##########################################################



(declaim (inline String-To-Symbol))
(defun String-To-Symbol (str &optional (package *package*))
  (declare 
   (type simple-base-string str)
   (optimize (speed 3) (safety 0) (debug 0)))
  "Convert a string to a non-escaped symbol.
This is a wrapper for intern that converts the string to whatever the readtable expects"
  (let ((c (readtable-case *readtable*)))
    (intern
     (cond ((eq c :Upcase) (String-Upcase str))
           ((eq c :Downcase) (String-Downcase str))
           (t (String-Capitalize str)))
     package)))

    
(declaim (inline n-string-equal))
(defun N-String-equal (str1 str2)
  (declare (type simple-base-string str1)
           (type simple-base-string str2)
           (optimize (speed 3) (safety 0) (debug 0)))
  "Compare strings, based on the length of the smallest one"

    (= (or (string<= str1 str2) 0) (length str1)))
    

(defun n-split-string (n string &optional (char #\space))
  "Split string n times"
  (let ((output (Make-String-Output-Stream))
        (values nil)
        (n n))
    (labels ((add ()
               (let ((s (Get-Output-Stream-String output)))
                 (unless (String= s "")
                   (decf n)
                   (push s values)))))
      (loop for c across string
            do
            (cond ((= n 0) (Write-Char c output))
                  ((Char= c char) (Add))
                  (t (Write-Char c output))))
      (Add)
      (nreverse values))))

(defun split-string (string &optional (char #\space))
  "Split a string"
  (let ((output (Make-String-Output-Stream))
        (values nil))
    (labels ((add ()
               (let ((s (Get-Output-Stream-String output)))
                 (unless (String= s "")
                   (push s values)))))
      (loop for c across string
            do
            (if (Char= c char)
                (Add)
                (Write-Char c output)))
      (Add)
      (nreverse values))))

(declaim (inline i-string=))
(defun i-string= (a b)
  "Compare string case insensitive"
  (if (= (length a) (length b))
      (loop for c across a
            for d across b
            unless (Char= (Char-Downcase c) (Char-Downcase d))
            do
            (return nil)
            finally (return t))
      nil))



;; Misc Functions ############################################################

;; 
(defun memo-lambda (fn &key (key #'first) (test #'eql))
  "Memo lambda, will not respond to clearing"
  (let ((table (make-hash-table :test test)))
    (lambda (&rest args)
      (let ((k (funcall key args)))
        (multiple-value-bind (val foundp) (gethash k table)
            (if foundp
                val
                (setf (gethash k table) (apply fn args))))))))


;; memo functions  are from PAIP
(defun memo (fn name key test)
  "Memoize a lambda, only works if it's idempotent"
  (let ((table (make-hash-table :test test)))
    (setf (get name 'memo) table)
    (lambda (&rest args)
      (let ((k (funcall key args)))
      (multiple-value-bind (val foundp)
          (gethash k table)
        (if foundp
            val
            (setf (gethash k table) (apply fn args))))))))

(defun memoize (fn &key (key #'first) (test #'eql))
  "Memoize a function, only works if it's idempotent"
  (setf (symbol-function fn) (memo (symbol-function fn) fn key test)))

(defun clear-memoize (fn)
  (let ((table (get fn 'memo)))
    (when table (clrhash table))))

(defmacro defun-memo (fn args &body body)
  `(memoize (defun ,fn ,args . ,body)))


;;;; more Misc

(declaim (inline symbol-equal))
(defun symbol-equal (x y  &key (ignore-case nil))
  "Symbol compare without regard for packages I have founds this is only
really useful during macro expansion time when you don't necessarily
want a keyword or when doing symbol manipulation from an I/O source
(where a normal read will intern them into current package).  If the latter 
is the case within-package might be of use."
  (and (symbolp x) (symbolp y)
       (funcall (if ignore-case #'i-string= #'string=)  (symbol-name x) (symbol-name y))))




(defmacro deflambda (v l)
  "Similar to scheme's (define f (lambda ...))"
  `(setf (symbol-function ',v) ,l))


(defmacro with-gensyms ((&rest vars) &rest body)
  `(let ,(mapcar (lambda (v) (list v '(gensym))) vars)
    ,@body))
  

(defun read-chars (&optional (stream *standard-input*))
  "Read all chars on a stream"
  (loop for input = (ignore-errors (read-char stream nil nil))
        while input
        collect input))

(defun read-lines (&optional (stream *standard-input*))
  "Read all lines on a stream"
  (loop for input = (ignore-errors (read-line stream nil nil))
      while input
      collect input))

(defmacro read-lines-until (p &optional (stream *standard-input*))
  "Read lines until p returns t."
  (with-gensyms (pred str input)
    `(let* ((,pred ,p) (,str ,stream))
      (loop for ,input = (read-line ,str nil nil)
       while (and ,input (not (funcall ,pred ,input)))
       collect ,input))))

(declaim (inline blank-line-p))
(defun blank-line-p (s)
  (string= s ""))

;; This was inspired by a conversation on c.l.l but shares no 
;; code with it
(defmacro make-fsm (args init-state end-states &body states)
  "Create a fsm.  Returns CLOSURE over a FSM.
Syntax: (make-fsm <arguement lambda list> 
          <start state> (<end state1> <end state2> ...)
          (<state name> <body> (values <next state to go to> 
                                       <misc values...>))   ... )"

  (let ((state (Gensym))
        (valid-states (Gensym))
        (new-state (Gensym))
        (result (Gensym)))
    `(let ((,state ,init-state)
           (,valid-states  
            ',(append end-states (unzip1 states))))
      (lambda ,args
        (if (member ,state ',end-states)
            (values t ,state)
            (let* ((,result (multiple-value-list (case ,state ,@states)))
                   (,new-state (car ,result)))
              (unless (member ,new-state ,valid-states) 
                (error "Invalid state"))
              (setq ,state ,new-state)
              ,result))))))


(defmacro within-package (pkg &rest body) 
  "Execute body in the specified package (package may be symbol name)
Note:  no guarantee about what is used or imported in to the specified
package.  FQN might not be a bad idea"
  (let ((p (gensym)) 
        (result (gensym)))
    `(let ((,p *package*)) 
      (in-package ,pkg) 
      (let ((,result (progn ,@body)))
        (setf *package* ,p)
        ,result))))




;; Anaphoric Macros ##########################################################

#|
Macros in this section were inspired by paul graham, although honestly
I caught this section just skimming and I have no idea how he implements
them or if these even fit his definition

The one thing I did take from him (and from SML) is everything 
all anaphora are bound to it ('it is external in this package)
if you use the package you should be able to just use the symbol
it
|#

(defmacro aif (if then &optional (else nil))
  "Anaphoric if"
  `(let ((it ,if))
    (if it
        ,then
        ,else)))

(defmacro awhen (if then)
  "Anaphoric when"
  `(aif ,if ,then))

(defmacro aunless (if else)
  "Anaphoric unless"
  `(aif (not ,if) ,else))

(defmacro acond (&rest conds)
  "Anaphoric cond"
  `(let ((it nil))
    (cond
      ,@(loop for item in conds
              collect
              (list* `(setq it ,(car item)) (cdr item))))))
    
;; Pattern Matching Macros ###################################################

#| 
   This is partially inspired by PAIP by Norvig and a bit from Bigloo's
   nice match-lambda and match-case facility.  Although, I have no bloody
   idea how the latter is implemented.
|#

(defun Variablep (x)
  (and (Symbolp x) (> (Length (Symbol-Name x)) 1) 
       (Char= (Elt (Symbol-Name x) 0) #\?)))

(defun Variable-Name (x)
  (String-To-Symbol (Subseq (Symbol-Name x) 1)))

(defun Variable-Match (pattern input bindings)
  (let* ((pat (car pattern))
         (inp (car input))
         (val (assoc (variable-name pat) bindings)))
    (cond ((Null val) ;; no existing binding
           (Pattern-Match (cdr pattern) (cdr input) 
                          (cons (cons (Variable-Name pat) inp) bindings)))
          ((Eql (cdr val) inp) ;; existing binding that matches this symbol
           (Pattern-Match (cdr pattern) (cdr input) bindings))
          (t nil))))

(defun Segmentp (x)
  (And (Symbolp x) (> (length (Symbol-Name x)) 2) 
       (String= (Subseq (Symbol-Name x) 0 2) "?*")))

(defun Segment-Name (x)
  "Create a variable for a segment"
   (String-To-Symbol (subseq (Symbol-Name x) 2)))

(defun Segment-Match (pattern input bindings &optional (start 0))
  "Segment match against a rule"
  (if (Null (cadr pattern)) ;; last match
      (cons (cons (Segment-Name (car pattern)) input) bindings)
      (let ((pos (Position (Second pattern) input :start start))
            (name (Segment-Name (car pattern))))
        (if pos
            (or
             (pattern-match (cdr pattern) (drop input pos)
                            (cons (cons name (take input pos)) bindings))
             (Segment-Match pattern input bindings (1+ pos)))
            nil))))


(defun collect-variables (pattern)
  (loop for item in pattern
        with list = nil
        for it = (variablep item)
        if (or it (segmentp item))
        do (pushnew (if it (variable-name item) (segment-name item)) list)
        finally (return (nreverse list))))


(defmacro match-lambda (pattern-rules)
  "Match a case wrapped up in a lambda awaiting a case to try to match"
  (with-gensyms (patterns pattern rule input match)
    `(let ((,patterns (list ,@(loop for (pattern . rule) in pattern-rules
                                    for vars = (collect-variables pattern)
                                    collect
                                    `(list ',pattern (lambda ,vars ,@rule))))))
           (lambda (,input)
             (loop for (,pattern ,rule) in ,patterns
                   do
                   (let ((,match (pattern-match ,pattern ,input)))
                     (if ,match
                         (return 
                           (apply ,rule 
                                  (nreverse (mapcar #'cdr ,match)))))))))))
  
(defmacro match-case (case pattern-rules)
  "Match a case against patterns and apply arguements collected by patterns
to a specified lambda.  Patterns can contain a ?<symbol> which binds to a 
value, and a ?*<symbol> which binds a list of things to the symbol.  A symbol
can only be of either type.  Pattern-rules are a list followed by a body
the body is turned into a lambda with the variables listed in the pattern
as arguements.  
E.g.  (case-match '(a 3 b) (((a ?x b) (print x)) ((b ?y c) (print y)))) would
match a ?x b then (lambda (x) (print x)) would be called with 3 as an arguement."
  (with-gensyms (input)
    `(let* ((,input ,case)) ;; just to ensure case gets eval'd first
      (funcall (match-lambda ,pattern-rules) ,input))))


(defun pattern-match (pattern input &optional (bindings nil))
  "Pattern match against a rule"
  (let ((pat (car pattern))
        (inp (car input)))
  ;; if no more input and no more pattern return bindings or t
    (cond ((and (null pattern) (null input)) (or bindings t))
          ((segmentp pat) ;; check for variable length matches
           (segment-match pattern input bindings))
          ((variablep pat) ;; check variables match
           (variable-match pattern input bindings))

          ((eql pat inp) ;; check if tokens are the same
           (pattern-match (cdr pattern) (cdr input) bindings))
          (t nil)))) ;; otherwise we failed