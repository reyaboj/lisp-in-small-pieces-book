;;; smol1.el --- A scheme interpreter -*- lexical-binding: t; -*-

;; Copyright (C) 2024 Md Istiaque Al Jobayer

;; Author: Md Istiaque Al Jobayer <mdia.jobayer+lisp@gmail.com>
;; Maintainer: Md Istiaque Al Jobayer <mdia.jobayer+lisp@gmail.com>
;; Keywords: scheme, interpreter, lisp, metacircular
;; URL: https://github.com/reyaboj/lisp-in-small-pieces-book
;; Package-Requires: ((emacs "29.4"))

;; This file is not part of GNU Emacs.

;;; Commentary:
;; This is an implementation of the interpreter described in chapter 1 of the
;; book, Lisp in Small Pieces.  The focus is on clarity and pedagogic value over
;; efficiency, so newcomers to Lisp (or Scheme) may find this valuable in their
;; study of Lisp and its fundamental building blocks.  The curious reader will
;; benefit from perusing the accompanying test suite, where the evaluator's
;; expected input-output relations are clearly declared for verification,
;; insofar as realistically possible.

;;; Code:

(require 'cl-lib)

(defun smol1-eval (exp &optional env)
  "Evaluate EXP as a smol1 program, using ENV as the environment of bindings for
free variables. The smol1 dialect is a subset of scheme.

The following forms F are evaluated:

  a symbol S is evaluated as a variable reference;
    when S is `$t' or `'$f', S evaluates to the true / false booleans

  numbers, characters, strings, and vectors evaluate to themselves
    vector elements are not evaluated (i.e., they are implicitly quoted)

  a list of the form (OPERATOR OPERAND ...) is evaluated as follows
    if OPERATOR is not special:
      F <- evaluate OPERATOR
      X <- list of (evaluate OPERAND ...)
      evaluate the body of F with its formal parameters bound to corresponding
      values (matched positionally) in X, binding a rest parameter (if present)

    if OPERATOR is special, yield the usual meaning of that operator in scheme

These are the broad strokes of the evaluator. For details, refer to the source
code 😎"
  (setq env (or env (smol1-env-create)))
  (cond
   ((atom exp)
    (cond ((or (numberp exp) (characterp exp) (stringp exp) (vectorp exp))
	   exp)
	  ((smol1-boolean-p exp) (smol1-boolean<-literal exp))
	  ((symbolp exp) (smol1-eval/variable exp env))))
   (:else
    (let ((operator-form (car exp))
	  (operand-forms (cdr exp)))
      (cl-case operator-form
	((quote) (smol1-eval/quote operand-forms))
	((if) (smol1-eval/if operand-forms env))
	((begin)
	 (if (null operand-forms)
	     (smol1-error "Empty BEGIN" '( :expected (begin FORM-1 FORM ...)
					   :actual (begin) ))
	   (named-let eval-begin ((body operand-forms))
	     (if (null (cdr body))
		 (smol1-eval (car body) env)
	       (smol1-eval (car body) env)
	       (eval-begin (cdr body))))))
	((set!)
	 (let* ((variable (car operand-forms))
		(value-form (cadr operand-forms))
		(value (smol1-eval value-form env)))
	   (smol1-env-rebind env (smol1-key<-symbol variable) value)))
	((lambda)
	 (let* ((parameter-spec (car operand-forms))
		(body (cdr operand-forms))
		(parameters (smol1-lambda-parameters-parse parameter-spec))
		(required-parameters
		 (smol1-lambda-parameters-get parameters :required))
		(rest-parameter
		 (smol1-lambda-parameters-get parameters :rest))
		(num-required-parameters (length required-parameters))
		(definition-env env))
	   (if (null body)
	       (smol1-error
		"Lambda with empty body"
		`( :expected (lambda ,parameter-spec BODY-FORM...+)
		   :actual ,exp )))
	   (lambda (call-env &optional arguments)
	     (let ((required-arguments (take num-required-parameters arguments)))
	       (if (not (= num-required-parameters (length required-arguments)))
		   (smol1-error "Arity mismatch"
				`( :parameters ,parameters
				   :arguments ,arguments ))
		 (let* ((env (apply #'smol1-env-bind
				    definition-env
				    (smol1-interleave-params-and-args
				     required-parameters
				     required-arguments)))
			(env (if (not rest-parameter) env
			       (smol1-env-bind
				env
				rest-parameter
				(nthcdr num-required-parameters arguments)))))
		   (smol1-eval `(begin ,@body) env)))))))
	(otherwise
	 (and smol1-trace-on
	      (run-hook-with-args 'smol1-trace-functions exp))
	 (let* ((operator (smol1-eval operator-form env))
		(operands (mapcar #'(lambda (arg-form)
				      (smol1-eval arg-form env))
				  operand-forms))
		(value (funcall operator env operands)))
	   (and smol1-trace-on
		(run-hook-with-args 'smol1-trace-functions
				    `(,operator-form ,@operands)
				    value))
	   value)))))))

(defun smol1-eval/variable (exp env)
  "Evaluate a variable reference EXP given environment ENV by looking up the
value stored at the location to which the variable is bound."
  (let ((variable-value (smol1-env-get env (smol1-key<-symbol exp))))
	     (if (eq smol1-constant-void variable-value)
		 (smol1-error "Unbound variable"
			      `(:variable ,exp :current-environment ,env))
	       variable-value)))

(defun smol1-eval/quote (arguments)
  "Return the single argument in the list, ARGUMENTS, without further
evaluation."
  (if (cdr arguments)
      (smol1-error "QUOTE form with excess arguments"
		   `( :expected (quote ,(car arguments))
		      :actual (quote ,@arguments) ))
    (car arguments)))

(defun smol1-eval/if (operands env)
  "Return the result of a branching computation of form (if TEST THEN ELSE)
where the result is obtained by evaluating THEN if TEST evaluates to true (not
false), otherwise the result is simply what ELSE evaluates to, if it is
present. If the ELSE branch is missing, the result is the special void value."
  (let* ((test (car operands))
	 (consequent (cadr operands))
	 (alternate (caddr operands))
	 (test-result (smol1-eval test env)))
    (if (eq smol1-constant-false test-result)
	(if alternate (smol1-eval alternate env) smol1-constant-void)
      (smol1-eval consequent env))))

;;; Special values
(defconst smol1-constant-void (list 'smol1 :void)
  "A special value indicating the absence of any appropriate value.")

(defconst smol1-constant-true (list 'smol1 :true)
  "The boolean true in smol1.")

(defconst smol1-constant-false (list 'smol1 :false)
  "The boolean false in smol1.")

(defun smol1-boolean<-literal (literal)
  "Return the smol1 boolean value corresponding to its LITERAL."
  (cond ((eq literal '$t) smol1-constant-true)
	((eq literal '$f) smol1-constant-false)
	(:else (error "Not a boolean literal: %S" literal))))

;;; Type predicates
(defun smol1-boolean-p (exp)
  "Return non-nil if EXP is a smol1 boolean."
  (or (eq exp '$t) (eq exp '$f)))

;;; Lambda parameter lists
(defun smol1-lambda-parameters-get (parameters key)
  (plist-get parameters key))

(defun smol1-lambda-parameters-parse (parameter-spec)
  "Return the parsed PARAMETER-SPEC of the form (:required REQUIRED :rest REST),
where REQUIRED is a (possibly empty) list of required formal parameters, and
REST is the formal rest parameter (possibly nil, if absent).

PARAMETER-SPEC := <symbol> | () | (<symbol> . PARAMETER-SPEC)"
  (cond
   ((and (not (null parameter-spec)) (symbolp parameter-spec))
    `(:required nil :rest ,parameter-spec))
   ((listp parameter-spec)
    (named-let parse-list-spec ((spec parameter-spec)
				(required nil))
      (cond ((null spec) `(:required ,(reverse required) :rest nil))
	    ((symbolp spec) `(:required ,(reverse required) :rest ,spec))
	    (:else (parse-list-spec (cdr spec) (cons (car spec) required))))))
   (:else (smol1-error "Malformed parameter specification"
		       `( :expected (or symbol nil (symbol ... . rest))
			  :actual ,parameter-spec )))))

;;; Variables
(defun smol1-key<-symbol (identifier)
  "Return the environment lookup key associated with IDENTIFIER."
  ;; It seems silly in this case, but this transformation could be non-trivial
  ;; for a sophisticated interpreter or compiler. Also not made explicit are
  ;; possible intermediate transformations `variable<-symbol' and
  ;; `key<-variable', which would convert a symbol (syntactic entity) to a
  ;; variable (semantic entity), and a variable to a lookup key in the
  ;; environment, which associates (binds) storage locations to variables.
  identifier)

;;; Environment
(defun smol1-env-create ()
  "Return a fresh environment for bindings."
  nil)

(defun smol1-env-get (env key)
  "Return the associated value for KEY in ENV, or `smol1-constant-void' if there
is no such value. Keys are compared by `eq'. Note that KEY has no connection to
keyword symbols."
  (alist-get key env smol1-constant-void nil #'eq))

(defun smol1-env-bind (env &rest key-value-pairs)
  "Return a new environment with the same bindings as ENV, but extended with
associations between KEY1 VALUE1, KEY2 VALUE2, ... as supplied in
KEY-VALUE-PAIRS.

Any previous associations are unchanged. The caller should `setq' the return
value, otherwise, the result would be discarded. The result shares structure
with the provided ENV."
  (named-let bind ((pairs key-value-pairs))
    (if (null pairs)
	env
      (let ((key (car pairs))
	    (value (cadr pairs)))
	(push (cons key value) env)
	(bind (cddr pairs))))))

(defun smol1-env-rebind (env key value)
  "Modify the association for KEY in ENV so that the new association is with
VALUE. This is a destructive operation. If KEY has no previous association,
return nil. If an association was successfully modified, return non-nil."
  (let ((binding (assoc key env #'eq)))
    (if (null binding)
	nil
      (setcdr binding value)
      binding)))

(defun smol1-interleave-params-and-args (parameters arguments)
  "Return an interleaved list of elements (P1 A1 P2 A2 ...) where Pi is from
PARAMETERS and Ai is from ARGUMENTS."
  (if parameters
      (cons (car parameters)
	    (cons (car arguments)
		  (smol1-interleave-params-and-args (cdr parameters)
						    (cdr arguments))))
    nil))

;;; Guest / Host interaction
(defmacro smol1-lambda (env args &rest body)
  "Create an arbitrary host procedure that follows smol1 calling conventions in
its parameter list, using ENV and ARGS as the names of the calling environment
and argument lists, respectively, and BODY as the procedure body."
  `#'(lambda (,env &optional ,args) ,@body))

(defun smol1-env-defprimitive ( env primitive-name host-fun check-args-p-fun transform-fun )
  "Return a new environment that is the same as ENV, but with PRIMITIVE-NAME
bound to a procedure callable via that environment.

The bound procedure uses CHECK-ARGS-P-FUN to verify that the argument list to be
passed to HOST-FUN is valid (e.g., correct arity); errors from attempting to
call CHECK-ARGS-P-FUN are caught and handled as failures in handling the
argument list. This bound primitive works as described next.

If CHECK-ARGS-P-FUN returns non-nil when passed the same arguments as HOST-FUN,
HOST-FUN is called with the arguments as seen by CHECK-ARGS-P-FUN, and the
result is passed to TRANSFORM-FUN, which yields the final result appropriate to
the guest language.

If CHECK-ARGS-P-FUN returns nil, or an error is signaled from within its body or
as a result of attempting to call CHECK-ARGS-P-FUN, then the argument list is
considered invalid and an error is thrown from the bound primitive."
  (smol1-env-bind
   env
   primitive-name
   (smol1-lambda _ args			; ignore call site environment
		 (let (host-error-data)
		   (if (condition-case e
			   (apply check-args-p-fun args)
			 (error (setq host-error-data e) nil))
		       (funcall transform-fun (apply host-fun args))
		     (smol1-error "Invalid call to primitive"
				  `( :primitive ,primitive-name
				     :arguments ,args
				     :host-error ,host-error-data )))))))

;;; Initial environment
(defconst smol1-initial-environment (smol1-env-create)
  "The initial, empty environment.")

;;; Global environment
(defvar smol1-global-environment smol1-initial-environment
  "The global environment, which is the initial environment extended with useful
functions.")

(let ((e smol1-initial-environment))
  (setq e (smol1-env-defprimitive
	   e 'eq? #'eq
	   #'(lambda (o1 o2) t)
	   #'(lambda (x) (if x smol1-constant-true
			   smol1-constant-false))))
  (setq smol1-global-environment e))

;;; Error / warning reporting:
(defun smol1-error (message error-context)
  "Signal an error with the supplied MESSAGE, printing the read representation
of ERROR-CONTEXT."
  (error "%s\n%S" message error-context))

;;; Tracing hook
(defvar smol1-trace-on nil
  "Controls whether function tracing is performed by `smol1-eval'")

(defvar smol1-trace-functions nil
  "An abormal hook run with intermediate forms, optionally supplying their
results, during evaluation. These functions could be used to perform tracing
evaluation steps or similar operations.")

(defun smol1-stepwise-trace-function (form-now &optional form-value)
  "Log a message displaying the smol1 form FORM-NOW (and possibly its result
FORM-VALUE) at this evaluation step."
  (if form-value
      (message "smol1> %S => %S" form-now form-value)
    (message "smol1> %S" form-now)))

(add-hook 'smol1-trace-functions #'smol1-stepwise-trace-function)

(provide 'smol1)

;;; smol1.el ends here
