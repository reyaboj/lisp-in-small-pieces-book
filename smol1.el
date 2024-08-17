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
	  ((symbolp exp)
	   (let ((variable-value (smol1-env-get env (smol1-key<-symbol exp))))
	     (if (eq smol1-constant-void variable-value)
		 (smol1-error "Unbound variable"
			      `(:variable ,exp :current-environment ,env))
	       variable-value)))))
   (:else
    (let ((operator-form (car exp))
	  (operand-forms (cdr exp)))
      (cl-case operator-form
	((quote)
	 (if (cdr operand-forms)
	     (smol1-error "QUOTE form with excess arguments"
			  `( :expected (quote ,(car operand-forms))
			     :actual (quote ,@operand-forms) ))
	   (car operand-forms)))
	((if)
	 (let* ((test (car operand-forms))
		(consequent (cadr operand-forms))
		(alternate (caddr operand-forms))
		(test-result (smol1-eval test env)))
	   (if (eq smol1-constant-false test-result)
	       (if alternate (smol1-eval alternate env) smol1-constant-void)
	     (smol1-eval consequent env))))
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
	(otherwise (funcall (smol1-eval operator-form env)
			    env
			    (mapcar #'(lambda (arg-form)
					(smol1-eval arg-form env))
				    operand-forms))))))))

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

;;; Error / warning reporting:
(defun smol1-error (message error-context)
  "Signal an error with the supplied MESSAGE, printing the read representation
of ERROR-CONTEXT."
  (error "%s\n%S" message error-context))

(provide 'smol1)

;;; smol1.el ends here
