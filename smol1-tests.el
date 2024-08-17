;;; smol1-tests.el --- Test suite for smol1 -*- lexical-binding: t; -*-

;; Copyright (C) 2024 Md Istiaque Al Jobayer

;; Author: Md Istiaque Al Jobayer <mdia.jobayer+lisp@gmail.com>
;; Maintainer: Md Istiaque Al Jobayer <mdia.jobayer+lisp@gmail.com>
;; Keywords: test, smol1, scheme, interpreter, lisp
;; URL: https://github.com/reyaboj/lisp-in-small-pieces-book
;; Package-Requires: ((emacs "29.4"))

;; This file is not part of GNU Emacs.

;;; Commentary:
;; Test suite for smol1.el

;;; Code:

(add-to-list 'load-path default-directory)
(require 'ert)
(require 'smol1)
(setq smol1-trace-on nil)		; disable tracing

;;; Evaluator

(ert-deftest smol1/void ()
  "Special void value has a predefined structure."
  (should (equal '(smol1 :void) smol1-constant-void)))

(ert-deftest smol1-eval/self-quoted-constants ()
  "Self-quoted forms evaluate to themselves."
  ;; Booleans
  (should (equal smol1-constant-true (smol1-eval '$t)))
  (should (equal smol1-constant-false (smol1-eval '$f)))
  ;; Numbers
  (should (equal 42 (smol1-eval 42)))
  (should (equal -42 (smol1-eval -42)))
  ;; Characters
  (should (equal ?x (smol1-eval ?x)))
  (should (equal ?\u03bb (smol1-eval ?\u03bb)))
  ;; Strings
  (should (equal "foo" (smol1-eval "foo")))
  ;; Vectors
  (should (equal [a 1 b c "bar"]
		 (smol1-eval [a 1 b c "bar"]))))

(ert-deftest smol1-eval/variable-reference ()
  "Variables evaluate to the value stored at their bound location."
  (let* ((e (smol1-env-create))
	 (e (smol1-env-bind e 'x 1 'y 2)))
    (should (equal 1 (smol1-eval 'x e)))
    (should (equal 2 (smol1-eval 'y e)))
    (should-error (smol1-eval 'z e))))

(ert-deftest smol1-eval/special-form/quote ()
  "(quote FORM) yields data FORM, literally."
  (should (equal 1 (smol1-eval '(quote 1))))
  (should (equal -1 (smol1-eval '(quote -1))))
  (should (equal ?L (smol1-eval '(quote ?L))))
  (should (equal ?\u03bb (smol1-eval '(quote ?\u03bb))))
  (should (equal "foo" (smol1-eval '(quote "foo"))))
  (should (equal [a 1 b c "bar"]
		 (smol1-eval '(quote [a 1 b c "bar"]))))
  (should (equal '(begin a b) (smol1-eval '(quote (begin a b)))))
  (should (equal '(1 2 3) (smol1-eval '(quote (1 2 3))))))

(ert-deftest smol1-eval/special-form/if ()
  "(if TEST THEN ELSE) yields THEN when TEST is true, otherwise ELSE."
  (should (equal 1 (smol1-eval '(if $t 1 0))))
  (should (equal 0 (smol1-eval '(if $f 1 0))))
  ;; Anything not $f is true
  (should (equal 1 (smol1-eval '(if 0 1 0))))
  ;; A missing ELSE results in void (unspecified according to standard)
  (should (equal smol1-constant-void
		 (smol1-eval '(if $f 1)))))

(ert-deftest smol1-eval/special-form/begin ()
  "(begin FORM-1 FORM-2 ... FORM-N) evaluates FORMs and returns result of FORM-N."
  ;; TODO add test cases to verify sequential evaluation (e.g., side effects)
  (should-error (smol1-eval '(begin)))
  (should (equal 1 (smol1-eval '(begin 1))))
  (should (equal 2 (smol1-eval '(begin 1 2)))))

(ert-deftest smol1-eval/special-form/set! ()
  "(set! VARIABLE VALUE) modifies location for VARIABLE, storing VALUE."
  (let ((e (smol1-env-bind (smol1-env-create)
			   'x 1 'y 2)))
    (should (equal 1 (smol1-eval 'x e)))
    (should (equal 2 (smol1-eval 'y e)))
    (smol1-eval '(set! x 42) e)
    (should (equal 42 (smol1-eval 'x e)))
    (should (equal 2 (smol1-eval 'y e)))))

(ert-deftest smol1-eval/special-form/lambda ()
  "(lambda PARAM-SPEC BODY-FORMS) creates a procedure."
  ;; Representation of closures in the language is a function in the host
  (should (functionp (smol1-eval '(lambda (x) x))))
  ;; Lambda cannot have empty body
  (should-error (smol1-eval '(lambda (x))))
  ;; Simple application
  (should (equal 1 (smol1-eval '((lambda (x) x) 1))))
  ;; Closure of definition environment
  (should (equal 'closed
		 (smol1-eval '(((lambda (x) (lambda (y) x)) 'closed)
			       'get)))))


;;; Syntax

(ert-deftest smol1-lambda-parameters-parse ()
  "Parameter specifications should be one of: <symbol> | () | (<symbols> . <symbol>)"
  (should (equal '(:required nil :rest args)
		 (smol1-lambda-parameters-parse 'args)))
  (should (equal '(:required (x) :rest args)
		 (smol1-lambda-parameters-parse '(x . args))))
  (should (equal '(:required (x y z) :rest zs)
		 (smol1-lambda-parameters-parse '(x y z . zs))))
  (should (equal '(:required (x y z) :rest nil)
		 (smol1-lambda-parameters-parse '(x y z))))
  (should-error (smol1-lambda-parameters-parse "x"))
  (should-error (smol1-lambda-parameters-parse '(x . "y"))))


;;; Environment

(ert-deftest smol1-env/create/bind/get ()
  "Environment can be created and new bindings follow stack discipline."
  (let ((e0 (smol1-env-create))
	e1 e2)
    ;; Unbound
    (should (equal smol1-constant-void
		   (smol1-env-get e0 'x)))
    ;; Bound
    (setq e1 (smol1-env-bind e0 'x 1 'y 2))
    (should (equal 1 (smol1-env-get e1 'x)))
    (should (equal 2 (smol1-env-get e1 'y)))
    ;; Stack discipline
    (setq e2 (smol1-env-bind e1 'x 42))
    (should (equal 42 (smol1-env-get e2 'x)))
    (should (equal 2 (smol1-env-get e2 'y)))
    (should (equal 1 (smol1-env-get e1 'x)))))

(ert-deftest smol1-env-rebind ()
  "Environment bindings can be mutated."
  (let ((e (smol1-env-create)))
    (setq e (smol1-env-bind e 'x 1 'y 2))
    (smol1-env-rebind e 'x 42)
    (should (equal 42 (smol1-env-get e 'x)))))


;;; smol1-tests.el ends here
