
# Table of Contents

1.  [Overview](#orgc85bf11)
2.  [Project layout](#orge477922)
3.  [Running the code](#orgf7e11f6)
4.  [Running tests](#org03e7a5a)
    1.  [Prerequisites](#org2a5a1d1)
    2.  [Steps to run](#org6e771ec)



<a id="orgc85bf11"></a>

# Overview

This repository contains implementations of various Lisp flavors and features described in the book, Lisp in Small Pieces, written by Queinnec and Callaway.  The code is written to be self-explanatory and pedagogic in nature so that newcomers to Lisp can appreciate the simplicity of a meta-circular evaluator, as well as the many nuances in language design and engineering trade-offs involved in a practical Lisp.


<a id="orge477922"></a>

# Project layout

-   `docs/` : documentation files
-   `logs/` : output directory for test run logs
-   `FEATURE.el` : source files
-   `FEATURE-tests.el` : test for `FEATURE`


<a id="orgf7e11f6"></a>

# Running the code

You need a working Emacs installation to run the code.  Doom Emacs, or similar starter kits, can provide an easy entry into the Emacs world, if you are new to it.  Simply open Emacs and load the `.el` file corresponding to the Lisp variant you would like to play with.  The source files contain enough documentation as to be self-explanatory, but if the documentation isn't clear, please feel free to raise an issue or send a PR.


<a id="org03e7a5a"></a>

# Running tests


<a id="org2a5a1d1"></a>

## Prerequisites

-   `emacs`
-   `make` (GNU is preferred, but others should work)
-   a typical UNIX userspace (e.g., `rm`, `mkdir`, etc.) which means Linux, WSL, and so on


<a id="org6e771ec"></a>

## Steps to run

With your shell in the project directory containing the `Makefile`, run the following, which will create a `logs/` directory (if it doesn't exist) and report the results of the test run on your screen as well as save it in a log file.

    # default test run
    make tests
    
    # less verbose output
    make ERT_QUIET=t tests
    
    # the form evaluated to trigger a test run, if you want more control
    # check the Makefile for details
    make ERT_TEST_FORM='(ert-summarize-tests-batch-and-exit)' tests

