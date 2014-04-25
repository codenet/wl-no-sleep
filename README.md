wl-no-sleep
===========

This is a project for course CS 56500 at Purdue University. This project proves that applying reaching definition based bug detection for no-sleep bugs is sound.

Description of the files
------------------------

* SfLib.v - Software foundations Library that defines basics like lists, nat, and proves theorems on them.
* WLImp.v - Defines semantics of a simple imperative language that just contains wakelocks.
* WLHoare.v - Defines Assertions and hoare_triple. 
* WLDup.v - Proves that the "wakelock state" can never have duplicate wakelocks in it.
* WLBug.v - Formally defines "correct program" (a program that does not have no-sleep bugs). Definies the reaching definition based analysis. Finally proves that the analysis is sound for finding no-sleep bugs.
* WLUtil.v - Utility theorems related to wakelocks
* Util.v - Other utility theorems

Order of Compilation
------------------------

1. SfLib.v
2. WLImp.v
3. WLHoare.v
4. Util.v
5. WLUtil.v
6. WLDup.v
7. WLBug.v