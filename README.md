HOUVES
==

HOU for Dependent Types via Explicit Substitutions.

Author: Cesar A. Munoz 

Last updtate: Oct 28 1999.

The HOUVES system is a prototype that implements some of the concepts I
have developed in my thesis:

@PHDTHESIS{Mun97d,
        AUTHOR = "C. Mu{\~{n}}oz",
        TITLE = "Un calcul de substitutions pour la repr\'esentation
                  de preuves partielles en th\'eorie de types",
        SCHOOL = {Universit\'e Paris 7},
        YEAR = "1997",
        Note = {English version available as technical report:INRIA RR-3309},        
        Type = {Th\`ese de Doctorat}
}

To install/run you need OCaml 2.02 (http://caml.inria.fr/ocaml/). 

Installation:
------------
0. Download, gunzip and untar houves.tar.gz 
1. make 

To run use: houves
------------------
Commands in houves start with an uppercase letter and end with a dot, just like in Coq :-). A useful command is Help.

Things to have in mind
----------------------
* The environment is a signature.
* A signature is a list of meta-variables, assignments 
  (solved meta-variables) and constraints.
* The actual goal is a pointer to a position in the environment.
* Go. Go to the initial position of the signature.
* Go n. Go to the actual position + n (n may be negative).
* Notice that meta-variables can be typed only in the next position where 
  they have been declared. That is, if the list of goals is:
  ....  |- X?:A.   %%% X? is not typed here.
  ....  |- Y?:B.   %%% X? is well-typed here.
  ..... |- X?=Y?.  %%% X? and Y? are well-typed here.
* Go X. Go to the position where meta-variable X has been declared. 
* Lemma X:... Introduces the meta-variable X?. The habitation problem for
  this meta-variable should be solved.
* Metavar X:... Introduces the meta-variable X!. The habitation problem for
  this meta-variable is not going to be solved.
* The system cooks for you! It means that meta-variables are automatically
  cooked. However, you can reset the oven by using Cook n, or explicitly
  cook a term by using <<n:t>> (turnoff the oven, i.e. Cook -1,
  if you want to cook the terms by yourself).
* About the prompt:
  - ">" means that the signature is empty.
  - ">>" means that there is not a current goal, 
         but the signature is not empty.
  - In any other case, it points to the current-goal.
* The "limit" for HOU can be set by "Limit n" where n is a natural number.
  The measure for the limit is (n+m/e). 
  (n=unsolved meta-variables, m=solved meta-variables and e=equations).
* Use the command Verbose to see the HOU step by step.

Examples
--------
Try Load "examples.hou".


