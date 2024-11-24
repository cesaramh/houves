CSLC=ocamlc
CSLOPT=ocamlopt
CSLDEP=ocamldep
CSLLEX=ocamllex
CSLYACC=ocamlyacc
INCLUDES=                #all relevant -I options here
CSLFLAGS= $(INCLUDES)    #add other options for ocamlc here
CSLOPTFLAGS=$(INCLUDES)  #add other options for ocamlopt here
EXAMPLES = examples.hou

objects = liblist.cmo link.cmo term.cmo com.cmo version.cmo pp.cmo par.cmo lex.cmo main.cmo

all: depend term.cmi lex.ml par.ml $(objects) main

# Common rules
.SUFFIXES: .ml .mli .cmo .cmi .cmx .mll .mly

.ml.cmo:
	$(CSLC) $(CSLFLAGS) -c $<

.mli.cmi:
	$(CSLC) $(CSLFLAGS) -c $<

.ml.cmx:
	$(CSLOPT) $(CSLOPTFLAGS) -c $<

.mll.ml:
	$(CSLLEX) $(CSLFLAGS) $<

.mly.ml:
	$(CSLYACC) $(CSLFLAGS) $<
        
main: 
	$(CSLC) -custom -o houves $(CSLFLAGS) unix.cma $(objects) -cclib -lunix   

clean: 
	rm -f houves par.ml houves.tar.gz lex.ml par.ml par.mli *.cm[iox] *~
        
depend:
	$(CSLDEP) $(INCLUDES) *.mli *.ml *.mll *.mly > .depend

par.cmi:
	$(CSLC) $(CSLFLAGS) -c par.mli

par.cmi: com.cmi
lex.cmo: par.cmi
par.cmo: par.cmi
include .depend

tar:
	tar cvf houves.tar *.ml *.mli *.mll *.mly $(EXAMPLES) .depend README Makefile
	gzip houves.tar


publish:
	rsync houves.tar.gz README examples.hou distrib/
