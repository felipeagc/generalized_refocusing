#Installation (tested on coq 8.9):

#cd to the top directory (the one with _CoqProject file) and run the
#following commands.

coq_makefile -f _CoqProject -o Makefile
make clean
make
runhaskell draw_coqdeps.hs
