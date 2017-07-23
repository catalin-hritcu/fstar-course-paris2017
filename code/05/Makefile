FSTAR_HOME=/home/hritcu/Projects/fstar/pub

include $(FSTAR_HOME)/ulib/ml/Makefile.include

all:
	fstar.exe --verify_all AbstractStackClient.fst AbstractStack.fst BinaryTrees.fst StatefulStack.fst

clean:
	rm -dfr *~ *.exe out
