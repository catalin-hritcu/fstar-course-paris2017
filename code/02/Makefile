FSTAR_HOME=/home/hritcu/Projects/fstar/pub

include $(FSTAR_HOME)/ulib/ml/Makefile.include

all:
	fstar.exe --verify_all AppExtrinsic.fst AppIntrinsic.fst BinarySearchTree.fst InsertionSort.fst Log.fst RefinedStackClient.fst RefinedStack.fst Rev.fst
clean:
	rm -dfr *~ *.exe out
