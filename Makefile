all:
	coqc SfLib.v
	coqc WLImp.v
	coqc WLHoare.v
	coqc Util.v
	coqc WLUtil.v
	coqc WLDup.v
	coqc WLBug.v

clean:
	rm *.glob *.vo
