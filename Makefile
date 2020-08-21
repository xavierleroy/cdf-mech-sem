include CoqMakefile

CoqMakefile:
	coq_makefile -f _CoqProject -o CoqMakefile

documentation:
	coq2html -base CDF -short-names -no-css -d docs *.glob *.v
