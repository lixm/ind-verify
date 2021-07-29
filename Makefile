
all: sem.vo tactics.vo arith.vo lists.vo while.vo while_ext.vo fun.vo

sem.vo: sem.v
	coqc sem.v

tactics.vo: tactics.v
	coqc tactics.v

arith.vo: arith.v
	coqc arith.v

lists.vo: lists.v
	coqc lists.v

while.vo: while.v
	coqc while.v

while_ext.vo: while_ext.v
	coqc while_ext.v

fun.vo: fun.v
	coqc fun.v

.PHONY: clean
clean:
	-rm *.vo *.glob *.vos *.vok
