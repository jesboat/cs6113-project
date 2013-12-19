all: operational_semantics.vo type_rules.vo

operational_semantics.vo: operational_semantics.v SfLib.vo  Rel.vo syntax.vo
	coqc operational_semantics.v

type_rules.vo: type_rules.v syntax.vo SfLib.vo
	coqc type_rules.v

syntax.vo: syntax.v
	coqc syntax.v

SfLib.vo: SfLib.v
	coqc SfLib.v

Rel.vo: Rel.v
	coqc Rel.v

clean:
	rm -f *.vo *.glob

