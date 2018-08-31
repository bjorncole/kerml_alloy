
// KerML Alloy file

// An attempt at mapping semantic elements of KerML metamodel (things that can be resolved
// to individuals) into relational logic to be solved and demonstrate how relevant things would work

// This is a version where the Feature is NOT reified but instead defines a slot on the class
// This is tricky, because what is below is the M1 USER MODEL and doesn't have syntactic sugar

// --------------------------------------- CLASS AND FEATURE -----------------------------

abstract sig AbstractAnything {}

// Here we are M1 so now Feature is shown because it is not a reified thing
// We can capture user properties by subsetting feature

sig Anything extends AbstractAnything {
	feature : some AbstractAnything
}

sig NullThing extends AbstractAnything {}

// can't have yourself as a feature

fact no_self_reference {
	all a : Anything | a not in a.feature
}

// can't have reflexive featuring or a cycle of features

fact no_reflect_feature {
	all a1, a2 : Anything | a1 in a2.feature => not a2 in a1.*feature
}

// hack for multiplicity of 0 when multiple things for Alloy

fact null_replaces {
	all a: Anything | #(a.feature :> NullThing) > 0 iff #(a.feature :> Anything) = 0
}

fact null_is_single {
	all a: Anything | #(a.feature :> NullThing) <= 1
}

// end multiciplity of 0 hack

// ----------------------- END CLASS AND FEATURE -------------------------------------

// ----------------------------------- ASSOCIATION -------------------------------------------

// source ends and target ends as collections allows for n-ary associations (multiple source relationships to be 
// interpreted as a set of objects that lead to another set)

sig Link {
	sourceEnd : some Anything,
	targetEnd : some Anything,
	participant : some Anything
}

// all ends are also participants

fact sends_are_participants {
	all l : Link, a : Anything | a in l.sourceEnd => a in l.participant
}

fact tends_are_participants {
	all l : Link, a : Anything | a in l.targetEnd => a in l.participant
}

// source, target are unique

fact disjoint_end_sides {
	all l : Link, a : Anything | a in l.sourceEnd => a not in l.targetEnd
}

fact disjoint_end_sides {
	all l : Link, a : Anything | a in l.targetEnd => a not in l.sourceEnd
}

// Special case for when sourceEnd is multiplicity 1? Forces targetEnd and feature leading from sourceEnd to match

fact source_goes_to_features {
	all l : Link, a1, a2 : Anything | (#(l.sourceEnd) = 1 and a1 in l.sourceEnd) => (a2 in l.targetEnd iff a2 in a1.feature)
}

// Should there be a different interpretation for the multiplicities on participants versus ends?
// The intentional interpretation paper talks about association ends as collections of items
// separate from the links themselves (seems like that should match up with the participants)

// ------------------------------  END ASSOCIATION ---------------------------------------

// a test for the features link by forcing a special link

sig OneSidedLink extends Link {}

fact osl_is_onesided {
	all o : OneSidedLink | #(o.sourceEnd) = 1
}

pred show () {}

run show for  8 AbstractAnything, 2 Link, 1 OneSidedLink
