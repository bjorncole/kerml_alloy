
// KerML Alloy file

// An attempt at mapping semantic elements of KerML metamodel (things that can be resolved
// to individuals) into relational logic to be solved and demonstrate how relevant things would work

// This is a version where the Feature IS reified as a separate object

// The example include demonstrates:

// Binary links for composition of system from parts
// Adding in named features for parts
// Binding features to links for binary associations (association ends)
// Controlling multiplicity of features
// Controlling type of features
// Subsetting features (no reason this can't extend)


// --------------------------------------- CLASS AND FEATURE -----------------------------

abstract sig AbstractAnything {}

// Here we are M1 so now Feature is shown because it is not a reified thing
// We can capture user properties by subsetting feature

sig Anything extends AbstractAnything {}

sig NullThing extends AbstractAnything {}

abstract sig AbstractFeature {}

// The definition below allows for a Feature to have multiple values

sig Feature extends AbstractFeature {
	featuringClass : one Anything,
	type : some Anything
}

sig NullFeature extends AbstractFeature{}

// can't have yourself as a feature

fact no_self_reference {
	all f : Feature | f.featuringClass not in f.type
}

// multiplicity of 0 handled by non-existance of Feature

// ----------------------- END CLASS AND FEATURE -------------------------------------

// ----------------------------------- ASSOCIATION -------------------------------------------

// source ends and target ends as collections allows for n-ary associations (multiple source relationships to be 
// interpreted as a set of objects that lead to another set)

// links can be n-ary in UML according to 
//http://etutorials.org/Programming/Learning+uml/Part+II+Structural+Modeling/
//Chapter+3.+Class+and+Object+Diagrams/3.2+Associations+and+Links/

// and link action descriptions

sig Link {
	domainEnd : some Anything,
	rangeEnd : some Anything,
	participant : some Anything
}

// when we have subclasses of this, we can subset sourceEnd and targetEnd and also
// change the legal types to link

// also can hold multiplicities on each end here

// all ends are also participants

fact sends_are_participants {
	all l : Link, a : Anything | a in l.domainEnd => a in l.participant
}

fact tends_are_participants {
	all l : Link, a : Anything | a in l.rangeEnd => a in l.participant
}

// source, target are unique

fact disjoint_end_sides {
	all l : Link, a : Anything | a in l.domainEnd => a not in l.rangeEnd
}

fact disjoint_end_sides {
	all l : Link, a : Anything | a in l.rangeEnd => a not in l.domainEnd
}

// Special case for when sourceEnd is multiplicity 1? Forces targetEnd and feature leading from sourceEnd to match
// Oddly enough, this looks / feels a lot like a junction table in database design ... only one-to-manys can live with a table

// Also, hence the diamond ... duh.

// I tried iff in the second implication but it was too strong - broke binary links because feature couldn't simultaneously be in all rangeEnds

fact source_goes_to_features {
	all l : Link, a1, a2 : Anything | (#(l.domainEnd) = 1 and a1 in l.domainEnd and a2 in l.rangeEnd) =>
		one f : Feature | f.featuringClass = a1 and a2 in f.type
}

// Should there be a different interpretation for the multiplicities on participants versus ends?
// Currently multiplicities on Association ends indicates the total count of allowable link ends to a given class of objects

// The intentional interpretation paper talks about association ends as collections of items
// separate from the links themselves (seems like that should match up with the participants)

// ------------------------------  END ASSOCIATION ---------------------------------------

// a test for the features link by forcing a special link

sig OneSidedLink extends Link {}

fact osl_is_onesided {
	all o : OneSidedLink | #(o.domainEnd) = 1
}

sig BinaryLink extends Link {}

fact binary_is_one_a_side {
	all b : BinaryLink | #(b.domainEnd) = 1 and #(b.rangeEnd) = 1
}

// --------------------------- AIRCRAFT EXAMPLE OBJECTS ------------------------

// Definitions

sig Aircraft extends Anything {
}

sig WingFeature extends Feature {}
sig EngineFeature extends Feature {}
sig FuselageFeature extends Feature {}
sig EmpennageFeature extends Feature {}

sig VTailFeature extends Feature {}
sig HTailFeature extends Feature {}

// set featuringClass and feature types

fact wing_featuring_set {
	all wf : WingFeature | #(wf.featuringClass :> Aircraft) = 1
}

fact wing_type_set {
	all wf : WingFeature | #(wf.type :> Wing) = #(wf.type)
}

fact engine_featuring_set {
	all ef : EngineFeature | #(ef.featuringClass :> Aircraft) = 1
}

fact engine_type_set {
	all ef : EngineFeature | #(ef.type :> Engine) = #(ef.type)
}

fact fuselage_featuring_set {
	all ff : FuselageFeature | #(ff.featuringClass :> Aircraft) = 1
}

fact fuselage_type_set {
	all ff : FuselageFeature | #(ff.type :> Fuselage) = #(ff.type)
}

fact empennage_featuring_set {
	all ef : EmpennageFeature | #(ef.featuringClass :> Aircraft) = 1
}

fact empennage_type_set {
	all ef : EmpennageFeature | #(ef.type :> Empennage) = #(ef.type)
}

fact vtail_featuring_set {
	all vf : VTailFeature | #(vf.featuringClass :> Empennage) = 1
}

fact vtail_type_set {
	all vf : VTailFeature | #(vf.type :> VTail) = #(vf.type)
}

fact htail_featuring_set {
	all hf : HTailFeature | #(hf.featuringClass :> Empennage) = 1
}

fact htail_type_set {
	all hf : HTailFeature | #(hf.type :> HTail) = #(hf.type)
}

// set feature type multiplicity

fact wing_type_set {
	all wf : WingFeature | #(wf.type) = 2
}

fact engine_type_set {
	all ef : EngineFeature | #(ef.type) = 2
}

fact fuselage_type_set {
	all ff : FuselageFeature | #(ff.type) = 1
}

fact engine_type_set {
	all ef : EmpennageFeature | #(ef.type) = 1
}

fact vtail_type_set {
	all vf : VTailFeature | #(vf.type) = 2
}

fact htail_type_set {
	all hf : HTailFeature | #(hf.type) = 2
}

sig Wing extends Anything {}

sig Engine extends Anything {}

sig Fuselage extends Anything {}

sig Empennage extends Anything {}

sig VTail extends Anything {}

sig HTail extends Anything {}

/*

// Subsetting and other constraints

fact wing_sub_feature {
	all w : Wing, ac : Aircraft | w in ac.wing iff w in ac.feature
}

fact engine_sub_feature {
	all e : Engine, ac : Aircraft | e in ac.engine iff e in ac.feature
}

fact fuselage_sub_feature {
	all f: Fuselage, ac : Aircraft | ac.fuselage = f iff f in ac.feature
}

fact empennage_sub_feature {
	all e : Empennage, ac : Aircraft | ac.empennage = e iff e in ac.feature
}

fact vtail_sub_feature {
	all e : Empennage, v : VTail | v in e.vtail iff v in e.feature
}

fact htail_sub_feature {
	all e : Empennage, h : HTail | h in e.htail iff h in e.feature
}

// allow only entries from the sets described in the defintion

fact close_aircraft_feature {
	all ac : Aircraft | #(ac.feature :> (Wing + Engine + Fuselage + Empennage)) = #ac.feature
}

fact close_wing_feature {
	all w : Wing | #(w.feature :> NullThing) = 1
}

fact close_engine_feature {
	all e : Engine | #(e.feature :> NullThing) = 1
}

fact close_fuselage_feature {
	all f: Fuselage | #(f.feature :> NullThing) = 1
}

fact close_empennage_feature {
	all e : Empennage | #(e.feature :> (VTail + HTail)) = #e.feature
}

fact close_htail_feature {
	all v: VTail | #(v.feature :> NullThing) = 1
}

fact close_vtail_feature {
	all h: HTail | #(h.feature :> NullThing) = 1
}

//--------------------------------------- END EXAMPLE OBJECTS -------------------------

// -------------------------- AIRCRAFT EXAMPLE LINKS -----------------------------------

// TODO - expand the example
*/

sig AircraftToWing extends BinaryLink {
	wing_context_as_aircraft : one Aircraft,
	wing_end : one Wing
}

sig AircraftToEngine extends BinaryLink {
	engine_context_as_aircraft : one Aircraft,
	engine_end : one Engine
}

sig AircraftToFuselage extends BinaryLink {
	fuselage_context_as_aircraft : one Aircraft,
	fuselage_end : one Fuselage
}

sig AircraftToEmpennage extends BinaryLink {
	empennage_context_as_aircraft : one Aircraft,
	empennage_end : one Empennage
}

sig EmpennageToHTail extends BinaryLink {
	htail_context_as_empennage : one Empennage,
	htail_end : one HTail
}

sig EmpennageToVTail extends BinaryLink {
	vtail_context_as_empennage : one Empennage,
	vtail_end : one VTail
}

// subsetting ends

fact map_domain_AircraftToWing {
	all atw : AircraftToWing | atw.wing_context_as_aircraft in atw.domainEnd
}

fact map_range_AircraftToWing {
	all atw : AircraftToWing | atw.wing_end in atw.rangeEnd
}

fact map_domain_AircraftToEmpennage {
	all atw : AircraftToEmpennage | atw.empennage_context_as_aircraft in atw.domainEnd
}

fact map_range_AircraftToEmpennage {
	all atw : AircraftToEmpennage | atw.empennage_end in atw.rangeEnd
}

fact map_domain_EmpennageToHTail {
	all atw : EmpennageToHTail | atw.htail_context_as_empennage in atw.domainEnd
}

fact map_range_EmpennageToHTail {
	all atw : EmpennageToHTail | atw.htail_end in atw.rangeEnd
}

fact map_domain_EmpennageToVTail {
	all atw : EmpennageToVTail | atw.vtail_context_as_empennage in atw.domainEnd
}

fact map_range_EmpennageToVTail {
	all atw : EmpennageToVTail | atw.vtail_end in atw.rangeEnd
}

// no additional participants in definition

fact AircraftToWing_has_no_extra_participants {
	all atw : AircraftToWing | #(atw.participant) = 2
}

fact AircraftToEmpennage_has_no_extra_participants {
	all atw : AircraftToEmpennage | #(atw.participant) = 2
}

fact EmpennageToHTail_has_no_extra_participants {
	all atw : EmpennageToHTail | #(atw.participant) = 2
}

fact EmpennageToVTail_has_no_extra_participants {
	all atw : EmpennageToVTail | #(atw.participant) = 2
}

// don't let links duplicate

fact unique_AircraftToWing {
	all atw1, atw2 : AircraftToWing | (atw1.wing_context_as_aircraft = atw2.wing_context_as_aircraft and
		atw1.wing_end = atw2.wing_end) => atw1 = atw2
}

fact unique_AircraftToEmpennage {
	all atw1, atw2 : AircraftToEmpennage | (atw1.empennage_context_as_aircraft = atw2.empennage_context_as_aircraft and
		atw1.empennage_end = atw2.empennage_end) => atw1 = atw2
}

fact unique_EmpennageToHTail {
	all atw1, atw2 : EmpennageToHTail | (atw1.htail_context_as_empennage = atw2.htail_context_as_empennage and
		atw1.htail_end = atw2.htail_end) => atw1 = atw2
}

fact unique_EmpennageToVTail {
	all atw1, atw2 : EmpennageToVTail | (atw1.vtail_context_as_empennage = atw2.vtail_context_as_empennage and
		atw1.vtail_end = atw2.vtail_end) => atw1 = atw2
}

// link Link to feature

fact AircraftToWing_means_aircraft_featureClass {
	all wf : WingFeature | some atw : AircraftToWing | atw.wing_end in wf.type
}

fact AircraftToWing_means_wing_type {
	all wf : WingFeature | some atw : AircraftToWing | atw.wing_context_as_aircraft = wf.featuringClass
}

fact AircraftToEmpennage_means_aircraft_featureClass  {
	all ef : EmpennageFeature | some atw : AircraftToEmpennage | atw.empennage_context_as_aircraft = ef.featuringClass
}

fact AircraftToEmpennage_means_empennage_type {
	all ef : EmpennageFeature | some atw : AircraftToEmpennage | atw.empennage_end in ef.type
}

fact EmpennageToVTail_means_empennage_featureClass  {
	all vf : VTailFeature | some atw : EmpennageToVTail  | atw.vtail_context_as_empennage = vf.featuringClass
}

fact EmpennageToVTail_means_vtail_type {
	all vf : VTailFeature | some atw : EmpennageToVTail  | atw.vtail_end in vf.type
}

fact EmpennageToHTail_means_empennage_featureClass  {
	all hf : HTailFeature | some atw : EmpennageToHTail  | atw.htail_context_as_empennage = hf.featuringClass
}

fact EmpennageToHTail_means_vtail_type {
	all hf : HTailFeature | some atw : EmpennageToHTail  | atw.htail_end in hf.type
}

// do we need additional constraints to get multiplicity right?

/*

fact AircraftToEmpennage_means_empennage_feature {
	all a : Aircraft | one atw : AircraftToEmpennage | atw.empennage_end = a.empennage
}

fact EmpennageToHTail_means_htail_feature {
	all e : Empennage | some atw : EmpennageToHTail | atw.htail_end in e.htail
}

fact EmpennageToVTail_means_vtail_feature {
	all e : Empennage | some atw : EmpennageToVTail | atw.vtail_end in e.vtail
}
*/

// -------------------------------------- END EXAMPLE LINKS -------------------------------

pred show () {}

run show for 12 AbstractAnything, 6 AbstractFeature, 8 Link, exactly 1 Aircraft, exactly 1 WingFeature, exactly 1 EngineFeature,
	exactly 1 FuselageFeature, exactly 1 EmpennageFeature, exactly 1 VTailFeature, exactly 1 HTailFeature,
	exactly 2 AircraftToWing, exactly 2 EmpennageToVTail, exactly 2 EmpennageToHTail
