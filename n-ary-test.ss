@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
@prefix org: <http://www.w3.org/ns/org#> .
@prefix nary: <http://gallows.inf.ed.ac.uk/schema/n-ary#> .
@prefix xsddec: <http://id.ninebynine.org/2003/XMLSchema/decimal#> .
@prefix ex: <http://example.org/> .

### Is this really necessary?
@read :nary <n-ary.n3>

################################################################
###
### Rules for n-ary relations and curried predicates
###
################################################################

################################################################
###
### Rule #1 - Convert from a binary relation to reified form.
###
################################################################
@rule :binary :- {
    ?x ?rel ?y .
    ?rel a nary:BinaryRelation ;
        nary:reifiedType ?reified ;
        nary:subjectPredicate ?subjP ;
        nary:objectPredicate ?objP ;
        nary:arg ?arg .
    ?arg nary:predicate ?argP ;
         nary:object ?argO .
} => {
    [
        a ?reified ;
        ?subjP ?x ;
        ?objP ?y ;
        ?argP ?argO
    ] .
}

################################################################
###
### Rule #2 - Convert from a reified form to a binary relation.
###
################################################################
@rule :revBinary :- {
    ?rel a nary:BinaryRelation ;
        nary:reifiedType ?reified ;
        nary:subjectPredicate ?subjP ;
        nary:objectPredicate ?objP ;
        nary:arg ?arg .
    ?arg nary:predicate ?argP ;
         nary:object ?argO .
    ?nary a ?reified ;
        ?subjP ?subj ;
        ?objP ?obj ;
        ?argP ?argO .
} => {
    ?subj ?rel ?obj .
}

################################################################
###
### Rule #3 - When nary:CurriedPredicates inherit, they carry
###           along the nary:reifiedType.
###
################################################################
@rule :inheritType :- {
    ?super a nary:CurriedPredicate ;
        nary:reifiedType ?type .
    ?sub rdfs:subPropertyOf ?super .
} => {
    ?sub nary:reifiedType ?type .
}

################################################################
###
### Rule #4 - When nary:CurriedPredicates inherit, they carry
###           along the arguments. This is what gives us N>3.
###
################################################################
@rule :inheritArgs :- {
    ?super a nary:CurriedPredicate ;
        nary:arg ?arg .
    ?sub rdfs:subPropertyOf ?super .
} => {
    ?sub nary:arg ?arg .
}

################################################################
###
### Test Case I: curried binary org:Membership
### This means simply converting in one direction from,
###
###     ex:org ex:president ex:alice
###
### to,
###
###     [ a org:Membership ;
###       org:organisation ex:org ;
###       org:role ex:president ;
###       org:member ex:alice ]
###
################################################################

### definition of a curried binary version of org:Membership
### which always has org:role of ex:president
:president :- {
    ex:president a nary:BinaryRelation ;
        nary:reifiedType org:Membership ;
        nary:subjectPredicate org:organisation ;
        nary:objectPredicate org:member ;
        nary:arg [
            nary:predicate org:role ;
            nary:object ex:president
        ] .
}

### simple test input
:membershipTest :- {
    ex:org ex:president ex:alice .
}

### run the binary relation test and check the result
@ruleset :rules :- (:nary) ; (:binary)
@fwdchain :rules :binary (:president :membershipTest) => :membershipResult
:membershipExp :- {
    [
        a org:Membership ;
        org:organisation ex:org ;
        org:role ex:president ;
        org:member ex:alice
    ] .
}
@asserteq :membershipResult :membershipExp ; Check for a reified membership
    

#################################################################
##
## Test Case II: Unit conversions, flattening of reified n-ary
## relations into binary relations. This means converting back
## and forth between the forms,
##
##     :foo :massInBar 123.0.
##
## and
##
##     [ a :MassObservation ;
##       :system :foo ;
##       :value 123.0 ;
##       :unit :bar ]
##
## adding in a unit conversion, we implement the desired 
## implication,
##
##    { :foo :massInBar 123.0 } <=> { :foo :massInBaz 456.0 }
##
#################################################################

:mass :- {
    ### a curried predicate embedding the kilogram unit
    ex:massInKilograms a nary:BinaryRelation ;
        nary:reifiedType ex:MassObservation ;
        nary:subjectPredicate ex:system ;
        nary:objectPredicate ex:value ;
        nary:arg [
            nary:predicate ex:unit ;
            nary:object ex:kg
        ] .

    ### a curried predicate embedding the pounds unit
    ex:massInPounds a nary:BinaryRelation ;
        nary:reifiedType ex:MassObservation ;
        nary:subjectPredicate ex:system ;
        nary:objectPredicate ex:value ;
        nary:arg [
            nary:predicate ex:unit ;
            nary:object ex:lb
        ] .
}

:conversion :- {
    ### a unit conversion description from kg to lbs
    [ 
        a ex:UnitConversion ;
        ex:fromUnit ex:kg ;
        ex:toUnit ex:lb ;
        ex:factor 2.2
    ] .
}

### A simplistic unit conversion rule
@rule :convert :- {
    ?obs a ex:MassObservation ;
        ex:system ?sys ;
        ex:value ?val ;
        ex:unit ?unit .
    ?conv a ex:UnitConversion ;
        ex:fromUnit ?unit ;
        ex:toUnit ?toUnit ;
        ex:factor ?factor .
} => {
    [
        a ex:MassObservation ;
        ex:system ?sys ;
        ex:value ?toVal ;
        ex:unit ?toUnit
    ] .
} | ( xsddec:prod ?toVal ?val ?factor )

### Initial input for unit conversion test case
:massTest :- {
    ex:spaceship ex:massInKilograms 1000.0 .
}

@ruleset :rules :- (:mass :conversion) ; (:binary :revBinary :convert)

### First step is to produce the decurried version of the mass observation
@fwdchain :rules :binary (:mass :conversion :massTest) => :reifiedKg
:reifiedKgExp :- {
    [
        a ex:MassObservation ;
        ex:system ex:spaceship ;
        ex:value 1000.0 ;
        ex:unit ex:kg
    ] .
}
@asserteq :reifiedKg :reifiedKgExp ; Check for correct mass in kg

### Then we do a unit conversion
@fwdchain :conversionRules :convert (:mass :conversion :reifiedKg) => :reifiedLbs
:reifiedLbsExp :- {
    [
        a ex:MassObservation ;
        ex:system ex:spaceship ;
        ex:value 2200.0 ;
        ex:unit ex:lb
    ] .
}
@asserteq :reifiedLbs :reifiedLbsExp ; Check the correct mass in lbs

### Finally we generate the result in terms of the curried predicate for pounds
@fwdchain :rules :revBinary (:mass :conversion :reifiedLbs) => :lbs
:lbsExp :- {
    ex:spaceship ex:massInPounds 2200.0 .
}
@asserteq :lbs :lbsExp ; Check the correct curried mass in lbs 


###########################################################################
###
### Test Case III - N-ary curried predicate where N > 3
###
### In this case we add an extra parameter to the mass observation,
### the reference frame. And so we convert back and forth between,
###
###     [ a :MassObservation ;
###       :system :spaceship ;
###       :refFrame :rest ;
###       :value 1000.0 ;
###       :units :kg ].
###
### and
###
###     :spaceship :restMassInKilograms 1000.0 .
###
###########################################################################
:relMass :- {
    ### a curried partial predicate embedding the reference frame
    ex:restMass a nary:CurriedPredicate ;
        nary:reifiedType ex:MassObservation ;
        nary:arg [
            nary:predicate ex:refFrame ;
            nary:object ex:rest
        ] .

    ### a curried binary predicate embedding the kilogram unit
    ex:restMassInKilograms a nary:BinaryRelation ;
        rdfs:subPropertyOf ex:restMass ;
        nary:subjectPredicate ex:system ;
        nary:objectPredicate ex:value ;
        nary:arg [
            nary:predicate ex:unit ;
            nary:object ex:kg
        ] .
}

### test input
:spaceship :- {
    ex:spaceship ex:restMassInKilograms 1000.0 .
}

@ruleset :rules :- (:relMass) ; (:binary :revBinary :inheritType :inheritArgs)
### fill out the implied bits of schema that come when predicates inherit
@fwdchain :rules :inheritType (:relMass) => :relMassType
@fwdchain :rules :inheritArgs (:relMass) => :relMassArgs

### run the rules to reify the observation
@fwdchain :rules :binary (:relMass :relMassType :relMassArgs :spaceship) => :spaceshipReified
:spaceshipReifiedExp :- {
    [
        a ex:MassObservation ;
        ex:system ex:spaceship ;
        ex:refFrame ex:rest ;
        ex:value 1000.0 ;
        ex:unit ex:kg
    ] .
}
@asserteq :spaceshipReified :spaceshipReifiedExp ; Check correct reified relativistic mass

### run the rules in reverse to curry the observation
@fwdchain :rules :revBinary (:relMass :relMassType :relMassArgs :spaceshipReified) => :spaceshipCurried
:spaceshipCurriedExp :- {
    ex:spaceship ex:restMassInKilograms 1000.0 .
}
@asserteq :spaceshipCurried :spaceshipCurriedExp ; Check correct curried relativistic mass
