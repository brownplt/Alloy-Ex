module exercises/tube

abstract sig Station {
	jubilee, central, circle: set Station,
	}

sig Jubilee, Central, Circle in Station {}

one sig
	Stanmore, BakerStreet, BondStreet, Westminster, Waterloo, 
	WestRuislip, EalingBroadway, NorthActon, NottingHillGate,
	LiverpoolStreet, Epping
	extends Station {
	}

fact numConstraints {
	#Jubilee >4
	#Central >6
	#Circle >3
	}

// Every station is on at least one line
fact noWidows {
	all s: Station | ((s in Jubilee) or (s in Central) or (s in Circle))
	}

// Every station in a given line is served by that line, and vice versa
pred servicesAllStations (stations: set Station, line: Station -> set Station) {
	all s: stations | some s2: stations | ((s in s2.^line) or (s2 in s.^line))
	all s1, s2: Station | s1 in s2.^line implies (s1 in stations and s2 in stations)
	}

// There are no gaps in a line
-- I'm not sure why, but this dramatically increases solving time
pred connected (stations: set Station, line: Station -> set Station) {
	all s1, s2: stations | (s1 = s2) or (s2 in s1.^line) or (s1 in s2.^line) or (some s3: stations | s3 in s1.^line and s3 in s2 .^line)
	}

// Any two stations on the same line can find a common meeting station
pred meetingPoint (stations: set Station, line: Station -> set Station) {
	all s1, s2: stations | some s3: stations | (s3 in s1.^line or s1 = s3) and (s3 in s2.^line or s2 = s3)
	}

// The lines are one way 
--	Can't use the transitive closure of line, because it would prohibit a circle
pred oneWay (stations: set Station, line: Station -> set Station) {
	all s1, s2: stations | (s1 in s2.line) implies not (s2 in s1.line)
	}
// A line is a circle!
pred isCircle (stations: set Station, line: Station -> set Station) {
	all s: stations | s in s.^line
	}
// A line is NOT a circle!
pred hasEndPoints (stations: set Station, line: Station -> set Station) {
	some start: stations | no s: stations | start in s.line
	some end: stations | no s: stations | s in end.line
	}

//fact lines {
//	Stanmore, BakerStreet, BondStreet, Westminster, Waterloo in Jubilee
//	WestRusisip, EalingBroadway, NorthActon, NottingHillGate, BondStreet, LiverpoolStreet, Epping in Central
//	NottingHillGate, Westminster, LiverpoolStreet, BakerStreet in Circle
//	}

run {
	servicesAllStations[Jubilee, jubilee]
	servicesAllStations[Central, central]
	servicesAllStations[Circle, circle]
	connected[Jubilee, jubilee]
	connected[Central, central]
	connected[Circle, circle]
	meetingPoint[Jubilee, jubilee]
	meetingPoint[Central, central]
	meetingPoint[Circle, circle]
	oneWay[Jubilee, jubilee]
	oneWay[Central, central]
	oneWay[Circle, circle]
	hasEndPoints[Jubilee, jubilee]
	isCircle[Circle, circle]
	hasEndPoints[Central, central]
	}
