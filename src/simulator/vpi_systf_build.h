#pragma once

namespace delta {

struct RtlirDesign;
class SimContext;
class Arena;

// §36.8: run the build-period routines of every registration the design's
// system calls name. A VPI-based system task or system function has three
// routines, sizetf, compiletf and calltf, each doing its own part of the work
// and each called in its own period of processing. Two of those three periods
// are this one, and the clause's own rule is what makes them a period rather
// than a moment each routine happens to be reached at: §36.8.1 has a sizetf
// called when the design holds its system function, and §36.8.2 a compiletf
// called when the parse or compile of the source code meets the user-defined
// system task or system function's name. Neither is a thing the
// design's own execution does, so neither has anywhere else to be called from.
//
// The third period is execution, where §36.8.3 has the calltf called on every
// execution of its user-defined system task or system function.
// VpiContext::CallRegisteredSystf is that one, and it is a different period
// from this: a design that calls a registration a thousand times runs the
// calltf a thousand times and the two routines here no more often than the
// build ran.
//
// Called from Lowerer::Lower, after the simulation data structure is built and
// before the scheduler runs a single event, because building that structure is
// what §38.37.1's compile or build step means in this simulator. That caller
// has already refused a design that is not there, and refused one §20.10.1
// marked unstartable, so `design` is a design that was built rather than one
// that might have been.
//
// `ctx` and `arena` are what §36.8.2's compiletf is given its call through.
// The clause has the routine verify the arguments the source code passes to
// the user-defined system task or system function, and §36.4 has an application
// read those arguments off the call object rather than off its own parameter
// list, so the call each compiletf is run for is built here: `ctx` is where an
// argument that names a variable finds it, and `arena` is what the call and its
// arguments are allocated out of.
void CallBuildPeriodSystfRoutines(const RtlirDesign* design, SimContext& ctx,
                                  Arena& arena);

}  // namespace delta
