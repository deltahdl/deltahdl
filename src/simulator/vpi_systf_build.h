#pragma once

namespace delta {

struct RtlirDesign;
class SimContext;
class Arena;

// §36.8: run the build-period routines of every registration the design's
// system calls name. "VPI-based system tasks have sizetf, compiletf, and calltf
// routines, which perform specific actions for the task or system function. The
// sizetf, compiletf, and calltf routines are called during specific periods
// during processing." Two of those three periods are this one, and the clause's
// own sentence is what makes them a period rather than a moment each routine
// happens to be reached at: §36.8.1 has a sizetf called "if its associated
// system function appears in the design", and §36.8.2 a compiletf called "when
// the user-defined system task or system function name is encountered during
// parsing or compiling the SystemVerilog source code". Neither is a thing the
// design's own execution does, so neither has anywhere else to be called from.
//
// The third period is execution, where §36.8.3 has the calltf called "each time
// the associated user-defined system task or system function is executed".
// VpiContext::CallRegisteredSystf is that one, and it is a different period
// from this: a design that calls a registration a thousand times runs the
// calltf a thousand times and the two routines here no more often than the
// build ran.
//
// Called from Lowerer::Lower, after the simulation data structure is built and
// before the scheduler runs a single event, because building that structure is
// what §38.37.1's "compiled or built" names in this simulator. That caller has
// already refused a design that is not there, and refused one §20.10.1 marked
// unstartable, so `design` is a design that was built rather than one that
// might have been.
//
// `ctx` and `arena` are what §36.8.2's compiletf is given its call through.
// The clause has the routine "check the correctness of any arguments passed to
// the user-defined system task or system function in the SystemVerilog source
// code", and §36.4 has an application read those arguments off the call object
// rather than off its own parameter list, so the call each compiletf is run for
// is built here: `ctx` is where an argument that names a variable finds it, and
// `arena` is what the call and its arguments are allocated out of.
void CallBuildPeriodSystfRoutines(const RtlirDesign* design, SimContext& ctx,
                                  Arena& arena);

}  // namespace delta
