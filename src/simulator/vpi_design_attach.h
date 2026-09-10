#pragma once

namespace delta {

class SimContext;

// §36.6: put the design the run has just built within reach of the PLI
// applications linked into this tool, so that "the library of PLI C functions"
// they call has something to answer with. The clause is what those applications
// are: "C language functions that utilize the library of PLI C functions to
// access and interact dynamically with SystemVerilog software implementations
// as the SystemVerilog source code is executed". The library is there whatever
// this does -- vpi_handle_by_name and vpi_get_value are compiled into the tool
// -- and what is not there without it is the design they name, so an
// application calling vpi_handle_by_name from inside its calltf resolves the
// name against an empty registry of objects and reaches nothing the run holds.
//
// Called from Lowerer::Lower, where every variable the design declares has been
// created and no event has run yet, which is both before §36.8's build period
// and before the execution this clause describes.
//
// The design is attached where the run has a PLI application in it and not
// otherwise. §36.9 gives an application two ways of becoming part of the tool,
// a system task or system function registration (§36.9.1) and a simulation
// callback (§36.9.2), so a run holding neither has nobody to reach the design
// through this library and is left with the objects it would have had.
void AttachDesignToPliApplications(SimContext& ctx);

}  // namespace delta
