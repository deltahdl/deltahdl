#pragma once

namespace delta {

class SimContext;
struct RtlirDesign;
struct VpiObject;

// §36.6: put the design the run has just built within reach of the PLI
// applications linked into this tool, so that the PLI library of C functions
// they call has something to answer with. The clause is what those applications
// are: C functions that use that library to reach the design and act on it
// while its source code executes. The library is there whatever
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
//
// `design` is what §37.14's ports are read off: the simulator keys a port's
// storage under the instance prefix like any other object, but the direction
// and the order the module declared them in live in the elaborated design.
void AttachDesignToPliApplications(const RtlirDesign* design, SimContext& ctx);

// §37.43: one subroutine activation, as the frame the VPI reaches. Detail 1 has
// a frame stand for a procedural scope activated at run time, with the
// automatic variables, events and event arrays it declares, and §37.44 detail 1
// says when one is activated: on entering each task or function down a
// thread's chain of calls. So the activation is an object whose life
// is the call's, which is what this is -- constructed where the body is entered
// and destroyed however the body leaves, including the early return out of the
// middle of one.
//
// Detail 4 is what it is for: a thread has at most one active frame at a time,
// and vpi_handle(vpiFrame, NULL) answers it. Nothing in the tool ever made a
// frame active, so that routine answered null under every design.
class VpiActiveFrameScope {
 public:
  VpiActiveFrameScope();
  ~VpiActiveFrameScope();

  VpiActiveFrameScope(const VpiActiveFrameScope&) = delete;
  VpiActiveFrameScope& operator=(const VpiActiveFrameScope&) = delete;

 private:
  // The thread the frame was activated in, which it is left in, declared first
  // so that it is set before the activation writes it.
  const void* thread_ = nullptr;
  VpiObject* outer_ = nullptr;
};

}  // namespace delta
