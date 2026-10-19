#pragma once

namespace delta {

struct VpiObject;

// §37.43: what a frame the run activated reports through vpiOrigin and the
// frame to stmt transition, which the activation and the statements run in it
// record, apart from the frame's children, which a frame's end releases with
// it (§37.2.2). Kept apart from vpi_object.h, which stands near the size the
// assert-no-oversized-source-files job fails at.
struct VpiFrameFacts {
  // Detail 6: the point in the elaboration hierarchy the frame was activated
  // from, the call of the task or function it is an activation of; null where
  // the model holds no object for that call.
  VpiObject* origin = nullptr;
  // Details 4 and 5: the statement that ran in the frame last, which is the one
  // active in it while it is the active frame, and once another frame was
  // activated from it, the one whose execution activated that frame.
  VpiObject* stmt = nullptr;
};

}  // namespace delta
