#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

// The §37.44 thread helpers, apart from the statement helpers of
// vpi_helpers_statements.cpp, which stood at the size the
// assert-no-oversized-source-files job fails at.

namespace delta {

// ===========================================================================
// §37.44 Threads.
// ===========================================================================

VpiHandle VpiThreadParent(VpiHandle thread) {
  // §37.44 (vpiParent -> thread): a thread reaches the thread that spawned it
  // through its parent link, provided that parent is itself a thread. A root
  // thread (no parent) and a null handle report none.
  if (!thread || !thread->parent) return nullptr;
  return thread->parent->type == vpiThread ? thread->parent : nullptr;
}

VpiHandle VpiThreadOrigin(VpiHandle thread) {
  // §37.44 (vpiOrigin -> stmt): the statement a thread was started from, held
  // apart from its children (ThreadObjectFor). Null when the handle is null or
  // the thread was started from no statement the model holds.
  return thread != nullptr ? thread->body : nullptr;
}

VpiHandle VpiThreadFrame(VpiHandle thread) {
  // §37.44 (frame -- thread) with §37.43 detail 4: the frame active in the
  // thread now. The outermost frame of its call chain hangs from the thread
  // and each frame activated from another from that one (ActivateFrame), and
  // every frame of the chain still running is active, so the frame active now
  // is the innermost of them; none once every frame of the chain has ended.
  VpiHandle active = nullptr;
  for (VpiHandle at = thread; at != nullptr;) {
    VpiHandle next = nullptr;
    for (auto* child : at->children) {
      if (child->type == vpiFrame && child->active) next = child;
    }
    if (next != nullptr) active = next;
    at = next;
  }
  return active;
}

bool VpiTryResolveThreadRelation(int type, VpiHandle ref, VpiHandle& out) {
  if (ref->type != vpiThread) return false;
  if (type == vpiParent) {
    out = VpiThreadParent(ref);
  } else if (type == vpiOrigin) {
    out = VpiThreadOrigin(ref);
  } else if (type == vpiFrame) {
    out = VpiThreadFrame(ref);
  } else {
    return false;
  }
  return true;
}

std::vector<VpiHandle> VpiThreadThreads(VpiHandle thread) {
  // §37.44 (thread one-to-many thread): the child threads this thread spawned,
  // as the thread iteration yields them - its thread children, in order.
  std::vector<VpiHandle> threads;
  if (!thread) return threads;
  for (auto* child : thread->children) {
    if (child->type == vpiThread) threads.push_back(child);
  }
  return threads;
}

}  // namespace delta
