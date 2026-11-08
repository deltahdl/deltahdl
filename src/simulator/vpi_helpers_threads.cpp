#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

VpiHandle VpiThreadParent(VpiHandle thread) {
  if (!thread || !thread->parent) return nullptr;
  return thread->parent->type == vpiThread ? thread->parent : nullptr;
}

VpiHandle VpiThreadOrigin(VpiHandle thread) {
  return thread != nullptr ? thread->body : nullptr;
}

VpiHandle VpiThreadFrame(VpiHandle thread) {
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
  if (ref->type != vpiThread ||
      (type != vpiParent && type != vpiOrigin && type != vpiFrame)) {
    return false;
  }
  if (type == vpiParent) out = VpiThreadParent(ref);
  if (type == vpiOrigin) out = VpiThreadOrigin(ref);
  if (type == vpiFrame) out = VpiThreadFrame(ref);
  return true;
}

bool VpiTryResolveFrameRelation(int type, VpiHandle ref, VpiHandle& out) {
  if (ref->type != vpiFrame || (type != vpiParent && type != vpiOrigin &&
                                type != vpiStmt && type != vpiThread)) {
    return false;
  }
  if (type == vpiParent) out = VpiFrameParent(ref);
  if (type == vpiOrigin) out = VpiFrameOrigin(ref);
  if (type == vpiStmt) out = VpiFrameStmt(ref);
  if (type == vpiThread) out = VpiFrameThread(ref);
  return true;
}

bool VpiCollectFrameAutomatics(int type, VpiHandle ref, VpiHandle iter) {
  if (type != vpiAutomatics || ref->type != vpiFrame) return false;
  for (VpiHandle automatic : VpiFrameAutomatics(ref)) {
    iter->children.push_back(automatic);
  }
  return true;
}

std::vector<VpiHandle> VpiThreadThreads(VpiHandle thread) {
  std::vector<VpiHandle> threads;
  if (!thread) return threads;
  for (auto* child : thread->children) {
    if (child->type == vpiThread) threads.push_back(child);
  }
  return threads;
}

}  // namespace delta
