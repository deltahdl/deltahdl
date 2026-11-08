#pragma once

namespace delta {

class VpiContext;
struct VpiObject;

void WatchObjectChanges(VpiContext& vpi, VpiObject* obj);

}  // namespace delta
