#pragma once

namespace delta {

class VpiContext;
struct VpiObject;

// §38.36.1 with §37.17 detail 14: watch the storage of `obj` and, as it is
// written, call back the cbSizeChange registrations placed on it where its
// size changed, then the cbValueChange ones where its value did, until none
// of either is left.
void WatchObjectChanges(VpiContext& vpi, VpiObject* obj);

}  // namespace delta
