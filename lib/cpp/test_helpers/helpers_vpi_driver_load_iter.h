#pragma once

#include <algorithm>
#include <vector>

#include "simulator/vpi.h"

using namespace delta;

// Walk an iterator to completion, collecting every object it yields in order.
inline std::vector<VpiHandle> CollectVpiIteration(VpiContext& ctx,
                                                  VpiHandle iterator) {
  std::vector<VpiHandle> objects;
  if (!iterator) return objects;
  while (VpiHandle next = ctx.Scan(iterator)) objects.push_back(next);
  return objects;
}

inline bool VpiIterationContains(const std::vector<VpiHandle>& objects,
                                 VpiHandle wanted) {
  return std::find(objects.begin(), objects.end(), wanted) != objects.end();
}
