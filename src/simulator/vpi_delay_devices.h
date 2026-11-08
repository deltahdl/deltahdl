#pragma once

#include <functional>

namespace delta {

struct VpiObject;

VpiObject* VpiPlaceDelayDevice(VpiObject* source, VpiObject* net,
                               VpiObject* module, int delay_type,
                               const std::function<VpiObject*()>& alloc);

VpiObject* VpiPlaceInterModPathDevice(VpiObject* path,
                                      const std::function<VpiObject*()>& alloc);

VpiObject* VpiPlacePortDelayDevice(VpiObject* port,
                                   const std::function<VpiObject*()>& alloc);

VpiObject* VpiDelayTermValueNet(const VpiObject& term);

}  // namespace delta
