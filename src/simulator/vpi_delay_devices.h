#pragma once

#include <functional>

namespace delta {

struct VpiObject;

// §37.45: the delay device that the delay `source` holds places on `net`, of
// vpiDelayType `delay_type` and under the module `module` holding the net.
// `source` is the module path, intermodule path or input port whose delay it
// is. The first call makes the device with its input and output delay terms,
// hanging both on the net, where §37.46 lists a delay term among its loads and
// among its drivers; a later call for the same source finds that device again.
// `alloc` makes each object.
VpiObject* VpiPlaceDelayDevice(VpiObject* source, VpiObject* net,
                               VpiObject* module, int delay_type,
                               const std::function<VpiObject*()>& alloc);

// §37.37 with §37.45: the delay device the intermodule path `path` places once
// given a delay, of vpiDelayType vpiInterModPathDelay, on the net its driving
// port's higher connection names in the scope connecting its two ports, under
// the module holding that net; null where that connection is no net.
VpiObject* VpiPlaceInterModPathDevice(VpiObject* path,
                                      const std::function<VpiObject*()>& alloc);

// §37.14 with §37.45: the delay device the port `port` places once given a
// module input port delay, of vpiDelayType vpiMIPDelay, on the net its lower
// connection names inside its instance, under that instance; null where that
// connection is no net.
VpiObject* VpiPlacePortDelayDevice(VpiObject* port,
                                   const std::function<VpiObject*()>& alloc);

// §37.45 details 1 and 2: the net whose value the delay term `term` reads. An
// input term takes the value ahead of the delay, which is its own net's. An
// output term takes the value past it: for a module path's device, whose delay
// a run applies where the instance's output port drives the net above, the net
// that port's higher connection names; otherwise its own net's.
VpiObject* VpiDelayTermValueNet(const VpiObject& term);

}  // namespace delta
