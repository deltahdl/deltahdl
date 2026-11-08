#pragma once

#include <string>

namespace delta {

struct Net;
class SimContext;

struct InoutPortLinkEnds {
  Net& outer;
  Net& inner;
  std::string outer_origin;
  std::string inner_origin;
  std::string port;
  std::string source;
  std::string load;
};

void LinkInoutPortNets(InoutPortLinkEnds ends, SimContext& ctx);

std::string SdfHierName(const std::string& dotted);

}  // namespace delta
