#pragma once

#include <string_view>

namespace delta {

class Arena;
class SimContext;
struct Net;

void AttachNettypeResolution(Net& net, std::string_view func_name,
                             SimContext& ctx);

bool ResolveThroughNettypeFunction(Net& net, Arena& arena);

}  // namespace delta
