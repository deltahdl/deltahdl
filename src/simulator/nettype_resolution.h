#pragma once

#include <string_view>

namespace delta {

class Arena;
class SimContext;
struct Net;

// §6.6.7 (printed pages 97 to 99): a net of a user-defined nettype declared
// with a resolution function takes the value the function returns for the
// net's drivers, handed to it as a dynamic array of the nettype's data type.
// Gives `net` the hook that calls `func_name` in `ctx` for it; a nettype with
// no resolution function leaves the net without one.
void AttachNettypeResolution(Net& net, std::string_view func_name,
                             SimContext& ctx);

// Resolves `net` through its nettype's resolution function, where it has one
// and at least one driver. Answers whether it did; otherwise the net resolves
// as any other.
bool ResolveThroughNettypeFunction(Net& net, Arena& arena);

}  // namespace delta
