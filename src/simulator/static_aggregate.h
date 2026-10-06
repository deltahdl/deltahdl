#pragma once

#include <string_view>

namespace delta {

class Arena;
class SimContext;

// §13.3.1 (printed page 339) and §13.4.2 (printed 344): a subroutine defined
// in a module, interface, program or package is static by default, every item
// it declares allocated statically, and §13.3.2 (printed 339) has its
// variables, its arguments of every direction among them, keep their values
// from one call to the next. A static subroutine's frame is pushed
// with the variables it held when the last call returned
// (SimContext::PushStaticScope), but a queue, an associative array and a
// fixed-size array's shape stand in the frame's own maps, which start empty,
// so a static `int q[$]` was a new empty queue on every call after the first
// and `a[0]` of a static `int a[2]` found no array to select from.
//
// RetainStaticAggregate keeps what the top frame holds under `name` -- its
// queue, associative array and shape -- as the static storage of the
// subroutine `frame`, in the running instance, making the frame refer to that
// storage; a later call's contents are copied into the same storage.
// RestoreStaticAggregate makes the top frame's `name` refer to that storage
// again, answering whether any was kept. `name` is a view the frame keeps as
// a key, so it outlives the frame.
void RetainStaticAggregate(std::string_view frame, std::string_view name,
                           SimContext& ctx, Arena& arena);
bool RestoreStaticAggregate(std::string_view frame, std::string_view name,
                            SimContext& ctx);

}  // namespace delta
