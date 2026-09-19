#pragma once

// §25.9: what a name written as the base of a member access in procedural
// code, `v` in `v.clk`, `bus` in `bus.req <= 1'b1`, denotes when it is a
// virtual interface, and which component of which instance the access then
// reaches. A virtual interface is a value, the handle of the interface
// instance it represents (SimContext::VirtualInterfaceHandle), and the
// declaration holding it can be a variable of the design, a formal of the
// running subroutine, or a property of the class whose method is running --
// the clause has a class property initialized procedurally or through an
// argument of new() and used by the class's own methods, which is how a
// transactor reaches its bus. The three readers of such a base -- the
// expression evaluator (TryVirtualInterfaceMember in eval_expr.cpp), the
// assignment target resolver (ResolveVirtualInterfaceField in
// statement_assign.cpp) and the event control awaiter
// (CollectVirtualInterfaceMember in awaiters_event_control.h) -- resolve it
// here, so that a property of `this` is a virtual interface to all three or to
// none.

#include <cstdint>
#include <string>
#include <string_view>

namespace delta {

class Arena;
class SimContext;

// §25.9: the null handle, which a virtual interface holds before it is
// initialized and after `null` is assigned to it.
inline constexpr uint64_t kNullVirtualInterface = 0;

struct VirtualInterfaceBase {
  // Whether the name denotes a virtual interface at all: a variable the
  // running scope resolves it to that was declared so, or, where no variable
  // answers the name, a property declared so of the class whose method is
  // running. A local of the name shadows the property, as it shadows it for
  // every other read.
  bool is_virtual_interface = false;
  // The handle the declaration holds; kNullVirtualInterface for one bound to
  // no instance, and for a property asked with no object in scope.
  uint64_t handle = kNullVirtualInterface;
};

// §25.9: resolves `name` as the base of a member access. `arena` is what a
// property read hands back a default through.
VirtualInterfaceBase ResolveVirtualInterfaceBase(std::string_view name,
                                                 SimContext& ctx, Arena& arena);

// §25.9: the full name of component `field` of the instance `handle`
// represents, `top.dif.clk` for `clk` of the instance at `top.dif`, which is
// the variable a read, a write or an event control through the virtual
// interface reaches. Empty for the null handle, which represents no instance.
std::string VirtualInterfaceComponentName(uint64_t handle,
                                          std::string_view field,
                                          const SimContext& ctx);

}  // namespace delta
