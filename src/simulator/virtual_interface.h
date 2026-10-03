#pragma once

// §25.9: what the expression written as the base of a member access in
// procedural code, `v` in `v.clk`, `bus` in `bus.req <= 1'b1`, `d.vif` in
// `d.vif.a`, denotes when it is a virtual interface, and which component of
// which instance the access then reaches. A virtual interface is a value, the
// handle of the interface instance it represents
// (SimContext::VirtualInterfaceHandle), and the declaration holding it can be
// a variable of the design or a local of the running subroutine, a formal of
// that subroutine, or a property of a class object -- the clause has a class
// property initialized procedurally or through an argument of new() and used
// by the class's own methods, which is how a transactor reaches its bus, and
// a module or another object reaches the same property through a handle to
// the transactor. The three readers of such a base -- the expression
// evaluator (TryVirtualInterfaceMember in eval_expr.cpp), the assignment
// target resolver (ResolveVirtualInterfaceField in statement_assign.cpp) and
// the event control awaiter (CollectVirtualInterfaceMember in
// awaiters_event_control.h) -- resolve it here, so that a property of `this`
// or of an object reached through a handle is a virtual interface to all
// three or to none.

#include <cstdint>
#include <string>
#include <string_view>

namespace delta {

class Arena;
class SimContext;
struct DataType;
struct Expr;
struct Logic4Vec;
struct SourceLoc;

// §25.9: the null handle, which a virtual interface holds before it is
// initialized and after `null` is assigned to it.
inline constexpr uint64_t kNullVirtualInterface = 0;

struct VirtualInterfaceBase {
  // Whether the base denotes a virtual interface at all: a variable the
  // running scope resolves a bare name to that was declared so, or, where no
  // variable answers the name, a property declared so of the class whose
  // method is running, or a property declared so of the object a handle
  // expression (`this`, `d`, `outer.inner`) refers to. A local of the name
  // shadows the property, as it shadows it for every other read.
  bool is_virtual_interface = false;
  // The handle the declaration holds; kNullVirtualInterface for one bound to
  // no instance, and for a property asked with no object in scope.
  uint64_t handle = kNullVirtualInterface;
};

// §25.9 and §6.18: whether a declaration written with `type` declares a
// virtual interface: the type itself, or a typedef name that stands for one,
// which the elaborated type-kind table answers. A local of a subroutine body
// or a formal declared so holds an instance handle and is flagged so, as a
// variable of the design declared so is.
bool DeclaresAVirtualInterface(const DataType& type, const SimContext& ctx);

// §25.9: resolves the bare name `name` as the base of a member access.
// `arena` is what a property read hands back a default through.
VirtualInterfaceBase ResolveVirtualInterfaceBase(std::string_view name,
                                                 SimContext& ctx, Arena& arena);

// §25.9: resolves the expression `base` as the base of a member access: a
// bare name as ResolveVirtualInterfaceBase resolves it, or a member access
// `h.p` whose `h` denotes a class object -- `this`, a class-handle variable
// of the running scope, a class-handle property of the running method's
// object, or such a member access in turn, as deep as the design writes it --
// and whose `p` is a property of that object declared a virtual interface.
// §8.9 with §8.23: `C::p`, a static property of the class C declared so.
// §7 with §25.9: an element of a container declared with virtual interface
// elements -- `v[0]` of a fixed array, `q[1]` of a queue, `m["two"]` of an
// associative array, `vifs[i]` of an array property -- whose handle is the
// element's value. Answers no virtual interface for any other shape.
VirtualInterfaceBase ResolveVirtualInterfaceBaseExpr(const Expr* base,
                                                     SimContext& ctx,
                                                     Arena& arena);

// §25.9 with §27.5 and §23.6: a member access whose path passes through a
// virtual interface before its last step, `vif.g.v` for the variable v of the
// named generate block g of the instance `vif` represents. Answers that
// virtual interface and puts in `field` the path after it, "g.v", which
// VirtualInterfaceComponentName joins to the instance. Answers no virtual
// interface for a path through none, and where the base of the last step is
// the virtual interface itself, `vif.v`, which the caller resolves.
VirtualInterfaceBase ResolveVirtualInterfaceInnerPath(const Expr* expr,
                                                      SimContext& ctx,
                                                      Arena& arena,
                                                      std::string& field);

// §25.9: the full name of component `field` of the instance `handle`
// represents, `top.dif.clk` for `clk` of the instance at `top.dif`, which is
// the variable a read, a write or an event control through the virtual
// interface reaches. Empty for the null handle, which represents no instance.
std::string VirtualInterfaceComponentName(uint64_t handle,
                                          std::string_view field,
                                          const SimContext& ctx);

// §25.9: the handle an operand of `==` or `!=` against a virtual interface
// stands for: the null handle for `null`, and otherwise the operand's value,
// which is a handle for a virtual interface held anywhere -- a variable, a
// formal, a class property, a function's result -- and for an interface
// instance named by a name or a path (ResolveInstanceScope). Handles are
// interned one per instance, so two operands representing one instance
// answer the same handle.
uint64_t VirtualInterfaceOperandHandle(const Expr* operand, SimContext& ctx,
                                       Arena& arena);

// §25.9 with §23.6: an interface instance named by a path rather than a
// simple name -- an element of an instance array, `s[1]`, an instance in a
// generate block, `g[1].s`, or one reached from a top, `top.s1` -- is the
// handle of that instance where a value is wanted, as its simple name is
// (TryInterfaceInstanceHandle in evaluation.cpp). Answers true and puts the
// handle in `out` where `expr` is such a path; false for any other
// expression, a member of an instance among them, and without reading it for
// a path headed by a name that holds storage -- a variable, an array, a net
// or a property of the running method's class -- whose select is an element
// and whose index is read once, by the caller.
bool TryInterfaceInstancePathHandle(const Expr* expr, SimContext& ctx,
                                    Arena& arena, Logic4Vec& out);

// §25.9: a reference through a virtual interface that represents no instance
// is a fatal run-time error, so it is reported at `loc` and the run is ended
// as `$fatal` ends it (§20.10): the running block stops at its next
// statement, and no further time step is taken.
void ReportNullVirtualInterface(SourceLoc loc, SimContext& ctx);

}  // namespace delta
