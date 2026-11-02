#pragma once

#include <string_view>

namespace delta {

class Arena;
class SimContext;
struct Stmt;

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

// §6.21 with §13.3.1: a variable a block declares is static unless declared
// automatic or declared in an automatic subroutine, and the block's frame,
// `frame`, is pushed with the variables it held when last left
// (SimContext::PushStaticScope), its maps of queues, associative arrays and
// shapes empty again. RetainBlockAggregates keeps, as RetainStaticAggregate
// does, the aggregates such declarations of `block` made in the top frame;
// RestoreBlockAggregates makes that frame refer to them again on the next
// entry. A declaration IsEffectivelyStaticLocal holds keeps its own.
// §6.21 and §13.3.2: true where the declaration `stmt`, run while the
// subroutine `func_name` (empty for none) is running, is a static variable its
// declaration keeps in a static frame: one written static, or one not written
// automatic in a subroutine declared static.
bool IsEffectivelyStaticLocal(const Stmt* stmt, std::string_view func_name,
                              SimContext& ctx);

// §6.21 with §13.3.1 and §8.6: true where the declaration `stmt` makes a new
// variable on each entry to its block: one written automatic, or one not
// written static in an automatic subroutine or a class method.
bool IsAutomaticLocal(const Stmt& stmt, SimContext& ctx);

void RetainBlockAggregates(const Stmt& block, std::string_view frame,
                           SimContext& ctx, Arena& arena);
void RestoreBlockAggregates(const Stmt& block, std::string_view frame,
                            SimContext& ctx);

}  // namespace delta
