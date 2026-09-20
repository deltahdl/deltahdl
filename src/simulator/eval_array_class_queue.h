#pragma once

#include <string_view>

#include "common/types.h"

namespace delta {

struct QueueObject;
struct ClassObject;
struct ClassTypeInfo;
struct Expr;
class SimContext;
class Arena;

// §7.10/§8.5: a class property declared with a queue dimension, `Item q[$]`
// or `T fifo[$:DEPTH-1]`, is a queue of the object: §8.5 puts no restriction
// on a property's data type, and §7.10 has a queue with no initial value
// start empty and grow and shrink with the operations of §7.10.1 and the
// methods of §7.10.2. The object holds one QueueObject per such property
// (ClassObject::queue_properties), and a static one is the class's
// (ClassTypeInfo::static_queue_properties, §8.9), each built on the first
// reference to the property with the element width the property record gives
// it and the bound §7.10.5 reads off the dimension.
//
// The queue named `name` on the class chain from `from` -- the property's
// declaration is looked for from that class upward, so an unqualified name in
// a method is resolved in the enclosing class's scope (§8.15) -- held by `obj`,
// or by the declaring class where the property is static, in which case `obj`
// may be null. Null where no class of the chain declares `name` as a property
// with one dimension IsQueueDim answers for.
QueueObject* ClassQueueProperty(ClassObject* obj, const ClassTypeInfo* from,
                                std::string_view name, SimContext& ctx);

// §8.7: builds the queue the property `name` of the level `info` of `obj`
// declares and fills it from the declaration's initializer `init`, an
// unpacked array concatenation or an assignment pattern (§7.10), so that
// `int q[$] = {1, 2}` holds two elements once the object is constructed.
// Returns false, building nothing, where `info` declares no queue property of
// the name, and the caller then stores the initializer as a value.
bool InitClassQueueProperty(ClassObject* obj, const ClassTypeInfo* info,
                            std::string_view name, const Expr* init,
                            SimContext& ctx);

// The queue the bare name `name` designates where it is written: the declared
// queue SimContext::FindQueue knows under the name, else -- where no variable
// or fixed array of the name shadows it -- the property of the running
// method's object (§8.11) or of its class (§8.10). `owner` receives the
// object whose property answered, or null where the queue is a declared one
// or a static property, so a writer knows which watchers §9.4.2 has it tell.
QueueObject* FindQueueOfName(std::string_view name, SimContext& ctx,
                             ClassObject** owner = nullptr);

// The queue the expression `base` designates, as the base of an element
// select, the receiver of a method call or the left of a member access: a
// bare name as FindQueueOfName reads it, `this.name` and `handle.name` naming
// the property of the object the handle refers to, and `C::name` a static
// property of class C. `owner` as above. Null where `base` is of no such
// shape or names no queue.
QueueObject* FindQueueOfBase(const Expr* base, SimContext& ctx, Arena& arena,
                             ClassObject** owner = nullptr);

// §9.4.2's announcement of a change to the queue `base` designates: to the
// watchers on the variables designating the object whose property it is,
// `owner`; to the static watchers of the class whose static property it is
// (§8.9), `C::all`, `p::C::all` or the bare `all` inside a method of C; or to
// those on the variable under a declared queue's name.
void AnnounceQueueChange(const Expr* base, ClassObject* owner, SimContext& ctx);

// §8.4/§7.10: `q[1].v` reads the property `v` of the object the element
// `q[1]` of a queue of class handles refers to, the queue a declared one or a
// property of an object. Returns false for a member access of any other
// shape, one on a queue whose elements are no handles, or an element that
// refers to no object.
bool TryEvalQueueElementMember(const Expr* expr, SimContext& ctx, Arena& arena,
                               Logic4Vec& out);

}  // namespace delta
