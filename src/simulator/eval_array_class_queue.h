#pragma once

#include <string_view>

#include "common/types.h"

namespace delta {

struct QueueObject;
struct ClassMember;
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

// §8.5/§7.10: whether the property declaration `member` of `declaring` is a
// queue, its one unpacked dimension `[$]` or `[$:N]`, written on it or on the
// typedef its type names.
bool IsQueuePropertyDecl(const ClassMember* member,
                         const ClassTypeInfo* declaring, SimContext& ctx);

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

// §7.8.7 with §7.4: the queue `base` designates as the base of an element
// select a write is about to write through, as FindQueueOfBase finds it, but
// with an element of an associative array whose elements are queues or
// fixed-size arrays allocated where its key is missing, as a write allocates
// an associative element: `af[1][0] = 5` on `int af[int][2]` makes af[1].
QueueObject* FindWrittenQueueOfBase(const Expr* base, SimContext& ctx,
                                    Arena& arena, ClassObject** owner);

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

// §7.12 with §8.5: the array manipulation methods apply to a queue property
// as to any queue, but read their receiver by the name SimContext::FindQueue
// answers, which a property has none of. For the call `call` -- `h.q.sum()`,
// `h.q.find with (...)`, or `q.sum()` in a method, where no declared queue
// answers `q` -- on a queue property, a scope frame is pushed for as long as
// this lives in which the receiver's spelling, "h.q" or "q", names the
// property's queue, and Call() is `call` with that spelling as a bare name
// for its receiver. The queue an array method returns, `IA.find(x) with
// (x > 5).unique`, is named so too, as is a fixed or dynamic array property,
// `h.d.max`, or a subarray of a multidimensional one, `h.g[1].min()` (§7.4.4),
// by a queue holding a copy of its elements, which serves the reductions and
// locators this is for, as they only read the elements.
// Nothing is pushed, and Call() is null, for a call of any other shape or on
// any other receiver.
class QueuePropertyReceiver {
 public:
  QueuePropertyReceiver(const Expr* call, SimContext& ctx, Arena& arena);
  ~QueuePropertyReceiver();
  QueuePropertyReceiver(const QueuePropertyReceiver&) = delete;
  QueuePropertyReceiver& operator=(const QueuePropertyReceiver&) = delete;

  const Expr* Call() const { return call_; }

 private:
  SimContext& ctx_;
  const Expr* call_ = nullptr;
};

}  // namespace delta
