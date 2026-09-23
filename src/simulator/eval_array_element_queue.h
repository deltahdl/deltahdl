#pragma once

namespace delta {

struct Expr;
struct QueueObject;
class SimContext;
class Arena;

// §7.4 with §7.10 (printed pages 153 and 169): an array whose element type is
// a queue -- a queue of queues `int qq[$][$]`, a dynamic array `q_t d[]` or an
// associative array `int aq[string][$]` -- holds a queue in each element, and
// `sel`, a select of one element of such an array, `qq[1]` or `aq["a"]`,
// designates that element's queue. The queue is found in the array the base
// of `sel` designates (QueueObject::element_queues,
// AssocArrayObject::int_element_queues and str_element_queues) and made the
// first time the element is reached. Null where the base designates no array
// whose elements are queues, where the index holds an x or z bit (§7.8.6,
// §7.10.1), and where a queue or dynamic array holds no element at the index.
//
// `allocate` says whether the element is being written, as a method that
// changes the queue (push_back, pop_front, delete and the rest) writes it.
// §7.8.7 allocates a missing associative entry when it is the target of a
// write, so with `allocate` the entry is made, and with it the queue starts
// empty whatever a deleted entry of the key held. Read alone, a missing entry
// allocates nothing and is an empty queue, the value Table 7-1 gives a queue
// element that does not exist.
QueueObject* ElementQueueOfSelect(const Expr* sel, SimContext& ctx,
                                  Arena& arena, bool allocate);

// §7.10.2 with §10.10 (printed pages 170 and 264): the queue an element pushed
// onto `outer`, a queue whose elements are queues, holds, made from the
// method's argument `item`: the elements of the queue `item` designates,
// `qq.push_back(inner)`, or the items of the unpacked array concatenation or
// the positional assignment pattern `item` is, `qq.push_back({})` and
// `qq.push_back('{1, 2})`, an item designating a queue contributing its
// elements and any other one value.
QueueObject* ElementQueueFromItem(const QueueObject* outer, const Expr* item,
                                  SimContext& ctx, Arena& arena);

}  // namespace delta
