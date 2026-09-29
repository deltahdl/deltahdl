#pragma once

#include <cstddef>
#include <string_view>

namespace delta {

struct ArrayInfo;
struct Expr;
struct QueueObject;
struct Stmt;
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

// §7.12 with §7.10: binds the iterator `iter_name` of a with clause, in the
// current scope, to the element at position `pos` of `outer`, a queue or
// dynamic array whose elements are queues or fixed-size arrays: a local
// queue holding a copy of that element's values, so that `item.sum()` and
// `item[1]` read them.
void BindElementQueueIterator(const QueueObject& outer, size_t pos,
                              std::string_view iter_name, SimContext& ctx,
                              Arena& arena);

// §7.4 with §10.9 (printed pages 153 and 261): `q`, a queue or dynamic array
// whose elements are queues, assigned the positional assignment pattern
// `pattern`, holds one element per item, each item making that element's
// queue as a pushed argument makes it (ElementQueueFromItem): §10.10.3's
// `'{ {1}, T_QI'{2,3,4}, {5,6} }` is three elements of one, three and two
// values. §7.12.1 with §7.4.4: `pattern` may instead be a locator selecting
// rows of a two-dimensional array, `m.find with (item.sum() > 5)`, and each
// selected row becomes an element holding a copy of the row's elements. §10.10:
// `pattern` may also be an unpacked array concatenation, each item of the
// element type one element and each array of that type its elements. What
// `q` held before, the queues of its elements with it, is gone. False, with
// `q` left alone, where its elements are no queues or `pattern` is none of
// these.
bool FillQueueOfQueues(QueueObject* q, const Expr* pattern, SimContext& ctx,
                       Arena& arena);

// §7.6 with §7.4 and §7.10 (printed pages 159, 153 and 169): `stmt`, whose
// target is the fixed-size array `dst` describes, as an assignment from one
// element of an array whose elements are queues, `row = q[0]` on `int
// q[$][3]` (ElementQueueOfSelect): the element's values are copied into the
// target from the left, and where their count differs from the target's size
// the assignment is the §7.6 error and writes nothing. False where the source
// is no such element.
bool TryCopyElementQueueToArray(const Stmt* stmt, const ArrayInfo& dst,
                                SimContext& ctx, Arena& arena);

}  // namespace delta
