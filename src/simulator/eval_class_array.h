#pragma once

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/types.h"
#include "simulator/class_object.h"

namespace delta {

struct Expr;
struct Stmt;
class SimContext;
class Arena;

// §7.4.2: a class property declared with one fixed unpacked dimension holds
// its elements one by one on the object, under the key this forms for each
// declared index, rather than one value under its own name. The key spells the
// element as a select of the property does, which is what lets a constraint
// name the element the way its relations are written (18.5.7): the solver's
// variable for the element and the local a trial binds it to carry this key.
std::string ClassArrayElementKey(std::string_view name, int64_t index);

// §7.5: a class property declared with a dynamic dimension holds its element
// count on the object under the key this forms, spelled as the size method
// of the property is written in a constraint, which is what lets a
// randomize() that constrains the size solve it as a variable of that name
// and a foreach read it as the state variable it is there (18.5.7.1).
std::string ClassArraySizeKey(std::string_view name);

// The array property named `name` on the class chain of `type`, or null where
// the chain declares none of that name or the property is no array.
const ClassTypeInfo::PropertyInfo* FindClassArrayProperty(
    const ClassTypeInfo* type, std::string_view name);

// The array property an expression addresses, the object holding it, and
// the elements it holds: `size` of them from the index `lo` up, the
// declared dimension's for a fixed array and the object's count from 0 for a
// dynamic one. `bare` records that the expression named the property without
// a handle, from within the object's own scope, which is where a local
// variable of an element's key stands for the element: a constraint's trial
// binds each element so (18.5.7), and nothing outside the object's scope
// does.
struct ClassArrayRef {
  ClassObject* obj = nullptr;
  const ClassTypeInfo::PropertyInfo* prop = nullptr;
  bool bare = false;
  uint32_t size = 0;
  int64_t lo = 0;
};

// §7.5: the element count a dynamic array property holds on `obj`, 0 where
// none has been set.
uint32_t ClassArraySize(const ClassObject* obj,
                        const ClassTypeInfo::PropertyInfo& prop);

// §7.5.1: resizes the dynamic array `ref` to `size` elements, each taking the
// element type's default, or, where `init` addresses an array, the value of
// the element of the same index it holds, for the indexes it holds one.
void ResizeClassArray(const ClassArrayRef& ref, uint32_t size,
                      const ClassArrayRef* init, SimContext& ctx, Arena& arena);

// §8.11/§7.4.2: the array property `base` names -- an unqualified name read
// against the running method's object where no variable or array of the name
// is in scope, or a member access on `this` or on a live handle -- filling
// `out` and answering true; false where `base` names no array property.
bool ResolveClassArray(const Expr* base, SimContext& ctx, Arena& arena,
                       ClassArrayRef& out);

// §7.4.6: the value of the element at declared index `index`: the local of
// its key where the reference is bare and one is in scope, else the object's
// element, and the element type's x or 0 where the index addresses none.
Logic4Vec ReadClassArrayElement(const ClassArrayRef& ref, int64_t index,
                                SimContext& ctx, Arena& arena);

// §7.4.6: `expr` as a single-index select of an array property, read into
// `out`; false where its base names no array property.
bool TryClassArrayElementSelect(const Expr* expr, int64_t index,
                                SimContext& ctx, Arena& arena, Logic4Vec& out);

// §7.12/§7.5.3: `expr` as a call of size() or of one of §7.12.3's reduction
// methods sum, product, and, or and xor on an array property, read into
// `out`, or of delete() on a dynamic one, which empties it; false where the
// receiver names no array property, or the method is another or carries a
// with clause.
bool TryEvalClassArrayMethodCall(const Expr* expr, SimContext& ctx,
                                 Arena& arena, Logic4Vec& out);

// §7.5.1: `stmt` as an assignment of `new[size]` or `new[size](init)` to a
// dynamic array property, resized as ResizeClassArray does; false where its
// target names no dynamic array property or its value is no `new[]`.
bool TryClassArrayNewAssign(const Stmt* stmt, SimContext& ctx, Arena& arena);

// §7.6: the elements of the array property `src` names -- a fixed or dynamic
// one, or a queue, bare in a method or through a handle -- from the left,
// into `out`; a declared queue a bare name answers is read too. False for any
// other expression.
bool PropertyArrayElements(const Expr* src, SimContext& ctx, Arena& arena,
                           std::vector<Logic4Vec>& out);

// §7.6 with §7.5, §7.10 and §8.5: `stmt` as an assignment of one array
// property to another -- fixed, dynamic or queue, through handles or bare in
// a method: `g.arr = h.arr`, `b.d = a.q`, `a.q = b.d` -- which copies the
// source's elements from the left into the target, a dynamic target or a
// queue taking the source's size. False where either side names no array
// property, a declared queue on the left among them.
bool TryClassArrayWholeAssign(const Stmt* stmt, SimContext& ctx, Arena& arena);

// §8.11 with §23.9: whether `base` is a bare name a method's own array
// property answers -- the running object's class declares a fixed-size or
// dynamic array property of the name and no local of the method shadows it --
// which a variable of the module the class is declared in does not shadow.
bool NamesOwnArrayProperty(const Expr* base, SimContext& ctx);

// §7.4.6: writes the element at declared index `index` of `ref` with `value`
// coerced as a write to the property is; an index that addresses no element
// writes nothing.
void StoreClassArrayElement(const ClassArrayRef& ref, int64_t index,
                            const Logic4Vec& value, SimContext& ctx,
                            Arena& arena);

// §7.4.6: `lhs` as a single-index select of an array property, written with
// `rhs_val` coerced as a write to the property is; false where its base names
// no array property. An index that addresses no element writes nothing.
bool TryWriteClassArrayElement(const Expr* lhs, const Logic4Vec& rhs_val,
                               SimContext& ctx, Arena& arena);

}  // namespace delta
