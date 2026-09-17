#pragma once

#include <cstdint>
#include <string>
#include <string_view>

#include "common/types.h"
#include "simulator/class_object.h"

namespace delta {

struct Expr;
class SimContext;
class Arena;

// §7.4.2: a class property declared with one fixed unpacked dimension holds
// its elements one by one on the object, under the key this forms for each
// declared index, rather than one value under its own name. The key spells the
// element as a select of the property does, which is what lets a constraint
// name the element the way its relations are written (18.5.7): the solver's
// variable for the element and the local a trial binds it to carry this key.
std::string ClassArrayElementKey(std::string_view name, int64_t index);

// The array property named `name` on the class chain of `type`, or null where
// the chain declares none of that name or the property is no array.
const ClassTypeInfo::PropertyInfo* FindClassArrayProperty(
    const ClassTypeInfo* type, std::string_view name);

// The array property an expression addresses, and the object holding it.
// `bare` records that the expression named the property without a handle,
// from within the object's own scope, which is where a local variable of an
// element's key stands for the element: a constraint's trial binds each
// element so (18.5.7), and nothing outside the object's scope does.
struct ClassArrayRef {
  ClassObject* obj = nullptr;
  const ClassTypeInfo::PropertyInfo* prop = nullptr;
  bool bare = false;
};

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

// §7.12: `expr` as a call of size() or of one of §7.12.3's reduction methods
// sum, product, and, or and xor on an array property, read into `out`; false
// where the receiver names no array property, or the method is another or
// carries a with clause.
bool TryEvalClassArrayMethodCall(const Expr* expr, SimContext& ctx,
                                 Arena& arena, Logic4Vec& out);

// §7.4.6: `lhs` as a single-index select of an array property, written with
// `rhs_val` coerced as a write to the property is; false where its base names
// no array property. An index that addresses no element writes nothing.
bool TryWriteClassArrayElement(const Expr* lhs, const Logic4Vec& rhs_val,
                               SimContext& ctx, Arena& arena);

}  // namespace delta
