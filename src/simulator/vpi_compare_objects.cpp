#include <algorithm>
#include <cstdint>
#include <string_view>
#include <utility>

#include "simulator/class_object.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"
#include "simulator/vpi_collection_elements.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_expr_values.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"

namespace delta {

namespace {

// §38.3: the bits of one piece of the run's storage an object stands for --
// the storage, where its bits start above the storage's least significant end
// and how many there are, or all of it.
struct StorageSpan {
  const void* storage = nullptr;
  uint64_t offset = 0;
  uint64_t width = 0;
  bool whole = true;

  bool operator==(const StorageSpan&) const = default;
};

// The storage `obj` is read from, its variable's or, `by_net`, its net's.
const void* StorageKey(const VpiObject& obj, bool by_net) {
  if (by_net) return obj.net;
  return obj.var;
}

// §38.3 with §37.16 and §37.17: the bits of the run's storage `obj` stands
// for. A member of a structure or union holds a copy of its bits, so it stands
// for the bits at its offset in the variable it is a member of; a bit stands
// for its one bit of what its parent stands for; anything else for the whole
// of its own storage.
StorageSpan SpanOf(const VpiObject& obj, bool by_net) {
  const auto kWidth = static_cast<uint64_t>(std::max(obj.size, 1));
  if (obj.member_of != nullptr) {
    const StorageSpan kRoot = SpanOf(*obj.member_of, by_net);
    return {kRoot.storage, kRoot.offset + obj.member_offset, kWidth, false};
  }
  if (obj.bit_offset >= 0) {
    const VpiObject* parent = obj.parent;
    const StorageSpan kBase =
        parent != nullptr &&
                StorageKey(*parent, by_net) == StorageKey(obj, by_net)
            ? SpanOf(*parent, by_net)
            : StorageSpan{StorageKey(obj, by_net)};
    return {kBase.storage, kBase.offset + static_cast<uint64_t>(obj.bit_offset),
            kWidth, false};
  }
  return {StorageKey(obj, by_net)};
}

// Whether `a` and `b` stand for the same bits of one piece of storage, a
// variable's or a net's.
bool SameStorageBits(const VpiObject& a, const VpiObject& b) {
  for (const bool kByNet : {false, true}) {
    const StorageSpan kA = SpanOf(a, kByNet);
    if (kA.storage != nullptr && kA == SpanOf(b, kByNet)) return true;
  }
  return false;
}

// §37.61 detail 1: whether `obj` is a reference a class var prefixes, such as
// `c.a`.
bool IsClassMemberReference(const VpiObject& obj) {
  return obj.type == vpiRefObj && obj.prefix != nullptr &&
         obj.prefix->type == vpiClassVar;
}

// The name of the member a reference written `c.a` names: `a`.
std::string_view MemberName(const VpiObject& ref) {
  return ref.name.substr(ref.name.rfind('.') + 1);
}

// The class object the class var `class_var` holds now in the run `sim`, or
// null while it holds none.
ClassObject* ReferencedClassObject(VpiObject& class_var, SimContext* sim) {
  if (class_var.var == nullptr || sim == nullptr) return nullptr;
  VpiRefreshElementCopy(class_var);
  return sim->GetClassObject(class_var.var->value.ToUint64());
}

// §38.3 Example 3: a member of a class object, reached either through a
// reference its class var prefixes or as a property variable of the object,
// stands for the member of the object the handle holds at the time of the
// call; while the handle is null there is no member to stand for.
std::pair<ClassObject*, std::string_view> ClassMemberNow(VpiObject& obj,
                                                         SimContext* sim) {
  if (IsClassMemberReference(obj)) {
    return {ReferencedClassObject(*obj.prefix, sim), MemberName(obj)};
  }
  return {obj.property_of, obj.name};
}

}  // namespace

int VpiContext::CompareObjects(VpiHandle obj1, VpiHandle obj2) {
  // §38.3: a null handle names no object, so it can never refer to the same
  // object as anything.
  if (obj1 == nullptr || obj2 == nullptr) return 0;

  VpiObject* a = VpiResolveSameObject(obj1);
  VpiObject* b = VpiResolveSameObject(obj2);

  // §38.3: the comparison holds only while the simulation object exists. A
  // handle whose underlying object is absent (e.g. a class handle
  // that is still null) is never equal to anything, even to itself.
  if (!a->object_exists || !b->object_exists) return 0;

  // §38.3 Example 3: `c.a` and `d.a` are one object while `c` and `d` hold
  // one class object, and no object while either holds none.
  if (IsClassMemberReference(*a) || IsClassMemberReference(*b)) {
    const auto kMember = ClassMemberNow(*a, sim_ctx_);
    return kMember.first != nullptr && kMember == ClassMemberNow(*b, sim_ctx_)
               ? 1
               : 0;
  }

  // §38.3 Example 2: `i[j]` is the element of `i` that `j` names at the time
  // of the call, and no object while `j` names none.
  if (a->type == vpiVarSelect) a = VpiVarSelectElement(*a, sim_ctx_);
  if (b->type == vpiVarSelect) b = VpiVarSelectElement(*b, sim_ctx_);
  if (a == nullptr || b == nullptr) return 0;

  // §38.3: TRUE when both handles resolve to the same underlying object. The
  // representatives are compared, not the original handle pointers, so two
  // distinct handles that alias one object still compare equal - object
  // equivalence cannot be settled by a C "==" of the handles.
  if (a == b) return 1;

  // §38.3 asks whether the handles name one underlying simulation object, and
  // for a variable or a net that object is bits of the storage the run keeps
  // for it - which two objects of the model can name at once: a net and the
  // variable its resolution writes, and Example 1's bit of a packed structure
  // and the same bit of its member. Two bits of one vector, or a bit and its
  // vector, share the storage but not the bits, and are different objects.
  return SameStorageBits(*a, *b) ? 1 : 0;
}

}  // namespace delta
