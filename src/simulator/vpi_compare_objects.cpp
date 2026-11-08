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
#include "simulator/vpi_user.h"

namespace delta {

namespace {

struct StorageSpan {
  const void* storage = nullptr;
  uint64_t offset = 0;
  uint64_t width = 0;
  bool whole = true;

  bool operator==(const StorageSpan&) const = default;
};

const void* StorageKey(const VpiObject& obj, bool by_net) {
  if (by_net) return obj.net;
  return obj.var;
}

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

bool SameStorageBits(const VpiObject& a, const VpiObject& b) {
  for (const bool kByNet : {false, true}) {
    const StorageSpan kA = SpanOf(a, kByNet);
    if (kA.storage != nullptr && kA == SpanOf(b, kByNet)) return true;
  }
  return false;
}

bool IsClassMemberReference(const VpiObject& obj) {
  return obj.type == vpiRefObj && obj.prefix != nullptr &&
         obj.prefix->type == vpiClassVar;
}

std::string_view MemberName(const VpiObject& ref) {
  return ref.name.substr(ref.name.rfind('.') + 1);
}

ClassObject* ReferencedClassObject(VpiObject& class_var, SimContext* sim) {
  if (class_var.var == nullptr || sim == nullptr) return nullptr;
  VpiRefreshElementCopy(class_var);
  return sim->GetClassObject(class_var.var->value.ToUint64());
}

std::pair<ClassObject*, std::string_view> ClassMemberNow(VpiObject& obj,
                                                         SimContext* sim) {
  if (IsClassMemberReference(obj)) {
    return {ReferencedClassObject(*obj.prefix, sim), MemberName(obj)};
  }
  return {obj.property_of, obj.name};
}

}  // namespace

int VpiContext::CompareObjects(VpiHandle obj1, VpiHandle obj2) {
  if (obj1 == nullptr || obj2 == nullptr) return 0;

  VpiObject* a = VpiResolveSameObject(obj1);
  VpiObject* b = VpiResolveSameObject(obj2);

  if (!a->object_exists || !b->object_exists) return 0;

  if (IsClassMemberReference(*a) || IsClassMemberReference(*b)) {
    const auto kMember = ClassMemberNow(*a, sim_ctx_);
    return kMember.first != nullptr && kMember == ClassMemberNow(*b, sim_ctx_)
               ? 1
               : 0;
  }

  if (a->type == vpiVarSelect) a = VpiVarSelectElement(*a, sim_ctx_);
  if (b->type == vpiVarSelect) b = VpiVarSelectElement(*b, sim_ctx_);
  if (a == nullptr || b == nullptr) return 0;

  if (a == b) return 1;

  return SameStorageBits(*a, *b) ? 1 : 0;
}

}  // namespace delta
