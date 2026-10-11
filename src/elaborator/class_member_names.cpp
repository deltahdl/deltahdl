#include "elaborator/class_member_names.h"

#include <cstddef>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "elaborator/elaborator_helpers.h"
#include "parser/ast_class.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

// Adds to `names` each member, value parameter, type parameter and enumeration
// constant `cls` declares itself; false where an enumeration writes a range of
// constants (§6.19.2), whose names it does not write out.
bool AddOwnMemberNames(const ClassDecl& cls,
                       std::unordered_set<std::string_view>& names) {
  for (const auto& [name, value] : cls.params) names.insert(name);
  names.insert(cls.type_param_names.begin(), cls.type_param_names.end());
  for (const ClassMember* member : cls.members) {
    names.insert(member->name);
    const DataType& type = member->typedef_item != nullptr
                               ? member->typedef_item->typedef_type
                               : member->data_type;
    for (const EnumMember& constant : type.enum_members) {
      if (constant.range_start != nullptr) return false;
      names.insert(constant.name);
    }
  }
  return true;
}

}  // namespace

const ClassDecl* SoleClassIndex::Find(std::string_view name) const {
  if (!built_) {
    built_ = true;
    std::unordered_set<std::string_view> shared;
    for (const ClassDecl* cls : AllClassDecls(&unit_)) {
      if (!by_name_.emplace(cls->name, cls).second) shared.insert(cls->name);
    }
    for (const std::string_view kName : shared) by_name_.erase(kName);
  }
  const auto kFound = by_name_.find(name);
  return kFound == by_name_.end() ? nullptr : kFound->second;
}

bool SoleClassIndex::SelectableNames(
    const ClassDecl& cls, std::unordered_set<std::string_view>& names) const {
  // §18.6 randomize, pre_randomize and post_randomize, §18.8 rand_mode, §18.9
  // constraint_mode and §18.13 srandom, get_randstate and set_randstate.
  names.insert({"randomize", "pre_randomize", "post_randomize", "rand_mode",
                "constraint_mode", "srandom", "get_randstate",
                "set_randstate"});
  std::unordered_set<const ClassDecl*> seen;
  std::vector<const ClassDecl*> work{&cls};
  while (!work.empty()) {
    const ClassDecl* walked = work.back();
    work.pop_back();
    if (!seen.insert(walked).second) continue;
    if (!AddOwnMemberNames(*walked, names)) return false;
    std::vector<std::string_view> bases;
    if (!walked->base_class.empty()) bases.push_back(walked->base_class);
    for (const auto* refs :
         {&walked->extends_interfaces, &walked->implements_types}) {
      for (const InterfaceRef& ref : *refs) bases.push_back(ref.name);
    }
    for (const std::string_view kBase : bases) {
      const ClassDecl* base = Find(kBase);
      if (base == nullptr || walked->type_param_names.contains(kBase)) {
        return false;
      }
      work.push_back(base);
    }
  }
  return true;
}

void SoleClassIndex::AddLocalTypes(
    const ClassDecl& cls, std::unordered_set<std::string_view>& names) const {
  for (const ClassDecl* walked = &cls; walked != nullptr;
       walked = Find(walked->base_class)) {
    names.insert(walked->type_param_names.begin(),
                 walked->type_param_names.end());
    for (const ClassMember* member : walked->members) {
      if (member->kind == ClassMemberKind::kTypedef ||
          member->kind == ClassMemberKind::kClassDecl) {
        names.insert(member->name);
      }
    }
  }
}

const ClassDecl* SoleClassIndex::PropertyClass(const ClassDecl& cls,
                                               std::string_view name,
                                               std::size_t selects) const {
  for (const ClassDecl* walked = &cls; walked != nullptr;
       walked = Find(walked->base_class)) {
    for (const ClassMember* member : walked->members) {
      if (member->kind != ClassMemberKind::kProperty || member->name != name) {
        continue;
      }
      const DataType& type = member->data_type;
      std::unordered_set<std::string_view> local;
      AddLocalTypes(*walked, local);
      const bool kClassName = type.kind == DataTypeKind::kNamed &&
                              member->unpacked_dims.size() == selects &&
                              !local.contains(type.type_name);
      return kClassName ? Find(type.type_name) : nullptr;
    }
  }
  return nullptr;
}

}  // namespace delta
