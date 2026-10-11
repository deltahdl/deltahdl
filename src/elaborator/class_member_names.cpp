#include "elaborator/class_member_names.h"

#include <cstddef>
#include <initializer_list>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "elaborator/const_eval.h"
#include "elaborator/elaborator_enum_constants.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/type_site_lookup.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

// Adds to `names` each member, value parameter, type parameter and enumeration
// constant `cls` declares itself. A range of constants, S[2] or T[3:4],
// declares the names it generates, S0 and S1 or T3 and T4 (§6.19.2), which
// `generated` owns; its bounds are integral numbers, which fold in any scope.
void AddOwnMemberNames(const ClassDecl& cls,
                       std::unordered_set<std::string_view>& names,
                       std::unordered_set<std::string>& generated) {
  const ScopeMap kNoScope;
  for (const auto& [name, value] : cls.params) names.insert(name);
  names.insert(cls.type_param_names.begin(), cls.type_param_names.end());
  for (const ClassMember* member : cls.members) {
    names.insert(member->name);
    const DataType& type = member->typedef_item != nullptr
                               ? member->typedef_item->typedef_type
                               : member->data_type;
    for (const EnumMember& constant : type.enum_members) {
      for (std::string& name : EnumMemberDeclaredNames(constant, kNoScope)) {
        names.insert(*generated.insert(std::move(name)).first);
      }
    }
  }
}

// The names of the classes `cls` extends or implements.
std::vector<std::string_view> BaseNames(const ClassDecl& cls) {
  std::vector<std::string_view> bases;
  if (!cls.base_class.empty()) bases.push_back(cls.base_class);
  for (const auto* refs : {&cls.extends_interfaces, &cls.implements_types}) {
    for (const InterfaceRef& ref : *refs) bases.push_back(ref.name);
  }
  return bases;
}

}  // namespace

void SoleClassIndex::Build() const {
  if (built_) return;
  built_ = true;
  std::unordered_set<std::string_view> shared;
  for (const ClassDecl* cls : AllClassDecls(&unit_)) {
    if (!by_name_.emplace(cls->name, cls).second) shared.insert(cls->name);
  }
  for (const std::string_view kName : shared) by_name_.erase(kName);
  const TypeSite kUnit{&unit_.cu_items, unit_.cu_items.size(), SiteKind::kUnit};
  for (const ClassDecl* cls : unit_.classes) sites_.emplace(cls, kUnit);
  for (const auto* group :
       {&unit_.modules, &unit_.interfaces, &unit_.programs, &unit_.checkers}) {
    for (const ModuleDecl* decl : *group) {
      AddSites(decl->items, SiteKind::kModule);
    }
  }
  for (const PackageDecl* package : unit_.packages) {
    AddSites(package->items, SiteKind::kPackage);
  }
}

void SoleClassIndex::AddSites(const std::vector<ModuleItem*>& items,
                              SiteKind kind) const {
  for (const ModuleItem* item : items) {
    if (item->kind == ModuleItemKind::kClassDecl) {
      sites_.emplace(item->class_decl, TypeSite{&items, items.size(), kind});
    }
  }
}

const ClassDecl* SoleClassIndex::Find(std::string_view name) const {
  Build();
  const auto kFound = by_name_.find(name);
  return kFound == by_name_.end() ? nullptr : kFound->second;
}

const ClassDecl* SoleClassIndex::FindFrom(const ClassDecl& from,
                                          std::string_view name) const {
  Build();
  const auto kSite = sites_.find(&from);
  const ClassDecl* seen =
      kSite == sites_.end() ? nullptr : ClassIn(unit_, kSite->second, name);
  return seen != nullptr ? seen : Find(name);
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
    AddOwnMemberNames(*walked, names, generated_);
    for (const std::string_view kBase : BaseNames(*walked)) {
      const ClassDecl* base = FindFrom(*walked, kBase);
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
       walked = FindFrom(*walked, walked->base_class)) {
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
       walked = FindFrom(*walked, walked->base_class)) {
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
      return kClassName ? FindFrom(*walked, type.type_name) : nullptr;
    }
  }
  return nullptr;
}

}  // namespace delta
