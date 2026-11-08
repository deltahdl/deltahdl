#pragma once

#include <algorithm>
#include <cstddef>
#include <deque>
#include <functional>
#include <initializer_list>
#include <memory>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "elaborator/class_member_names.h"
#include "elaborator/local_type_sites.h"
#include "elaborator/struct_member_selects.h"
#include "elaborator/type_site_lookup.h"
#include "parser/ast_type.h"

namespace delta {

class DiagEngine;
struct ClassDecl;
struct CompilationUnit;
struct Expr;
struct ModuleItem;

struct DeclaredVar {
  const DataType* type = nullptr;
  std::size_t dims = 0;
  const TypeSite* site = nullptr;
};

struct DataScope {
  const std::function<bool(std::string_view)>& visible;
  const CompilationUnit& unit;
  const std::vector<ModuleItem*>& items;
  std::unordered_map<std::string_view, DeclaredVar> module_vars = {};
  std::unordered_map<std::string_view, DeclaredVar> properties = {};
  std::unordered_set<std::string_view> module = {};
  std::vector<std::pair<std::string_view, DeclaredVar>> blocks = {};
  std::unordered_set<std::string_view> uncallable = {};
  std::unordered_set<std::string_view> subroutines = {};
  std::deque<std::string> numbered_names = {};
  SiteKind site = SiteKind::kModule;
  std::unordered_set<std::string_view> local_types = {};
  std::shared_ptr<const SoleClassIndex> classes = nullptr;
  const ClassDecl* cls = nullptr;
  LocalTypeSites local_sites = {};

  TypeSite Site() const { return {&items, items.size(), site}; }

  TypeSite SiteOf(const DeclaredVar& var) const {
    return var.site != nullptr ? *var.site : Site();
  }

  bool Names(std::string_view name) const {
    return module.contains(name) ||
           std::ranges::any_of(blocks, [name](const auto& declared) {
             return declared.first == name;
           });
  }

  const DeclaredVar* Declared(std::string_view name) const {
    for (auto it = blocks.rbegin(); it != blocks.rend(); ++it) {
      if (it->first == name) return &it->second;
    }
    for (const auto* vars : {&properties, &module_vars}) {
      const auto kFound = vars->find(name);
      if (kFound != vars->end()) return &kFound->second;
    }
    return nullptr;
  }

  const DeclaredVar* Property(std::string_view name) const {
    const auto kFound = properties.find(name);
    return kFound == properties.end() ? nullptr : &kFound->second;
  }
};

inline constexpr std::string_view kStringMethods[] = {
    "len",      "putc",   "getc",   "toupper", "tolower", "compare",
    "icompare", "substr", "atoi",   "atohex",  "atooct",  "atobin",
    "atoreal",  "itoa",   "hextoa", "octtoa",  "bintoa",  "realtoa"};

const ClassDecl* ClassNamed(const DataScope& scope, const DeclaredVar& var,
                            std::size_t selects);

const Expr& SelectRoot(const Expr& e, std::size_t& selects);

const ClassDecl* HandleClass(const Expr& e, const DataScope& scope);

SitedType HeldPropertyType(const Expr& access, const DataScope& scope);

DataTypeKind AppliedValueKind(const Expr& value, const DataScope& scope);

void ReportNoBuiltInMethod(const Expr& access, const DataScope& scope,
                           DiagEngine& diag);

}  // namespace delta
