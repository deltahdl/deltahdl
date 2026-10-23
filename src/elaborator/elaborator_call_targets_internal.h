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
#include "elaborator/type_site_lookup.h"
#include "parser/ast_type.h"

// What elaborator_call_targets.cpp, which judges the calls and member accesses
// the procedures of a module or a class write, shares with
// elaborator_applied_values.cpp, which says what value such a member access is
// applied to: the scope a walk of the procedures sees, and the lookups both
// make of it.

namespace delta {

class DiagEngine;
struct ClassDecl;
struct CompilationUnit;
struct Expr;
struct ModuleItem;

// A variable's declaration: the type it was declared with, the number of
// unpacked dimensions it writes after its name (§7.4), and, for one a scope
// within the module declares, the site of that scope, whose typedefs its type
// names first (LocalTypeSites); null for one the module declares.
struct DeclaredVar {
  const DataType* type = nullptr;
  std::size_t dims = 0;
  const TypeSite* site = nullptr;
};

// The names a walk of one module's procedures sees as variables or nets: the
// module's own, and those each block around the statement walked declares,
// the innermost last (§23.9); the other names the module itself declares, or
// imports as data, which a call statement cannot call; the tasks and
// functions the module declares; and, first, whether the scope or a module
// enclosing it sees a name at all.
struct DataScope {
  const std::function<bool(std::string_view)>& visible;
  const CompilationUnit& unit;
  const std::vector<ModuleItem*>& items;
  // The declaration of each variable of the module and of a block around the
  // statement walked.
  std::unordered_map<std::string_view, DeclaredVar> module_vars = {};
  // In a method of a class, the declaration of each property the class
  // declares or inherits (§8.13), which hides a variable of the scope around
  // the class of its name and is what `this` reaches (§8.11).
  std::unordered_map<std::string_view, DeclaredVar> properties = {};
  std::unordered_set<std::string_view> module = {};
  std::vector<std::pair<std::string_view, DeclaredVar>> blocks = {};
  std::unordered_set<std::string_view> uncallable = {};
  std::unordered_set<std::string_view> subroutines = {};
  // The numbered constants of the scope's ranged enumeration members (§6.19.2),
  // which no source text spells for `module_vars` to key them by.
  std::deque<std::string> numbered_names = {};
  // The kind of scope `items` belong to, which the types of the scope's
  // variables are looked up from.
  SiteKind site = SiteKind::kModule;
  // The names a type of the scope may be written as without naming a class of
  // the scope around it: a type parameter of the module, and in a method a
  // type parameter, typedef or nested class of its class or a class it
  // extends.
  std::unordered_set<std::string_view> local_types = {};
  // The classes of the unit known by their name alone, shared by every scope
  // copied from the one that made them.
  std::shared_ptr<const SoleClassIndex> classes = nullptr;
  // In a method of a class, the class, whose methods a call by a name alone
  // calls first (§8.13).
  const ClassDecl* cls = nullptr;
  // The sites of the scopes within the module around the item walked.
  LocalTypeSites local_sites = {};

  // The site of the scope `items` belong to, seeing each of them.
  TypeSite Site() const { return {&items, items.size(), site}; }

  // The site of the scope declaring the variable `var`, whose typedefs its
  // type names first (§23.9).
  TypeSite SiteOf(const DeclaredVar& var) const {
    return var.site != nullptr ? *var.site : Site();
  }

  bool Names(std::string_view name) const {
    return module.contains(name) ||
           std::ranges::any_of(blocks, [name](const auto& declared) {
             return declared.first == name;
           });
  }

  // The declaration of the variable `name` names in the scope, the innermost
  // block's first, then a property of the class a method's scope is in, then
  // the module's (§23.9); null for a name no variable bears.
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

  // §8.11: the declaration of the property `name` names through `this`; null
  // for a name no property of the class bears, and outside a method.
  const DeclaredVar* Property(std::string_view name) const {
    const auto kFound = properties.find(name);
    return kFound == properties.end() ? nullptr : &kFound->second;
  }
};

// §6.16: the built-in methods of a string.
inline constexpr std::string_view kStringMethods[] = {
    "len",      "putc",   "getc",   "toupper", "tolower", "compare",
    "icompare", "substr", "atoi",   "atohex",  "atooct",  "atobin",
    "atoreal",  "itoa",   "hextoa", "octtoa",  "bintoa",  "realtoa"};

// §8.3 with §7.4: the class declaration whose handle the element of the
// variable `var` that `selects` selects reach holds, through the typedefs its
// type is written as, their unpacked dimensions counted with the variable's
// own (§6.18); null where none is, and where the selects reach no element.
const ClassDecl* ClassNamed(const DataScope& scope, const DeclaredVar& var,
                            std::size_t selects);

// The expression the selects in front of `e` select from, the number of them
// counted into `selects`: `va` of va[0][1], two.
const Expr& SelectRoot(const Expr& e, std::size_t& selects);

// §8.4: the class whose handle `e` holds, where the scope tells it for
// certain: a variable of the scope, or an element of one, one select per
// unpacked dimension (§7.4), whose type names a class, or a property of such a
// class (§8.5), h.p or h.p[0]; null for anything else.
const ClassDecl* HandleClass(const Expr& e, const DataScope& scope);

// The kind of the type of the value `value` stands for, written with no select
// in front of a member access, as far as the scope tells it for certain: a
// variable of the scope, the result of a call or of a system function, or a
// property of the class a handle holds; kImplicit for anything else.
DataTypeKind AppliedValueKind(const Expr& value, const DataScope& scope);

// §6.16 and §6.19.5: a member access `access`, s.m or e.m, applied to a string
// or an enumeration (AppliedValueKind), naming none of its type's built-in
// methods, and
// §23.7 a): one applied to an integral or real value, which has none. A random
// property of a class, but a string, also has rand_mode (§18.8).
void ReportNoBuiltInMethod(const Expr& access, const DataScope& scope,
                           DiagEngine& diag);

}  // namespace delta
