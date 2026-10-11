#pragma once

#include <cstddef>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "elaborator/type_site_lookup.h"

namespace delta {

struct ClassDecl;
struct CompilationUnit;
struct ModuleItem;

// The classes of a compilation unit known by their name alone: each name the
// unit declares exactly one class under, wherever the class is declared, in
// the compilation unit, a package, a module, an interface, a program or a
// checker, or nested in another class (§8.23). A name two classes share, a
// type parameter and a class of the std package are none of them, so whatever
// is asked of a class through one is left unanswered rather than answered for
// the wrong class. The index is built on the first question asked of it.
class SoleClassIndex {
 public:
  explicit SoleClassIndex(const CompilationUnit& unit) : unit_(unit) {}

  // The one class the unit declares under `name`; null where none or several
  // do.
  const ClassDecl* Find(std::string_view name) const;

  // §8.5 and §8.6: adds to `names` each name a member access applied to a
  // handle of `cls` may name: a member, value parameter or enumeration
  // constant `cls` or a class it extends or implements declares (§8.13,
  // §8.26), its types among them, whose access §8.5 forbids by a rule of its
  // own, and the methods §18 gives every object. False where the names are not
  // known in full: a class of the chain extends or implements one FindFrom
  // does not give.
  bool SelectableNames(const ClassDecl& cls,
                       std::unordered_set<std::string_view>& names) const;

  // Adds to `names` each name `cls` or a class it extends declares as a type
  // parameter, a typedef or a nested class: a type written inside the class
  // by one of them names no class of the scope around it.
  void AddLocalTypes(const ClassDecl& cls,
                     std::unordered_set<std::string_view>& names) const;

  // §8.5: the class a handle the property `name` of `cls`, or of the nearest
  // class it extends declaring one by that name, holds, where the property
  // writes `selects` unpacked dimensions (§7.4) and its type is a name
  // FindFrom gives a class for, not a type the class declares itself; null for
  // anything else.
  const ClassDecl* PropertyClass(const ClassDecl& cls, std::string_view name,
                                 std::size_t selects) const;

 private:
  // Fills by_name_ and sites_ on the first question asked.
  void Build() const;

  // Records the site of each class declared directly among `items`, a scope
  // of kind `kind`.
  void AddSites(const std::vector<ModuleItem*>& items, SiteKind kind) const;

  // The class the name `name` that the class `from` writes names: the one the
  // scope declaring `from` sees (§3.13, §26.3), else the one Find gives,
  // which answers too for a class standing in a generate block or in another
  // class, whose scope is not recorded.
  const ClassDecl* FindFrom(const ClassDecl& from, std::string_view name) const;

  const CompilationUnit& unit_;
  mutable bool built_ = false;
  mutable std::unordered_map<std::string_view, const ClassDecl*> by_name_;
  // The site of each class a module, interface, program, checker, package or
  // the compilation unit declares directly.
  mutable std::unordered_map<const ClassDecl*, TypeSite> sites_;
  // The names of the enumeration constants the classes declare, those a range
  // generates (§6.19.2) among them, which no source text holds.
  mutable std::unordered_set<std::string> generated_;
};

}  // namespace delta
