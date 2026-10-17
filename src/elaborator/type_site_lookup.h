#pragma once

#include <cstddef>
#include <cstdint>
#include <string_view>
#include <vector>

namespace delta {

struct ClassDecl;
struct CompilationUnit;
struct DataType;
struct ModuleItem;

// The kind of scope a type name is written in (§23.9): a module's, which the
// compilation unit's scope surrounds, the compilation unit's own, or a
// package's, which sees neither (§26.2).
enum class SiteKind : std::uint8_t { kModule, kUnit, kPackage };

// Where a type name is looked up: among the items of the scope it is written
// in, those before `end` alone, as a typedef names only a type declared before
// it (§6.18), then in the scopes around that one: for a scope within a
// module, a generate block (§27.5), a task, a function or a block (§23.9), the
// site of the scope around it, `outer`, and null for any other scope.
struct TypeSite {
  const std::vector<ModuleItem*>* items = nullptr;
  std::size_t end = 0;
  SiteKind kind = SiteKind::kModule;
  const TypeSite* outer = nullptr;
};

// An item a lookup found, with the site the names its declaration writes are
// looked up at: the items of its own scope before it.
struct FoundItem {
  const ModuleItem* item = nullptr;
  TypeSite site = {};
};

// §8.3: the class named `name` the scope of `site` sees, wherever in that scope
// its declaration stands, as a class may be referred to before it is declared
// once a forward typedef names it (§6.18); null where none is. A module's or
// the compilation unit's search reaches the compilation unit's classes.
const ClassDecl* ClassIn(const CompilationUnit& unit, const TypeSite& site,
                         std::string_view name);

// §8.24 with §26.3: the class named `name` written behind the scope
// `scope_name`, p::K or H::Inner: one the package of that name declares, else
// one nested in the class of that name the site sees; null where neither is.
const ClassDecl* ScopedClass(const CompilationUnit& unit, const TypeSite& site,
                             std::string_view scope_name,
                             std::string_view name);

// §6.18: the typedef the named type `type`, written at `site`, names: behind
// its package's scope, p::KT, or else the one the site sees.
FoundItem TypedefOf(const CompilationUnit& unit, const TypeSite& site,
                    const DataType& type);

}  // namespace delta
