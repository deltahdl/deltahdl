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

enum class SiteKind : std::uint8_t { kModule, kUnit, kPackage };

struct TypeSite {
  const std::vector<ModuleItem*>* items = nullptr;
  std::size_t end = 0;
  SiteKind kind = SiteKind::kModule;
  const TypeSite* outer = nullptr;
};

struct FoundItem {
  const ModuleItem* item = nullptr;
  TypeSite site = {};
};

const ClassDecl* ClassIn(const CompilationUnit& unit, const TypeSite& site,
                         std::string_view name);

const ClassDecl* ScopedClass(const CompilationUnit& unit, const TypeSite& site,
                             std::string_view scope_name,
                             std::string_view name);

const ClassDecl* BaseClassIn(const CompilationUnit& unit, const TypeSite& site,
                             const ClassDecl& cls);

FoundItem TypedefOf(const CompilationUnit& unit, const TypeSite& site,
                    const DataType& type);

}  // namespace delta
