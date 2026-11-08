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

class SoleClassIndex {
 public:
  explicit SoleClassIndex(const CompilationUnit& unit) : unit_(unit) {}

  const ClassDecl* Find(std::string_view name) const;

  bool SelectableNames(const ClassDecl& cls,
                       std::unordered_set<std::string_view>& names) const;

  void AddLocalTypes(const ClassDecl& cls,
                     std::unordered_set<std::string_view>& names) const;

  const ClassDecl* PropertyClass(const ClassDecl& cls, std::string_view name,
                                 std::size_t selects) const;

 private:
  void Build() const;

  void AddSites(const std::vector<ModuleItem*>& items, SiteKind kind) const;

  const ClassDecl* FindFrom(const ClassDecl& from, std::string_view name) const;

  const ClassDecl* FindFrom(const ClassDecl& from, std::string_view scope,
                            std::string_view name) const;

  const CompilationUnit& unit_;
  mutable bool built_ = false;
  mutable std::unordered_map<std::string_view, const ClassDecl*> by_name_;
  mutable std::unordered_map<const ClassDecl*, TypeSite> sites_;
  mutable std::unordered_set<std::string> generated_;
};

}  // namespace delta
