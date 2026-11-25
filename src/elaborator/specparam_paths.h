#pragma once

#include <span>
#include <string_view>
#include <unordered_set>
#include <vector>

namespace delta {

struct BindDirective;
struct CompilationUnit;
struct Expr;
struct ModuleDecl;
struct ModuleItem;

using InstancePath = std::vector<std::string_view>;
using InstancePathView = std::span<const std::string_view>;

InstancePath InstancePathOf(const Expr& name);

class SpecparamPaths {
 public:
  explicit SpecparamPaths(const CompilationUnit& unit) : unit_(unit) {}

  bool EndsAtSpecparam(const InstancePath& path, const ModuleDecl* from) const;

 private:
  const ModuleDecl* ModuleAt(const std::vector<ModuleItem*>& items,
                             InstancePathView path) const;

  const ModuleDecl* ModuleThrough(const ModuleItem& item,
                                  InstancePathView path) const;

  const ModuleDecl* BoundModule(const BindDirective& bind) const;

  bool ReachesIn(const std::vector<ModuleItem*>& items,
                 const InstancePath& path) const;

  bool ReachesUpward(const ModuleDecl& from, const InstancePath& path,
                     std::unordered_set<const ModuleDecl*>& seen) const;

  std::vector<const ModuleDecl*> Instantiators(std::string_view name) const;

  const CompilationUnit& unit_;
};

}  // namespace delta
