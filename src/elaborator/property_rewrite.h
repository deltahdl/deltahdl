#pragma once

#include <cstddef>
#include <optional>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "elaborator/sampled_value.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"

namespace delta {

bool DisableConditionSampledValueRequiresExplicitClock(SampledValueFunction fn);

bool DisableConditionSampledValueClockIsWellFormed(
    SampledValueFunction fn, bool clock_explicitly_specified);

struct FlattenedProperty {
  std::string_view name;
  std::size_t formal_count = 0;
  int disable_iff_count = 0;
  bool legal = false;
  int remaining_instances = 0;
};

class PropertyRegistry {
 public:
  void Register(const ModuleItem* decl);

  void RegisterAs(std::string_view name, const ModuleItem* decl);

  void RegisterShadowing(const ModuleItem* decl);

  const ModuleItem* Find(std::string_view name) const;

  std::vector<std::string_view> DependencyRefs(const ModuleItem* decl) const;

  const ModuleItem* FindInstance(const Expr* instance) const;

  int FlattenedDisableIffCount(const ModuleItem* decl) const;

  FlattenedProperty Flatten(std::string_view name,
                            std::size_t actual_arg_count) const;

  static bool IsAcceptableAsTopLevelConcurrent(const FlattenedProperty& fp);

  bool HasCyclicSequenceDependency(const ModuleItem* decl) const;

  bool IsRecursiveProperty(const ModuleItem* decl) const;

  bool ReachesRecursiveProperty(const ModuleItem* decl) const;

  bool IsOnZeroWeightCycle(const ModuleItem* decl) const;

 private:
  std::unordered_map<std::string_view, const ModuleItem*> by_name_;
  std::unordered_map<std::string_view, std::vector<std::string_view>>
      argument_refs_;

  void RecordArgumentRefs(const ModuleItem* decl);
};

class BlockDeclarationShadow {
 public:
  BlockDeclarationShadow(PropertyRegistry* registry,
                         const std::vector<ModuleItem*>& items);
  ~BlockDeclarationShadow();
  BlockDeclarationShadow(const BlockDeclarationShadow&) = delete;
  BlockDeclarationShadow& operator=(const BlockDeclarationShadow&) = delete;

 private:
  PropertyRegistry* registry_;
  std::optional<PropertyRegistry> enclosing_;
};

}  // namespace delta
