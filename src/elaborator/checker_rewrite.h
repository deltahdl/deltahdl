#pragma once

#include <cstddef>
#include <string_view>
#include <unordered_map>

#include "parser/ast_module.h"

namespace delta {

struct FlattenedChecker {
  std::string_view name;
  std::size_t input_formal_count = 0;
  std::size_t output_formal_count = 0;
  int remaining_instances = 0;
  bool legal = false;
};

class CheckerRegistry {
 public:
  void Register(const ModuleDecl* decl);

  const ModuleDecl* Find(std::string_view name) const;

  static bool AlgorithmAppliesToFormal(const PortDecl& formal);

  std::size_t InputFormalCount(const ModuleDecl* decl) const;

  std::size_t OutputFormalCount(const ModuleDecl* decl) const;

  int CheckerInstanceCount(const ModuleDecl* decl) const;

  FlattenedChecker Flatten(std::string_view name,
                           std::size_t actual_input_arg_count) const;

  static bool IsAcceptableAsCheckerInstance(const FlattenedChecker& fc);

 private:
  std::unordered_map<std::string_view, const ModuleDecl*> by_name_;
};

}  // namespace delta
