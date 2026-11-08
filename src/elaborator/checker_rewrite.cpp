#include "elaborator/checker_rewrite.h"

#include <cstddef>
#include <string_view>

#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

void CheckerRegistry::Register(const ModuleDecl* decl) {
  if (decl == nullptr) return;
  if (decl->decl_kind != ModuleDeclKind::kChecker) return;
  by_name_.emplace(decl->name, decl);
}

const ModuleDecl* CheckerRegistry::Find(std::string_view name) const {
  auto it = by_name_.find(name);
  if (it == by_name_.end()) return nullptr;
  return it->second;
}

bool CheckerRegistry::AlgorithmAppliesToFormal(const PortDecl& formal) {
  return formal.direction != Direction::kOutput;
}

std::size_t CheckerRegistry::InputFormalCount(const ModuleDecl* decl) const {
  if (decl == nullptr) return 0;
  std::size_t count = 0;
  for (const auto& formal : decl->ports) {
    if (AlgorithmAppliesToFormal(formal)) ++count;
  }
  return count;
}

std::size_t CheckerRegistry::OutputFormalCount(const ModuleDecl* decl) const {
  if (decl == nullptr) return 0;
  std::size_t count = 0;
  for (const auto& formal : decl->ports) {
    if (!AlgorithmAppliesToFormal(formal)) ++count;
  }
  return count;
}

int CheckerRegistry::CheckerInstanceCount(const ModuleDecl* decl) const {
  if (decl == nullptr) return 0;
  int count = 0;
  for (const auto* item : decl->items) {
    if (item == nullptr) continue;
    if (item->kind != ModuleItemKind::kModuleInst) continue;
    if (Find(item->inst_module) != nullptr) ++count;
  }
  return count;
}

FlattenedChecker CheckerRegistry::Flatten(
    std::string_view name, std::size_t actual_input_arg_count) const {
  FlattenedChecker fc;
  fc.name = name;
  const ModuleDecl* decl = Find(name);
  if (decl == nullptr) {
    fc.legal = false;
    return fc;
  }
  fc.input_formal_count = InputFormalCount(decl);
  fc.output_formal_count = OutputFormalCount(decl);
  fc.remaining_instances = 0;
  bool args_ok = actual_input_arg_count <= fc.input_formal_count;
  std::size_t input_index = 0;
  for (const auto& formal : decl->ports) {
    if (!AlgorithmAppliesToFormal(formal)) continue;
    if (input_index >= actual_input_arg_count &&
        formal.default_value == nullptr) {
      args_ok = false;
    }
    ++input_index;
  }
  fc.legal = args_ok;
  return fc;
}

bool CheckerRegistry::IsAcceptableAsCheckerInstance(
    const FlattenedChecker& fc) {
  return fc.legal && fc.remaining_instances == 0;
}

}  // namespace delta
