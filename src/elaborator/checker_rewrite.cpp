#include "elaborator/checker_rewrite.h"

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
  // §F.4.2: output-direction formals are treated differently (see §17.2) and
  // are outside the rewriting algorithm. Everything else is an input formal.
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
    // An instance is a checker instance only when its target names a
    // registered checker declaration.
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
    // §F.4.2: an unresolved source cannot be flattened, so it is not legal.
    fc.legal = false;
    return fc;
  }
  fc.input_formal_count = InputFormalCount(decl);
  fc.output_formal_count = OutputFormalCount(decl);
  // The flattened result is a checker without instances.
  fc.remaining_instances = 0;
  // §F.4.2: actuals are substituted for references to the formal input
  // arguments, so every input formal must be bound by an actual. Output
  // formals are not bound by the algorithm and are excluded from the count.
  // §F.4.2: a flattened checker that is not legal makes its source not legal.
  fc.legal = actual_input_arg_count == fc.input_formal_count;
  return fc;
}

bool CheckerRegistry::IsAcceptableAsCheckerInstance(
    const FlattenedChecker& fc) {
  // §F.4.2: nested and top-level checker instances are equally acceptable
  // targets of the algorithm once the flattened checker is legal and free of
  // remaining instances.
  return fc.legal && fc.remaining_instances == 0;
}

}  // namespace delta
