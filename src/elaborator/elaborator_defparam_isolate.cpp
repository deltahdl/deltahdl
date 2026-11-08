#include <algorithm>
#include <cstddef>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "elaborator/elaborator_data.h"
#include "elaborator/pending_generate.h"
#include "elaborator/rtlir.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"

namespace delta {

RtlirModule* ElaboratorData::CopyModuleTree(
    RtlirModule* mod, Arena& arena,
    std::unordered_map<const RtlirModule*, RtlirModule*>& copies) {
  if (mod == nullptr) return nullptr;
  auto found = copies.find(mod);
  if (found != copies.end()) return found->second;
  auto* copy = arena.Create<RtlirModule>(*mod);
  copies[mod] = copy;
  for (auto& child : copy->children) {
    child.resolved = CopyModuleTree(child.resolved, arena, copies);
  }
  auto own = generate_defparams_.find(mod);
  if (own != generate_defparams_.end()) {
    std::vector<DefparamSite> copied = own->second;
    generate_defparams_[copy] = std::move(copied);
  }
  const std::size_t kQueued = pending_generates_.size();
  for (std::size_t i = 0; i < kQueued; ++i) {
    if (pending_generates_[i].mod != mod) continue;
    PendingGenerate queued = pending_generates_[i];
    queued.mod = copy;
    pending_generates_.push_back(std::move(queued));
  }
  return copy;
}

void ElaboratorData::IsolateArrayElement(const RtlirModule& parent,
                                         RtlirModuleInst& elem, Arena& arena) {
  if (elem.resolved == nullptr || elem.array.name.empty()) return;
  bool shared = false;
  for (const auto& sibling : parent.children) {
    if (&sibling != &elem && sibling.resolved == elem.resolved) shared = true;
  }
  if (!shared) return;
  std::unordered_map<const RtlirModule*, RtlirModule*> copies;
  elem.resolved = CopyModuleTree(elem.resolved, arena, copies);
}

void ElaboratorData::IsolateArrayElements(RtlirModule& mod, Arena& arena,
                                          const CompilationUnit& unit) {
  if (!WritesDefparams(unit)) return;
  for (auto& child : mod.children) IsolateArrayElement(mod, child, arena);
}

static bool DeclaresDefparam(const ModuleDecl& decl) {
  return std::any_of(decl.items.begin(), decl.items.end(),
                     [](const ModuleItem* item) {
                       return item->kind == ModuleItemKind::kDefparam;
                     });
}

bool ElaboratorData::WritesDefparams(const CompilationUnit& unit) {
  if (!generate_defparams_.empty()) return true;
  if (!declares_defparams_) {
    declares_defparams_ = false;
    for (const auto* decls :
         {&unit.modules, &unit.interfaces, &unit.programs}) {
      if (std::any_of(decls->begin(), decls->end(),
                      [](const ModuleDecl* d) { return DeclaresDefparam(*d); }))
        declares_defparams_ = true;
    }
  }
  return *declares_defparams_;
}

}  // namespace delta
