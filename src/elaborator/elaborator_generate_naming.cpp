#include <cstdint>
#include <format>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_items_internal.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"

namespace delta {

static bool IsGenerateConstruct(ModuleItemKind k) {
  return k == ModuleItemKind::kGenerateIf ||
         k == ModuleItemKind::kGenerateFor ||
         k == ModuleItemKind::kGenerateCase;
}

static std::string_view GenerateBlockName(
    int64_t n, const std::unordered_set<std::string_view>& used, Arena& arena) {
  std::string digits = std::to_string(n);
  std::string candidate = "genblk" + digits;
  while (used.count(candidate)) {
    digits.insert(digits.begin(), '0');
    candidate = "genblk" + digits;
  }
  auto* buf = arena.AllocString(candidate.c_str(), candidate.size());
  return {buf, candidate.size()};
}

static void NameConstructBlocks(ModuleItem* it, std::string_view name,
                                Arena& arena);

static void NameGenerateBlocksInScope(const std::vector<ModuleItem*>& items,
                                      std::unordered_set<std::string_view> used,
                                      Arena& arena) {
  for (auto* it : items) {
    if (!it->name.empty()) used.insert(it->name);
  }

  int64_t n = 0;
  for (auto* it : items) {
    if (!IsGenerateConstruct(it->kind)) continue;
    ++n;
    std::string_view name = GenerateBlockName(n, used, arena);
    used.insert(name);
    NameConstructBlocks(it, name, arena);
  }
}

namespace {
struct GenerateBlockNameSlot {
  std::string_view& name;
  bool& is_generated;
};
}  // namespace

static void NameGenerateBlock(GenerateBlockNameSlot slot,
                              const std::vector<ModuleItem*>& body,
                              bool has_begin_end, std::string_view name,
                              Arena& arena) {
  if (slot.name.empty()) {
    slot.name = name;
    slot.is_generated = true;
  }
  if (IsDirectlyNestedBlock(body, has_begin_end)) {
    NameConstructBlocks(body[0], name, arena);
    return;
  }
  NameGenerateBlocksInScope(body, {}, arena);
}

static void NameConstructBlocks(ModuleItem* it, std::string_view name,
                                Arena& arena) {
  if (!IsConditionalGenerateConstruct(it->kind)) {
    if (it->name.empty()) {
      it->name = name;
      it->name_is_generated = true;
    }
    NameGenerateBlocksInScope(it->gen_body, {}, arena);
    return;
  }
  NameGenerateBlock({it->name, it->name_is_generated}, it->gen_body,
                    it->gen_body_has_begin_end, name, arena);
  for (auto& alt : it->gen_case_items) {
    NameGenerateBlock({alt.label, alt.name_is_generated}, alt.body,
                      alt.has_begin_end, name, arena);
  }
  if (it->gen_else == nullptr) return;
  if (it->gen_else->gen_cond != nullptr) {
    NameConstructBlocks(it->gen_else, name, arena);
    return;
  }
  NameGenerateBlock({it->gen_else->name, it->gen_else->name_is_generated},
                    it->gen_else->gen_body,
                    it->gen_else->gen_body_has_begin_end, name, arena);
}

static void NameModuleGenerateBlocks(const ModuleDecl* decl, Arena& arena) {
  std::unordered_set<std::string_view> used;
  for (const auto& port : decl->ports) used.insert(port.name);
  for (const auto& p : decl->params) used.insert(p.first);
  NameGenerateBlocksInScope(decl->items, std::move(used), arena);
}

void Elaborator::AssignGenerateBlockNames(const ModuleDecl* decl) {
  NameModuleGenerateBlocks(decl, arena_);
}

static void NameScopeTreeGenerateBlocks(const ModuleDecl* decl, Arena& arena) {
  NameModuleGenerateBlocks(decl, arena);
  for (const ModuleItem* item : decl->items) {
    if (item->nested_module_decl != nullptr) {
      NameScopeTreeGenerateBlocks(item->nested_module_decl, arena);
    }
  }
}

void AssignUnitGenerateBlockNames(const CompilationUnit* unit, Arena& arena) {
  for (const auto* scopes :
       {&unit->modules, &unit->interfaces, &unit->programs, &unit->checkers}) {
    for (const ModuleDecl* scope : *scopes) {
      NameScopeTreeGenerateBlocks(scope, arena);
    }
  }
}

static void CollectGenerateBlockNames(
    const ModuleItem* item, std::unordered_set<std::string_view>& out);

static void CollectDirectlyNestedBlockNames(
    const std::vector<ModuleItem*>& body, bool has_begin_end,
    std::unordered_set<std::string_view>& out) {
  if (IsDirectlyNestedBlock(body, has_begin_end)) {
    CollectGenerateBlockNames(body[0], out);
  }
}

static void CollectGenerateBlockNames(
    const ModuleItem* item, std::unordered_set<std::string_view>& out) {
  switch (item->kind) {
    case ModuleItemKind::kGenerateIf:
      if (!item->name.empty() && !item->name_is_generated)
        out.insert(item->name);
      CollectDirectlyNestedBlockNames(item->gen_body,
                                      item->gen_body_has_begin_end, out);
      if (item->gen_else) CollectGenerateBlockNames(item->gen_else, out);
      break;
    case ModuleItemKind::kGenerateCase:
      for (const auto& ci : item->gen_case_items) {
        if (!ci.label.empty() && !ci.name_is_generated) out.insert(ci.label);
        CollectDirectlyNestedBlockNames(ci.body, ci.has_begin_end, out);
      }
      break;
    case ModuleItemKind::kGenerateFor:
      if (!item->name.empty() && !item->name_is_generated)
        out.insert(item->name);
      break;
    default:
      break;
  }
}

static void CollectNonGenerateDeclNames(
    const std::vector<ModuleItem*>& items,
    std::unordered_set<std::string_view>& decl_names) {
  for (const auto* item : items) {
    if (IsGenerateConstruct(item->kind)) continue;
    if (!item->name.empty()) decl_names.insert(item->name);
    if (!item->inst_name.empty()) decl_names.insert(item->inst_name);
    if (!item->gate_inst_name.empty()) decl_names.insert(item->gate_inst_name);
  }
}

static std::unordered_map<std::string_view, int> CountGenerateConstructUses(
    const std::vector<ModuleItem*>& items) {
  std::unordered_map<std::string_view, int> construct_uses;
  for (const auto* item : items) {
    if (!IsGenerateConstruct(item->kind)) continue;
    std::unordered_set<std::string_view> names;
    CollectGenerateBlockNames(item, names);
    for (auto n : names) ++construct_uses[n];
  }
  return construct_uses;
}

static void ReportConditionalGenerateNameConflicts(
    DiagEngine& diag, const ModuleItem* item,
    const std::unordered_set<std::string_view>& decl_names,
    std::unordered_map<std::string_view, int>& construct_uses) {
  std::unordered_set<std::string_view> names;
  CollectGenerateBlockNames(item, names);
  for (auto n : names) {
    if (decl_names.count(n)) {
      diag.Error(item->loc,
                 std::format("generate block '{}' conflicts with another "
                             "declaration in the same scope",
                             n),
                 Subclause("27.5"));
    } else if (construct_uses[n] > 1) {
      diag.Error(item->loc,
                 std::format("generate block '{}' has the same name as a "
                             "generate block in another generate construct "
                             "in the same scope",
                             n),
                 Subclause("27.5"));
    }
  }
}

static void CheckConstructBlockScopes(DiagEngine& diag, const ModuleItem* item);

static void CheckGenerateNamingInScope(
    DiagEngine& diag, const std::vector<ModuleItem*>& items,
    std::unordered_set<std::string_view> decl_names) {
  CollectNonGenerateDeclNames(items, decl_names);
  std::unordered_map<std::string_view, int> construct_uses =
      CountGenerateConstructUses(items);
  for (const auto* item : items) {
    if (!IsGenerateConstruct(item->kind)) continue;
    if (IsConditionalGenerateConstruct(item->kind)) {
      ReportConditionalGenerateNameConflicts(diag, item, decl_names,
                                             construct_uses);
    }
    CheckConstructBlockScopes(diag, item);
  }
}

static void CheckBlockScope(DiagEngine& diag,
                            const std::vector<ModuleItem*>& body,
                            bool has_begin_end) {
  if (IsDirectlyNestedBlock(body, has_begin_end)) {
    CheckConstructBlockScopes(diag, body[0]);
    return;
  }
  CheckGenerateNamingInScope(diag, body, {});
}

static void CheckConstructBlockScopes(DiagEngine& diag,
                                      const ModuleItem* item) {
  if (!IsConditionalGenerateConstruct(item->kind)) {
    CheckGenerateNamingInScope(diag, item->gen_body, {});
    return;
  }
  CheckBlockScope(diag, item->gen_body, item->gen_body_has_begin_end);
  for (const auto& alt : item->gen_case_items) {
    CheckBlockScope(diag, alt.body, alt.has_begin_end);
  }
  if (item->gen_else != nullptr)
    CheckConstructBlockScopes(diag, item->gen_else);
}

static void CheckConditionalGenerateNaming(const ModuleDecl* decl,
                                           DiagEngine& diag) {
  std::unordered_set<std::string_view> decl_names;
  for (const auto& port : decl->ports)
    if (!port.name.empty()) decl_names.insert(port.name);
  for (const auto& p : decl->params)
    if (!p.first.empty()) decl_names.insert(p.first);
  CheckGenerateNamingInScope(diag, decl->items, std::move(decl_names));
}

void Elaborator::CheckGenerateConstructs(const ModuleDecl* decl) {
  CheckConditionalGenerateNaming(decl, diag_);
  ReportUndeclaredLoopGenvars(decl, diag_);
}

}  // namespace delta
