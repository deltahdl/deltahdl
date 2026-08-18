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
#include "parser/ast.h"

namespace delta {

static bool IsGenerateConstruct(ModuleItemKind k) {
  return k == ModuleItemKind::kGenerateIf ||
         k == ModuleItemKind::kGenerateFor ||
         k == ModuleItemKind::kGenerateCase;
}

// §27.6: "All unnamed generate blocks will be given the name genblk<n> where
// <n> is the number assigned to its enclosing generate construct. If such a
// name would conflict with an explicitly declared name, then leading zeros are
// added in front of the number until the name does not conflict."
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

// Declared here because NameConstructBlocks and NameGenerateBlocksInScope call
// each other: a scope numbers the constructs it holds, and a construct's blocks
// are each a scope in their own right.
static void NameConstructBlocks(ModuleItem* it, std::string_view name,
                                Arena& arena);

// §27.6: "Each generate construct in a given scope is assigned a number. The
// number will be 1 for the construct that appears textually first in that
// scope and will increase by 1 for each subsequent generate construct in that
// scope." A construct that carries a name still takes a number, which is why
// the standard's own example names the construct written after `begin : g1`
// genblk4 rather than genblk3.
//
// The count restarts in each scope, so this recurses into the body of every
// construct it numbers. §27.4 rules that a generate block "comprises a
// separate scope and a new level of hierarchy when it is instantiated", and
// §27.6 writes the first nested construct of a block named g1 as
// top.g1[0].genblk1. Each alternative of a conditional construct is walked on
// its own, since only one of them is ever instantiated.
static void NameGenerateBlocksInScope(const std::vector<ModuleItem*>& items,
                                      std::unordered_set<std::string_view> used,
                                      Arena& arena) {
  for (auto* it : items) {
    if (!it->name.empty()) used.insert(it->name);
  }

  // The §27.6 name is computed for every construct and not only for the unnamed
  // ones, because one construct has more than one block and each of them needs
  // the name independently: a named then-block must not stop the unnamed else
  // block beside it from taking the construct's number.
  int64_t n = 0;
  for (auto* it : items) {
    if (!IsGenerateConstruct(it->kind)) continue;
    ++n;
    std::string_view name = GenerateBlockName(n, used, arena);
    used.insert(name);
    NameConstructBlocks(it, name, arena);
  }
}

// Where one generate block's name is written, and where the fact that §27.6
// assigned it rather than the source is recorded beside it. ModuleItem and
// GenerateCaseItem hold the pair under different member names, so it is passed
// rather than the node holding it.
namespace {
struct GenerateBlockNameSlot {
  std::string_view& name;
  bool& is_generated;
};
}  // namespace

// Name one generate block, then walk what it holds. The §27.6 name is recorded
// as assigned, because §23.6 lets a hierarchical name written outside the block
// reach into it only when the source named it.
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

// Name every block of one construct, and of any construct directly nested in
// it, which §27.5 rules belong to the outer construct and therefore share its
// number rather than taking one of their own.
static void NameConstructBlocks(ModuleItem* it, std::string_view name,
                                Arena& arena) {
  if (!IsConditionalGenerateConstruct(it->kind)) {
    // §27.5: direct nesting "does not apply in any way to loop generate
    // constructs", so a loop generate block is a scope whatever it holds.
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

void Elaborator::AssignGenerateBlockNames(const ModuleDecl* decl) {
  std::unordered_set<std::string_view> used;
  for (const auto& port : decl->ports) used.insert(port.name);
  for (const auto& p : decl->params) used.insert(p.first);
  NameGenerateBlocksInScope(decl->items, std::move(used), arena_);
}

// §27.5: gather the block names introduced by the alternatives of a single
// generate construct. An if-generate contributes its then-block name and,
// recursively, the names of every else / else-if alternative; a case-generate
// contributes the label of each case item (including default); a loop generate
// contributes its array name. Names are collected into a set so that the same
// name labelling more than one alternative of one conditional construct counts
// only once -- at most one alternative is ever instantiated, so reusing a name
// across the alternatives of a single conditional construct is permitted.
static void CollectGenerateBlockNames(
    const ModuleItem* item, std::unordered_set<std::string_view>& out) {
  switch (item->kind) {
    case ModuleItemKind::kGenerateIf:
      if (!item->name.empty()) out.insert(item->name);
      if (item->gen_else) CollectGenerateBlockNames(item->gen_else, out);
      break;
    case ModuleItemKind::kGenerateCase:
      for (const auto& ci : item->gen_case_items) {
        if (!ci.label.empty()) out.insert(ci.label);
      }
      break;
    case ModuleItemKind::kGenerateFor:
      if (!item->name.empty()) out.insert(item->name);
      break;
    default:
      break;
  }
}

// Names of ordinary declarations in this scope: ports, parameters, and the
// named module items that are not themselves generate constructs.
static std::unordered_set<std::string_view> CollectNonGenerateDeclNames(
    const ModuleDecl* decl) {
  std::unordered_set<std::string_view> decl_names;
  for (const auto& port : decl->ports)
    if (!port.name.empty()) decl_names.insert(port.name);
  for (const auto& p : decl->params)
    if (!p.first.empty()) decl_names.insert(p.first);
  for (const auto* item : decl->items) {
    if (IsGenerateConstruct(item->kind)) continue;
    if (!item->name.empty()) decl_names.insert(item->name);
    if (!item->inst_name.empty()) decl_names.insert(item->inst_name);
    if (!item->gate_inst_name.empty()) decl_names.insert(item->gate_inst_name);
  }
  return decl_names;
}

// How many distinct generate constructs in this scope declare a block of each
// name. A name claimed by more than one construct violates the rule against
// sharing a block name across conditional or loop generate constructs.
static std::unordered_map<std::string_view, int> CountGenerateConstructUses(
    const ModuleDecl* decl) {
  std::unordered_map<std::string_view, int> construct_uses;
  for (const auto* item : decl->items) {
    if (!IsGenerateConstruct(item->kind)) continue;
    std::unordered_set<std::string_view> names;
    CollectGenerateBlockNames(item, names);
    for (auto n : names) ++construct_uses[n];
  }
  return construct_uses;
}

// Report any conditional-generate naming conflicts for the block names declared
// by a single if/case generate construct. A name colliding with an ordinary
// declaration in the same scope, or with a generate block of a different
// construct, is an error; names are deduplicated per construct so that reusing
// one across the alternatives of the same construct is not flagged.
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
                 Subclause("23.9"));
    } else if (construct_uses[n] > 1) {
      diag.Error(item->loc,
                 std::format("generate block '{}' has the same name as a "
                             "generate block in another generate construct "
                             "in the same scope",
                             n),
                 Subclause("23.9"));
    }
  }
}

// §27.5: enforce the naming rules for conditional generate constructs. A named
// generate block shares the enclosing scope's namespace, so the name of a block
// in an if-generate or case-generate must not also name another declaration in
// that scope, nor a generate block belonging to a different generate construct
// in the same scope. The check looks at every alternative of the construct,
// independent of which one (if any) elaboration selects for instantiation, so a
// collision is reported even when the offending block is not instantiated.
// Reusing a name across the alternatives of one conditional construct is left
// untouched: those names are deduplicated per construct, so only one will be
// counted.
void Elaborator::CheckConditionalGenerateNaming(const ModuleDecl* decl) {
  std::unordered_set<std::string_view> decl_names =
      CollectNonGenerateDeclNames(decl);
  std::unordered_map<std::string_view, int> construct_uses =
      CountGenerateConstructUses(decl);

  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kGenerateIf &&
        item->kind != ModuleItemKind::kGenerateCase) {
      continue;
    }
    ReportConditionalGenerateNameConflicts(diag_, item, decl_names,
                                           construct_uses);
  }
}

}  // namespace delta
