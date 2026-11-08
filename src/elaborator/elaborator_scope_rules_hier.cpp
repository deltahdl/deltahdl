#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <format>
#include <functional>
#include <optional>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/class_method_reads.h"
#include "elaborator/const_eval.h"
#include "elaborator/constant_scope.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/elaborator_scope_rules_names.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_enum_member.h"
#include "elaborator/rtlir_scopes.h"
#include "lexer/token.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

void CollectMemberAccess(const Expr* e, std::vector<const Expr*>& out) {
  if (!e) return;
  if (e->kind == ExprKind::kMemberAccess) {
    out.push_back(e);
  }
  CollectMemberAccess(e->lhs, out);
  CollectMemberAccess(e->rhs, out);
  CollectMemberAccess(e->base, out);
  CollectMemberAccess(e->index, out);
  CollectMemberAccess(e->index_end, out);
  CollectMemberAccess(e->condition, out);
  CollectMemberAccess(e->true_expr, out);
  CollectMemberAccess(e->false_expr, out);
  CollectMemberAccess(e->repeat_count, out);
  CollectMemberAccess(e->with_expr, out);
  CollectMemberAccess(e->stream_range, out);
  for (const auto* a : e->args) CollectMemberAccess(a, out);
  for (const auto* el : e->elements) CollectMemberAccess(el, out);
}

void CollectOwnMemberAccess(const Stmt* s, std::vector<const Expr*>& out) {
  CollectMemberAccess(s->condition, out);
  CollectMemberAccess(s->lhs, out);
  CollectMemberAccess(s->rhs, out);
  CollectMemberAccess(s->delay, out);
  CollectMemberAccess(s->cycle_delay, out);
  CollectMemberAccess(s->for_cond, out);
  CollectMemberAccess(s->expr, out);
  CollectMemberAccess(s->assert_expr, out);
  for (const auto& ci : s->case_items) {
    for (const auto* p : ci.patterns) CollectMemberAccess(p, out);
  }
  for (const auto& rc : s->randcase_items) CollectMemberAccess(rc.first, out);
}

void CollectMemberAccessInStmt(const Stmt* s, std::vector<const Expr*>& out) {
  if (!s) return;
  CollectOwnMemberAccess(s, out);
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { CollectMemberAccessInStmt(sub, out); });
}

struct InstanceArrayBounds {
  int64_t low;
  int64_t high;
};

bool DecodeInstanceArrayBase(const Expr* ma, std::string_view& name,
                             const Expr*& select_index) {
  if (!ma || ma->kind != ExprKind::kMemberAccess || !ma->lhs) return false;
  const Expr* base = ma->lhs;
  if (base->kind == ExprKind::kIdentifier) {
    name = base->text;
    select_index = nullptr;
    return true;
  }
  if (base->kind == ExprKind::kSelect && base->base &&
      base->base->kind == ExprKind::kIdentifier) {
    name = base->base->text;
    select_index = base->index;
    return true;
  }
  return false;
}

void CollectModuleMemberAccesses(const ModuleDecl* decl,
                                 std::vector<const Expr*>& accesses) {
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      CollectMemberAccess(item->assign_lhs, accesses);
      CollectMemberAccess(item->assign_rhs, accesses);
    }
    if (IsProceduralItemKind(item->kind)) {
      CollectMemberAccessInStmt(item->body, accesses);
    }
  }
}

bool ImportWildcardProvides(const CompilationUnit* unit,
                            std::string_view package_name,
                            std::string_view name) {
  for (const auto* pkg : unit->packages) {
    if (pkg->name != package_name) continue;
    for (const auto* pi : pkg->items) {
      if (pi->name == name) return true;
      if (pi->kind == ModuleItemKind::kClassDecl && pi->class_decl &&
          pi->class_decl->name == name) {
        return true;
      }
    }
  }
  return false;
}

bool ImportedIntoModule(const CompilationUnit* unit, const RtlirModule* m,
                        std::string_view name) {
  for (const auto& imp : m->imports) {
    if (!imp.is_wildcard && imp.item_name == name) return true;
    if (imp.is_wildcard &&
        ImportWildcardProvides(unit, imp.package_name, name)) {
      return true;
    }
  }
  return false;
}

bool ModuleDeclaresMember(const RtlirModule* m, std::string_view name);

void CheckHierRefImportedMemberAccess(
    DiagEngine& diag, const CompilationUnit* unit,
    const std::unordered_map<std::string_view, const RtlirModule*>& inst_type,
    const Expr* ma) {
  if (!ma || ma->kind != ExprKind::kMemberAccess) return;
  if (!ma->lhs || ma->lhs->kind != ExprKind::kIdentifier) return;
  if (!ma->rhs || ma->rhs->kind != ExprKind::kIdentifier) return;
  auto it = inst_type.find(ma->lhs->text);
  if (it == inst_type.end()) return;
  if (ModuleDeclaresMember(it->second, ma->rhs->text)) return;
  if (ImportedIntoModule(unit, it->second, ma->rhs->text)) {
    diag.Error(
        ma->range.start,
        std::format("hierarchical reference '{}.{}' targets a name imported "
                    "into '{}' from a package; imported names are not "
                    "visible through hierarchical references",
                    ma->lhs->text, ma->rhs->text, it->second->name),
        Subclause("26.3"));
  }
}

std::unordered_map<std::string_view, const RtlirModule*>
CollectResolvedChildren(const RtlirModule* mod) {
  std::unordered_map<std::string_view, const RtlirModule*> inst_type;
  for (const auto& child : mod->children) {
    if (child.resolved) inst_type[child.inst_name] = child.resolved;
  }
  return inst_type;
}

template <typename Range, typename Proj>
bool RangeHasName(const Range& range, Proj proj, std::string_view name) {
  for (const auto& e : range) {
    if (proj(e) == name) return true;
  }
  return false;
}

bool EnumTypesDeclare(const RtlirModule* m, std::string_view name) {
  for (const auto& entry : m->enum_types) {
    if (RangeHasName(
            entry.second, [](const RtlirEnumMember& e) { return e.name; },
            name)) {
      return true;
    }
  }
  return false;
}

bool ModuleDeclaresMember(const RtlirModule* m, std::string_view name) {
  auto ptr_name = [](const auto* d) {
    return d ? d->name : std::string_view{};
  };
  auto declares_module_level_param = [&] {
    for (const auto& p : m->params) {
      if (p.name != name) continue;
      if (ParamVisibleFromScopes(p.gen_block_prefix, {})) return true;
    }
    return false;
  };
  bool selected_by_a_port =
      std::any_of(m->ports.begin(), m->ports.end(),
                  [&](const RtlirPort& p) { return PortSelectsFrom(p, name); });
  return selected_by_a_port ||
         RangeHasName(
             m->ports, [](const RtlirPort& p) { return p.name; }, name) ||
         RangeHasName(
             m->nets, [](const RtlirNet& n) { return n.name; }, name) ||
         RangeHasName(
             m->variables, [](const RtlirVariable& v) { return v.name; },
             name) ||
         declares_module_level_param() ||
         RangeHasName(m->function_decls, ptr_name, name) ||
         RangeHasName(m->let_decls, ptr_name, name) ||
         RangeHasName(m->dpi_import_decls, ptr_name, name) ||
         RangeHasName(m->sequence_decls, ptr_name, name) ||
         RangeHasName(m->class_decls, ptr_name, name) ||
         RangeHasName(
             m->children, [](const RtlirModuleInst& c) { return c.inst_name; },
             name) ||
         RangeHasName(m->clocking_blocks, ptr_name, name) ||
         EnumTypesDeclare(m, name);
}

bool ChildDeclAllowsMemberCheck(const ModuleDecl* child) {
  if (!child) return false;
  if (child->decl_kind != ModuleDeclKind::kModule) return false;
  if (!child->modports.empty()) return false;
  for (const auto* item : child->items) {
    if (IsProceduralItemKind(item->kind)) return false;
    if (item->kind == ModuleItemKind::kGenerateFor ||
        item->kind == ModuleItemKind::kGenerateIf ||
        item->kind == ModuleItemKind::kGenerateCase) {
      return false;
    }
  }
  return true;
}

std::unordered_map<std::string_view, InstanceArrayBounds>
CollectInstanceArrayBounds(const ModuleDecl* decl) {
  std::unordered_map<std::string_view, InstanceArrayBounds> arrayed;
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kModuleInst) continue;
    if (!item->inst_range_left || !item->inst_range_right) continue;
    auto lhi = ConstEvalInt(item->inst_range_left);
    auto rhi = ConstEvalInt(item->inst_range_right);
    if (!lhi || !rhi) continue;
    InstanceArrayBounds b;
    b.low = std::min(*lhi, *rhi);
    b.high = std::max(*lhi, *rhi);
    arrayed[item->inst_name] = b;
  }
  return arrayed;
}

bool ReportInstanceSelectForm(DiagEngine& diag, std::string_view name,
                              const Expr* select, const ConstantScope& scope) {
  if (select->index_end != nullptr) {
    diag.Error(select->index->range.start,
               std::format("instance select of '{}' is a range; an instance "
                           "select names one instance",
                           name),
               Subclause("23.6"));
    return true;
  }
  if (IsConstantExpr(select->index, scope.constants)) return false;
  diag.Error(
      select->index->range.start,
      std::format("instance select of '{}' is not a constant expression", name),
      Subclause("23.6"));
  return true;
}

std::unordered_set<std::string_view> NamedLoopGenerateBlocks(
    const ModuleDecl* decl) {
  std::unordered_set<std::string_view> names;
  for (const ModuleItem* item : decl->items) {
    if (item->kind == ModuleItemKind::kGenerateFor &&
        !item->name_is_generated) {
      names.insert(item->name);
    }
  }
  return names;
}

void CheckHierRefLoopBlockSelect(
    DiagEngine& diag, const std::unordered_set<std::string_view>& loops,
    const Expr* ma, const ConstantScope& scope) {
  std::string_view name;
  const Expr* select_index = nullptr;
  if (!DecodeInstanceArrayBase(ma, name, select_index)) return;
  if (select_index == nullptr || !loops.contains(name)) return;
  ReportInstanceSelectForm(diag, name, ma->lhs, scope);
}

void CheckHierRefInstanceArrayAccess(
    DiagEngine& diag,
    const std::unordered_map<std::string_view, InstanceArrayBounds>& arrayed,
    const Expr* ma, const ConstantScope& scope) {
  std::string_view name;
  const Expr* select_index = nullptr;
  if (!DecodeInstanceArrayBase(ma, name, select_index)) return;
  auto it = arrayed.find(name);
  if (it == arrayed.end()) return;
  if (!select_index) {
    diag.Error(ma->range.start,
               std::format("hierarchical reference to instance array '{}' "
                           "requires an instance select",
                           name),
               Subclause("23.6"));
    return;
  }
  if (ReportInstanceSelectForm(diag, name, ma->lhs, scope)) return;
  auto idx = ConstEvalInt(select_index, scope.fold);
  if (!idx) return;
  if (*idx < it->second.low || *idx > it->second.high) {
    diag.Error(select_index->range.start,
               std::format("instance select [{}] is out of range for "
                           "instance array '{}' [{}:{}]",
                           *idx, name, it->second.high, it->second.low),
               Subclause("23.6"));
  }
}

struct InstanceSelectWalk {
  DiagEngine& diag;
  const std::unordered_map<std::string_view, InstanceArrayBounds>& arrayed;
  const std::unordered_set<std::string_view>& loops;
  ConstantScope scope;

  void Check(const Expr* ma) {
    CheckHierRefInstanceArrayAccess(diag, arrayed, ma, scope);
    CheckHierRefLoopBlockSelect(diag, loops, ma, scope);
  }

  void Walk(const Stmt* stmt) {
    if (stmt == nullptr) return;
    std::vector<const Expr*> accesses;
    CollectOwnMemberAccess(stmt, accesses);
    for (const Expr* ma : accesses) Check(ma);
    if (DeclaresParam(stmt)) scope.Declare(stmt->var_name, stmt->var_init);
    std::optional<ConstantScope> outer;
    if (BlockDeclaresParam(*stmt)) outer = scope;
    ForEachChildStmt(stmt, [this](Stmt* const& sub) { Walk(sub); });
    if (outer.has_value()) scope = std::move(*outer);
  }
};

}  // namespace

void Elaborator::CheckHierRefUndeclaredMember(
    const std::unordered_map<std::string_view, const RtlirModule*>& inst_type,
    const Expr* ma) {
  if (!ma->lhs || ma->lhs->kind != ExprKind::kIdentifier) return;
  if (!ma->rhs || ma->rhs->kind != ExprKind::kIdentifier) return;
  auto it = inst_type.find(ma->lhs->text);
  if (it == inst_type.end()) return;
  if (!ChildDeclAllowsMemberCheck(FindModule(it->second->name))) return;
  if (ModuleDeclaresMember(it->second, ma->rhs->text)) return;
  if (ImportedIntoModule(unit_, it->second, ma->rhs->text)) return;
  if (BindIntroducesName(unit_, it->second->name, ma->lhs->text, ma->rhs->text))
    return;
  diag_.Error(
      ma->range.start,
      std::format("hierarchical reference '{}.{}' is unresolved: '{}' is not "
                  "declared in module '{}'",
                  ma->lhs->text, ma->rhs->text, ma->rhs->text,
                  it->second->name),
      Subclause("23.6"));
}

UnitHierHeadNames::UnitHierHeadNames(const CompilationUnit* unit)
    : declared_(unit) {
  for (const auto* scopes :
       {&unit->modules, &unit->interfaces, &unit->programs, &unit->checkers}) {
    for (const ModuleDecl* scope : *scopes) scope_names_.AddScope(scope);
  }
  for (const ModuleItem* item : unit->cu_items) scope_names_.AddItem(item);
  for (const BindDirective* bd : unit->bind_directives) {
    if (bd->instantiation != nullptr) scope_names_.AddItem(bd->instantiation);
  }
}

bool UnitHierHeadNames::Admits(std::string_view name) const {
  return declared_.Declares(name) || scope_names_.Contains(name);
}

void ScopeNameSet::Insert(std::string_view name) {
  if (!name.empty()) names_.insert(name);
}

bool ScopeNameSet::Contains(std::string_view name) const {
  if (names_.contains(name)) return true;
  size_t digits = name.find_last_not_of("0123456789");
  if (digits == std::string_view::npos || digits + 1 == name.size()) {
    return false;
  }
  return numbered_enum_names_.contains(name.substr(0, digits + 1));
}

void ScopeNameSet::AddScope(const ModuleDecl* scope) {
  Insert(scope->name);
  for (const PortDecl& port : scope->ports) Insert(port.name);
  for (const ModportDecl* mp : scope->modports) Insert(mp->name);
  for (const ModuleItem* item : scope->items) AddItem(item);
  for (const BindDirective* bd : scope->bind_directives) {
    if (bd->instantiation != nullptr) AddItem(bd->instantiation);
  }
}

void ScopeNameSet::AddItem(const ModuleItem* item) {
  if (item == nullptr) return;
  AddItemOwnNames(item);
  if (item->nested_module_decl != nullptr) AddScope(item->nested_module_decl);
  for (const ModuleItem* sub : item->gen_body) AddItem(sub);
  AddItem(item->gen_else);
  for (const auto& ci : item->gen_case_items) {
    if (!ci.name_is_generated) Insert(ci.label);
    for (const ModuleItem* sub : ci.body) AddItem(sub);
  }
  if (item->gen_init != nullptr) AddStmt(item->gen_init);
  AddStmt(item->body);
  for (const auto& arg : item->func_args) Insert(arg.name);
  for (const Stmt* s : item->func_body_stmts) AddStmt(s);
}

void ScopeNameSet::AddItemOwnNames(const ModuleItem* item) {
  if (!item->name_is_generated) Insert(item->name);
  for (std::string_view name : {item->inst_name, item->gate_inst_name}) {
    Insert(name);
  }
  AddEnumerations(item->data_type);
  if (item->kind == ModuleItemKind::kTypedef) {
    AddEnumerations(item->typedef_type);
  }
  if (item->kind == ModuleItemKind::kContAssign) {
    AddImplicitNets(item->assign_lhs);
  }
  for (const auto& [port, conn] : item->inst_ports) AddImplicitNets(conn);
  for (const Expr* terminal : item->gate_terminals) AddImplicitNets(terminal);
}

void ScopeNameSet::AddEnumerations(const DataType& type) {
  for (const EnumMember& member : type.enum_members) {
    if (member.range_start != nullptr) {
      numbered_enum_names_.insert(member.name);
    } else {
      Insert(member.name);
    }
  }
}

void ScopeNameSet::AddImplicitNets(const Expr* e) {
  std::vector<const Expr*> idents;
  CollectBareIdents(e, idents);
  for (const Expr* ident : idents) Insert(ident->text);
}

void ScopeNameSet::AddStmt(const Stmt* s) {
  if (s == nullptr) return;
  for (std::string_view name : {s->label, s->var_name}) Insert(name);
  for (std::string_view name : s->foreach_vars) Insert(name);
  if (s->decl_item != nullptr) AddItem(s->decl_item);
  ForEachChildStmt(s, [&](Stmt* const& sub) { AddStmt(sub); });
}

namespace {

using GenerateBlockScopes = std::unordered_map<std::string_view, ScopeNameSet>;

void AddConstructBlocks(const ModuleItem* item, GenerateBlockScopes& blocks);

void AddConditionalBlock(std::string_view name, bool name_is_generated,
                         const std::vector<ModuleItem*>& body,
                         bool has_begin_end, GenerateBlockScopes& blocks) {
  if (IsDirectlyNestedBlock(body, has_begin_end)) {
    AddConstructBlocks(body[0], blocks);
    return;
  }
  if (name.empty() || name_is_generated) return;
  ScopeNameSet& names = blocks[name];
  for (const ModuleItem* sub : body) names.AddItem(sub);
}

void AddIfBlocks(const ModuleItem* item, GenerateBlockScopes& blocks) {
  AddConditionalBlock(item->name, item->name_is_generated, item->gen_body,
                      item->gen_body_has_begin_end, blocks);
  const ModuleItem* other = item->gen_else;
  if (other == nullptr) return;
  if (other->gen_cond != nullptr) {
    AddIfBlocks(other, blocks);
    return;
  }
  AddConditionalBlock(other->name, other->name_is_generated, other->gen_body,
                      other->gen_body_has_begin_end, blocks);
}

void AddLoopBlock(const ModuleItem* item, GenerateBlockScopes& blocks) {
  if (item->name.empty() || item->name_is_generated) return;
  ScopeNameSet& names = blocks[item->name];
  for (const ModuleItem* sub : item->gen_body) names.AddItem(sub);
  const Stmt* init = item->gen_init;
  if (init == nullptr) return;
  names.Insert(init->var_name);
  if (init->lhs != nullptr && init->lhs->kind == ExprKind::kIdentifier) {
    names.Insert(init->lhs->text);
  }
}

void AddConstructBlocks(const ModuleItem* item, GenerateBlockScopes& blocks) {
  switch (item->kind) {
    case ModuleItemKind::kGenerateIf:
      AddIfBlocks(item, blocks);
      return;
    case ModuleItemKind::kGenerateCase:
      for (const auto& ci : item->gen_case_items) {
        AddConditionalBlock(ci.label, ci.name_is_generated, ci.body,
                            ci.has_begin_end, blocks);
      }
      return;
    case ModuleItemKind::kGenerateFor:
      AddLoopBlock(item, blocks);
      return;
    default:
      return;
  }
}

void DropShadowedBlocks(const ModuleDecl* decl, GenerateBlockScopes& blocks) {
  for (const PortDecl& port : decl->ports) blocks.erase(port.name);
  std::unordered_set<std::string_view> locals;
  for (const ModuleItem* item : decl->items) {
    if (IsProceduralItemKind(item->kind)) {
      CollectProcReadableNames(item->body, locals);
      continue;
    }
    if (item->kind == ModuleItemKind::kGenerateIf ||
        item->kind == ModuleItemKind::kGenerateCase ||
        item->kind == ModuleItemKind::kGenerateFor) {
      continue;
    }
    for (std::string_view name :
         {item->name, item->inst_name, item->gate_inst_name}) {
      blocks.erase(name);
    }
  }
  for (std::string_view name : locals) blocks.erase(name);
}

}  // namespace

void ReportUndeclaredGenerateBlockMembers(const ModuleDecl* decl,
                                          DiagEngine& diag) {
  GenerateBlockScopes blocks;
  for (const ModuleItem* item : decl->items) AddConstructBlocks(item, blocks);
  DropShadowedBlocks(decl, blocks);
  if (blocks.empty()) return;
  std::vector<const Expr*> accesses;
  CollectModuleMemberAccesses(decl, accesses);
  for (const Expr* ma : accesses) {
    if (ma->is_scope_resolution || ma->rhs == nullptr ||
        ma->rhs->kind != ExprKind::kIdentifier) {
      continue;
    }
    std::string_view block;
    const Expr* select_index = nullptr;
    if (!DecodeInstanceArrayBase(ma, block, select_index)) continue;
    auto it = blocks.find(block);
    if (it == blocks.end() || it->second.Contains(ma->rhs->text)) continue;
    diag.Error(ma->range.start,
               std::format("hierarchical reference '{}.{}' is unresolved: '{}' "
                           "is not declared in generate block '{}'",
                           block, ma->rhs->text, ma->rhs->text, block),
               Subclause("23.6"));
  }
}

namespace {

void AddGeneratedBlockNames(const ModuleItem* item,
                            std::unordered_set<std::string_view>& out);

void AddGeneratedBlockName(std::string_view name, bool name_is_generated,
                           const std::vector<ModuleItem*>& body,
                           bool has_begin_end,
                           std::unordered_set<std::string_view>& out) {
  if (IsDirectlyNestedBlock(body, has_begin_end)) {
    AddGeneratedBlockNames(body[0], out);
    return;
  }
  if (name_is_generated) out.insert(name);
}

void AddGeneratedBlockNames(const ModuleItem* item,
                            std::unordered_set<std::string_view>& out) {
  if (!IsConditionalGenerateConstruct(item->kind)) {
    if (item->name_is_generated) out.insert(item->name);
    return;
  }
  AddGeneratedBlockName(item->name, item->name_is_generated, item->gen_body,
                        item->gen_body_has_begin_end, out);
  for (const auto& ci : item->gen_case_items) {
    AddGeneratedBlockName(ci.label, ci.name_is_generated, ci.body,
                          ci.has_begin_end, out);
  }
  if (item->gen_else != nullptr) AddGeneratedBlockNames(item->gen_else, out);
}

}  // namespace

std::unordered_set<std::string_view> UnnamedGenerateBlockNames(
    const ModuleDecl* decl) {
  std::unordered_set<std::string_view> generated;
  for (const ModuleItem* item : decl->items) {
    AddGeneratedBlockNames(item, generated);
  }
  return generated;
}

void ReportUnnamedGenerateBlockReaches(const ModuleDecl* decl,
                                       DiagEngine& diag) {
  std::unordered_set<std::string_view> generated =
      UnnamedGenerateBlockNames(decl);
  std::vector<const Expr*> accesses;
  CollectModuleMemberAccesses(decl, accesses);
  for (const Expr* ma : accesses) {
    std::string_view block;
    const Expr* select_index = nullptr;
    if (!DecodeInstanceArrayBase(ma, block, select_index)) continue;
    if (block == decl->name) block = ma->rhs->text;
    if (!generated.contains(block)) continue;
    diag.Error(ma->range.start,
               std::format("hierarchical name reaches into unnamed generate "
                           "block '{}', whose generated name no hierarchical "
                           "name may use",
                           block),
               Subclause("27.6"));
  }
}

namespace {

const Expr* HierHead(const Expr* e) {
  while (e != nullptr) {
    if (e->kind == ExprKind::kMemberAccess) {
      if (e->is_scope_resolution) return nullptr;
      e = e->lhs;
    } else if (e->kind == ExprKind::kSelect) {
      e = e->base;
    } else {
      break;
    }
  }
  if (e == nullptr || e->kind != ExprKind::kIdentifier) return nullptr;
  if (!e->scope_prefix.empty() || e->text.starts_with('$')) return nullptr;
  if (e->text == "this" || e->text == "super") return nullptr;
  return e;
}

using NameSet = std::unordered_set<std::string_view>;

const NameSet* Widened(const NameSet* base, const NameSet& names,
                       NameSet& storage) {
  if (names.empty()) return base;
  storage = *base;
  storage.insert(names.begin(), names.end());
  return &storage;
}

void CollectDesignElementHeads(const Expr* call,
                               std::vector<const Expr*>& out) {
  for (const Expr* arg : call->args) {
    const Expr* head = HierHead(arg);
    if (head != nullptr) out.push_back(head);
  }
}

void CollectHierHeads(const Expr* e, const NameSet& bound,
                      std::vector<const Expr*>& out) {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kMemberAccess) {
    const Expr* head = HierHead(e);
    if (head != nullptr && !bound.contains(head->text)) out.push_back(head);
    return;
  }
  if (ArgNamesDesignElement(e)) {
    CollectDesignElementHeads(e, out);
    return;
  }
  NameSet storage;
  if (e->kind == ExprKind::kTernary) {
    const NameSet& inner =
        *Widened(&bound, MatchesBindingsOf(e->condition), storage);
    CollectHierHeads(e->condition, inner, out);
    CollectHierHeads(e->true_expr, inner, out);
    CollectHierHeads(e->false_expr, bound, out);
    return;
  }
  if (e->kind == ExprKind::kBinary && e->op == TokenKind::kAmpAmpAmp) {
    CollectHierHeads(e->lhs, bound, out);
    CollectHierHeads(e->rhs,
                     *Widened(&bound, MatchesBindingsOf(e->lhs), storage), out);
    return;
  }
  for (const Expr* child :
       {e->lhs, e->rhs, e->condition, e->true_expr, e->false_expr, e->base,
        e->index, e->index_end, e->repeat_count}) {
    CollectHierHeads(child, bound, out);
  }
  for (const Expr* child : e->args) CollectHierHeads(child, bound, out);
  for (const Expr* child : e->elements) CollectHierHeads(child, bound, out);
}

void CollectStmtHierHeads(const Stmt* s, const NameSet& bound,
                          std::vector<const Expr*>& out) {
  if (s == nullptr) return;
  std::vector<std::string_view> header = ForHeaderDeclaredNames(s);
  NameSet storage;
  const NameSet& inner =
      *Widened(&bound, NameSet(header.begin(), header.end()), storage);
  ForEachChildExpr(s, [&](const Expr* e) { CollectHierHeads(e, inner, out); });
  NameSet code_block_names;
  CollectRandsequenceDeclaredNames(s, code_block_names);
  ForEachChildStmtWithBindings(s, [&](const Stmt* sub, const NameSet& names) {
    NameSet in_scope = code_block_names;
    in_scope.insert(names.begin(), names.end());
    NameSet sub_storage;
    CollectStmtHierHeads(sub, *Widened(&inner, in_scope, sub_storage), out);
  });
}

}  // namespace

void ReportUnresolvedHierHeads(
    const ModuleDecl* decl, const std::function<bool(std::string_view)>& admits,
    DiagEngine& diag) {
  std::vector<const Expr*> heads;
  for (const ModuleItem* item : decl->items) {
    if (IsProceduralItemKind(item->kind))
      CollectStmtHierHeads(item->body, {}, heads);
    bool is_subroutine = item->kind == ModuleItemKind::kTaskDecl ||
                         item->kind == ModuleItemKind::kFunctionDecl;
    if (!is_subroutine || !item->method_class.empty()) continue;
    for (const Stmt* s : item->func_body_stmts)
      CollectStmtHierHeads(s, {}, heads);
  }
  for (const Expr* head : heads) {
    if (admits(head->text)) continue;
    diag.Error(head->range.start,
               std::format("hierarchical name '{}' resolves to no declaration",
                           head->text),
               Subclause("23.8"));
  }
}

std::vector<const Expr*> UnitSubroutineHierHeads(const CompilationUnit& unit) {
  std::vector<const Expr*> heads;
  for (const ModuleItem* item : unit.cu_items) {
    bool is_subroutine = item->kind == ModuleItemKind::kTaskDecl ||
                         item->kind == ModuleItemKind::kFunctionDecl;
    if (!is_subroutine || !item->method_class.empty()) continue;
    NameSet locals;
    CollectSubroutineLocalNames(item, locals);
    for (const Stmt* s : item->func_body_stmts)
      CollectStmtHierHeads(s, locals, heads);
  }
  return heads;
}

void Elaborator::ValidateHierRefToImportedName(const ModuleDecl* decl,
                                               const RtlirModule* mod) {
  if (!mod || mod->children.empty()) return;
  std::unordered_map<std::string_view, const RtlirModule*> inst_type =
      CollectResolvedChildren(mod);
  if (inst_type.empty()) return;

  std::vector<const Expr*> accesses;
  CollectModuleMemberAccesses(decl, accesses);
  for (const auto* ma : accesses) {
    CheckHierRefImportedMemberAccess(diag_, unit_, inst_type, ma);
    CheckHierRefUndeclaredMember(inst_type, ma);
  }
}

void Elaborator::ValidateHierRefInstanceArray(const ModuleDecl* decl,
                                              const RtlirModule* mod) {
  std::unordered_map<std::string_view, InstanceArrayBounds> arrayed =
      CollectInstanceArrayBounds(decl);
  std::unordered_set<std::string_view> loops = NamedLoopGenerateBlocks(decl);
  if (arrayed.empty() && loops.empty()) return;

  ScopeMap module_params = mod ? BuildParamScope(mod) : ScopeMap{};
  InstanceSelectWalk walk{
      diag_, arrayed, loops,
      ConstantScope{module_params, std::move(module_params)}};
  for (const ModuleItem* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      std::vector<const Expr*> accesses;
      CollectMemberAccess(item->assign_lhs, accesses);
      CollectMemberAccess(item->assign_rhs, accesses);
      for (const Expr* ma : accesses) walk.Check(ma);
    }
    if (IsProceduralItemKind(item->kind)) walk.Walk(item->body);
  }
}

}  // namespace delta
