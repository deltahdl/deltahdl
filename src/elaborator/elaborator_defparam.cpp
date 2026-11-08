#include <cstddef>
#include <cstdint>
#include <format>
#include <optional>
#include <set>
#include <string>
#include <string_view>
#include <tuple>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/const_eval.h"
#include "elaborator/const_eval_internal.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_data.h"
#include "elaborator/elaborator_defparam_walk.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_items_params.h"
#include "elaborator/net_data_type.h"
#include "elaborator/param_value_assignability.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "elaborator/type_eval.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

static bool CollectPathSteps(const Expr* expr, const ScopeMap& scope,
                             HierPath& out) {
  if (expr->kind == ExprKind::kMemberAccess) {
    if (!CollectPathSteps(expr->lhs, scope, out)) return false;
    out.push_back({expr->rhs->text, false, 0, {}, {}});
    return true;
  }
  if (expr->kind == ExprKind::kSelect) {
    if (!CollectPathSteps(expr->base, scope, out)) return false;
    if (out.empty()) return false;
    auto index = ConstEvalInt(expr->index, scope);
    if (!index) return false;
    out.back().has_index = true;
    out.back().index = *index;
    return true;
  }
  if (expr->kind == ExprKind::kIdentifier) {
    out.push_back({expr->text, false, 0, {}, {}});
    return true;
  }
  return false;
}

static bool RhsContainsHierarchicalRef(const Expr* e);

static bool AnyScalarChildContainsHierarchicalRef(const Expr* e) {
  return RhsContainsHierarchicalRef(e->lhs) ||
         RhsContainsHierarchicalRef(e->rhs) ||
         RhsContainsHierarchicalRef(e->base) ||
         RhsContainsHierarchicalRef(e->index) ||
         RhsContainsHierarchicalRef(e->index_end) ||
         RhsContainsHierarchicalRef(e->condition) ||
         RhsContainsHierarchicalRef(e->true_expr) ||
         RhsContainsHierarchicalRef(e->false_expr) ||
         RhsContainsHierarchicalRef(e->repeat_count);
}

static bool AnyListChildContainsHierarchicalRef(const Expr* e) {
  for (const auto* a : e->args) {
    if (RhsContainsHierarchicalRef(a)) return true;
  }
  for (const auto* elem : e->elements) {
    if (RhsContainsHierarchicalRef(elem)) return true;
  }
  return false;
}

static bool RhsContainsHierarchicalRef(const Expr* e) {
  if (!e) return false;
  if (e->kind == ExprKind::kMemberAccess) return true;
  if (e->kind == ExprKind::kIdentifier && !e->scope_prefix.empty()) return true;
  if (AnyScalarChildContainsHierarchicalRef(e)) return true;
  return AnyListChildContainsHierarchicalRef(e);
}

RtlirParamDecl* Elaborator::ResolveDefparamSteps(RtlirModule* root,
                                                 const HierPath& path,
                                                 const HierPath& writer,
                                                 RtlirModule** out_mod) {
  if (path.size() < 2) return nullptr;

  std::vector<PathDescent> descents;
  RtlirModule* cur =
      DescendDefparamPath(root, path, writer, descents,
                          [this](RtlirModule& parent, RtlirModuleInst& elem) {
                            IsolateArrayElement(parent, elem, arena_);
                          });
  if (!cur) return nullptr;

  auto param_name = path.back().name;
  for (auto& p : cur->params) {
    if (p.name == param_name) {
      if (out_mod) *out_mod = cur;
      return &p;
    }
  }
  return nullptr;
}

RtlirParamDecl* Elaborator::ResolveDefparamFromTop(const HierPath& path,
                                                   DefparamTopRooted& rooted) {
  const RtlirModule* writer = rooted.root;
  RtlirModule* top = nullptr;
  for (auto* candidate : defparam_top_roots_) {
    if (candidate->name == path.front().name) top = candidate;
  }
  if (top == nullptr) return nullptr;
  rooted.root = top;
  rooted.steps.assign(path.begin() + 1, path.end());
  if (EscapesWriterBlock(defparam_writer_blocks_, writer, top, rooted.steps))
    return nullptr;
  if (rooted.steps.size() != 1) {
    return ResolveDefparamSteps(top, rooted.steps, {}, &rooted.target_mod);
  }
  for (auto& p : top->params) {
    if (p.name == rooted.steps.front().name) {
      rooted.target_mod = top;
      return &p;
    }
  }
  return nullptr;
}

static TypedefMap ModuleTypedefTable(const TypedefMap& all,
                                     const ModuleDecl* decl) {
  TypedefMap typedefs = all;
  if (decl == nullptr) return typedefs;
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kTypedef ||
        item->typedef_type.kind == DataTypeKind::kImplicit)
      continue;
    typedefs.insert_or_assign(item->name, item->typedef_type);
  }
  return typedefs;
}

static bool DeclTypeRangeFollowsScope(const RtlirParamDecl& p,
                                      const TypedefMap& typedefs) {
  const DataType* dtype = p.decl_type;
  if (dtype == nullptr) return false;
  if (dtype->packed_dim_left != nullptr) return true;
  return dtype->kind == DataTypeKind::kNamed &&
         FindNamedType(*dtype, typedefs) != nullptr;
}

static void RefoldOverride(RtlirParamDecl& p, const Expr* expr,
                           const ScopeMap& scope) {
  auto val = FoldParamValue(p, expr, scope);
  p.resolved_value = ConvertOverrideValue(val.value_or(p.resolved_value), p);
  RecordResolvedHighWords(p, expr, scope);
}

static bool OverrideExprReproducesValue(const RtlirParamDecl& p) {
  if (p.override_expr == nullptr || p.override_module == nullptr) return false;
  ParamRangeRegistryGuard instantiating_module_guard(p.override_module);
  auto val = FoldParamValue(p, p.override_expr, p.override_scope);
  return val && ConvertOverrideValue(*val, p) == p.resolved_value;
}

static void ReconvertOverrideValue(RtlirParamDecl& p, bool refold_override) {
  if (p.defparam_value_expr != nullptr) {
    ParamRangeRegistryGuard defparam_module_guard(p.defparam_module);
    RegisteredGenScopeGuard gen_scope_guard(p.defparam_value_scopes);
    RefoldOverride(p, p.defparam_value_expr, p.defparam_value_scope);
    return;
  }
  if (refold_override) {
    ParamRangeRegistryGuard instantiating_module_guard(p.override_module);
    RefoldOverride(p, p.override_expr, p.override_scope);
    return;
  }
  p.resolved_value = ConvertOverrideValue(p.resolved_value, p);
}

static void ResizeParamToRecomputedRange(RtlirParamDecl& p,
                                         const TypedefMap& typedefs,
                                         const ScopeMap& scope) {
  if (!DeclTypeRangeFollowsScope(p, typedefs)) return;
  const bool kRefoldOverride = OverrideExprReproducesValue(p);
  const DataType& dtype = *p.decl_type;
  PopulateParamTypeInfo(p, dtype, typedefs, scope);
  RecordParamDeclRange(p, dtype, scope);
  if (p.from_override) ReconvertOverrideValue(p, kRefoldOverride);
}

static ScopeMap ScopeOverlaidWith(ScopeMap outer, const ScopeMap& own) {
  for (const auto& [name, value] : own) outer[name] = value;
  return outer;
}

static bool RefoldsFromInstantiation(const RtlirParamDecl& p,
                                     const RtlirModule* parent) {
  return !p.is_type_param && p.override_expr != nullptr &&
         p.override_module == parent && p.defparam_value_expr == nullptr;
}

void Elaborator::RefoldChildOverrides(RtlirModule* mod,
                                      const ScopeMap& mod_scope) {
  for (auto& child : mod->children) {
    RtlirModule* cm = child.resolved;
    if (cm == nullptr || cm == mod) continue;
    bool changed = false;
    for (auto& p : cm->params) {
      if (!RefoldsFromInstantiation(p, mod)) continue;
      int64_t before = p.resolved_value;
      ScopeMap scope = ScopeOverlaidWith(p.override_scope, mod_scope);
      if (p.config_locked) {
        scope = ScopeOverlaidWith(std::move(scope), config_localparam_scope_);
      }
      RefoldOverride(p, p.override_expr, scope);
      changed = changed || p.resolved_value != before;
    }
    if (changed) RecomputeDependentParams(cm);
  }
}

static void RefoldFixedUnpackedDims(RtlirVariable& var, const ScopeMap& scope) {
  if (var.declared_unpacked_dims == nullptr ||
      var.unpacked_dim_sizes.size() != var.declared_unpacked_dims->size()) {
    return;
  }
  std::vector<RtlirUnpackedDim> dims;
  for (const Expr* dim : *var.declared_unpacked_dims) {
    auto folded = FoldUnpackedDimBounds(dim, scope);
    if (!folded) return;
    dims.push_back(*folded);
  }
  var.unpacked_dims = dims;
  var.unpacked_dim_sizes.clear();
  for (const auto& dim : dims) var.unpacked_dim_sizes.push_back(dim.Size());
  var.unpacked_size = dims[0].Size();
  var.unpacked_lo = dims[0].Low();
  var.is_descending = dims[0].left > dims[0].right;
}

static void ResizeParamSizedDecls(RtlirModule* mod, const TypedefMap& typedefs,
                                  const ScopeMap& scope) {
  for (auto& var : mod->variables) {
    ScopeMap var_scope = scope;
    for (const auto& [name, value] : var.gen_block_consts)
      var_scope[name] = value;
    RefoldFixedUnpackedDims(var, var_scope);
    if (var.dtype == nullptr) continue;
    var.width = EvalTypeWidth(*var.dtype, typedefs, var_scope);
  }
  for (auto& net : mod->nets) {
    if (net.dtype == nullptr || net.name.find('.') != std::string_view::npos)
      continue;
    net.width = EvalTypeWidth(*net.dtype, typedefs, scope);
  }
}

void Elaborator::RecomputeDependentParams(RtlirModule* mod) {
  if (!mod) return;
  ParamRangeRegistryGuard param_range_guard(mod);
  const TypedefMap kTypedefs =
      ModuleTypedefTable(typedefs_, FindModule(mod->name));
  TypedefRegistryGuard typedef_guard(&kTypedefs, &aggregate_typedef_names_,
                                     &type_ref_compare_);
  for (auto& p : mod->params) {
    if (p.is_type_param) continue;
    if (p.is_unbounded) continue;
    auto scope = BuildParamScope(mod, {});
    ResizeParamToRecomputedRange(p, kTypedefs, scope);
    if (p.from_override) continue;
    if (!p.default_value) continue;
    auto val = FoldParamValue(p, p.default_value, scope);
    if (val) {
      p.resolved_value = *val;
      p.is_resolved = true;
      RecordResolvedHighWords(p, p.default_value, scope);
    }
  }
  ResizeParamSizedDecls(mod, kTypedefs, BuildParamScope(mod, {}));
  RefoldChildOverrides(mod, BuildParamScope(mod, {}));
}

static bool DefparamOverrideAllowed(DiagEngine& diag,
                                    const RtlirParamDecl* param,
                                    const Expr* val_expr, SourceLoc loc) {
  if (param->is_type_param) {
    diag.Error(loc, "defparam cannot override a type parameter",
               Subclause("23.10.1"));
    return false;
  }
  if (param->is_localparam) {
    diag.Error(loc, "defparam cannot override a local parameter",
               Subclause("23.10.1"));
    return false;
  }
  if (param->config_locked) {
    return false;
  }
  if (RhsContainsHierarchicalRef(val_expr)) {
    diag.Error(loc,
               "defparam right-hand side may only reference parameters "
               "declared in the same module",
               Subclause("23.10.1"));
    return false;
  }
  return true;
}

struct DefparamOverride {
  const RtlirParamDecl* param;
  const Expr* val_expr;
  const ScopeMap& scope;
  SourceLoc loc;
  const RtlirModule* writer;
  bool whole;
};

using DefparamAppliedKey =
    std::tuple<RtlirModule*, const ModuleItem*, size_t, std::string_view>;
struct DefparamAppliedRecord {
  std::set<DefparamAppliedKey>& applied;
  const DefparamAppliedKey& key;
};

static void ReportNonConstantDefparam(DiagEngine& diag, SourceLoc loc) {
  diag.Error(loc,
             "defparam right-hand side must be a constant expression built "
             "from numbers and parameters",
             Subclause("23.10.1"));
}

static std::optional<int64_t> EvalDefparamOverride(
    DiagEngine& diag, const DefparamOverride& ovr,
    const DefparamAppliedRecord& rec) {
  if (!DefparamOverrideAllowed(diag, ovr.param, ovr.val_expr, ovr.loc)) {
    rec.applied.insert(rec.key);
    return std::nullopt;
  }
  if (auto real = RealOverrideValue(ovr.val_expr, ovr.scope)) {
    return ConvertOverrideValue(RoundRealToInteger(*real), *ovr.param);
  }
  auto val = FoldParamValue(*ovr.param, ovr.val_expr, ovr.scope);
  if (!val) {
    if (!IsConstantExpr(ovr.val_expr, ovr.scope)) {
      ReportNonConstantDefparam(diag, ovr.loc);
    } else {
      diag.Warning(ovr.loc, "defparam value is not constant",
                   Subclause("23.10.1"));
    }
    rec.applied.insert(rec.key);
    return std::nullopt;
  }
  return ConvertOverrideValue(*val, *ovr.param);
}

static void ReplaceStringParamValue(RtlirParamDecl& pd, const Expr* val_expr,
                                    Arena& arena) {
  if (!pd.is_string_value) return;
  if (!RecordStringParamChars(pd, val_expr, arena)) pd.is_string_value = false;
}

auto Elaborator::CollectDefparamSites(RtlirModule* mod,
                                      const ModuleDecl* decl) const
    -> std::vector<DefparamSite> {
  std::vector<DefparamSite> sites;
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kDefparam) continue;
    sites.push_back({item, {}, {}, {}, {}});
  }
  auto it = generate_defparams_.find(mod);
  if (it != generate_defparams_.end())
    sites.insert(sites.end(), it->second.begin(), it->second.end());
  return sites;
}

static const Expr* DefparamOverrideExpr(const Expr* val_expr) {
  return val_expr->kind == ExprKind::kIntegerLiteral ? val_expr : nullptr;
}

static bool IsConstantWholeValue(const Expr* value, const ScopeMap& names) {
  const Expr* pattern = UntypedPattern(value);
  if (pattern->kind != ExprKind::kAssignmentPattern)
    return IsConstantExpr(value, names);
  for (const Expr* item : pattern->elements) {
    if (!ConstEvalInt(item, names) && !IsConstantWholeValue(item, names))
      return false;
  }
  return true;
}

static bool WholeValueIsConstant(DiagEngine& diag,
                                 const DefparamOverride& ovr) {
  ScopeMap names = ovr.scope;
  for (const auto& p : ovr.writer->params) names.try_emplace(p.name, 0);
  if (IsConstantWholeValue(ovr.val_expr, names)) return true;
  ReportNonConstantDefparam(diag, ovr.loc);
  return false;
}

static bool SetWholeAggregateDefparamValue(DiagEngine& diag,
                                           RtlirParamDecl& param,
                                           const DefparamOverride& ovr,
                                           const DefparamAppliedRecord& rec) {
  if (!DefparamOverrideAllowed(diag, &param, ovr.val_expr, ovr.loc) ||
      !WholeValueIsConstant(diag, ovr)) {
    rec.applied.insert(rec.key);
    return false;
  }
  param.override_expr = ovr.val_expr;
  return true;
}

static bool SetDefparamValue(DiagEngine& diag, RtlirParamDecl& param,
                             const DefparamOverride& ovr,
                             const DefparamAppliedRecord& rec) {
  if (ovr.whole) {
    if (!SetWholeAggregateDefparamValue(diag, param, ovr, rec)) return false;
  } else {
    auto value = EvalDefparamOverride(diag, ovr, rec);
    if (!value) return false;
    param.resolved_value = *value;
    ApplyOverrideRealness(param, RealOverrideValue(ovr.val_expr, ovr.scope));
    param.override_expr = DefparamOverrideExpr(ovr.val_expr);
  }
  param.is_resolved = true;
  param.from_override = true;
  return true;
}

void Elaborator::ApplyDefparamSite(RtlirModule* mod, const DefparamSite& site,
                                   const ScopeMap& scope) {
  for (size_t idx = 0; idx < site.item->defparam_assigns.size(); ++idx) {
    auto key = std::make_tuple(mod, site.item, idx, site.prefix);
    if (applied_defparams_.count(key)) continue;
    const auto& [path_expr, val_expr] = site.item->defparam_assigns[idx];
    HierPath path;
    if (!CollectPathSteps(path_expr, scope, path)) continue;
    DefparamTopRooted rooted{mod, path, mod};
    auto* param =
        ResolveDefparamSteps(mod, path, site.path, &rooted.target_mod);
    if (param == nullptr && site.path.empty()) {
      param = ResolveDefparamFromTop(path, rooted);
    }
    if (!param) {
      BlockParamDefparam block{val_expr, scope, site.item->loc, diag_, arena_};
      if (ApplyBlockParamDefparam(mod, site.path, path, block)) {
        applied_defparams_.insert(key);
      }
      continue;
    }
    RtlirModule* target_mod = rooted.target_mod;
    const TypedefMap kTargetTypes =
        ModuleTypedefTable(typedefs_, FindModule(target_mod->name));
    DefparamOverride ovr{
        param, val_expr,
        scope, site.item->loc,
        mod,   TakesValueWhole(*param, val_expr, kTargetTypes),
    };
    DefparamAppliedRecord rec{applied_defparams_, key};
    if (!SetDefparamValue(diag_, *param, ovr, rec)) continue;
    const TypeShapeTables kTargetTables{kTargetTypes, td_array_dims_,
                                        class_names_};
    ReportOverrideNotAssignable(
        *param, {kTargetTables, BuildParamScope(target_mod), unit_},
        {val_expr, mod, scope, site.prefix}, diag_);
    RecordResolvedHighWords(*param, val_expr, scope);
    param->defparam_value_expr = val_expr;
    param->defparam_value_scope = scope;
    param->defparam_value_scopes = site.scopes;
    param->defparam_module = mod;
    mod->defparams.push_back(
        {target_mod,
         std::string(param->gen_block_prefix) + std::string(param->name),
         val_expr});
    ReplaceStringParamValue(*param, val_expr, arena_);
    RecomputeDependentParams(target_mod);
    applied_defparams_.insert(key);
  }
}

void Elaborator::ApplyDefparams(RtlirModule* mod, const ModuleDecl* decl) {
  ParamRangeRegistryGuard param_range_guard(mod);
  for (const auto& site : CollectDefparamSites(mod, decl)) {
    RegisteredGenScopeGuard gen_scope_guard(site.scopes);
    ScopeMap scope = BuildParamScope(mod, site.scopes);
    for (const auto& [name, value] : site.consts) scope[name] = value;
    ApplyDefparamSite(mod, site, scope);
  }
}

static void CollectLocalGenerateBlockNames(
    const ModuleItem* item, std::unordered_set<std::string_view>& out) {
  switch (item->kind) {
    case ModuleItemKind::kGenerateIf:
      if (!item->name.empty()) out.insert(item->name);
      if (item->gen_else) CollectLocalGenerateBlockNames(item->gen_else, out);
      break;
    case ModuleItemKind::kGenerateCase:
      for (const auto& ci : item->gen_case_items)
        if (!ci.label.empty()) out.insert(ci.label);
      break;
    case ModuleItemKind::kGenerateFor:
      if (!item->name.empty()) out.insert(item->name);
      break;
    default:
      break;
  }
}

static void CheckDefparamItemEarlyAmbiguity(
    DiagEngine& diag, const ModuleItem* item,
    const std::unordered_set<std::string_view>& block_names,
    const std::unordered_set<std::string_view>& top_names) {
  for (const auto& assign : item->defparam_assigns) {
    HierPath parts;
    if (!CollectPathSteps(assign.first, {}, parts)) continue;
    if (parts.size() < 2) continue;
    auto lead = parts.front().name;
    if (block_names.count(lead) && top_names.count(lead)) {
      diag.Error(item->loc,
                 "defparam hierarchical name would resolve differently once "
                 "the like-named generate block is elaborated",
                 Subclause("23.10.4.2"));
    }
  }
}

void Elaborator::CheckEarlyResolutionAmbiguity(
    RtlirModule* mod, const std::unordered_set<std::string_view>& top_names) {
  if (!mod) return;
  const auto* decl = FindModule(mod->name);
  if (!decl) return;

  std::unordered_set<std::string_view> block_names;
  for (const auto* item : decl->items)
    CollectLocalGenerateBlockNames(item, block_names);
  if (block_names.empty()) return;

  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kDefparam) continue;
    CheckDefparamItemEarlyAmbiguity(diag_, item, block_names, top_names);
  }
}

static bool RefersToArrayedInterface(const RtlirModule* parent,
                                     const RtlirModuleInst& child) {
  for (const RtlirPortBinding& binding : child.port_bindings) {
    const Expr* head = binding.connection;
    if (head != nullptr && head->kind == ExprKind::kSelect) head = head->base;
    if (head == nullptr || head->kind != ExprKind::kIdentifier) continue;
    for (const RtlirModuleInst& sibling : parent->children) {
      if (sibling.array.name == head->text) return true;
    }
  }
  return false;
}

static void NoteInstanceBlock(DefparamWriterBlocks& blocks, RtlirModule* parent,
                              const RtlirModuleInst& child) {
  if (child.resolved == nullptr) return;
  if (RefersToArrayedInterface(parent, child)) {
    blocks[child.resolved] = {parent, {}, child.resolved, true};
    return;
  }
  if (!child.array.name.empty()) {
    blocks[child.resolved] = {parent, {}, child.resolved};
    return;
  }
  if (!child.gen_block_path.empty()) {
    blocks[child.resolved] = {parent, child.gen_block_path, nullptr};
    return;
  }
  auto it = blocks.find(parent);
  if (it == blocks.end()) return;
  const DefparamWriterBlock kOuter = it->second;
  blocks[child.resolved] = kOuter;
}

void Elaborator::ApplyDefparamsRecursively(RtlirModule* mod) {
  if (!mod) return;
  IsolateArrayElements(*mod, arena_, *unit_);
  if (auto* decl = FindModule(mod->name)) {
    ApplyDefparams(mod, decl);
  }
  for (auto& child : mod->children) {
    NoteInstanceBlock(defparam_writer_blocks_, mod, child);
    ApplyDefparamsRecursively(child.resolved);
  }
}

static bool StepsEndAtSpecparam(RtlirModule* root, const HierPath& steps) {
  std::vector<PathDescent> descents;
  const RtlirModule* owner = DescendDefparamPath(root, steps, {}, descents);
  return owner != nullptr &&
         DeclaredSpecparamNames(owner->decl).contains(steps.back().name);
}

static bool DefparamTargetsSpecparam(RtlirModule* mod, const HierPath& path,
                                     const std::vector<RtlirModule*>& tops) {
  if (path.empty()) return false;
  if (StepsEndAtSpecparam(mod, path)) return true;
  for (RtlirModule* top : tops) {
    if (path.size() < 2 || top->name != path.front().name) continue;
    if (StepsEndAtSpecparam(top, HierPath(path.begin() + 1, path.end())))
      return true;
  }
  return false;
}

static const RtlirParamDecl* ParamAtPath(RtlirModule* root,
                                         const HierPath& path) {
  std::vector<PathDescent> descents;
  DefparamPathEnd reach = WalkDefparamPath(root, path, {}, descents);
  std::string block_prefix;
  for (const HierStep& block : reach.blocks) {
    block_prefix += std::format("{}_", block.name);
    if (block.has_index) block_prefix += std::format("{}_", block.index);
  }
  for (const auto& p : reach.mod->params) {
    if (p.gen_block_prefix == block_prefix && p.name == path.back().name)
      return &p;
  }
  return nullptr;
}

const RtlirParamDecl* Elaborator::ParamAtPathFromAnyRoot(RtlirModule* mod,
                                                         const HierPath& path) {
  if (const RtlirParamDecl* p = ParamAtPath(mod, path)) return p;
  for (RtlirModule* top : defparam_top_roots_) {
    if (path.size() < 2 || top->name != path.front().name) continue;
    if (const RtlirParamDecl* p =
            ParamAtPath(top, HierPath(path.begin() + 1, path.end())))
      return p;
  }
  return nullptr;
}

const RtlirParamDecl* Elaborator::ParamOfWhichPathNamesAPart(
    RtlirModule* mod, const HierPath& path) {
  for (size_t len = 1; len < path.size(); ++len) {
    HierPath whole(path.begin(),
                   path.begin() + static_cast<std::ptrdiff_t>(len));
    if (const RtlirParamDecl* p = ParamAtPathFromAnyRoot(mod, whole)) return p;
  }
  return nullptr;
}

bool Elaborator::ReportUnappliedDefparamPath(RtlirModule* mod, SourceLoc loc,
                                             const HierPath& path) {
  DefparamTopRooted any{nullptr, path, mod};
  if (ResolveDefparamSteps(mod, path, {}) != nullptr ||
      ResolveDefparamFromTop(path, any) != nullptr) {
    auto block = defparam_writer_blocks_.find(mod);
    if (block != defparam_writer_blocks_.end() &&
        block->second.arrayed_interface) {
      diag_.Error(loc,
                  "defparam inside an instance whose port actuals refer to "
                  "an arrayed interface reaches a parameter outside that "
                  "instance",
                  Subclause("25.3"));
      return true;
    }
    diag_.Error(loc,
                "defparam inside a generate block or an array of instances "
                "reaches a parameter outside that hierarchy",
                Subclause("23.10.1"));
    return true;
  }
  if (const RtlirParamDecl* whole = ParamOfWhichPathNamesAPart(mod, path)) {
    diag_.Error(loc,
                std::format("defparam names a part of parameter '{}', which "
                            "is overridden only as a whole",
                            whole->name),
                Subclause("6.20.2"));
    return true;
  }
  if (!DefparamTargetsSpecparam(mod, path, defparam_top_roots_)) return false;
  diag_.Error(
      loc,
      std::format("defparam cannot override specparam '{}'", path.back().name),
      Subclause("6.20.5"));
  return true;
}

void Elaborator::ReportUnresolvedDefparamSite(RtlirModule* mod,
                                              const DefparamSite& site,
                                              const ScopeMap& mod_scope) {
  ScopeMap scope = mod_scope;
  for (const auto& [name, value] : site.consts) scope[name] = value;
  for (size_t idx = 0; idx < site.item->defparam_assigns.size(); ++idx) {
    auto key = std::make_tuple(mod, site.item, idx, site.prefix);
    if (applied_defparams_.count(key)) continue;
    const Expr* path_expr = site.item->defparam_assigns[idx].first;
    HierPath path;
    if (CollectPathSteps(path_expr, scope, path) &&
        ReportUnappliedDefparamPath(mod, site.item->loc, path)) {
      continue;
    }
    diag_.Warning(site.item->loc, "defparam target not found",
                  Subclause("23.10.1"));
  }
}

void Elaborator::ReportUnresolvedDefparams(RtlirModule* mod,
                                           const ModuleDecl* decl) {
  ParamRangeRegistryGuard param_range_guard(mod);
  for (const auto& site : CollectDefparamSites(mod, decl)) {
    RegisteredGenScopeGuard gen_scope_guard(site.scopes);
    ReportUnresolvedDefparamSite(mod, site, BuildParamScope(mod, site.scopes));
  }
}

void Elaborator::WarnUnresolvedDefparams(RtlirModule* mod) {
  if (!mod) return;
  if (auto* decl = FindModule(mod->name)) {
    ReportUnresolvedDefparams(mod, decl);
  }
  for (auto& child : mod->children) {
    WarnUnresolvedDefparams(child.resolved);
  }
}

}  // namespace delta
