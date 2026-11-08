#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <format>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/packed_range.h"
#include "common/source_loc.h"
#include "elaborator/checker_instance_binding.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_child_type_params.h"
#include "elaborator/elaborator_gen_block_interfaces.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_items_params.h"
#include "elaborator/elaborator_module_inst_internal.h"
#include "elaborator/elaborator_port_binding_internal.h"
#include "elaborator/implication_operator_rules.h"
#include "elaborator/interconnect_uses.h"
#include "elaborator/property_instance.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "elaborator/type_eval.h"
#include "elaborator/uwire_drivers.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/expr_substitute.h"

namespace delta {

static std::vector<DataType> OverrideSpecializationArgs(
    const Expr* name, const CompilationUnit* unit, DiagEngine& diag,
    SourceLoc loc) {
  std::vector<DataType> args;
  args.reserve(name->elements.size());
  for (size_t i = 0; i < name->elements.size(); ++i) {
    DataType arg =
        TypeParamOverrideToDataType(name->elements[i], unit, diag, loc);
    if (i < name->arg_names.size()) arg.param_arg_name = name->arg_names[i];
    args.push_back(arg);
  }
  return args;
}

static void FillDefaultSpecializationArgs(std::vector<DataType>& args,
                                          const ClassDecl* cls) {
  if (!args.empty()) return;
  args = cls->param_types;
}

static DataType ClassScopedOverrideToDataType(const Expr* expr,
                                              const CompilationUnit* unit,
                                              DiagEngine& diag, SourceLoc loc) {
  DataType dt;
  if (expr->lhs == nullptr || expr->lhs->kind != ExprKind::kIdentifier) {
    return dt;
  }
  if (expr->rhs == nullptr || expr->rhs->kind != ExprKind::kIdentifier) {
    return dt;
  }
  if (expr->lhs->has_param_spec) {
    const auto* cls = FindClassDecl(expr->lhs->text, unit);
    if (cls == nullptr) return dt;
    dt.kind = DataTypeKind::kNamed;
    dt.scope_name = expr->lhs->text;
    dt.type_name = expr->rhs->text;
    dt.type_params = OverrideSpecializationArgs(expr->lhs, unit, diag, loc);
    FillDefaultSpecializationArgs(dt.type_params, cls);
    if (!ResolveParameterizedType(dt, unit, diag, loc)) return DataType{};
    return dt;
  }
  const DataType* resolved =
      FindClassScopedTypedefType(expr->lhs->text, expr->rhs->text, unit);
  if (resolved == nullptr) {
    dt.kind = DataTypeKind::kNamed;
    dt.scope_name = expr->lhs->text;
    dt.type_name = expr->rhs->text;
    return dt;
  }
  dt = *resolved;
  dt.type_ref_expr = nullptr;
  return dt;
}

static bool IsPackedDimSelect(const Expr* expr) {
  return expr != nullptr && expr->kind == ExprKind::kSelect &&
         expr->index != nullptr && expr->index_end != nullptr &&
         !expr->is_part_select_plus && !expr->is_part_select_minus;
}

static const Expr* PeelPackedDimSelects(const Expr* expr,
                                        std::vector<const Expr*>& sels) {
  while (IsPackedDimSelect(expr)) {
    sels.push_back(expr);
    expr = expr->base;
  }
  return expr;
}

static void PrependWrittenPackedDims(DataType& dt,
                                     const std::vector<const Expr*>& sels) {
  if (sels.empty()) return;
  std::vector<std::pair<Expr*, Expr*>> dims;
  dims.reserve(sels.size() + 1 + dt.extra_packed_dims.size());
  for (size_t n = sels.size(); n > 0; --n) {
    dims.push_back({sels[n - 1]->index, sels[n - 1]->index_end});
  }
  if (dt.packed_dim_left != nullptr) {
    dims.push_back({dt.packed_dim_left, dt.packed_dim_right});
  }
  dims.insert(dims.end(), dt.extra_packed_dims.begin(),
              dt.extra_packed_dims.end());
  dt.packed_dim_left = dims.front().first;
  dt.packed_dim_right = dims.front().second;
  dt.extra_packed_dims.assign(dims.begin() + 1, dims.end());
}

static DataType OverrideHeadToDataType(const Expr* head,
                                       const CompilationUnit* unit,
                                       DiagEngine& diag, SourceLoc loc) {
  if (head == nullptr) return DataType{};
  if (head->kind == ExprKind::kTypeRef && head->type_value != nullptr) {
    return *head->type_value;
  }
  if (head->kind == ExprKind::kIdentifier) {
    DataType dt = TypeNameToDataType(head->text);
    if (head->has_param_spec) {
      dt.type_params = OverrideSpecializationArgs(head, unit, diag, loc);
    }
    return dt;
  }
  if (head->kind == ExprKind::kMemberAccess && head->is_scope_resolution) {
    return ClassScopedOverrideToDataType(head, unit, diag, loc);
  }
  return DataType{};
}

DataType TypeParamOverrideToDataType(const Expr* expr,
                                     const CompilationUnit* unit,
                                     DiagEngine& diag, SourceLoc loc) {
  std::vector<const Expr*> sels;
  const Expr* head = PeelPackedDimSelects(expr, sels);
  DataType dt = OverrideHeadToDataType(head, unit, diag, loc);
  if (dt.kind == DataTypeKind::kImplicit) return dt;
  PrependWrittenPackedDims(dt, sels);
  return dt;
}

static uint32_t EvalInstDimSize(const Expr* left, const Expr* right,
                                const ScopeMap& scope) {
  if (left && right) {
    auto lv = ConstEvalInt(left, scope);
    auto rv = ConstEvalInt(right, scope);
    if (lv && rv) return static_cast<uint32_t>(std::abs(*lv - *rv) + 1);
  } else if (left) {
    auto v = ConstEvalInt(left, scope);
    if (v && *v > 0) return static_cast<uint32_t>(*v);
  }
  return 0;
}

namespace {

void ResolvePositionalInstParams(const ModuleItem* item,
                                 const ModuleDecl* child_decl,
                                 const ScopeMap& parent_scope,
                                 Elaborator::ParamList& child_params,
                                 DiagEngine& diag) {
  const std::vector<std::string_view> kTargets =
      OverridableParamNames(child_decl);
  if (item->inst_params.size() > kTargets.size()) {
    diag.Error(item->loc,
               std::format("too many positional parameter overrides for module "
                           "'{}': {} provided, {} allowed",
                           item->inst_module, item->inst_params.size(),
                           kTargets.size()),
               Subclause("23.10.2.1"));
  }
  size_t n = std::min(item->inst_params.size(), kTargets.size());
  for (size_t i = 0; i < n; ++i) {
    auto* pexpr = item->inst_params[i].second;
    if (!pexpr) continue;
    PushInstParamAssignment(child_decl, kTargets[i], pexpr, parent_scope,
                            child_params);
  }
}

void ResolveNamedInstParams(const ModuleItem* item,
                            const ModuleDecl* child_decl,
                            const ScopeMap& parent_scope,
                            Elaborator::ParamList& child_params,
                            DiagEngine& diag) {
  const std::vector<std::string_view> kNames =
      OverridableParamNames(child_decl);
  const std::unordered_set<std::string_view> kOverridable(kNames.begin(),
                                                          kNames.end());
  for (const auto& [pname, pexpr] : item->inst_params) {
    if (kOverridable.count(pname) == 0) {
      diag.Error(item->loc,
                 std::format("module '{}' has no parameter '{}'",
                             item->inst_module, pname),
                 Subclause("23.10.2.2"));
      continue;
    }
    if (!pexpr) continue;
    PushInstParamAssignment(child_decl, pname, pexpr, parent_scope,
                            child_params);
  }
}

void MarkConfigLockedParams(
    RtlirModuleInst& inst, const std::vector<std::string_view>& config_locked) {
  if (!inst.resolved) return;
  for (auto pname : config_locked) {
    for (auto& p : inst.resolved->params) {
      if (p.name == pname) {
        p.config_locked = true;
        break;
      }
    }
  }
}

uint32_t ComputeInstDimSizes(const ModuleItem* item, const ScopeMap& scope,
                             std::vector<uint32_t>& inst_dim_sizes) {
  uint32_t total_instances = 1;
  for (const auto& [left, right] : item->inst_dims) {
    uint32_t sz = EvalInstDimSize(left, right, scope);
    if (sz > 0) {
      inst_dim_sizes.push_back(sz);
      total_instances *= sz;
    }
  }
  return total_instances;
}

bool InstUsesPositionalParams(const ModuleItem* item) {
  for (const auto& [pname, pexpr] : item->inst_params) {
    if (pname.empty() && pexpr) return true;
  }
  return false;
}

void ReportUnknownModule(const ModuleItem* item, DiagEngine& diag) {
  if (item->inst_scope.empty())
    diag.Error(item->loc, std::format("unknown module '{}'", item->inst_module),
               Subclause("23.3.2"));
  else
    diag.Error(item->loc,
               std::format("unknown module '{}::{}'", item->inst_scope,
                           item->inst_module),
               Subclause("23.3.2"));
}

using VarArrayInfoMap =
    std::unordered_map<std::string_view, Elaborator::VarArrayInfo>;

struct InstArrayDistribCtx {
  Arena& arena;
  const RtlirModule* parent_mod;
  const VarArrayInfoMap& var_array_info;
  const ScopeMap& parent_scope;
};

Expr* MakeIntLitExpr(Arena& arena, uint64_t v) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIntegerLiteral;
  e->int_val = v;
  return e;
}

Expr* MakeElementSelectExpr(Arena& arena, Expr* base, uint32_t idx) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kSelect;
  e->base = base;
  e->index = MakeIntLitExpr(arena, idx);
  return e;
}

Expr* MakePartSelectPlusExpr(Arena& arena, Expr* base, int64_t base_index,
                             uint32_t width) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kSelect;
  e->base = base;
  e->index = MakeIntLitExpr(arena, static_cast<uint64_t>(base_index));
  e->index_end = MakeIntLitExpr(arena, width);
  e->is_part_select_plus = true;
  return e;
}

int64_t ConnPartSelectBase(const InstArrayDistribCtx& ctx,
                           const RtlirPortBinding& binding, uint32_t position,
                           uint32_t total) {
  const Expr* conn = binding.connection;
  uint32_t port_width = binding.width;
  PackedRange range =
      (conn->kind == ExprKind::kIdentifier)
          ? SignalDeclaredRange(conn->text, ctx.parent_mod, ctx.parent_scope)
          : PackedRange::Implicit(port_width * total);
  return range.PlusSelectBase(static_cast<int64_t>(position) * port_width,
                              port_width);
}

uint32_t ConcatConnWidth(const Expr* conn, const RtlirModule* mod) {
  uint32_t w = 0;
  for (const Expr* el : conn->elements) {
    if (!el || el->kind != ExprKind::kIdentifier) return 0;
    w += FindSignalWidth(el->text, mod);
  }
  return w;
}

bool ConcatElementsUniform(const Expr* conn, uint32_t total,
                           uint32_t port_width, const RtlirModule* mod) {
  if (conn->elements.size() != total) return false;
  for (const Expr* el : conn->elements) {
    if (!el || el->kind != ExprKind::kIdentifier) return false;
    if (FindSignalWidth(el->text, mod) != port_width) return false;
  }
  return true;
}

std::vector<int64_t> FromLeftOffsets(const std::vector<InstArrayDim>& dims,
                                     uint32_t position) {
  std::vector<int64_t> from_left(dims.size());
  int64_t rest = position;
  for (std::size_t d = dims.size(); d-- > 0;) {
    const int64_t kSize = dims[d].Size();
    from_left[d] = kSize - 1 - rest % kSize;
    rest /= kSize;
  }
  return from_left;
}

std::optional<std::vector<int64_t>> UnpackedElementForInstance(
    const InstArrayDistribCtx& ctx, std::string_view name,
    const std::vector<int64_t>& from_left) {
  auto it = ctx.var_array_info.find(name);
  if (it != ctx.var_array_info.end() && it->second.num_unpacked_dims > 0) {
    std::vector<int64_t> indices = from_left;
    const auto& declared = it->second.declared_dims;
    for (std::size_t d = 0; d < indices.size() && d < declared.size(); ++d) {
      indices[d] =
          InstArrayDim{declared[d].left, declared[d].right}.IndexFromLeft(
              from_left[d]);
    }
    return indices;
  }
  for (const auto& net : ctx.parent_mod->nets) {
    if (net.name == name && net.num_unpacked_dims > 0) return from_left;
  }
  return std::nullopt;
}

Expr* DistributeInstanceConnection(const InstArrayDistribCtx& ctx,
                                   const RtlirPortBinding& binding,
                                   uint32_t position, uint32_t total,
                                   const std::vector<int64_t>& from_left) {
  Expr* conn = binding.connection;
  uint32_t port_width = binding.width;
  if (!conn || port_width == 0 || total < 2) return conn;

  if (conn->kind == ExprKind::kIdentifier) {
    if (auto indices = UnpackedElementForInstance(ctx, conn->text, from_left)) {
      Expr* element = conn;
      for (const int64_t kIndex : *indices) {
        element = MakeElementSelectExpr(ctx.arena, element,
                                        static_cast<uint32_t>(kIndex));
      }
      return element;
    }
    if (FindSignalWidth(conn->text, ctx.parent_mod) == port_width * total) {
      return MakePartSelectPlusExpr(
          ctx.arena, conn, ConnPartSelectBase(ctx, binding, position, total),
          port_width);
    }
    return conn;
  }

  if (conn->kind == ExprKind::kConcatenation &&
      ConcatConnWidth(conn, ctx.parent_mod) == port_width * total) {
    if (ConcatElementsUniform(conn, total, port_width, ctx.parent_mod)) {
      return conn->elements[total - 1 - position];
    }
    return MakePartSelectPlusExpr(
        ctx.arena, conn, ConnPartSelectBase(ctx, binding, position, total),
        port_width);
  }
  return conn;
}

void PushInstanceArray(const InstArrayDistribCtx& ctx, RtlirModule* mod,
                       const RtlirModuleInst& base,
                       const std::vector<InstArrayDim>& dims) {
  int64_t total = 1;
  for (const InstArrayDim& dim : dims) total *= dim.Size();
  InstArrayElement array;
  array.name = base.simple_inst_name;
  array.left = dims.front().left;
  array.right = dims.front().right;
  array.dims = dims;
  for (const RtlirPortBinding& b : base.port_bindings) {
    array.connections.push_back(b.unconnected ? nullptr : b.connection);
  }
  for (uint32_t p = 0; p < total; ++p) {
    const std::vector<int64_t> kFromLeft = FromLeftOffsets(dims, p);
    RtlirModuleInst copy = base;
    copy.array = array;
    std::string name(base.inst_name);
    for (std::size_t d = 0; d < dims.size(); ++d) {
      copy.array.indices.push_back(dims[d].IndexFromLeft(kFromLeft[d]));
      name += std::format("[{}]", copy.array.indices.back());
    }
    copy.array.index = copy.array.indices.front();
    auto* buf = ctx.arena.AllocString(name.c_str(), name.size());
    copy.inst_name = std::string_view(buf, name.size());
    for (auto& b : copy.port_bindings) {
      b.connection = DistributeInstanceConnection(
          ctx, b, p, static_cast<uint32_t>(total), kFromLeft);
    }
    mod->children.push_back(std::move(copy));
  }
}

std::vector<InstArrayDim> InstanceArrayDims(const ModuleItem* item,
                                            const ScopeMap& scope) {
  std::vector<InstArrayDim> dims;
  for (const auto& [left_expr, right_expr] : item->inst_dims) {
    const std::optional<int64_t> kLeft = ConstEvalInt(left_expr, scope);
    if (!kLeft) return {};
    if (right_expr == nullptr) {
      if (*kLeft < 1) return {};
      dims.push_back({0, *kLeft - 1});
      continue;
    }
    const std::optional<int64_t> kRight = ConstEvalInt(right_expr, scope);
    if (!kRight) return {};
    dims.push_back({*kLeft, *kRight});
  }
  return dims;
}

void AppendModuleInstOrArray(const InstArrayDistribCtx& ctx, RtlirModule* mod,
                             const RtlirModuleInst& inst,
                             const ModuleItem* item, const ScopeMap& scope) {
  const std::vector<InstArrayDim> kDims = InstanceArrayDims(item, scope);
  if (kDims.empty()) {
    mod->children.push_back(inst);
  } else {
    PushInstanceArray(ctx, mod, inst, kDims);
  }
}

}  // namespace

void ResolveInstParams(const ModuleItem* item, const ModuleDecl* child_decl,
                       const ScopeMap& parent_scope,
                       Elaborator::ParamList& child_params, DiagEngine& diag) {
  if (InstUsesPositionalParams(item)) {
    ResolvePositionalInstParams(item, child_decl, parent_scope, child_params,
                                diag);
  } else {
    ResolveNamedInstParams(item, child_decl, parent_scope, child_params, diag);
  }
}

static void BindCheckerTreeActuals(
    RtlirModuleInst& inst,
    const std::unordered_map<const RtlirModule*, ActualsByFormal>& trees) {
  auto found = trees.find(inst.resolved);
  if (found == trees.end()) return;
  for (RtlirPortBinding& binding : inst.port_bindings) {
    auto actual = found->second.find(binding.port_name);
    if (actual != found->second.end()) binding.connection = actual->second;
  }
}

void Elaborator::ElaborateModuleInst(ModuleItem* item, RtlirModule* mod) {
  std::string_view scoped_inst_name =
      item->inst_name.empty() ? item->inst_name : ScopedName(item->inst_name);
  DeclareInModuleNameSpace(item->inst_name, item->loc);
  ReportInterconnectInInstance(*item, interconnect_names_, diag_);
  RtlirModuleInst inst;
  inst.module_name = item->inst_module;
  inst.inst_name = scoped_inst_name;
  inst.simple_inst_name = item->inst_name;

  std::string saved_inst_path = current_inst_path_;
  if (!current_inst_path_.empty()) current_inst_path_.push_back('.');
  current_inst_path_.append(scoped_inst_name.data(), scoped_inst_name.size());
  std::string saved_config_path = std::exchange(
      config_inst_path_,
      HierInstancePath(config_inst_path_, gen_block_path_, item->inst_name));

  inst.is_nested_decl = nested_module_decls_.find(item->inst_module) !=
                        nested_module_decls_.end();
  auto* child_decl = FindModuleInScope(item->inst_module);
  if (!child_decl) child_decl = PackageCheckerNamedBy(item, mod, unit_);
  if (!child_decl) {
    if (!ReportConfigRuleBindingNothing(unit_, item, diag_))
      ReportUnknownModule(item, diag_);
    mod->children.push_back(inst);
    current_inst_path_ = std::move(saved_inst_path);
    config_inst_path_ = std::move(saved_config_path);
    return;
  }

  EnterGenBlockInstance(inst, child_decl,
                        {gen_block_path_, gen_loop_consts_, gen_prefix_scopes_},
                        interface_inst_types_);
  auto parent_scope = BuildParamScope(mod);
  const UnitUwireCounts kUwireCounts =
      CountUnitUwireDrivers(unit_uwire_drivers_);
  ElaborateChildInstance(inst, item, child_decl, mod, parent_scope);
  BindPorts(inst, item, mod, child_decl);
  BindCheckerTreeActuals(inst, checker_tree_actuals_);

  std::vector<uint32_t> inst_dim_sizes;
  uint32_t total_instances =
      ComputeInstDimSizes(item, parent_scope, inst_dim_sizes);
  RepeatUnitUwireDrivers(unit_uwire_drivers_, kUwireCounts, total_instances,
                         item->loc, diag_);

  if (!item->inst_dims.empty()) {
    ValidateInstanceArrayPorts(inst, item, mod, inst_dim_sizes,
                               total_instances);
  } else {
    ValidateUnpackedArrayPorts(inst, item, mod);
  }

  CheckInstancePorts(inst, item, mod);
  CoerceDrivenInputPorts(inst, mod);
  inst.attrs = ResolveAttributes(item->attrs, diag_, BuildParamScope(mod));
  if (item->inst_range_left && item->inst_range_right &&
      (!ConstEvalInt(item->inst_range_left, parent_scope) ||
       !ConstEvalInt(item->inst_range_right, parent_scope))) {
    diag_.Error(item->loc,
                "instance array range bound must be a constant expression",
                Subclause("28.3.5"));
  }
  InstArrayDistribCtx dctx{arena_, mod, var_array_info_, parent_scope};
  AppendModuleInstOrArray(dctx, mod, inst, item, parent_scope);
  current_inst_path_ = std::move(saved_inst_path);
  config_inst_path_ = std::move(saved_config_path);
}

void Elaborator::ElaborateChildInstance(RtlirModuleInst& inst,
                                        const ModuleItem* item,
                                        ModuleDecl* child_decl,
                                        RtlirModule* mod,
                                        const ScopeMap& parent_scope) {
  RecordCellClauseListBinding(item->inst_module);
  const ConfigDecl* delegated = DelegatedConfigFor(item->inst_module);
  if (delegated != nullptr) EnterDelegatedConfig(delegated);
  auto saved_nested = nested_module_decls_;
  Elaborator::ParamList child_params;
  ResolveInstParams(item, child_decl, parent_scope, child_params, diag_);

  std::vector<std::string_view> config_locked;
  ApplyConfigParamOverrides(item, child_decl, child_params, parent_scope,
                            config_locked);

  auto applied_type_params = ApplyChildTypeParams(
      TypeParamSourcesFor(item, instance_param_overrides_, config_inst_path_),
      child_decl, typedefs_, unit_, diag_);
  ReportChildTypeParamsOutsideRestrictions(
      child_decl, applied_type_params, {typedefs_, unit_, class_names_}, diag_);
  if (inst.is_nested_decl) {
    nested_default_disable_iff_ = mod->default_disable_iff;
    nested_default_clock_ = DefaultClockingEvent(mod);
    pending_enclosing_nested_decls_ = NestedDeclsSeenInside();
    BeginNestedDeclScope(child_decl, CaptureCurrentScopeNames());
  }
  if (child_decl->decl_kind == ModuleDeclKind::kChecker) {
    pending_checker_actuals_ =
        BindCheckerActuals(item, child_decl, parent_scope);
    pending_checker_tree_actuals_ = CheckerTreeActuals(item, child_decl);
  }
  pending_type_param_types_ = std::move(applied_type_params.written);
  inst.resolved = ElaborateModule(child_decl, child_params);
  RestoreChildTypeParams(typedefs_, applied_type_params.saved);
  nested_module_decls_ = std::move(saved_nested);
  MarkConfigLockedParams(inst, config_locked);
  if (delegated != nullptr) LeaveDelegatedConfig();
}

void Elaborator::CheckInstancePorts(RtlirModuleInst& inst,
                                    const ModuleItem* item, RtlirModule* mod) {
  CheckPortCoercion(inst, item->loc);
  ReportActualsOnlyACheckerTakes(inst, item, diag_);
  if (!inst.resolved->is_checker) {
    for (const auto& port : item->inst_ports) {
      ReportImplicationOperators(port.second, diag_);
    }
  }
  CheckUwirePortMerge(inst, item, mod);
  CheckInterconnectPortMerge(inst, item, mod);
}

}  // namespace delta
