#include "simulator/lowerer_register.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/packed_range.h"
#include "common/types.h"
#include "elaborator/const_eval.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "elaborator/type_eval.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/class_specialization.h"
#include "simulator/contassign_delay.h"
#include "simulator/covergroup_instance.h"
#include "simulator/dpi_formal_type.h"
#include "simulator/dpi_runtime.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/expr_walk.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/nettype_resolution.h"
#include "simulator/sequence_monitor.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/stmt_exec.h"
#include "simulator/unit_scope_items.h"
#include "simulator/variable.h"

namespace delta {

static std::optional<PackedRange> PackedElementRange(const DataType& dt,
                                                     SimContext& ctx,
                                                     Arena& arena) {
  if (dt.kind == DataTypeKind::kNamed) return ctx.FindTypeRange(dt.type_name);
  if (dt.kind != DataTypeKind::kEnum || dt.packed_dim_left == nullptr) {
    return std::nullopt;
  }
  return PackedRange{
      SelectBoundValue(EvalExpr(dt.packed_dim_left, ctx, arena)),
      SelectBoundValue(EvalExpr(dt.packed_dim_right, ctx, arena))};
}

static std::vector<std::pair<Expr*, Expr*>> PackedDimsOf(const DataType& dt) {
  std::vector<std::pair<Expr*, Expr*>> dims = dt.enum_array_dims;
  if (dims.empty() && dt.packed_dim_left != nullptr) {
    dims.emplace_back(dt.packed_dim_left, dt.packed_dim_right);
    dims.insert(dims.end(), dt.extra_packed_dims.begin(),
                dt.extra_packed_dims.end());
  }
  return dims;
}

static bool HasPackedElement(const DataType& dt) {
  return dt.kind == DataTypeKind::kNamed || dt.kind == DataTypeKind::kStruct ||
         dt.kind == DataTypeKind::kUnion || !dt.enum_array_dims.empty();
}

void RecordPackedRange(const DataType* dt, Variable* v, SimContext& ctx,
                       Arena& arena) {
  if (dt != nullptr) dt = ctx.PackedTypeBehind(*dt);
  if (dt == nullptr) return;
  const std::vector<std::pair<Expr*, Expr*>> kDims = PackedDimsOf(*dt);
  if (kDims.empty()) return;
  auto eval = [&](const Expr* e) {
    return SelectBoundValue(EvalExpr(e, ctx, arena));
  };
  auto span = [](int64_t l, int64_t r) {
    return static_cast<uint64_t>((l >= r ? l - r : r - l) + 1);
  };
  uint64_t stride = 1;
  std::vector<PackedRange> inner;
  for (size_t i = 1; i < kDims.size(); ++i) {
    inner.push_back({eval(kDims[i].first), eval(kDims[i].second)});
    stride *= span(inner.back().left, inner.back().right);
  }
  PackedRange range{eval(kDims[0].first), eval(kDims[0].second)};
  uint64_t outer = span(range.left, range.right) * stride;
  if (HasPackedElement(*dt) && outer > 0 && v->value.width > outer &&
      v->value.width % outer == 0) {
    auto named = static_cast<uint32_t>(v->value.width / outer);
    std::optional<PackedRange> declared = PackedElementRange(*dt, ctx, arena);
    inner.push_back(declared && span(declared->left, declared->right) == named
                        ? *declared
                        : PackedRange::Implicit(named));
    stride *= named;
  }
  if (stride > 1) {
    v->packed_elem_width = static_cast<uint32_t>(stride);
    v->inner_packed_dims = std::move(inner);
  }
  if (span(range.left, range.right) * stride != v->value.width) return;
  v->packed_range = range;
  v->has_packed_range = true;
  if (dt->kind == DataTypeKind::kNamed && DeclaredTypeIsSigned(*dt, ctx))
    v->signed_elem_depth = kDims.size() - 1;
}

static bool EveryNameHasStorage(const Expr* expr, SimContext& ctx) {
  std::vector<const Expr*> scoped;
  ForEachEvaluatedSubExpr(expr, [&](const Expr* e) {
    if (e->kind == ExprKind::kMemberAccess && e->is_scope_resolution) {
      scoped.push_back(e->lhs);
      scoped.push_back(e->rhs);
    }
  });
  bool all = true;
  ForEachEvaluatedSubExpr(expr, [&](const Expr* e) {
    if (e->kind == ExprKind::kCall) all = false;
    if (e->kind != ExprKind::kIdentifier) return;
    if (std::find(scoped.begin(), scoped.end(), e) != scoped.end()) return;
    if (ctx.FindVariable(e->text) == nullptr) all = false;
  });
  return all;
}

static bool HoldsXZLiteral(const Expr* expr) {
  bool found = false;
  ForEachEvaluatedSubExpr(expr, [&](const Expr* e) {
    if (e->kind != ExprKind::kUnbasedUnsizedLiteral &&
        e->kind != ExprKind::kIntegerLiteral)
      return;
    std::string_view text = e->text;
    auto tick = text.find('\'');
    if (tick == std::string_view::npos) return;
    if (text.find_first_of("xXzZ?", tick + 1) != std::string_view::npos)
      found = true;
  });
  return found;
}

static bool NamesAnUnknownValue(const Expr* expr, SimContext& ctx) {
  bool found = false;
  ForEachEvaluatedSubExpr(expr, [&](const Expr* e) {
    if (e->kind != ExprKind::kIdentifier) return;
    const Variable* v = ctx.FindVariable(e->text);
    if (v != nullptr && HasUnknownBits(v->value)) found = true;
  });
  return found;
}

const DataType* ParamValueType(const RtlirParamDecl& param) {
  return param.type_param_actual != nullptr ? param.type_param_actual
                                            : param.decl_type;
}

void ReevaluateParamValue(const RtlirParamDecl& param, Variable* var,
                          SimContext& ctx, Arena& arena) {
  uint32_t width = var->value.width;
  if (param.from_override && param.override_expr == nullptr) return;
  const Expr* expr = param.override_expr != nullptr ? param.override_expr
                                                    : param.default_value;
  if (expr == nullptr) return;
  std::string own = ctx.ActiveInstancePrefix();
  if (param.override_expr != nullptr)
    ctx.SetLoweringInstancePrefix(ctx.InstantiatingPrefix(own));
  bool folded = width <= 64 && param.is_resolved && !HoldsXZLiteral(expr) &&
                !NamesAnUnknownValue(expr, ctx);
  if (!folded && EveryNameHasStorage(expr, ctx)) {
    Logic4Vec value = EvalExpr(expr, ctx, arena, width);
    var->value = OwnRhsWords(ResizeToWidth(value, width, arena), arena);
    const DataType* type = ParamValueType(param);
    if (type != nullptr && !DeclaredTypeIs4State(*type, ctx))
      CoerceTo2State(var->value);
  }
  ctx.SetLoweringInstancePrefix(own);
}

bool UnfoldedParamEvaluable(const RtlirParamDecl& param, SimContext& ctx) {
  const Expr* expr = param.override_expr != nullptr ? param.override_expr
                                                    : param.default_value;
  return !param.is_type_param && expr != nullptr &&
         EveryNameHasStorage(expr, ctx);
}

uint64_t NetDecayTicks(const RtlirNet& net, const TimeScale& scale,
                       TimeUnit precision) {
  if (net.decay_is_real) {
    return RealDelayToTicks(net.decay_real, scale, precision);
  }
  return DelayToTicks(net.decay_ticks, scale, precision);
}

Net* CreateNetStorage(std::string_view name, const RtlirNet& net,
                      const TimeScale& scale, SimContext& ctx, Arena& arena) {
  auto* created = ctx.CreateNet(
      name, net.net_type, net.width,
      NetSpec{net.charge_strength,
              NetDecayTicks(net, scale, ctx.GlobalPrecision()), net.decays,
              net.is_user_nettype, net.resolve_func, net.is_signed});
  AttachNettypeResolution(*created, net.resolve_func, ctx);
  created->delay = NetDelayTicks(net, scale, ctx, arena);
  RecordPackedRange(net.dtype, created->resolved, ctx, arena);
  RegisterAggregateLayout(name, net.dtype, net.width, ctx, arena);
  return created;
}

void CreateDeclaredNet(std::string_view name, const RtlirNet& net,
                       const TimeScale& scale, SimContext& ctx, Arena& arena) {
  CreateNetStorage(name, net, scale, ctx, arena);
  CreateNetArrayElements(name, net, scale, ctx, arena);
}

void RegisterModuleNets(const RtlirModule* mod, SimContext& ctx, Arena& arena) {
  for (const auto& net : mod->nets) {
    CreateDeclaredNet(net.name, net, mod->timescale, ctx, arena);
  }
}

bool PortDefaultsToZero(const RtlirPort& port) {
  if (port.type_kind == DataTypeKind::kString ||
      port.type_kind == DataTypeKind::kEvent) {
    return false;
  }
  return !Is4stateType(port.type_kind);
}

static bool CreatePortArrayElements(std::string_view name,
                                    const RtlirPort& port, SimContext& ctx,
                                    Arena& arena) {
  if (port.num_unpacked_dims != 1 || port.unpacked_dims.size() != 1) {
    return false;
  }
  const RtlirUnpackedDim& dim = port.unpacked_dims.front();
  ArrayInfo info;
  info.lo = static_cast<uint32_t>(dim.Low());
  info.size = dim.Size();
  info.elem_width = port.width;
  info.is_descending = dim.left > dim.right;
  info.is_4state = !PortDefaultsToZero(port);
  info.elem_type_kind = port.type_kind;
  info.elem_is_signed = port.is_signed;
  info.elem_type_is_unpacked_array = port.elem_type_is_unpacked_array;
  ctx.RegisterArray(name, info);
  for (uint32_t i = 0; i < info.size; ++i) {
    auto* key = arena.Create<std::string>(std::string(name) + "[" +
                                          std::to_string(info.lo + i) + "]");
    Variable* elem = port.net_type != NetType::kNone
                         ? ctx.CreateNet(*key, port.net_type, port.width,
                                         NetSpec{.is_signed = port.is_signed})
                               ->resolved
                         : ctx.CreateVariable(*key, port.width);
    FillWithX(elem->value);
    if (!info.is_4state) elem->value = MakeLogic4VecVal(arena, port.width, 0);
    elem->is_4state = info.is_4state;
    elem->is_signed = port.is_signed;
    RecordPackedRange(port.dtype, elem, ctx, arena);
  }
  return true;
}

static void MarkRealPort(std::string_view name, const RtlirPort& port,
                         Variable& v, SimContext& ctx) {
  if (port.type_kind != DataTypeKind::kReal &&
      port.type_kind != DataTypeKind::kShortreal &&
      port.type_kind != DataTypeKind::kRealtime)
    return;
  v.is_real = true;
  ctx.RegisterRealVariable(name);
}

void CreatePortVariable(std::string_view name, const RtlirPort& port,
                        SimContext& ctx, Arena& arena) {
  ctx.Vcd().SetVcdPortDirection(name, port.direction);
  if (ctx.FindVariable(name) || ctx.FindArrayInfo(name)) return;
  if (CreatePortArrayElements(name, port, ctx, arena)) return;
  Variable* v = nullptr;
  bool is_net = port.net_type != NetType::kNone;
  if (is_net) {
    v = ctx.CreateNet(name, port.net_type, port.width,
                      NetSpec{.is_signed = port.is_signed})
            ->resolved;
  } else {
    v = ctx.CreateVariable(
        name, port.type_kind == DataTypeKind::kString ? 0 : port.width);
  }
  if (!is_net && PortDefaultsToZero(port))
    v->value = MakeLogic4VecVal(arena, port.width, 0);
  if (port.init_value != nullptr) {
    Logic4Vec init = OwnRhsWords(
        ResizeToWidth(EvalExpr(port.init_value, ctx, arena, port.width),
                      port.width, arena),
        arena);
    if (PortDefaultsToZero(port)) CoerceTo2State(init);
    v->value = init;
  }
  if (port.is_signed) v->is_signed = true;
  MarkRealPort(name, port, *v, ctx);
  if (port.type_kind == DataTypeKind::kString) ctx.RegisterStringVariable(name);
  RecordPackedRange(port.dtype, v, ctx, arena);
  RegisterAggregateLayout(name, port.dtype, port.width, ctx, arena);
  ctx.Vcd().SetVcdVarKind(name, port.type_kind);
}

void RegisterModulePorts(const RtlirModule* mod, SimContext& ctx,
                         Arena& arena) {
  for (const auto& port : mod->ports) CreatePortStorage("", port, ctx, arena);
}

void RegisterModuleSubroutines(const RtlirModule* mod, SimContext& ctx) {
  for (auto* func : mod->function_decls) {
    if (!func->method_class.empty()) continue;
    ctx.RegisterFunction(func->name, func);
  }
}

void RegisterInstanceSubroutines(const RtlirModule* mod,
                                 const std::string& inst_prefix,
                                 SimContext& ctx, Arena& arena) {
  for (auto* func : mod->function_decls) {
    if (!func->method_class.empty()) continue;
    auto* key =
        arena.Create<std::string>(inst_prefix + std::string(func->name));
    ctx.RegisterFunction(*key, func);
    if (func->is_extern && func->is_forkjoin) ctx.DeclareForkjoinTask(*key);
  }
}

std::string GenBlockName(const HierPath& path) {
  std::string name;
  for (const HierStep& step : path) {
    if (!name.empty()) name += '.';
    name += std::string(step.name);
    if (step.has_index) name += "[" + std::to_string(step.index) + "]";
  }
  return name;
}

void RegisterGenBlockSubroutines(const RtlirModule* mod,
                                 const std::string& key_prefix,
                                 const std::string& inst_prefix,
                                 SimContext& ctx, Arena& arena) {
  for (const RtlirGenBlockSubroutine& sub : mod->gen_block_subroutines) {
    bool unnamed = false;
    for (const HierStep& step : sub.gen_block_path)
      unnamed |= step.name.empty();
    if (unnamed) continue;
    auto* key = arena.Create<std::string>(key_prefix +
                                          GenBlockName(sub.gen_block_path) +
                                          "." + std::string(sub.decl->name));
    ctx.RegisterFunction(*key, sub.decl);
    GenBlockSubroutineScope scope;
    scope.inst_prefix = inst_prefix;
    scope.gen_prefixes.assign(sub.gen_block_prefixes.begin(),
                              sub.gen_block_prefixes.end());
    scope.consts = sub.gen_block_consts;
    ctx.RegisterGenBlockSubroutineScope(*key, std::move(scope));
  }
}

static void RegisterPackageScopedItem(const PackageDecl* pkg, ModuleItem* item,
                                      SimContext& ctx, Arena& arena) {
  if (item->kind == ModuleItemKind::kImportDecl) {
    const ImportItem& imp = item->import_item;
    ctx.RegisterPackageImport(pkg->name, imp.package_name,
                              imp.is_wildcard ? "*" : imp.item_name);
    return;
  }
  auto* key = arena.Create<std::string>(std::string(pkg->name) +
                                        "::" + std::string(item->name));
  if (item->kind == ModuleItemKind::kLetDecl ||
      item->kind == ModuleItemKind::kCovergroupDecl) {
    ctx.RegisterLetDecl(*key, item);
    return;
  }
  if (item->kind == ModuleItemKind::kSequenceDecl) {
    ctx.RegisterSequenceDecl(*key, item);
    return;
  }
  if (item->kind == ModuleItemKind::kPropertyDecl) {
    ctx.RegisterPropertyDecl(*key, item);
    return;
  }
  bool is_subroutine = item->kind == ModuleItemKind::kFunctionDecl ||
                       item->kind == ModuleItemKind::kTaskDecl;
  if (!is_subroutine || !item->method_class.empty()) return;
  ctx.RegisterSubroutinePackage(item, pkg->name);
  ctx.RegisterStaticFrameOwner(item, pkg->name);
  ctx.RegisterFunction(*key, item);
}

void RegisterPackageScopedSubroutines(const RtlirDesign* design,
                                      SimContext& ctx, Arena& arena) {
  for (auto* pkg : design->packages) {
    for (auto* item : pkg->items)
      RegisterPackageScopedItem(pkg, item, ctx, arena);
  }
}

static void RegisterDpiImportDecls(const std::vector<ModuleItem*>& decls,
                                   const ScopeMap& scope, SimContext& ctx,
                                   std::string_view unit_scope = {}) {
  DpiRuntime* dpi = nullptr;
  for (const auto* item : decls) {
    if (item->kind != ModuleItemKind::kDpiImport) continue;
    if (dpi == nullptr) dpi = &ctx.AcquireDpiRuntime();
    std::string_view sv_name = item->name;
    if (!unit_scope.empty()) {
      sv_name = *ctx.GetArena().Create<std::string>(
          std::string(unit_scope) + "::" + std::string(item->name));
    }
    if (dpi->HasImport(sv_name)) continue;
    DpiRtFunction func;
    func.sv_name = sv_name;
    func.c_name = item->dpi_c_name.empty() ? item->name : item->dpi_c_name;
    func.return_type = item->return_type.kind;
    func.return_is_unsigned = !item->return_type.is_signed;
    func.is_pure = item->dpi_is_pure;
    func.is_context = item->dpi_is_context;
    func.is_task = item->dpi_is_task;
    func.packed_arg_passing =
        DpiPassingSemanticsOfSpecString(item->dpi_spec_string);
    for (const auto& arg : item->func_args) {
      func.args.push_back(DpiFormalOfArg(arg, scope));
    }
    dpi->RegisterImport(std::move(func));
  }
}

void RegisterModuleDpiImports(const RtlirModule* mod, SimContext& ctx) {
  RegisterDpiImportDecls(mod->dpi_import_decls, DpiParameterScope(*mod), ctx);
}

static void RegisterTypedefItems(const std::vector<ModuleItem*>& items,
                                 std::string_view prefix, SimContext& ctx) {
  for (const ModuleItem* item : items) {
    if (item->kind != ModuleItemKind::kTypedef) continue;
    std::string_view key = item->name;
    if (!prefix.empty()) {
      key = *ctx.GetArena().Create<std::string>(std::string(prefix) +
                                                "::" + std::string(item->name));
    }
    ctx.RegisterTypeDeclaration(key, item);
  }
}

static void RegisterScopeTypedefs(const std::vector<ModuleDecl*>& decls,
                                  SimContext& ctx) {
  for (const ModuleDecl* decl : decls)
    RegisterTypedefItems(decl->items, {}, ctx);
}

static void RegisterTypeDeclarations(const RtlirDesign* design,
                                     SimContext& ctx) {
  const CompilationUnit* unit = design->compilation_unit;
  if (unit == nullptr) return;
  RegisterTypedefItems(unit->cu_items, {}, ctx);
  RegisterUnitCovergroups(unit->cu_items, {}, ctx);
  if (!design->compilation_units.empty()) {
    ForEachUnitScope(design, ctx.GetArena(),
                     [&](const CompilationUnit& own, std::string_view scope) {
                       RegisterTypedefItems(own.cu_items, scope, ctx);
                       RegisterUnitCovergroups(own.cu_items, scope, ctx);
                     });
  }
  for (const PackageDecl* pkg : unit->packages)
    RegisterTypedefItems(pkg->items, pkg->name, ctx);
  RegisterScopeTypedefs(unit->modules, ctx);
  RegisterScopeTypedefs(unit->interfaces, ctx);
  RegisterScopeTypedefs(unit->programs, ctx);
}

void RegisterTypeTargets(const RtlirDesign* design, SimContext& ctx) {
  RegisterTypeDeclarations(design, ctx);
  for (const auto& [alias, target] : design->type_targets)
    ctx.RegisterTypeTarget(alias, target);
}

static ClassTypeInfo* ClassNamedByTypedef(const DataType& target,
                                          const ClassTypeInfo* holder,
                                          SimContext& ctx, Arena& arena) {
  if (target.kind != DataTypeKind::kNamed) return nullptr;
  ClassTypeInfo* generic = nullptr;
  if (!target.scope_name.empty()) {
    generic = ctx.FindClassType(std::string(target.scope_name) +
                                "::" + std::string(target.type_name));
  }
  if (generic == nullptr) generic = ctx.FindClassType(target.type_name);
  if (generic == nullptr) return nullptr;
  ctx.PushMethodClass(holder);
  ClassTypeInfo* spec = SpecializationOf(
      generic, ActualsUnderSpecialization(holder, target.type_params, ctx), ctx,
      arena);
  ctx.PopMethodClass();
  return spec;
}

void RegisterClassScopeTypedefAliases(ClassTypeInfo* info, SimContext& ctx,
                                      Arena& arena) {
  if (info == nullptr || info->decl == nullptr) return;
  for (const ClassMember* member : info->decl->members) {
    if (member->kind != ClassMemberKind::kTypedef ||
        member->typedef_item == nullptr) {
      continue;
    }
    if (!member->typedef_item->unpacked_dims.empty()) continue;
    auto* alias = arena.Create<std::string>(std::string(info->name) +
                                            "::" + std::string(member->name));
    if (ctx.FindClassType(*alias) != nullptr) continue;
    ClassTypeInfo* cls = ClassNamedByTypedef(member->typedef_item->typedef_type,
                                             info, ctx, arena);
    if (cls != nullptr) ctx.RegisterClassType(*alias, cls);
  }
}

static ClassTypeInfo* ClassNamedByDesignTypedef(std::string_view alias,
                                                ClassTypeInfo* target,
                                                SimContext& ctx, Arena& arena) {
  const DataType* declared = ctx.FindTypeDeclaration(alias);
  for (size_t hops = 0;
       declared != nullptr && declared->kind == DataTypeKind::kNamed &&
       declared->type_params.empty() && hops < ctx.TypeDeclarationCount();
       ++hops) {
    declared = ctx.FindTypeDeclaration(declared->type_name);
  }
  if (declared == nullptr || declared->kind != DataTypeKind::kNamed ||
      declared->type_params.empty()) {
    return target;
  }
  return SpecializationOf(target, declared->type_params, ctx, arena);
}

void RegisterClassTypeAliases(const RtlirDesign* design, SimContext& ctx,
                              Arena& arena) {
  for (const auto& [alias, target] : design->type_targets) {
    if (ctx.FindClassType(alias) != nullptr) continue;
    ClassTypeInfo* cls = ctx.FindClassType(target);
    if (cls != nullptr) {
      ctx.RegisterClassType(alias,
                            ClassNamedByDesignTypedef(alias, cls, ctx, arena));
    }
  }
  for (ClassTypeInfo* info : ctx.RegisteredClassTypes())
    RegisterClassScopeTypedefAliases(info, ctx, arena);
}

std::string UnitBuiltinClassKey(const DataType& type) {
  bool std_or_bare = type.scope_name.empty() || type.scope_name == "std";
  bool builtin =
      type.type_name == "process" || type.type_name == "weak_reference";
  if (type.kind != DataTypeKind::kNamed || !std_or_bare || !builtin) return {};
  return std::string(type.type_name);
}

static std::string PackageClassKeyIn(const RtlirDesign* design,
                                     std::string_view pkg,
                                     std::string_view name) {
  for (const auto* p : design->packages) {
    if (p->name != pkg) continue;
    for (const auto* item : p->items) {
      if (item->kind == ModuleItemKind::kClassDecl && item->class_decl &&
          item->class_decl->name == name)
        return std::string(pkg) + "::" + std::string(name);
    }
  }
  return {};
}

static std::string UnitScopeClassKey(const RtlirDesign* design,
                                     std::string_view name) {
  for (const auto* cls : design->cu_class_decls) {
    if (cls->name == name) return std::string(name);
  }
  for (const auto* item : design->compilation_unit->cu_items) {
    if (item->kind != ModuleItemKind::kImportDecl) continue;
    const ImportItem& imp = item->import_item;
    if (!imp.is_wildcard && imp.item_name != name) continue;
    std::string key = PackageClassKeyIn(design, imp.package_name, name);
    if (!key.empty()) return key;
  }
  return {};
}

static std::string UnitClassKey(const RtlirDesign* design,
                                const DataType& type) {
  std::string key = UnitBuiltinClassKey(type);
  if (!key.empty() || type.kind != DataTypeKind::kNamed) return key;
  if (!type.scope_name.empty())
    return PackageClassKeyIn(design, type.scope_name, type.type_name);
  return UnitScopeClassKey(design, type.type_name);
}

void RegisterUnitClassVariables(const RtlirDesign* design, SimContext& ctx,
                                Arena& arena) {
  if (design->compilation_unit == nullptr) return;
  for (const auto* item : design->compilation_unit->cu_items) {
    if (item->kind != ModuleItemKind::kVarDecl) continue;
    std::string key = UnitClassKey(design, item->data_type);
    if (key.empty()) continue;
    ctx.SetVariableClassType(item->name, *arena.Create<std::string>(key));
    RecordClassParamActuals(item->name, key, item->data_type.type_params, ctx);
  }
}

void RegisterDesignScopeDpiImports(const RtlirDesign* design, SimContext& ctx) {
  for (const auto* pkg : design->packages) {
    RegisterDpiImportDecls(pkg->items, ScopeMap{}, ctx);
  }
  if (design->compilation_unit != nullptr) {
    RegisterDpiImportDecls(design->compilation_unit->cu_items, ScopeMap{}, ctx);
  }
  if (design->compilation_units.empty()) return;
  ForEachUnitScope(design, ctx.GetArena(),
                   [&](const CompilationUnit& unit, std::string_view scope) {
                     RegisterDpiImportDecls(unit.cu_items, ScopeMap{}, ctx,
                                            scope);
                   });
}

}  // namespace delta
