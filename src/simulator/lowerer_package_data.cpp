#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/queue_dim.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/eval_function_internal.h"
#include "simulator/eval_mailbox.h"
#include "simulator/eval_semaphore.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer_package_param.h"
#include "simulator/lowerer_register.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/sync_objects.h"
#include "simulator/sync_variable.h"
#include "simulator/unit_scope_items.h"
#include "simulator/unit_scopes.h"
#include "simulator/variable.h"

namespace delta {

static std::string_view PackageSyncObjectType(const ModuleItem* item,
                                              std::string_view key,
                                              const SimContext& ctx) {
  std::string_view name = item->data_type.type_name;
  if (item->kind != ModuleItemKind::kVarDecl ||
      item->data_type.kind != DataTypeKind::kNamed ||
      !ctx.GetVariableClassType(key).empty())
    return {};
  return name == "semaphore" || name == "mailbox" ? name : std::string_view();
}

static bool PackageItemIsHandle(const ModuleItem* item, std::string_view qname,
                                SimContext& ctx) {
  if (item->kind != ModuleItemKind::kVarDecl) return false;
  return !ctx.GetVariableClassType(qname).empty() ||
         !PackageSyncObjectType(item, qname, ctx).empty();
}

static void ShapePackageVariable(const ModuleItem* item, Variable* var,
                                 std::string_view qname, SimContext& ctx,
                                 Arena& arena) {
  const DataType& type = item->data_type;
  var->is_4state =
      DeclaredTypeIs4State(type, ctx) && !PackageItemIsHandle(item, qname, ctx);
  var->is_signed = DeclaredTypeIsSigned(type, ctx);
  var->value.is_signed = var->is_signed;
  var->is_event = type.kind == DataTypeKind::kEvent;
  if (!var->is_4state)
    var->value = MakeLogic4VecVal(arena, var->value.width, 0);
  if (DeclaredTypeIsString(type, ctx)) ctx.RegisterStringVariable(qname);
  bool is_real = DeclaredTypeIsReal(type, ctx);
  var->is_real = is_real;
  if (is_real) ctx.RegisterRealVariable(qname);
}

static bool DeclaresPackageData(const ModuleItem* item) {
  bool is_param = item->kind == ModuleItemKind::kParamDecl;
  bool is_var = item->kind == ModuleItemKind::kVarDecl;
  return is_var || (is_param && item->init_expr);
}

constexpr std::string_view kUnitScope = "$unit";

static std::string PackageDataKey(const ModuleItem* item,
                                  std::string_view pkg) {
  return std::string(pkg) + "." + std::string(item->name);
}

static uint32_t PackageDataWidth(const ModuleItem* item, std::string_view qname,
                                 SimContext& ctx) {
  bool is_var = item->kind == ModuleItemKind::kVarDecl;
  uint32_t width = is_var ? DeclaredTypeWidth(item->data_type, ctx)
                          : DeclaredParamStorageWidth(item, ctx);
  if (width != 0) return width;
  return PackageItemIsHandle(item, qname, ctx) ? 64 : 32;
}

static int32_t PackageQueueMaxSize(const Expr* dim, std::string_view pkg,
                                   SimContext& ctx, Arena& arena) {
  if (dim->rhs == nullptr) return -1;
  ctx.PushScope(pkg);
  auto bound = static_cast<int64_t>(EvalExpr(dim->rhs, ctx, arena).ToUint64());
  ctx.PopScope();
  std::optional<int32_t> size = QueueBoundMaxSize(bound);
  return size ? *size : -1;
}

static std::optional<RtlirUnpackedDim> PackageArrayDim(const Expr* dim,
                                                       SimContext& ctx,
                                                       Arena& arena) {
  auto eval = [&](const Expr* e) {
    return static_cast<int64_t>(EvalExpr(e, ctx, arena).ToUint64());
  };
  if (dim->kind == ExprKind::kBinary && dim->op == TokenKind::kColon)
    return RtlirUnpackedDim{eval(dim->lhs), eval(dim->rhs)};
  int64_t size = eval(dim);
  if (size <= 0) return std::nullopt;
  return RtlirUnpackedDim{0, size - 1};
}

static bool FoldPackageArrayDims(const ModuleItem* item, std::string_view pkg,
                                 RtlirVariable& var, SimContext& ctx,
                                 Arena& arena) {
  ctx.PushScope(pkg);
  bool folded = true;
  for (const Expr* dim : item->unpacked_dims) {
    std::optional<RtlirUnpackedDim> bounds =
        dim == nullptr ? std::nullopt : PackageArrayDim(dim, ctx, arena);
    if (!bounds) {
      folded = false;
      break;
    }
    var.unpacked_dims.push_back(*bounds);
    var.unpacked_dim_sizes.push_back(bounds->Size());
  }
  ctx.PopScope();
  if (!folded) return false;
  const RtlirUnpackedDim& outer = var.unpacked_dims.front();
  var.unpacked_lo = outer.Low();
  var.unpacked_size = outer.Size();
  var.is_descending = outer.left > outer.right;
  var.num_unpacked_dims = static_cast<uint32_t>(item->unpacked_dims.size());
  return true;
}

static std::optional<RtlirVariable> PackageArrayShape(const ModuleItem* item,
                                                      std::string_view pkg,
                                                      const Expr* init,
                                                      SimContext& ctx,
                                                      Arena& arena) {
  const DataType& type = item->data_type;
  RtlirVariable var;
  var.name = item->name;
  var.width = PackageDataWidth(item, PackageDataKey(item, pkg), ctx);
  var.is_4state = DeclaredTypeIs4State(type, ctx);
  var.is_signed = DeclaredTypeIsSigned(type, ctx);
  var.is_string = DeclaredTypeIsString(type, ctx);
  var.is_real = type.kind == DataTypeKind::kReal ||
                type.kind == DataTypeKind::kShortreal ||
                type.kind == DataTypeKind::kRealtime;
  var.init_expr = init;
  var.dtype = &type;
  var.elem_type_kind = type.kind;
  var.element.type_is_unpacked_array = type.names_unpacked_array;
  if (!FoldPackageArrayDims(item, pkg, var, ctx, arena)) return std::nullopt;
  return var;
}

static void CreatePackageArray(const ModuleItem* item, std::string_view pkg,
                               std::string_view qname, SimContext& ctx,
                               Arena& arena) {
  std::optional<RtlirVariable> var =
      PackageArrayShape(item, pkg, nullptr, ctx, arena);
  if (!var) return;
  ctx.PushScope(pkg);
  CreateArrayElements(qname, *var, ctx, arena);
  ctx.PopScope();
}

static void CreatePackageDynArray(std::string_view qname, uint32_t width,
                                  bool is_4state, bool is_signed,
                                  SimContext& ctx) {
  ctx.CreateQueue(qname, width, -1, is_4state)->is_signed = is_signed;
  ArrayInfo info;
  info.is_dynamic = true;
  info.elem_width = width;
  info.is_4state = is_4state;
  ctx.RegisterArray(qname, info);
}

static void CreatePackageAggregate(const ModuleItem* item, std::string_view pkg,
                                   std::string_view qname, SimContext& ctx,
                                   Arena& arena) {
  if (item->unpacked_dims.empty()) return;
  const Expr* dim = item->unpacked_dims.front();
  uint32_t width = PackageDataWidth(item, qname, ctx);
  bool is_4state = DeclaredTypeIs4State(item->data_type, ctx);
  bool is_signed = DeclaredTypeIsSigned(item->data_type, ctx);
  if (dim == nullptr) {
    CreatePackageDynArray(qname, width, is_4state, is_signed, ctx);
  } else if (IsQueueDim(dim)) {
    QueueObject* q = ctx.CreateQueue(
        qname, width, PackageQueueMaxSize(dim, pkg, ctx, arena), is_4state);
    q->is_signed = is_signed;
    q->holds_class_handles = !ctx.GetVariableClassType(qname).empty();
  } else if (item->unpacked_dims.size() == 1 && IsAssocIndexDim(dim, ctx)) {
    AssocArrayObject* aa =
        ctx.CreateAssocArray(qname, width, IsStringIndexDim(dim, ctx),
                             AssocIndexSpec(dim, is_4state, ctx));
    aa->is_signed = is_signed;
  } else {
    CreatePackageArray(item, pkg, qname, ctx, arena);
  }
}

static void CreatePackageSyncObject(std::string_view type,
                                    std::string_view qname, SimContext& ctx) {
  if (type == "semaphore") ctx.CreateSemaphore(qname, 0);
  if (type == "mailbox") ctx.CreateMailbox(qname, 0);
}

static bool InitPackageSyncObject(const ModuleItem* item, std::string_view key,
                                  SimContext& ctx, Arena& arena) {
  std::string_view type = PackageSyncObjectType(item, key, ctx);
  if (type.empty()) return false;
  const Expr* init = item->init_expr;
  if (init->kind != ExprKind::kCall || init->text != "new") return true;
  if (type == "semaphore") {
    if (SemaphoreObject* sem = ctx.FindSemaphore(key))
      sem->key_count = SemaphoreKeyArg(init, ctx, arena, 0);
  } else if (MailboxObject* mbx = ctx.FindMailbox(key)) {
    mbx->Build(MailboxBoundArg(init, ctx, arena));
  }
  HoldSyncVariable(key, ctx);
  return true;
}

static void CarryUnitClassRecord(const ModuleItem* item, std::string_view qname,
                                 SimContext& ctx) {
  std::string_view cls = ctx.GetVariableClassType(item->name);
  if (cls.empty()) return;
  ctx.SetVariableClassType(qname, cls);
  RecordClassParamActuals(qname, cls, item->data_type.type_params, ctx);
}

static void RegisterPackageDataLayout(const ModuleItem* item,
                                      std::string_view pkg,
                                      std::string_view qname, SimContext& ctx,
                                      Arena& arena) {
  const DataType& type = item->data_type;
  if (!type.struct_members.empty()) {
    RegisterAggregateLayout(qname, &type, PackageDataWidth(item, qname, ctx),
                            ctx, arena);
    return;
  }
  if (type.kind != DataTypeKind::kNamed) return;
  std::string scoped =
      std::string(type.scope_name.empty() ? pkg : type.scope_name) +
      "::" + std::string(type.type_name);
  const StructTypeInfo* info = ctx.FindStructType(scoped);
  if (info == nullptr) info = ctx.FindStructType(type.type_name);
  if (info != nullptr) ctx.SetVariableStructType(qname, info->type_name);
}

static void RegisterPackageDataEnumType(const ModuleItem* item,
                                        std::string_view pkg,
                                        std::string_view qname,
                                        SimContext& ctx) {
  const DataType& type = item->data_type;
  if (type.kind != DataTypeKind::kNamed) return;
  std::string scoped =
      std::string(type.scope_name.empty() ? pkg : type.scope_name) +
      "::" + std::string(type.type_name);
  const EnumTypeInfo* info = ctx.FindEnumType(scoped);
  if (info == nullptr) info = ctx.FindEnumType(type.type_name);
  if (info != nullptr) ctx.SetVariableEnumType(qname, info->type_name);
}

static std::string_view CreatePackageDataItem(const ModuleItem* item,
                                              std::string_view pkg,
                                              SimContext& ctx, Arena& arena) {
  if (!DeclaresPackageData(item)) return {};
  item = WithPackageOwnType(item, pkg, ctx, arena);
  auto* qname = arena.Create<std::string>(PackageDataKey(item, pkg));
  if (UnitScopes::IsUnitScope(pkg)) CarryUnitClassRecord(item, *qname, ctx);
  auto* var = ctx.CreateVariable(*qname, PackageDataWidth(item, *qname, ctx));
  var->declared_type = &item->data_type;
  if (!UnitScopes::IsUnitScope(pkg)) {
    auto* scope = arena.Create<std::string>(std::string(pkg) + "::");
    var->declared_scope = *scope;
  }
  RegisterPackageDataEnumType(item, pkg, *qname, ctx);
  ShapePackageVariable(item, var, *qname, ctx, arena);
  if (item->kind != ModuleItemKind::kVarDecl) {
    ctx.Vcd().MarkVcdParameter(*qname);
    CreatePackageAggregate(item, pkg, *qname, ctx, arena);
    return *qname;
  }
  RegisterPackageDataLayout(item, pkg, *qname, ctx, arena);
  RecordPackageVcdKind(item, *var, *qname, ctx);
  if (item->init_expr == nullptr)
    ApplyVariableLayoutDefaults(*qname, var, ctx, arena);
  std::string_view sync_type = PackageSyncObjectType(item, *qname, ctx);
  if (!sync_type.empty()) {
    CreatePackageSyncObject(sync_type, *qname, ctx);
    return *qname;
  }
  CreatePackageAggregate(item, pkg, *qname, ctx, arena);
  return *qname;
}

void CreatePackageDataVariables(const RtlirDesign* design, SimContext& ctx,
                                Arena& arena) {
  for (auto* pkg : design->packages) {
    ctx.Vcd().MarkVcdPackage(pkg->name);
    for (auto* item : pkg->items)
      CreatePackageDataItem(item, pkg->name, ctx, arena);
  }
}

void CreateUnitDataVariables(const RtlirDesign* design, SimContext& ctx,
                             Arena& arena) {
  ForEachUnitScope(design, arena,
                   [&](const CompilationUnit& unit, std::string_view scope) {
                     for (auto* item : unit.cu_items)
                       CreatePackageDataItem(item, scope, ctx, arena);
                   });
}

void AliasUnitDataItems(const RtlirDesign* design, const RtlirModule* mod,
                        std::string_view inst_prefix, SimContext& ctx,
                        Arena& arena) {
  const CompilationUnit* unit =
      mod->unit_index < 0
          ? design->compilation_unit
          : design->compilation_units[static_cast<size_t>(mod->unit_index)];
  if (unit == nullptr) return;
  const std::string kScope = UnitScopes::ScopeName(mod->unit_index);
  for (const auto* item : unit->cu_items) {
    bool is_net = item->kind == ModuleItemKind::kNetDecl;
    if (!(is_net || DeclaresPackageData(item)) ||
        ModuleDeclaresName(mod, item->name) ||
        EnclosingDeclHoldsVariable(inst_prefix, item->name, ctx))
      continue;
    std::string key = std::string(inst_prefix) + std::string(item->name);
    if (ctx.GetVariables().count(key) != 0) continue;
    std::string_view stored = *arena.Create<std::string>(key);
    std::string qname = PackageDataKey(item, kScope);
    ctx.AliasVariable(stored, qname);
    if (is_net) ctx.AliasNet(stored, qname);
    AliasVariableKinds(stored, qname, ctx, arena);
    ctx.RegisterImportedName(stored);
    if (mod->unit_index < 0) continue;
    std::string_view unit_key = *arena.Create<std::string>(
        std::string(inst_prefix) + std::string(kUnitScope) + "." +
        std::string(item->name));
    ctx.AliasVariable(unit_key, qname);
    AliasVariableKinds(unit_key, qname, ctx, arena);
  }
}

static bool InitPackageAggregate(const Expr* init, std::string_view key,
                                 SimContext& ctx, Arena& arena) {
  if (QueueObject* q = ctx.FindQueue(key)) {
    InitQueueFromDeclInit(q, init, ctx, arena);
    return true;
  }
  if (AssocArrayObject* aa = ctx.FindAssocArray(key)) {
    InitAssocFromDeclInit(init, aa, ctx, arena);
    return true;
  }
  return false;
}

static bool InitPackageArray(const ModuleItem* item, std::string_view pkg,
                             std::string_view key, SimContext& ctx,
                             Arena& arena) {
  if (ctx.FindArrayInfo(key) == nullptr || ctx.FindQueue(key) != nullptr)
    return false;
  std::optional<RtlirVariable> var =
      PackageArrayShape(item, pkg, item->init_expr, ctx, arena);
  if (var) InitArrayElements(key, *var, ctx, arena);
  return true;
}

static bool IsClassNewInit(const ModuleItem* item, std::string_view key,
                           SimContext& ctx) {
  const Expr* init = item->init_expr;
  if (init == nullptr || init->kind != ExprKind::kCall || init->text != "new")
    return false;
  return !ctx.GetVariableClassType(key).empty();
}

static void InitPackageCarrier(const Expr* init, std::string_view key,
                               Variable* var, SimContext& ctx, Arena& arena) {
  const StructTypeInfo* sinfo = ctx.GetVariableStructType(key);
  const Expr* pattern = UnwrapTypedPattern(init);
  if (sinfo != nullptr && pattern->kind == ExprKind::kAssignmentPattern) {
    var->value = EvalStructPatternValue(pattern, sinfo, ctx, arena);
    return;
  }
  const uint32_t kWidth = var->value.width;
  bool sized = !var->is_real && !var->is_event && !ctx.IsStringVariable(key);
  Logic4Vec value = EvalExpr(init, ctx, arena, sized ? kWidth : 0);
  var->value = sized ? HeldAtWidth(value, kWidth, *var, arena) : value;
  if (init->kind != ExprKind::kTagged || init->rhs == nullptr) return;
  ctx.SetVariableTag(*arena.Create<std::string>(std::string(key)),
                     init->rhs->text);
}

static void InitPackageDataItem(const ModuleItem* item, std::string_view pkg,
                                SimContext& ctx, Arena& arena) {
  if (!DeclaresPackageData(item) || item->init_expr == nullptr) return;
  std::string key = PackageDataKey(item, pkg);
  if (InitPackageSyncObject(item, key, ctx, arena)) return;
  if (IsClassNewInit(item, key, ctx)) return;
  if (InitPackageArray(item, pkg, key, ctx, arena)) return;
  if (InitPackageAggregate(item->init_expr, key, ctx, arena)) return;
  const auto& variables = ctx.GetVariables();
  auto found = variables.find(key);
  if (found == variables.end()) return;
  if (item->kind == ModuleItemKind::kParamDecl) {
    InitPackageParam(WithPackageOwnType(item, pkg, ctx, arena), found->second,
                     ctx, arena);
    return;
  }
  InitPackageCarrier(item->init_expr, key, found->second, ctx, arena);
}

static void InitScopeDataItems(const std::vector<ModuleItem*>& items,
                               std::string_view pkg, SimContext& ctx,
                               Arena& arena) {
  ctx.PushScope(pkg);
  for (auto* item : items) InitPackageDataItem(item, pkg, ctx, arena);
  ctx.PopScope();
}

void InitPackageDataVariables(const RtlirDesign* design, SimContext& ctx,
                              Arena& arena) {
  for (auto* pkg : design->packages)
    InitScopeDataItems(pkg->items, pkg->name, ctx, arena);
}

void InitUnitDataVariables(const RtlirDesign* design, SimContext& ctx,
                           Arena& arena) {
  ForEachUnitScope(design, arena,
                   [&](const CompilationUnit& unit, std::string_view scope) {
                     InitScopeDataItems(unit.cu_items, scope, ctx, arena);
                   });
}

static void ConstructClassNewInit(const ModuleItem* item, std::string_view pkg,
                                  SimContext& ctx, Arena& arena) {
  if (item->kind != ModuleItemKind::kVarDecl) return;
  std::string key = PackageDataKey(item, pkg);
  if (!IsClassNewInit(item, key, ctx)) return;
  std::string_view cls = ctx.GetVariableClassType(key);
  const auto& variables = ctx.GetVariables();
  auto found = variables.find(key);
  if (found == variables.end()) return;
  const Expr* init = item->init_expr;
  if (cls == "weak_reference") {
    found->second->value = EvalWeakReferenceNew(init, ctx, arena);
    return;
  }
  if (ctx.FindClassType(cls) == nullptr) return;
  found->second->value = EvalClassNew(cls, init, ctx, arena, init->range.start);
  ApplyClassParamOverrides(key, found->second->value.ToUint64(), ctx, arena);
}

static void ConstructScopeClassInits(const std::vector<ModuleItem*>& items,
                                     std::string_view pkg, SimContext& ctx,
                                     Arena& arena) {
  ctx.PushScope(pkg);
  for (auto* item : items) ConstructClassNewInit(item, pkg, ctx, arena);
  ctx.PopScope();
}

void ConstructDataClassInitializers(const RtlirDesign* design, SimContext& ctx,
                                    Arena& arena) {
  for (auto* pkg : design->packages)
    ConstructScopeClassInits(pkg->items, pkg->name, ctx, arena);
  ForEachUnitScope(design, arena,
                   [&](const CompilationUnit& unit, std::string_view scope) {
                     ConstructScopeClassInits(unit.cu_items, scope, ctx, arena);
                   });
}

}  // namespace delta
