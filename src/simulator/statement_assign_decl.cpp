#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <format>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/queue_dim.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "simulator/block_enums.h"
#include "simulator/class_object.h"
#include "simulator/class_specialization.h"
#include "simulator/covergroup_instance.h"
#include "simulator/declared_class_key.h"
#include "simulator/eval_array_class_assoc.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer_register.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/static_aggregate.h"
#include "simulator/stmt_exec_internal.h"
#include "simulator/stmt_result.h"
#include "simulator/sync_variable.h"
#include "simulator/virtual_interface.h"

namespace delta {

static bool DeclaresQueue(const Stmt* stmt) {
  return !stmt->var_unpacked_dims.empty() &&
         IsQueueDim(stmt->var_unpacked_dims[0]);
}

struct ElementQueues {
  const DataType* type = nullptr;
  uint32_t levels = 0;
};

static ElementQueues ElementQueuesOf(const Stmt* stmt, SimContext& ctx) {
  const std::vector<Expr*>& dims = stmt->var_unpacked_dims;
  if (dims.size() >= 2) {
    uint32_t levels = QueueLevelsFrom(dims, 1);
    if (levels == 0) return {};
    return {&stmt->var_decl_type, levels};
  }
  if (dims.size() != 1) return {};
  const ModuleItem* item =
      TypedefItemSeenFrom(stmt->var_decl_type, ctx.CurrentMethodClass(), ctx);
  if (item == nullptr) return {};
  uint32_t levels = QueueLevelsFrom(item->unpacked_dims, 0);
  if (levels == 0) return {};
  return {&item->typedef_type, levels};
}

static std::optional<FixedDimShape> BlockFixedDim(const Expr* dim,
                                                  SimContext& ctx,
                                                  Arena& arena) {
  if (dim == nullptr || IsQueueDim(dim)) return std::nullopt;
  if (dim->kind == ExprKind::kBinary && dim->op == TokenKind::kColon) {
    auto l = static_cast<int64_t>(EvalExpr(dim->lhs, ctx, arena).ToUint64());
    auto r = static_cast<int64_t>(EvalExpr(dim->rhs, ctx, arena).ToUint64());
    return FixedDimShape{static_cast<uint32_t>(std::abs(l - r) + 1),
                         std::min(l, r), l > r};
  }
  auto size = static_cast<int64_t>(EvalExpr(dim, ctx, arena).ToUint64());
  if (size <= 0) return std::nullopt;
  return FixedDimShape{static_cast<uint32_t>(size), 0, false};
}

static void MarkFixedElementArray(const Stmt* stmt, QueueObject* q,
                                  SimContext& ctx, Arena& arena) {
  const std::vector<Expr*>& dims = stmt->var_unpacked_dims;
  std::vector<FixedDimShape> fixed;
  for (size_t i = 1; i < dims.size(); ++i) {
    std::optional<FixedDimShape> dim = BlockFixedDim(dims[i], ctx, arena);
    if (!dim) return;
    fixed.push_back(*dim);
  }
  if (fixed.empty()) return;
  q->elements_are_queues = true;
  q->nested_queue_levels = static_cast<uint32_t>(fixed.size() - 1);
  q->element_array_size = fixed[0].size;
  q->element_array_lo = fixed[0].lo;
  q->element_array_descending = fixed[0].descending;
  q->element_inner_dims.assign(fixed.begin() + 1, fixed.end());
}

static void MarkElementQueues(const Stmt* stmt, QueueObject* q, SimContext& ctx,
                              Arena& arena) {
  MarkFixedElementArray(stmt, q, ctx, arena);
  ElementQueues queues = ElementQueuesOf(stmt, ctx);
  if (queues.type == nullptr) return;
  q->elements_are_queues = true;
  q->nested_queue_levels = queues.levels - 1;
  q->holds_class_handles = !DeclaredClassKey(*queues.type, ctx, arena).empty();
}

static bool CreateBlockQueue(const Stmt* stmt, uint32_t elem_width,
                             SimContext& ctx, Arena& arena) {
  if (!DeclaresQueue(stmt)) return false;
  const auto* dim = stmt->var_unpacked_dims[0];
  int32_t max_size = -1;
  if (dim->rhs) {
    auto bound =
        static_cast<int64_t>(EvalExpr(dim->rhs, ctx, arena).ToUint64());
    if (auto size = QueueBoundMaxSize(bound)) max_size = *size;
  }
  auto* q = ctx.CreateQueue(stmt->var_name, elem_width, max_size,
                            Is4stateType(stmt->var_decl_type.kind));
  q->is_signed = DeclaredTypeIsSigned(stmt->var_decl_type, ctx);
  q->holds_class_handles =
      !DeclaredClassKey(stmt->var_decl_type, ctx, arena).empty();
  MarkElementQueues(stmt, q, ctx, arena);
  return true;
}

static bool CreateBlockAssocArray(const Stmt* stmt, uint32_t elem_width,
                                  SimContext& ctx, Arena& arena) {
  ElementQueues queues = ElementQueuesOf(stmt, ctx);
  const DataType* queue_type = queues.type;
  if (queue_type != &stmt->var_decl_type &&
      stmt->var_unpacked_dims.size() != 1) {
    return false;
  }
  const Expr* dim = stmt->var_unpacked_dims.front();
  if (!IsAssocIndexDim(dim, ctx)) return false;
  AssocArrayObject* aa = ctx.CreateAssocArray(
      stmt->var_name, elem_width, IsStringIndexDim(dim, ctx),
      AssocIndexSpec(dim, DeclaredTypeIs4State(stmt->var_decl_type, ctx), ctx));
  aa->is_signed = DeclaredTypeIsSigned(stmt->var_decl_type, ctx);
  if (queue_type != nullptr) {
    aa->elements_are_queues = true;
    aa->nested_queue_levels = queues.levels - 1;
    aa->element_queue_handles =
        !DeclaredClassKey(*queue_type, ctx, arena).empty();
  }
  return true;
}

static bool CreateBlockDynArray(const Stmt* stmt, uint32_t elem_width,
                                SimContext& ctx, Arena& arena) {
  if (stmt->var_unpacked_dims.empty() || stmt->var_unpacked_dims[0] != nullptr)
    return false;
  bool is_4state = DeclaredTypeIs4State(stmt->var_decl_type, ctx);
  QueueObject* q = ctx.CreateQueue(stmt->var_name, elem_width, -1, is_4state);
  q->is_signed = DeclaredTypeIsSigned(stmt->var_decl_type, ctx);
  MarkElementQueues(stmt, q, ctx, arena);
  ArrayInfo info;
  info.is_dynamic = true;
  info.elem_width = elem_width;
  info.is_4state = is_4state;
  ctx.RegisterArrayInScope(stmt->var_name, info);
  return true;
}

void AssignDeclAggregateInit(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (stmt->var_init == nullptr || stmt->var_unpacked_dims.empty()) return;
  auto* target = arena.Create<Expr>();
  target->kind = ExprKind::kIdentifier;
  target->range = stmt->range;
  target->text = stmt->var_name;
  auto* assign = arena.Create<Stmt>();
  assign->kind = StmtKind::kBlockingAssign;
  assign->range = stmt->range;
  assign->lhs = target;
  assign->rhs = stmt->var_init;
  ExecImmediateBlockingAssign(assign, ctx, arena);
}

void CreateDeclAggregate(const Stmt* stmt, uint32_t elem_width, SimContext& ctx,
                         Arena& arena) {
  if (CreateBlockAssocArray(stmt, elem_width, ctx, arena)) return;
  if (CreateBlockDynArray(stmt, elem_width, ctx, arena)) return;
  if (!CreateBlockQueue(stmt, elem_width, ctx, arena)) {
    CreateBlockArrayElements(stmt, elem_width, ctx, arena);
  }
}

static std::string_view StaticFrameOf(const Stmt* stmt,
                                      std::string_view func_name,
                                      SimContext& ctx) {
  if (!func_name.empty()) {
    std::string_view block = ctx.InnermostStmtFrame();
    return block.empty() ? func_name : block;
  }
  auto* key = ctx.GetArena().Create<std::string>(
      std::format("static@{}:{}:{}", stmt->range.start.file_id,
                  stmt->range.start.line, stmt->range.start.column));
  return *key;
}

static void KeepStaticLocal(const Stmt* stmt, Variable* var, SimContext& ctx) {
  std::string_view func_name = ctx.CurrentFuncName();
  if (IsEffectivelyStaticLocal(stmt, func_name, ctx))
    ctx.SaveStaticFuncVar(StaticFrameOf(stmt, func_name, ctx), stmt->var_name,
                          var);
}

static bool TryExecWeakRefVarDecl(const Stmt* stmt, SimContext& ctx,
                                  Arena& arena) {
  if (stmt->var_decl_type.type_name != "weak_reference") return false;
  KeepStaticLocal(stmt, ctx.CreateVariable(stmt->var_name, 64), ctx);
  ctx.SetVariableClassType(stmt->var_name, "weak_reference");
  const auto& type_params = stmt->var_decl_type.type_params;
  if (!type_params.empty()) {
    std::vector<Expr*> exprs;
    exprs.reserve(type_params.size());
    for (const auto& tp : type_params) {
      exprs.push_back(tp.type_ref_expr);
    }
    ctx.SetVariableClassParamExprs(stmt->var_name, std::move(exprs));
  }
  if (!stmt->var_init || stmt->var_init->kind != ExprKind::kCall ||
      stmt->var_init->text != "new")
    return true;
  uint64_t referent = kNullClassHandle;
  if (!stmt->var_init->args.empty()) {
    auto val = EvalExpr(stmt->var_init->args[0], ctx, arena);
    referent = val.ToUint64();
  }
  auto wr_handle = ctx.AllocateWeakReference(referent, arena);
  auto* var = ctx.FindVariable(stmt->var_name);
  if (var) var->value = MakeLogic4VecVal(arena, 64, wr_handle);
  return true;
}

void RecordClassParamActuals(std::string_view var_name,
                             std::string_view class_name,
                             const std::vector<DataType>& type_params,
                             SimContext& ctx) {
  if (type_params.empty()) return;
  std::vector<Expr*> exprs;
  exprs.reserve(type_params.size());
  for (const auto& tp : type_params) {
    exprs.push_back(tp.type_ref_expr);
  }
  ctx.SetVariableClassParamExprs(var_name, std::move(exprs));
  ctx.RegisterVariableClassTypeParams(var_name, &type_params);
  ClassTypeInfo* generic = ctx.FindClassType(class_name);
  if (generic == nullptr) return;
  ClassTypeInfo* spec =
      SpecializationOf(generic, type_params, ctx, ctx.GetArena());
  if (spec != generic) ctx.SetVariableClassType(var_name, spec->name);
}

static bool TryExecClassShallowCopy(std::string_view var_name, const Expr* init,
                                    SimContext& ctx, Arena& arena) {
  if (!init->lhs || init->lhs->kind != ExprKind::kIdentifier) return false;
  auto src_val = EvalExpr(init->lhs, ctx, arena);
  auto* src_obj = ctx.GetClassObject(src_val.ToUint64());
  if (!src_obj) return false;
  auto* copy = src_obj->ShallowCopy(arena);
  auto copy_handle = ctx.AllocateClassObject(copy);
  auto* var = ctx.FindVariable(var_name);
  if (var) var->value = MakeLogic4VecVal(arena, 64, copy_handle);
  return true;
}

static Variable* CreateBlockVariable(std::string_view name, uint32_t width,
                                     SimContext& ctx) {
  std::string prefix = ctx.ActiveInstancePrefix();
  if (prefix.empty()) return ctx.CreateVariable(name, width);
  std::string key = prefix + std::string(name);
  if (Variable* existing = ctx.FindVariable(key)) {
    *existing = Variable{};
    existing->value = MakeLogic4Vec(ctx.GetArena(), width);
    FillWithX(existing->value);
    return existing;
  }
  return ctx.CreateVariable(*ctx.GetArena().Create<std::string>(std::move(key)),
                            width);
}

static Variable* CreateVarInScope(std::string_view name, uint32_t width,
                                  bool is_signed, SimContext& ctx) {
  if (ctx.HasLocalScope())
    return ctx.CreateLocalVariable(name, width, is_signed);
  Variable* var = CreateBlockVariable(name, width, ctx);
  var->is_signed = is_signed;
  var->value.is_signed = is_signed;
  return var;
}

struct KeptLocal {
  Variable* var = nullptr;
  std::string_view frame;
};

static KeptLocal KeptStaticLocal(const Stmt* stmt, SimContext& ctx) {
  std::string_view func_name = ctx.CurrentFuncName();
  if (!IsEffectivelyStaticLocal(stmt, func_name, ctx)) return {};
  std::string_view frame = StaticFrameOf(stmt, func_name, ctx);
  if (Variable* var = ctx.FindStaticFuncVar(frame, stmt->var_name))
    return {var, frame};
  if (func_name.empty() || frame == func_name) return {};
  return {ctx.FindStaticFuncVar(func_name, stmt->var_name), func_name};
}

static void BindClassHandle(std::string_view name, std::string_view class_type,
                            SimContext& ctx) {
  ctx.SetVariableClassType(name, class_type);
  std::string_view path = BindNamedBlockVariable(name, ctx);
  if (!path.empty()) ctx.SetVariableClassType(path, class_type);
}

static bool TryReuseKeptStaticLocal(const Stmt* stmt, SimContext& ctx,
                                    Arena& arena) {
  KeptLocal kept = KeptStaticLocal(stmt, ctx);
  if (kept.var == nullptr) return false;
  ctx.AliasLocalVariable(stmt->var_name, kept.var);
  RestoreStaticAggregate(kept.frame, stmt->var_name, ctx);
  std::string_view class_key =
      DeclaredClassKey(stmt->var_decl_type, ctx, arena);
  if (class_key.empty()) {
    BindNamedBlockVariable(stmt->var_name, ctx);
    return true;
  }
  BindClassHandle(stmt->var_name, class_key, ctx);
  RecordClassParamActuals(stmt->var_name, class_key,
                          stmt->var_decl_type.type_params, ctx);
  return true;
}

static bool TryExecClassVarDecl(const Stmt* stmt, SimContext& ctx,
                                Arena& arena) {
  if (!stmt->var_unpacked_dims.empty()) return false;
  std::string_view class_type =
      DeclaredClassKey(stmt->var_decl_type, ctx, arena);
  if (class_type.empty()) return false;
  KeepStaticLocal(stmt, CreateVarInScope(stmt->var_name, 64, false, ctx), ctx);
  BindClassHandle(stmt->var_name, class_type, ctx);

  RecordClassParamActuals(stmt->var_name, class_type,
                          stmt->var_decl_type.type_params, ctx);

  if (!stmt->var_init) return true;

  {
    Logic4Vec typed;
    if (TryEvalTypedConstructorNew(stmt->var_init, ctx, arena, typed)) {
      auto* var = ctx.FindVariable(stmt->var_name);
      if (var) var->value = typed;
      return true;
    }
  }

  if (stmt->var_init->kind != ExprKind::kCall ||
      stmt->var_init->text != "new") {
    auto val = EvalExpr(stmt->var_init, ctx, arena);
    auto* var = ctx.FindVariable(stmt->var_name);
    if (var) var->value = val;
    return true;
  }

  if (TryExecClassShallowCopy(stmt->var_name, stmt->var_init, ctx, arena)) {
    return true;
  }

  auto handle =
      EvalClassNew(ctx.GetVariableClassType(stmt->var_name), stmt->var_init,
                   ctx, arena, stmt->var_init->range.start);
  auto* var = ctx.FindVariable(stmt->var_name);
  if (var) var->value = handle;
  ApplyClassParamOverrides(stmt->var_name, handle.ToUint64(), ctx, arena);
  return true;
}

static void CreateDeclVariable(const Stmt* stmt, uint32_t width, bool is_real,
                               SimContext& ctx, Arena& arena) {
  bool is_signed = DeclaredTypeIsSigned(stmt->var_decl_type, ctx);
  if (width == 0 && DeclaredTypeIsString(stmt->var_decl_type, ctx)) {
    CreateVarInScope(stmt->var_name, 0, is_signed, ctx);
    ctx.RegisterStringVariable(stmt->var_name);
    CreateDeclAggregate(stmt, 0, ctx, arena);
  } else {
    if (width == 0) width = 32;
    Variable* var = CreateVarInScope(stmt->var_name, width, is_signed, ctx);
    var->is_real = is_real;
    if (is_real) ctx.RegisterRealVariable(stmt->var_name);
    var->is_event = stmt->var_decl_type.kind == DataTypeKind::kEvent;
    CreateDeclAggregate(stmt, width, ctx, arena);
  }
}

static bool TryReuseExistingDeclVar(const Stmt* stmt,
                                    std::string_view func_name,
                                    SimContext& ctx) {
  if (IsEffectivelyStaticLocal(stmt, func_name, ctx) ||
      IsAutomaticLocal(*stmt, ctx))
    return false;
  return ctx.InnermostScopeDeclares(stmt->var_name);
}

struct DeclaredObject {
  Variable* var;
  uint32_t declared_width;
  bool is_real;
};

static void InitializeDeclVariable(const Stmt* stmt, const DeclaredObject& obj,
                                   std::string_view func_name, SimContext& ctx,
                                   Arena& arena) {
  Variable* var = obj.var;
  var->is_4state = Is4stateType(DeclaredTypeKind(stmt->var_decl_type, ctx));
  if (!var->is_4state) CoerceTo2State(var->value);
  if (var->is_4state && !var->is_virtual_interface && !stmt->var_init &&
      stmt->var_unpacked_dims.empty() && var->value.width > 0) {
    var->value = MakeAllX(arena, var->value.width);
    var->value.is_signed = var->is_signed;
  }
  if (const StructTypeInfo* info = ctx.GetVariableStructType(stmt->var_name);
      info != nullptr && info->is_union)
    MarkUnpackedStructStorage(stmt->var_name, var, false, ctx);
  if (stmt->var_init && stmt->var_unpacked_dims.empty()) {
    Logic4Vec val = EvalTaggedOrPlain(
        stmt->var_init, ctx.GetVariableStructType(stmt->var_name), ctx, arena);
    if (stmt->var_init->kind == ExprKind::kStreamingConcat && !var->is_string &&
        !obj.is_real && obj.declared_width > 0) {
      val = WidenStreamPackToFixedTarget(
          val, obj.declared_width, stmt->var_init->range.start, ctx, arena);
    }
    uint32_t target = obj.is_real ? var->value.width : obj.declared_width;
    val = ConvertRealForKnownLhs(val, obj.is_real, target, arena);
    var->value = val;
    if (!var->is_4state) CoerceTo2State(var->value);
  }

  if (IsEffectivelyStaticLocal(stmt, func_name, ctx)) {
    std::string_view frame = StaticFrameOf(stmt, func_name, ctx);
    ctx.SaveStaticFuncVar(frame, stmt->var_name, var);
    RetainStaticAggregate(frame, stmt->var_name, ctx, arena);
  }
}

StmtResult ExecBlockItemDeclImpl(const Stmt* stmt, SimContext& ctx,
                                 Arena& arena) {
  RegisterBlockLet(stmt, ctx);
  ForEachBlockEnumMember(
      stmt, ctx, [&](const EnumMemberInfo& m, const EnumTypeInfo& info) {
        bool is_signed = ctx.FindTypeSigned(info.type_name);
        Variable* var = CreateVarInScope(m.name, info.width, is_signed, ctx);
        var->is_4state = info.is_4state;
        var->value = MakeLogic4VecVal(arena, info.width, m.value);
        var->value.words[0].bval = m.xz;
        var->value.is_signed = is_signed;
      });
  return StmtResult::kDone;
}

static const Stmt* DeclareInlineEnumOf(const Stmt* stmt, SimContext& ctx,
                                       Arena& arena) {
  if (stmt->var_decl_type.kind != DataTypeKind::kEnum) return stmt;
  ExecBlockItemDeclImpl(stmt, ctx, arena);
  const auto& shaped = ctx.ClassTypedefShapedDecls();
  auto it = shaped.find(stmt);
  return it == shaped.end() ? stmt : it->second;
}

static void BindBlockLocalLayout(const Stmt* stmt, uint32_t width,
                                 SimContext& ctx, Arena& arena) {
  const DataType& type = stmt->var_decl_type;
  if (type.kind == DataTypeKind::kNamed) {
    BindNamedLayout(stmt->var_name, type, ctx);
  } else if (type.kind == DataTypeKind::kStruct ||
             type.kind == DataTypeKind::kUnion) {
    RegisterAggregateLayout(stmt->var_name, &type, width, ctx, arena);
  }
}

static StmtResult ExecVarDeclBody(const Stmt* stmt, SimContext& ctx,
                                  Arena& arena) {
  stmt = DeclareInlineEnumOf(stmt, ctx, arena);
  stmt = DeclShapedByTypedef(stmt, ctx, arena);
  stmt = DeclParameterTypedByValue(stmt, ctx, arena);
  if (TryReuseKeptStaticLocal(stmt, ctx, arena)) return StmtResult::kDone;
  auto func_name = ctx.CurrentFuncName();
  if (TryReuseExistingDeclVar(stmt, func_name, ctx)) return StmtResult::kDone;
  if (TryExecWeakRefVarDecl(stmt, ctx, arena)) return StmtResult::kDone;
  if (TryExecClassVarDecl(stmt, ctx, arena)) return StmtResult::kDone;

  bool is_virtual_interface =
      DeclaresAVirtualInterface(stmt->var_decl_type, ctx);
  std::string_view class_key =
      DeclaredClassKey(stmt->var_decl_type, ctx, arena);
  bool is_class = !class_key.empty();
  uint32_t width = is_virtual_interface || is_class
                       ? 64
                       : DeclaredTypeWidth(stmt->var_decl_type, ctx);
  bool is_real = (stmt->var_decl_type.kind == DataTypeKind::kReal ||
                  stmt->var_decl_type.kind == DataTypeKind::kShortreal ||
                  stmt->var_decl_type.kind == DataTypeKind::kRealtime);
  CreateDeclVariable(stmt, width, is_real, ctx, arena);
  BindBlockLocalLayout(stmt, width, ctx, arena);
  if (stmt->var_init == nullptr)
    ApplyVariableLayoutDefaults(stmt->var_name,
                                ctx.FindVariable(stmt->var_name), ctx, arena);
  RecordVariableEnumType(stmt->var_name, stmt->var_decl_type, ctx);
  if (is_class) ctx.SetVariableClassType(stmt->var_name, class_key);
  auto* var = ctx.FindVariable(stmt->var_name);
  if (var) {
    BindNamedBlockVariable(stmt->var_name, ctx);
    var->is_virtual_interface = is_virtual_interface;
    if (is_virtual_interface) var->value = MakeLogic4VecVal(arena, width, 0);
    if (!is_virtual_interface)
      RecordDeclaredRange(stmt->var_decl_type, var, ctx, arena);
    AssignDeclAggregateInit(stmt, ctx, arena);
    InitializeDeclVariable(stmt, {var, width, is_real}, func_name, ctx, arena);
  }
  return StmtResult::kDone;
}

StmtResult ExecVarDeclImpl(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (stmt->kind == StmtKind::kBlockItemDecl)
    return ExecBlockItemDeclImpl(stmt, ctx, arena);
  if (KeptStaticLocal(stmt, ctx).var != nullptr)
    return ExecVarDeclBody(stmt, ctx, arena);
  StmtResult result = ExecVarDeclBody(stmt, ctx, arena);
  Variable* local = ctx.FindLocalVariable(stmt->var_name);
  CreateSyncObjectForLocal(stmt, local, ctx, arena);
  if (local != nullptr) {
    local->declared_type = &stmt->var_decl_type;
    TryCreateCovergroupLocal(stmt->var_decl_type, stmt->var_init, local, ctx,
                             arena);
  }
  return result;
}

}  // namespace delta
