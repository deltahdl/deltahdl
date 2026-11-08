#include "simulator/eval_mailbox.h"

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/types.h"
#include "elaborator/type_eval.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "simulator/awaiters.h"
#include "simulator/class_object.h"
#include "simulator/eval_call_result.h"
#include "simulator/eval_class_sync.h"
#include "simulator/eval_expr_internal.h"
#include "simulator/eval_function_internal.h"
#include "simulator/eval_semaphore.h"
#include "simulator/eval_string.h"
#include "simulator/evaluation.h"
#include "simulator/exec_task.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/stmt_result.h"
#include "simulator/sync_objects.h"
#include "simulator/sync_variable.h"
#include "simulator/variable.h"

namespace delta {

MailboxObject* MailboxCallTarget(const Expr* expr, SimContext& ctx,
                                 Arena& arena, std::string_view method) {
  if (!expr || expr->kind != ExprKind::kCall) return nullptr;
  const auto* access = expr->lhs;
  if (!access) return nullptr;
  if (access->kind == ExprKind::kIdentifier) {
    return BuiltinBaseMailbox(expr, method, ctx, arena);
  }
  if (access->kind != ExprKind::kMemberAccess) return nullptr;
  if (!access->rhs || access->rhs->text != method) return nullptr;
  SyncProperty prop = ResolveSyncProperty(access->lhs, ctx, arena);
  if (prop.kind != SyncKind::kNone) {
    return MailboxOfProperty(prop, method, access->rhs->range.start, ctx);
  }
  if (MailboxObject* mbx = MailboxOfFormal(access->lhs, ctx)) return mbx;
  if (MailboxObject* mbx = ContainedMailboxOf(access->lhs, ctx, arena)) {
    return mbx;
  }
  if (MailboxObject* base = BuiltinBaseMailbox(expr, method, ctx, arena)) {
    return base;
  }
  MethodCallParts parts;
  if (ExtractHandleMethodCallParts(expr, arena, parts)) {
    return ctx.FindMailbox(parts.var_name);
  }
  std::string_view key = ScopedOrBareTargetKey(access->lhs, arena);
  return key.empty() ? nullptr : ctx.FindMailbox(key);
}

int32_t MailboxBoundArg(const Expr* new_expr, SimContext& ctx, Arena& arena) {
  if (new_expr->args.empty() || !new_expr->args[0]) return 0;
  auto val = EvalExpr(new_expr->args[0], ctx, arena);
  return static_cast<int32_t>(static_cast<uint32_t>(val.ToUint64()));
}

static bool ElementTypeIsFixed(const std::vector<DataType>& params) {
  if (params.empty()) return false;
  const DataType& elem = params.front();
  return elem.kind != DataTypeKind::kNamed || elem.type_name != "dynamic_type";
}

static const DataType* TypeDeclarationFor(const DataType& named,
                                          std::string_view package,
                                          const SimContext& ctx) {
  if (!named.scope_name.empty()) {
    return ctx.FindTypeDeclaration(std::string(named.scope_name) +
                                   "::" + std::string(named.type_name));
  }
  if (!package.empty()) {
    const DataType* scoped = ctx.FindTypeDeclaration(
        std::string(package) + "::" + std::string(named.type_name));
    if (scoped != nullptr) return scoped;
  }
  return ctx.FindTypeDeclaration(named.type_name);
}

static const std::vector<DataType>* MailboxTypeParams(const DataType& type,
                                                      std::string_view package,
                                                      const SimContext& ctx) {
  const DataType* cur = &type;
  for (size_t steps = 0; steps <= ctx.TypeDeclarationCount(); ++steps) {
    if (cur->kind != DataTypeKind::kNamed) return nullptr;
    if (cur->scope_name.empty() && cur->type_name == "mailbox")
      return &cur->type_params;
    cur = TypeDeclarationFor(*cur, package, ctx);
    if (cur == nullptr) return nullptr;
  }
  return nullptr;
}

static bool IsParameterizedMailbox(const Expr* expr, SimContext& ctx,
                                   Arena& arena) {
  SyncProperty prop = ResolveSyncProperty(expr->lhs->lhs, ctx, arena);
  if (prop.kind == SyncKind::kMailbox) {
    const std::vector<DataType>* params =
        MailboxTypeParams(prop.member->data_type, prop.declaring->package, ctx);
    return params != nullptr && ElementTypeIsFixed(*params);
  }
  MethodCallParts parts;
  if (!ExtractHandleMethodCallParts(expr, arena, parts)) return false;
  for (const std::string& key : ctx.ScopedObjectKeys(parts.var_name)) {
    const std::vector<DataType>* params = ctx.FindVariableClassTypeParams(key);
    if (params != nullptr) return ElementTypeIsFixed(*params);
  }
  return false;
}

static MailboxMessageType ClassMessageType(std::string_view name,
                                           SimContext& ctx) {
  const ClassTypeInfo* cls = ctx.FindClassType(name);
  if (cls != nullptr) name = cls->name;
  return MailboxMessageType::Class(name);
}

static MailboxMessageType VariableMessageType(std::string_view name,
                                              SimContext& ctx) {
  std::string_view class_name = ctx.GetVariableClassType(name);
  if (!class_name.empty()) return ClassMessageType(class_name, ctx);
  const Variable* var = ctx.FindVariable(name);
  if (var == nullptr) return {};
  if (var->is_string) return MailboxMessageType::String();
  if (ctx.IsRealVariable(name) || var->value.is_real) {
    return MailboxMessageType::Real(var->value.width);
  }
  return MailboxMessageType::Integral(var->value.width, var->is_signed,
                                      var->is_4state
                                          ? MailboxMessageType::States::kFour
                                          : MailboxMessageType::States::kTwo);
}

static MailboxMessageType::States StatesOfKind(DataTypeKind kind) {
  if (kind == DataTypeKind::kNamed) return MailboxMessageType::States::kUnknown;
  return Is4stateType(kind) ? MailboxMessageType::States::kFour
                            : MailboxMessageType::States::kTwo;
}

static MailboxMessageType DeclaredKindType(DataTypeKind kind, uint32_t width,
                                           bool is_signed) {
  if (kind == DataTypeKind::kString) return MailboxMessageType::String();
  if (kind == DataTypeKind::kReal) return MailboxMessageType::Real(64);
  if (kind == DataTypeKind::kShortreal) return MailboxMessageType::Real(32);
  return MailboxMessageType::Integral(width, is_signed, StatesOfKind(kind));
}

static const Expr* MemberPathRoot(const Expr* access, std::string& path) {
  if (access->kind == ExprKind::kIdentifier) return access;
  if (access->kind != ExprKind::kMemberAccess || access->lhs == nullptr ||
      access->rhs == nullptr)
    return nullptr;
  const Expr* root = MemberPathRoot(access->lhs, path);
  if (!path.empty()) path += '.';
  path += access->rhs->text;
  return root;
}

static const StructFieldInfo* StructFieldByPath(const StructTypeInfo* info,
                                                std::string_view path) {
  while (info != nullptr) {
    size_t dot = path.find('.');
    const StructFieldInfo* field = FindStructField(
        info, dot == std::string_view::npos ? path : path.substr(0, dot));
    if (field == nullptr || dot == std::string_view::npos) return field;
    info = field->nested;
    path = path.substr(dot + 1);
  }
  return nullptr;
}

static MailboxMessageType MemberTargetType(const Expr* arg, SimContext& ctx) {
  std::string path;
  const Expr* root = MemberPathRoot(arg, path);
  if (root == nullptr) return {};
  const StructFieldInfo* field =
      StructFieldByPath(StructLayoutOfName(root->text, ctx), path);
  if (field == nullptr) return {};
  return DeclaredKindType(field->type_kind, field->width, field->is_signed);
}

static MailboxMessageType ArrayElementType(const ArrayInfo& info,
                                           std::string_view name,
                                           const Expr* index, SimContext& ctx,
                                           Arena& arena) {
  if (info.elem_type_kind == DataTypeKind::kImplicit) return {};
  uint64_t idx = EvalExpr(index, ctx, arena).ToUint64();
  std::string elem = std::string(name) + "[" + std::to_string(idx) + "]";
  const Variable* var = ctx.FindVariable(elem);
  bool is_signed =
      var != nullptr ? var->is_signed : IsImplicitlySigned(info.elem_type_kind);
  return DeclaredKindType(info.elem_type_kind, info.elem_width, is_signed);
}

static MailboxMessageType ElementTargetType(const Expr* arg, SimContext& ctx,
                                            Arena& arena) {
  const Expr* base = arg->base;
  if (base == nullptr || base->kind != ExprKind::kIdentifier) return {};
  std::string_view class_name = ctx.GetVariableClassType(base->text);
  if (!class_name.empty()) return ClassMessageType(class_name, ctx);
  if (const QueueObject* q = ctx.FindQueue(base->text)) {
    if (arg->index_end != nullptr || q->holds_class_handles) return {};
    return MailboxMessageType::Integral(q->elem_width, q->is_signed,
                                        q->is_4state
                                            ? MailboxMessageType::States::kFour
                                            : MailboxMessageType::States::kTwo);
  }
  if (const ArrayInfo* info = ctx.FindArrayInfo(base->text)) {
    if (arg->index_end != nullptr) return {};
    return ArrayElementType(*info, base->text, arg->index, ctx, arena);
  }
  const Variable* var = ctx.FindVariable(base->text);
  if (var == nullptr || var->is_string) return {};
  return MailboxMessageType::Integral(
      SelectExprWidth(*var, arg, ctx, arena), false,
      var->is_4state ? MailboxMessageType::States::kFour
                     : MailboxMessageType::States::kTwo);
}

static MailboxMessageType TargetType(const Expr* arg, SimContext& ctx,
                                     Arena& arena) {
  switch (arg->kind) {
    case ExprKind::kIdentifier:
      return VariableMessageType(arg->text, ctx);
    case ExprKind::kMemberAccess:
      return MemberTargetType(arg, ctx);
    case ExprKind::kSelect:
      return ElementTargetType(arg, ctx, arena);
    default:
      return {};
  }
}

static MailboxMessageType ComputedMessageType(const Logic4Vec& val) {
  if (val.is_string) return MailboxMessageType::String();
  if (val.is_real) return MailboxMessageType::Real(val.width);
  return MailboxMessageType::Integral(val.width, val.is_signed,
                                      MailboxMessageType::States::kUnknown);
}

static bool ArmIsAHandle(const Expr* arm, SimContext& ctx);

static bool TernaryChoosesAHandle(const Expr* arg, SimContext& ctx) {
  return ArmIsAHandle(arg->true_expr, ctx) ||
         ArmIsAHandle(arg->false_expr, ctx);
}

static bool ArmIsAHandle(const Expr* arm, SimContext& ctx) {
  if (arm == nullptr) return false;
  if (arm->kind == ExprKind::kTernary) return TernaryChoosesAHandle(arm, ctx);
  return arm->kind == ExprKind::kIdentifier &&
         !ctx.GetVariableClassType(arm->text).empty();
}

static MailboxMessageType ActualMessageType(const Expr* arg,
                                            const Logic4Vec& val, bool typed,
                                            SimContext& ctx, Arena& arena) {
  if (typed) return {};
  switch (arg->kind) {
    case ExprKind::kStringLiteral:
      return MailboxMessageType::String();
    case ExprKind::kRealLiteral:
    case ExprKind::kTimeLiteral:
      return MailboxMessageType::Real(val.width);
    case ExprKind::kIntegerLiteral:
      return MailboxMessageType::Integral(val.width, val.is_signed,
                                          MailboxMessageType::States::kUnknown);
    case ExprKind::kTernary:
      return TernaryChoosesAHandle(arg, ctx) ? MailboxMessageType{}
                                             : ComputedMessageType(val);
    case ExprKind::kUnary:
    case ExprKind::kBinary:
    case ExprKind::kConcatenation:
    case ExprKind::kReplicate:
      return ComputedMessageType(val);
    default:
      return TargetType(arg, ctx, arena);
  }
}

static const Expr* MailboxArg(const Expr* expr) {
  return expr->args.empty() ? nullptr : expr->args[0];
}

static MailboxMessageType ElementMessageType(const DataType& elem,
                                             SimContext& ctx) {
  if (elem.kind == DataTypeKind::kNamed) {
    if (ctx.FindClassType(elem.type_name) == nullptr) return {};
    return ClassMessageType(elem.type_name, ctx);
  }
  static const TypedefMap kNoTypedefs;
  return DeclaredKindType(elem.kind, EvalTypeWidth(elem),
                          IsSignedType(elem, kNoTypedefs));
}

static MailboxMessageType PropertyElementType(const Expr* expr, SimContext& ctx,
                                              Arena& arena) {
  SyncProperty prop = ResolveSyncProperty(expr->lhs->lhs, ctx, arena);
  if (prop.kind != SyncKind::kMailbox) return {};
  const std::vector<DataType>* params =
      MailboxTypeParams(prop.member->data_type, prop.declaring->package, ctx);
  if (params == nullptr || !ElementTypeIsFixed(*params)) return {};
  return ElementMessageType(params->front(), ctx);
}

static std::string TargetSpelling(const Expr* arg, SimContext& ctx,
                                  Arena& arena);

static bool RelatedClasses(const MailboxMessageType& a,
                           const MailboxMessageType& b, SimContext& ctx) {
  if (a.kind != MailboxMessageType::Kind::kClass ||
      b.kind != MailboxMessageType::Kind::kClass)
    return false;
  const ClassTypeInfo* ca = ctx.FindClassType(a.class_name);
  const ClassTypeInfo* cb = ctx.FindClassType(b.class_name);
  return ca != nullptr && cb != nullptr && (ca->IsA(cb) || cb->IsA(ca));
}

static bool RefusesParameterizedArg(const Expr* expr,
                                    const MailboxMessageType& actual,
                                    SimContext& ctx, Arena& arena) {
  MailboxMessageType elem = PropertyElementType(expr, ctx, arena);
  if (actual.EquivalentTo(elem) || RelatedClasses(actual, elem, ctx))
    return false;
  ctx.GetDiag().Error(
      expr->range.start,
      "argument to mailbox method '" + std::string(expr->lhs->rhs->text) +
          "' is not type-equivalent to the element type of parameterized "
          "mailbox '" +
          TargetSpelling(expr->lhs->lhs, ctx, arena) + "'",
      Subclause("15.4.9"));
  return true;
}

static bool RefusesRetrievalTarget(const Expr* expr, SimContext& ctx,
                                   Arena& arena) {
  const Expr* arg = MailboxArg(expr);
  if (arg == nullptr) return false;
  return RefusesParameterizedArg(expr, TargetType(arg, ctx, arena), ctx, arena);
}

static MailboxMessageType RetrievalTargetType(const Expr* expr, SimContext& ctx,
                                              Arena& arena) {
  const Expr* arg = MailboxArg(expr);
  if (arg == nullptr) return {};
  if (IsParameterizedMailbox(expr, ctx, arena)) return {};
  return TargetType(arg, ctx, arena);
}

struct MailboxMessage {
  Logic4Snapshot value;
  MailboxMessageType type;
  bool refused = false;
};

static MailboxMessage MailboxMessageArg(const Expr* expr, SimContext& ctx,
                                        Arena& arena) {
  MailboxMessage msg;
  const Expr* arg = MailboxArg(expr);
  if (arg == nullptr) return msg;
  Logic4Vec val = EvalExpr(arg, ctx, arena);
  msg.value.Capture(val);
  MailboxMessageType actual = ActualMessageType(arg, val, false, ctx, arena);
  msg.refused = RefusesParameterizedArg(expr, actual, ctx, arena);
  msg.type =
      IsParameterizedMailbox(expr, ctx, arena) ? MailboxMessageType{} : actual;
  msg.type.value_kind = actual.kind;
  return msg;
}

static void StoreMailboxMessage(const Expr* arg, const Logic4Vec& msg,
                                SimContext& ctx, Arena& arena) {
  Variable* var = arg->kind == ExprKind::kIdentifier
                      ? ctx.FindVariable(arg->text)
                      : nullptr;
  if (var != nullptr && var->is_string) {
    var->value = StripStringZeros(msg, arena);
    var->NotifyWatchers();
    return;
  }
  PerformBlockingAssign(arg, msg, ctx, arena);
}

static Logic4Vec EvalMailboxTryRetrieve(MailboxObject& mbx, bool remove,
                                        const Expr* expr, SimContext& ctx,
                                        Arena& arena) {
  if (RefusesRetrievalTarget(expr, ctx, arena))
    return MakeLogic4VecVal(arena, 32, 0);
  MailboxMessageType want = RetrievalTargetType(expr, ctx, arena);
  Logic4Snapshot msg;
  int32_t got = remove ? mbx.TryGet(msg, want) : mbx.TryPeek(msg, want);
  const Expr* arg = MailboxArg(expr);
  if (got > 0 && arg != nullptr)
    StoreMailboxMessage(arg, msg.Get(), ctx, arena);
  return MakeLogic4VecVal(arena, 32, static_cast<uint32_t>(got));
}

bool TryEvalMailboxMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                              Logic4Vec& out) {
  if (auto* mbx = MailboxCallTarget(expr, ctx, arena, "num")) {
    out = MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(mbx->Num()));
    return true;
  }
  if (auto* mbx = MailboxCallTarget(expr, ctx, arena, "try_put")) {
    MailboxMessage msg = MailboxMessageArg(expr, ctx, arena);
    auto placed = msg.refused ? 0 : mbx->TryPut(msg.value.Get(), msg.type);
    out = MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(placed));
    return true;
  }
  if (auto* mbx = MailboxCallTarget(expr, ctx, arena, "try_get")) {
    out = EvalMailboxTryRetrieve(*mbx, true, expr, ctx, arena);
    return true;
  }
  if (auto* mbx = MailboxCallTarget(expr, ctx, arena, "try_peek")) {
    out = EvalMailboxTryRetrieve(*mbx, false, expr, ctx, arena);
    return true;
  }
  return false;
}

bool TryMailboxNewAssign(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (!stmt->rhs || stmt->rhs->kind != ExprKind::kCall ||
      stmt->rhs->text != "new")
    return false;
  SyncProperty prop = ResolveSyncProperty(stmt->lhs, ctx, arena);
  if (prop.kind == SyncKind::kMailbox) {
    BuildSyncProperty(prop, stmt->rhs, ctx, arena);
    return true;
  }
  if (TryLocalSyncNewAssign(stmt, ctx, arena)) return true;
  std::string_view key = ScopedOrBareTargetKey(stmt->lhs, arena);
  if (key.empty()) return false;
  MailboxObject** slot = ctx.MailboxSlot(key);
  if (slot == nullptr) return false;
  if (*slot == nullptr || (*slot)->shared) {
    *slot = ctx.GetArena().Create<MailboxObject>();
  }
  (*slot)->Build(MailboxBoundArg(stmt->rhs, ctx, arena));
  HoldSyncVariable(key, ctx);
  return true;
}

bool IsMailboxBlockingCall(const Expr* expr, SimContext& ctx, Arena& arena) {
  return MailboxCallTarget(expr, ctx, arena, "put") != nullptr ||
         MailboxCallTarget(expr, ctx, arena, "get") != nullptr ||
         MailboxCallTarget(expr, ctx, arena, "peek") != nullptr;
}

static std::string_view PartSelectSeparator(const Expr* sel) {
  if (sel->is_part_select_plus) return "+:";
  if (sel->is_part_select_minus) return "-:";
  return ":";
}

static std::string IndexSpelling(const Expr* index, SimContext& ctx,
                                 Arena& arena) {
  if (!index->text.empty()) return std::string(index->text);
  return std::to_string(EvalExpr(index, ctx, arena).ToUint64());
}

static std::string TargetSpelling(const Expr* arg, SimContext& ctx,
                                  Arena& arena) {
  switch (arg->kind) {
    case ExprKind::kMemberAccess:
      return TargetSpelling(arg->lhs, ctx, arena) + "." +
             std::string(arg->rhs->text);
    case ExprKind::kSelect: {
      std::string index = IndexSpelling(arg->index, ctx, arena);
      if (arg->index_end != nullptr) {
        index += PartSelectSeparator(arg);
        index += IndexSpelling(arg->index_end, ctx, arena);
      }
      return TargetSpelling(arg->base, ctx, arena) + "[" + index + "]";
    }
    default:
      return std::string(arg->text);
  }
}

static void FinishMailboxRetrieval(const Expr* expr, const Logic4Vec& msg,
                                   bool type_error, SimContext& ctx,
                                   Arena& arena) {
  const Expr* arg = MailboxArg(expr);
  if (arg == nullptr) return;
  if (!type_error) {
    StoreMailboxMessage(arg, msg, ctx, arena);
    return;
  }
  std::string_view method = expr->lhs->rhs->text;
  ctx.GetDiag().Error(
      arg->range.start,
      "mailbox " + std::string(method) +
          "(): the message's type is not equivalent to the type of '" +
          TargetSpelling(arg, ctx, arena) + "'",
      method == "get" ? Subclause("15.4.5") : Subclause("15.4.7"));
}

static void ReportMailboxWouldBlock(const Expr* expr, std::string_view state,
                                    SimContext& ctx, Arena& arena) {
  std::string_view method = expr->lhs->rhs->text;
  ctx.GetDiag().Error(expr->range.start,
                      "mailbox " + std::string(method) + "(): '" +
                          TargetSpelling(expr->lhs->lhs, ctx, arena) + "' is " +
                          std::string(state) +
                          ", so the call would block inside a function",
                      Subclause("13.4"));
}

static void ExecMailboxRetrievalInFunction(MailboxObject& mbx, bool remove,
                                           const Expr* expr, SimContext& ctx,
                                           Arena& arena) {
  if (RefusesRetrievalTarget(expr, ctx, arena)) return;
  if (mbx.Num() == 0) {
    ReportMailboxWouldBlock(expr, "empty", ctx, arena);
    return;
  }
  MailboxMessageType want = RetrievalTargetType(expr, ctx, arena);
  Logic4Snapshot msg;
  bool type_error = remove ? mbx.Get(msg, want) == MbxGetStatus::kTypeError
                           : mbx.Peek(msg, want) == MbxPeekStatus::kTypeError;
  FinishMailboxRetrieval(expr, msg.Get(), type_error, ctx, arena);
}

bool TryExecMailboxCallInFunction(const Expr* expr, SimContext& ctx,
                                  Arena& arena) {
  if (auto* mbx = MailboxCallTarget(expr, ctx, arena, "put")) {
    MailboxMessage msg = MailboxMessageArg(expr, ctx, arena);
    if (msg.refused) return true;
    if (mbx->Put(msg.value.Get(), msg.type) == MbxPutStatus::kBlock) {
      ReportMailboxWouldBlock(expr, "full", ctx, arena);
    }
    return true;
  }
  if (auto* mbx = MailboxCallTarget(expr, ctx, arena, "get")) {
    ExecMailboxRetrievalInFunction(*mbx, true, expr, ctx, arena);
    return true;
  }
  if (auto* mbx = MailboxCallTarget(expr, ctx, arena, "peek")) {
    ExecMailboxRetrievalInFunction(*mbx, false, expr, ctx, arena);
    return true;
  }
  return false;
}

ExecTask ExecMailboxCall(const Expr* expr, SimContext& ctx, Arena& arena,
                         CallResultReceiverScope& held) {
  if (auto* mbx = MailboxCallTarget(expr, ctx, arena, "put")) {
    MailboxMessage msg = MailboxMessageArg(expr, ctx, arena);
    held.Release();
    if (msg.refused) co_return StmtResult::kDone;
    MailboxMessageType type = msg.type;
    co_await MailboxPutAwaiter{
        .mbx = *mbx, .msg = std::move(msg.value), .type = type, .ctx = &ctx};
    co_return StmtResult::kDone;
  }
  if (auto* mbx = MailboxCallTarget(expr, ctx, arena, "get")) {
    held.Release();
    if (RefusesRetrievalTarget(expr, ctx, arena)) co_return StmtResult::kDone;
    MailboxGetAwaiter get{.mbx = *mbx,
                          .expected = RetrievalTargetType(expr, ctx, arena),
                          .msg = {},
                          .ctx = &ctx};
    MbxGetStatus status = co_await get;
    FinishMailboxRetrieval(expr, get.msg.Get(),
                           status == MbxGetStatus::kTypeError, ctx, arena);
    co_return StmtResult::kDone;
  }
  if (auto* mbx = MailboxCallTarget(expr, ctx, arena, "peek")) {
    held.Release();
    if (RefusesRetrievalTarget(expr, ctx, arena)) co_return StmtResult::kDone;
    MailboxPeekAwaiter peek{.mbx = *mbx,
                            .expected = RetrievalTargetType(expr, ctx, arena),
                            .msg = {},
                            .ctx = &ctx};
    MbxPeekStatus status = co_await peek;
    FinishMailboxRetrieval(expr, peek.msg.Get(),
                           status == MbxPeekStatus::kTypeError, ctx, arena);
  }
  co_return StmtResult::kDone;
}

}  // namespace delta
