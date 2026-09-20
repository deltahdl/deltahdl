#include "simulator/eval_mailbox.h"

#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "simulator/awaiters.h"
#include "simulator/eval_function_internal.h"
#include "simulator/eval_semaphore.h"
#include "simulator/eval_string.h"
#include "simulator/evaluation.h"
#include "simulator/exec_task.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/stmt_result.h"
#include "simulator/sync_objects.h"
#include "simulator/variable.h"

namespace delta {

// §26.3 admits a package-qualified mailbox as the receiver, `p::mbx.get(x)`,
// found under the "p.mbx" key ExtractHandleMethodCallParts answers. This is
// asked of every call statement, so the method's name is matched before the
// key is made.
MailboxObject* MailboxCallTarget(const Expr* expr, SimContext& ctx,
                                 Arena& arena, std::string_view method) {
  if (!expr || expr->kind != ExprKind::kCall) return nullptr;
  const auto* access = expr->lhs;
  if (!access || access->kind != ExprKind::kMemberAccess) return nullptr;
  if (!access->rhs || access->rhs->text != method) return nullptr;
  MethodCallParts parts;
  if (!ExtractHandleMethodCallParts(expr, arena, parts)) return nullptr;
  return ctx.FindMailbox(parts.var_name);
}

int32_t MailboxBoundArg(const Expr* new_expr, SimContext& ctx, Arena& arena) {
  if (new_expr->args.empty() || !new_expr->args[0]) return 0;
  auto val = EvalExpr(new_expr->args[0], ctx, arena);
  return static_cast<int32_t>(static_cast<uint32_t>(val.ToUint64()));
}

// §15.4.9: whether the call's receiver was declared `mailbox #(T)` with a
// type other than dynamic_type. The compiler then verifies that every
// transfer method's argument is of a type equivalent to T (the elaborator's
// CheckMailboxCallExpr), so no mismatch is left for the run-time check to
// find, and the messages of such a mailbox record no type. The declaration's
// parameter list is recorded under the variable's own key by
// RecordClassSpecialization, one of the keys the mailbox itself is found
// under.
static bool IsParameterizedMailbox(const Expr* expr, SimContext& ctx,
                                   Arena& arena) {
  MethodCallParts parts;
  if (!ExtractHandleMethodCallParts(expr, arena, parts)) return false;
  for (const std::string& key : ctx.ScopedObjectKeys(parts.var_name)) {
    const std::vector<DataType>* params = ctx.FindVariableClassTypeParams(key);
    if (params == nullptr) continue;
    if (params->empty()) return false;
    const DataType& elem = params->front();
    return elem.kind != DataTypeKind::kNamed ||
           elem.type_name != "dynamic_type";
  }
  return false;
}

// §15.4.5 with §6.22.2: the type of the variable `name`, as the kind records
// the lowerer left describe it. A class handle is of its declared class,
// which §6.22.1 d) matches with itself alone; a string and a real are of
// their own built-in types (§6.22.1 a), a real told from a shortreal by its
// width; and anything else is integral, equivalent to another integral type
// when the total bits, the signedness and the number of states agree
// (§6.22.2 c). A subroutine's real formal is registered nowhere and is known
// by the mark its value carries. A name no variable answers records no type.
static MailboxMessageType VariableMessageType(std::string_view name,
                                              SimContext& ctx) {
  std::string_view class_name = ctx.GetVariableClassType(name);
  if (!class_name.empty()) return MailboxMessageType::Class(class_name);
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

// §15.4.5: the type a message is placed with, as the evaluator knows the
// actual: a variable is of its declared kind, a string or real literal of
// that type, and an integer literal an integral of its width and signedness
// whose number of states no literal spells out, so §6.22.2 c)'s state count
// is left unknown and a 2-state or a 4-state variable of the width alike
// retrieves it. A computed expression records no type, as the elaborator's
// compile-time check leaves one unchecked, and nor does any message of a
// parameterized mailbox.
static MailboxMessageType ActualMessageType(const Expr* arg,
                                            const Logic4Vec& val, bool typed,
                                            SimContext& ctx) {
  if (typed) return {};
  switch (arg->kind) {
    case ExprKind::kIdentifier:
      return VariableMessageType(arg->text, ctx);
    case ExprKind::kStringLiteral:
      return MailboxMessageType::String();
    case ExprKind::kRealLiteral:
    case ExprKind::kTimeLiteral:
      return MailboxMessageType::Real(val.width);
    case ExprKind::kIntegerLiteral:
      return MailboxMessageType::Integral(val.width, val.is_signed,
                                          MailboxMessageType::States::kUnknown);
    default:
      return {};
  }
}

// §15.4.5 through §15.4.8: the variable a retrieval or a copy names, its
// one argument, or nullptr when the call names none.
static const Expr* MailboxArg(const Expr* expr) {
  return expr->args.empty() ? nullptr : expr->args[0];
}

// §15.4.5 through §15.4.8: the type the message must be equivalent to, that
// of the variable the call names. A parameterized mailbox's messages were
// verified by the compiler (§15.4.9), and a target that is not a bare name
// -- a select or a member -- has no kind record to read, so both expect any
// type.
static MailboxMessageType RetrievalTargetType(const Expr* expr, SimContext& ctx,
                                              Arena& arena) {
  const Expr* arg = MailboxArg(expr);
  if (arg == nullptr || arg->kind != ExprKind::kIdentifier) return {};
  if (IsParameterizedMailbox(expr, ctx, arena)) return {};
  return VariableMessageType(arg->text, ctx);
}

// §15.4.3 and §15.4.4: the message put() or try_put() places, any singular
// expression, an object handle among them, evaluated whole and held with
// the type it is placed under.
struct MailboxMessage {
  Logic4Snapshot value;
  MailboxMessageType type;
};

static MailboxMessage MailboxMessageArg(const Expr* expr, SimContext& ctx,
                                        Arena& arena) {
  MailboxMessage msg;
  const Expr* arg = MailboxArg(expr);
  if (arg == nullptr) return msg;
  Logic4Vec val = EvalExpr(arg, ctx, arena);
  msg.value.Capture(val);
  msg.type = ActualMessageType(arg, val,
                               IsParameterizedMailbox(expr, ctx, arena), ctx);
  return msg;
}

// §15.4.5 through §15.4.8: the message a retrieval or a copy hands out goes
// to the variable the call's one argument names, a valid left-hand
// expression, sized to it as an assignment sizes its value. A string
// variable takes the message's characters whole, as an assignment to one
// does (AssignToScalarLhs) and as $sformat's store does: PerformBlockingAssign
// sizes a value to the variable's width, which for a string is the width of
// the characters it happened to hold.
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

// §15.4.6 and §15.4.8: try_get() removes the front message and try_peek()
// copies it, each answering 0 for an empty mailbox, a negative integer for a
// message whose type is not equivalent to the variable's, which stays where
// it is, and a positive integer once the message has reached the variable.
static Logic4Vec EvalMailboxTryRetrieve(MailboxObject& mbx, bool remove,
                                        const Expr* expr, SimContext& ctx,
                                        Arena& arena) {
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
    auto placed = mbx->TryPut(msg.value.Get(), msg.type);
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

// §26.3: the target may be a package's mailbox named through the package
// scope resolution operator, `p::mbx = new(2)`, held under the "p.mbx" key
// ScopedOrBareTargetKey answers; a package's mailbox is not created today,
// so the scoped form finds none until it is.
bool TryMailboxNewAssign(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (!stmt->rhs || stmt->rhs->kind != ExprKind::kCall ||
      stmt->rhs->text != "new")
    return false;
  std::string_view key = ScopedOrBareTargetKey(stmt->lhs, arena);
  if (key.empty()) return false;
  auto* mbx = ctx.FindMailbox(key);
  if (!mbx) return false;
  mbx->Build(MailboxBoundArg(stmt->rhs, ctx, arena));
  return true;
}

bool IsMailboxBlockingCall(const Expr* expr, SimContext& ctx, Arena& arena) {
  return MailboxCallTarget(expr, ctx, arena, "put") != nullptr ||
         MailboxCallTarget(expr, ctx, arena, "get") != nullptr ||
         MailboxCallTarget(expr, ctx, arena, "peek") != nullptr;
}

// §15.4.5 and §15.4.7: what get() and peek() do once the wait ends. The
// message goes to the variable the call names; a message whose type is not
// equivalent to the variable's is the run-time error both subclauses
// describe, reported at the variable under the subclause of the method that
// found it, with the message left in the queue and the variable as it was.
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
          std::string(arg->text) + "'",
      method == "get" ? Subclause("15.4.5") : Subclause("15.4.7"));
}

// §15.4.3: the message is evaluated before the process may suspend, so a
// put() that waits for room stores the value its argument had when the call
// was reached. §15.4.5 and §15.4.7: the message get() or peek() waited for
// reaches the named variable once the wait ends, at the time of the put()
// that ended it. The awaiters are named so their message outlives the wait.
ExecTask ExecMailboxCall(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (auto* mbx = MailboxCallTarget(expr, ctx, arena, "put")) {
    MailboxMessage msg = MailboxMessageArg(expr, ctx, arena);
    MailboxMessageType type = msg.type;
    co_await MailboxPutAwaiter{*mbx, std::move(msg.value), type};
    co_return StmtResult::kDone;
  }
  if (auto* mbx = MailboxCallTarget(expr, ctx, arena, "get")) {
    MailboxGetAwaiter get{*mbx, RetrievalTargetType(expr, ctx, arena)};
    MbxGetStatus status = co_await get;
    FinishMailboxRetrieval(expr, get.msg.Get(),
                           status == MbxGetStatus::kTypeError, ctx, arena);
    co_return StmtResult::kDone;
  }
  if (auto* mbx = MailboxCallTarget(expr, ctx, arena, "peek")) {
    MailboxPeekAwaiter peek{*mbx, RetrievalTargetType(expr, ctx, arena)};
    MbxPeekStatus status = co_await peek;
    FinishMailboxRetrieval(expr, peek.msg.Get(),
                           status == MbxPeekStatus::kTypeError, ctx, arena);
  }
  co_return StmtResult::kDone;
}

}  // namespace delta
