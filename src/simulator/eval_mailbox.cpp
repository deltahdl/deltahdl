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
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "simulator/awaiters.h"
#include "simulator/class_object.h"
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

// §6.22.1 b) and d) with §6.22.2 a): a typedef that renames a class is a
// matching type of the class, so a handle declared through it is of the
// class's own type and equivalent to one declared by the class name. A
// handle a procedural block declares through the typedef is recorded under
// the typedef's name (TryExecClassVarDecl in statement_assign_decl.cpp),
// which the run knows the class by through the alias RegisterClassTypeAliases
// binds, so the message is typed by the class's own name; recorded as the
// typedef's name, `c_t h` put and `C g` got were reported not equivalent. A
// name no class record answers -- the built-in semaphore's or mailbox's --
// is kept as recorded.
static MailboxMessageType ClassMessageType(std::string_view name,
                                           SimContext& ctx) {
  const ClassTypeInfo* cls = ctx.FindClassType(name);
  if (cls != nullptr) name = cls->name;
  return MailboxMessageType::Class(name);
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

// §6.22.2 c) with §6.11.2: the number of states a declared kind's values
// have -- four for logic, reg, integer and time, two for the rest -- and
// unknown for a type name, whose definition the kind records do not follow.
static MailboxMessageType::States StatesOfKind(DataTypeKind kind) {
  if (kind == DataTypeKind::kNamed) return MailboxMessageType::States::kUnknown;
  return Is4stateType(kind) ? MailboxMessageType::States::kFour
                            : MailboxMessageType::States::kTwo;
}

// §6.22.2: the type a declaration of kind `kind` and `width` bits gives a
// structure member or an array element: a string or a real is of its own
// built-in type, a real told from a shortreal by its width as
// VariableMessageType tells them, and anything else is integral.
static MailboxMessageType DeclaredKindType(DataTypeKind kind, uint32_t width,
                                           bool is_signed) {
  if (kind == DataTypeKind::kString) return MailboxMessageType::String();
  if (kind == DataTypeKind::kReal) return MailboxMessageType::Real(64);
  if (kind == DataTypeKind::kShortreal) return MailboxMessageType::Real(32);
  return MailboxMessageType::Integral(width, is_signed, StatesOfKind(kind));
}

// §7.2.1: the dotted member path of the access `s.f` or `s.p.f`, appended to
// `path`, and the variable at its root; nullptr where the root is not a
// bare name.
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

// §7.2.1: the field the dotted member path `f` or `p.f` names in the layout
// `info`, descending through the nested layouts, or nullptr where a segment
// names no member.
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

// §7.2.1 with §6.22.2 c): the type of the member `s.f` of a structure or
// union whose layout was registered, that of the member's declaration -- its
// kind, its width and its signedness, the modifier the member was declared
// with or its kind's default (StructFieldInfo::is_signed). Read as signed by
// its kind alone, a `logic signed [7:0]` member typed unsigned, so a get()
// into it refused the signed 8-bit message and took an unsigned one. A member
// of an object no layout was registered for -- a class property, a handle's
// member -- is of any type.
static MailboxMessageType MemberTargetType(const Expr* arg, SimContext& ctx) {
  std::string path;
  const Expr* root = MemberPathRoot(arg, path);
  if (root == nullptr) return {};
  const StructFieldInfo* field =
      StructFieldByPath(StructLayoutOfName(root->text, ctx), path);
  if (field == nullptr) return {};
  return DeclaredKindType(field->type_kind, field->width, field->is_signed);
}

// §7.4.2 with §6.22.2: the type of the element `a[i]` of the unpacked array
// `name`, that of the array's element type: the element's own variable says
// whether it is signed where the array's leaves were created, and the shape
// record answers the width, the kind and the number of states. A shape
// registered with no element kind -- a dynamic array's -- leaves the
// element of any type.
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

// §11.5 with §6.22.2: the type of the select `a[i]`: an element of an array
// of class handles is of the class recorded under the array's name; an
// element of any other unpacked array is of its element type; and a
// bit-select or part-select of a packed object is an unsigned integral of
// the bits it names (§11.8.1 has a select unsigned regardless of its
// operand) with the object's number of states. A slice of an unpacked
// array, a select of a string and a select whose base is not a bare name
// are of any type.
static MailboxMessageType ElementTargetType(const Expr* arg, SimContext& ctx,
                                            Arena& arena) {
  const Expr* base = arg->base;
  if (base == nullptr || base->kind != ExprKind::kIdentifier) return {};
  std::string_view class_name = ctx.GetVariableClassType(base->text);
  if (!class_name.empty()) return ClassMessageType(class_name, ctx);
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

// §15.4.5 through §15.4.8: the type of the left-hand expression a retrieval
// or a copy names, or of the same shape placed by put(): a variable is of
// its declared kind, a member of the member's declared type and a select of
// the element's. Any other shape is of any type.
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

// §11.6.1 and §11.8.1 with §6.22.2: the type of an operator expression, as
// its self-determined value carries it -- a string or a real of the value's
// width, else an integral of the computed width and signedness, whose
// number of states no operator records, so §6.22.2 c)'s state count is left
// unknown as it is for a literal.
static MailboxMessageType ComputedMessageType(const Logic4Vec& val) {
  if (val.is_string) return MailboxMessageType::String();
  if (val.is_real) return MailboxMessageType::Real(val.width);
  return MailboxMessageType::Integral(val.width, val.is_signed,
                                      MailboxMessageType::States::kUnknown);
}

// §11.4.11 with §8.4: whether a conditional operator chooses between class
// handles, whose value is a handle and not the integral its words are: an
// arm names a class variable, or is itself such a conditional.
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

// §15.4.5: the type a message is placed with, as the evaluator knows the
// actual: a variable is of its declared kind, a member or an element of its
// declared type, a string or real literal of that type, and an integer
// literal an integral of its width and signedness whose number of states no
// literal spells out, so §6.22.2 c)'s state count is left unknown and a
// 2-state or a 4-state variable of the width alike retrieves it. An
// operator expression is of its self-determined type, a conditional over
// class handles excepted, which is of any type as a call is; and so is
// every message of a parameterized mailbox, whose actuals the elaborator
// verified.
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

// §15.4.5 through §15.4.8: the variable a retrieval or a copy names, its
// one argument, or nullptr when the call names none.
static const Expr* MailboxArg(const Expr* expr) {
  return expr->args.empty() ? nullptr : expr->args[0];
}

// §15.4.5 through §15.4.8: the type the message must be equivalent to, that
// of the left-hand expression the call names. A parameterized mailbox's
// messages were verified by the compiler (§15.4.9), so its target expects
// any type.
static MailboxMessageType RetrievalTargetType(const Expr* expr, SimContext& ctx,
                                              Arena& arena) {
  const Expr* arg = MailboxArg(expr);
  if (arg == nullptr) return {};
  if (IsParameterizedMailbox(expr, ctx, arena)) return {};
  return TargetType(arg, ctx, arena);
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
  msg.type = ActualMessageType(
      arg, val, IsParameterizedMailbox(expr, ctx, arena), ctx, arena);
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

// §11.5.1: the separator a part-select was written with.
static std::string_view PartSelectSeparator(const Expr* sel) {
  if (sel->is_part_select_plus) return "+:";
  if (sel->is_part_select_minus) return "-:";
  return ":";
}

// The spelling of a select's index for a report: as written where it is a
// name or a literal, else the value it evaluated to.
static std::string IndexSpelling(const Expr* index, SimContext& ctx,
                                 Arena& arena) {
  if (!index->text.empty()) return std::string(index->text);
  return std::to_string(EvalExpr(index, ctx, arena).ToUint64());
}

// §15.4.5 through §15.4.8: the left-hand expression a retrieval names, as a
// report spells it -- a bare name, a member access `s.f` and a select
// `a[i]` or `v[7:0]` as written.
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
          TargetSpelling(arg, ctx, arena) + "'",
      method == "get" ? Subclause("15.4.5") : Subclause("15.4.7"));
}

// §13.4: the report for a put(), get() or peek() a function body reached
// while the mailbox, spelled as the receiver was written, is in the `state`
// -- full or empty -- that would make the call wait.
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

// §15.4.5 and §15.4.7 inside a function body: get() removes and peek()
// copies the front message where the mailbox holds one, which then reaches
// the named variable or is §15.4.5's and §15.4.7's type error as it is once
// ExecMailboxCall's wait ends; an empty mailbox, on which either would wait,
// is §13.4's report with the variable as it was.
static void ExecMailboxRetrievalInFunction(MailboxObject& mbx, bool remove,
                                           const Expr* expr, SimContext& ctx,
                                           Arena& arena) {
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

// §15.4.3 inside a function body: put() places its message where the
// mailbox has room, as ExecMailboxCall's awaiter does before it would wait,
// and a full bounded mailbox, on which it would wait, is §13.4's report with
// the message not placed.
bool TryExecMailboxCallInFunction(const Expr* expr, SimContext& ctx,
                                  Arena& arena) {
  if (auto* mbx = MailboxCallTarget(expr, ctx, arena, "put")) {
    MailboxMessage msg = MailboxMessageArg(expr, ctx, arena);
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
    MailboxGetAwaiter get{*mbx, RetrievalTargetType(expr, ctx, arena), {}};
    MbxGetStatus status = co_await get;
    FinishMailboxRetrieval(expr, get.msg.Get(),
                           status == MbxGetStatus::kTypeError, ctx, arena);
    co_return StmtResult::kDone;
  }
  if (auto* mbx = MailboxCallTarget(expr, ctx, arena, "peek")) {
    MailboxPeekAwaiter peek{*mbx, RetrievalTargetType(expr, ctx, arena), {}};
    MbxPeekStatus status = co_await peek;
    FinishMailboxRetrieval(expr, peek.msg.Get(),
                           status == MbxPeekStatus::kTypeError, ctx, arena);
  }
  co_return StmtResult::kDone;
}

}  // namespace delta
