// §20.10.1: the elaboration severity system tasks, $fatal, $error, $warning and
// $info written as module items, which run while the design is elaborated.
// Their message is formatted by the formatter $display uses (§21.2.1), the one
// place the elaborator reaches into the simulator, since the clause gives the
// two the same formatting.

#include <cstddef>
#include <cstdint>
#include <format>
#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/types.h"
#include "elaborator/const_eval.h"
#include "elaborator/const_eval_internal.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "simulator/evaluation.h"

namespace delta {

namespace {

// Syntax 20-11 in §20.10 writes finish_number ::= 0 | 1 | 2, and §20.10.1 gives
// the elaboration severity system tasks the same syntax as the run-time ones,
// so the first argument of an elaboration-time $fatal is an optional
// finish_number held to that enumeration. Returns the index of the first
// message-list argument: 1 when a leading integer literal was consumed as the
// finish_number, else 0.
size_t CheckFatalFinishNumber(const Expr* expr, bool is_fatal,
                              DiagEngine& diag) {
  if (is_fatal && !expr->args.empty()) {
    auto* first_arg = expr->args[0];
    if (first_arg->kind == ExprKind::kIntegerLiteral) {
      auto val = first_arg->int_val;
      if (val > 2) {
        diag.Error(first_arg->range.start, "finish_number must be 0, 1, or 2",
                   Subclause("20.10"));
      }
      return 1;
    }
  }
  return 0;
}

// Per §20.10.1, list_of_arguments may only contain a formatting string and
// constant expressions, including constant function calls.
void CheckElabTaskArgsConstant(const Expr* expr, size_t arg_start,
                               std::string_view name, const ScopeMap& scope,
                               DiagEngine& diag) {
  for (size_t i = arg_start; i < expr->args.size(); ++i) {
    auto* arg = expr->args[i];
    if (!arg) continue;
    if (i == arg_start && arg->kind == ExprKind::kStringLiteral) continue;
    if (arg->kind == ExprKind::kStringLiteral) continue;
    if (!IsConstantExpr(arg, scope)) {
      diag.Error(
          arg->range.start,
          std::format("argument to {} must be a constant expression", name),
          Subclause("20.10.1"));
    }
  }
}

// Compose the diagnostic scope name: the module name (if any) joined to the
// trailing generate prefix with underscores trimmed, separated by a dot.
std::string BuildElabTaskScopeName(const RtlirModule* mod,
                                   const std::string& gen_prefix) {
  std::string scope_name = mod ? std::string(mod->name) : std::string{};
  if (!gen_prefix.empty()) {
    std::string trimmed = gen_prefix;
    while (!trimmed.empty() && trimmed.back() == '_') trimmed.pop_back();
    if (!trimmed.empty()) {
      if (!scope_name.empty()) scope_name.push_back('.');
      scope_name += trimmed;
    }
  }
  return scope_name;
}

// Map the elaboration system task name flags to the severity label embedded in
// the emitted message.
std::string ElabTaskSeverity(bool is_fatal, bool is_error, bool is_warning) {
  if (is_fatal) return "FATAL";
  if (is_error) return "ERROR";
  if (is_warning) return "WARNING";
  return "INFO";
}

// Extract the optional user message: the leading string-literal argument of the
// message list, with surrounding double quotes stripped.
std::string ExtractElabTaskUserMsg(const Expr* expr, size_t arg_start) {
  std::string user_msg;
  if (arg_start < expr->args.size() &&
      expr->args[arg_start]->kind == ExprKind::kStringLiteral) {
    user_msg = std::string(expr->args[arg_start]->text);
    if (user_msg.size() >= 2 && user_msg.front() == '"' &&
        user_msg.back() == '"') {
      user_msg = user_msg.substr(1, user_msg.size() - 2);
    }
  }
  return user_msg;
}

// One constant argument as the value $display formats (§21.2.1): its width,
// its signedness and every word of its bits.
Logic4Vec ConstArgValue(const ConstVal& v, Arena& arena) {
  Logic4Vec out =
      MakeLogic4VecVal(arena, v.width, static_cast<uint64_t>(v.value));
  for (size_t i = 0; i < v.high_words.size() && i + 1 < out.nwords; ++i) {
    out.words[i + 1].aval = v.high_words[i];
  }
  out.is_signed = v.is_signed;
  return out;
}

// §20.10.1: the message of an elaboration severity task, its list_of_arguments
// formatted as $display formats them: a leading string literal is the format,
// and each constant expression after it the value of the next specifier. An
// argument that is not constant leaves the format as written, the call having
// been reported by CheckElabTaskArgsConstant.
std::string FormatElabTaskMessage(const Expr* expr, size_t arg_start,
                                  const ScopeMap& scope, Arena& arena) {
  std::string fmt = ExtractElabTaskUserMsg(expr, arg_start);
  std::vector<Logic4Vec> vals;
  for (size_t i = arg_start + 1; i < expr->args.size(); ++i) {
    std::optional<ConstVal> v = ConstEvalFull(expr->args[i], scope);
    if (!v) return fmt;
    vals.push_back(ConstArgValue(*v, arena));
  }
  return FormatDisplay(fmt, vals);
}

}  // namespace

void Elaborator::ValidateElabSystemTask(const ModuleItem* item,
                                        const RtlirModule* mod) {
  auto* expr = item->init_expr;
  if (!expr || expr->kind != ExprKind::kSystemCall) return;

  auto name = expr->callee;
  bool is_fatal = name == "$fatal";
  bool is_error = name == "$error";
  bool is_warning = name == "$warning";
  bool is_info = name == "$info";
  if (!is_fatal && !is_error && !is_warning && !is_info) return;

  size_t arg_start = CheckFatalFinishNumber(expr, is_fatal, diag_);

  ScopeMap scope = mod ? BuildParamScope(mod) : ScopeMap{};
  // §11.2.1: a genvar is a constant expression. When this task sits inside a
  // generate body, overlay the active generate bindings (genvar values and any
  // generate-block localparams) so a genvar argument — as in §20.10.1
  // Example 2 — is recognized as constant rather than wrongly rejected.
  for (const auto& [gname, gval] : gen_const_scope_) scope[gname] = gval;
  CheckElabTaskArgsConstant(expr, arg_start, name, scope, diag_);

  std::string scope_name = BuildElabTaskScopeName(mod, gen_prefix_);
  std::string severity = ElabTaskSeverity(is_fatal, is_error, is_warning);
  std::string user_msg = FormatElabTaskMessage(expr, arg_start, scope, arena_);

  std::string message =
      scope_name.empty() ? std::format("elaboration {}: {}", severity, user_msg)
                         : std::format("elaboration {} in scope '{}': {}",
                                       severity, scope_name, user_msg);

  // Per §20.10.1, $fatal and $error block simulation; $warning and $info do
  // not affect the rest of elaboration or simulation. All four shall emit a
  // tool-specific message that names the call site (file/line carried by
  // the DiagEngine, scope embedded in the message body), each with its own
  // severity: an error for $fatal and $error, a warning otherwise.
  if (is_fatal || is_error) {
    diag_.Error(item->loc, message, Subclause("20.10.1"));
  } else {
    diag_.Warning(item->loc, message, Subclause("20.10.1"));
  }
  elab_last_severity_ = severity;
  elab_last_severity_msg_ = user_msg;
  elab_last_severity_scope_ = scope_name;
  elab_last_severity_loc_ = item->loc;
  if (is_fatal || is_error) {
    elab_simulation_blocked_ = true;
  }
}

}  // namespace delta
