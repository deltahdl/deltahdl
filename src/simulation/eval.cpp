#include "simulation/eval.h"

#include <cstdio>
#include <iostream>
#include <string>

#include "common/arena.h"
#include "lexer/token.h"
#include "parser/ast.h"
#include "simulation/sim_context.h"

namespace delta {

// --- Literal evaluation ---

static Logic4Vec EvalIntLiteral(const Expr* expr, Arena& arena) {
  return MakeLogic4VecVal(arena, 32, expr->int_val);
}

static Logic4Vec EvalStringLiteral(const Expr* expr, Arena& arena) {
  auto text = expr->text;
  // Strip surrounding quotes.
  if (text.size() >= 2 && text.front() == '"') {
    text = text.substr(1, text.size() - 2);
  }
  uint32_t width = static_cast<uint32_t>(text.size()) * 8;
  if (width == 0) width = 8;
  auto vec = MakeLogic4Vec(arena, width);
  for (size_t i = 0; i < text.size(); ++i) {
    auto byte_idx = static_cast<uint32_t>(text.size() - 1 - i);
    uint32_t word = (byte_idx * 8) / 64;
    uint32_t bit = (byte_idx * 8) % 64;
    vec.words[word].aval |= static_cast<uint64_t>(text[i]) << bit;
  }
  return vec;
}

// --- Identifier evaluation ---

static Logic4Vec EvalIdentifier(const Expr* expr, SimContext& ctx,
                                Arena& arena) {
  auto* var = ctx.FindVariable(expr->text);
  if (var) return var->value;
  return MakeLogic4Vec(arena, 1);  // X for unknown
}

// --- Unary operations ---

static Logic4Vec EvalUnaryOp(TokenKind op, Logic4Vec operand, Arena& arena) {
  if (operand.nwords == 0) return operand;
  auto result = MakeLogic4Vec(arena, operand.width);

  switch (op) {
    case TokenKind::kTilde:
      for (uint32_t i = 0; i < result.nwords; ++i) {
        result.words[i] = Logic4Not(operand.words[i]);
      }
      return result;
    case TokenKind::kBang: {
      uint64_t val = operand.ToUint64();
      return MakeLogic4VecVal(arena, 1, val == 0 ? 1 : 0);
    }
    case TokenKind::kMinus: {
      uint64_t val = operand.ToUint64();
      return MakeLogic4VecVal(arena, operand.width, -val);
    }
    default:
      return operand;
  }
}

// --- Binary arithmetic ---

static Logic4Vec EvalBinaryArith(TokenKind op, Logic4Vec lhs, Logic4Vec rhs,
                                 Arena& arena) {
  uint64_t lv = lhs.ToUint64();
  uint64_t rv = rhs.ToUint64();
  uint32_t width = (lhs.width > rhs.width) ? lhs.width : rhs.width;
  uint64_t result = 0;

  switch (op) {
    case TokenKind::kPlus:
      result = lv + rv;
      break;
    case TokenKind::kMinus:
      result = lv - rv;
      break;
    case TokenKind::kStar:
      result = lv * rv;
      break;
    case TokenKind::kSlash:
      result = (rv != 0) ? lv / rv : 0;
      break;
    case TokenKind::kPercent:
      result = (rv != 0) ? lv % rv : 0;
      break;
    default:
      break;
  }
  return MakeLogic4VecVal(arena, width, result);
}

// --- Binary bitwise ---

static Logic4Vec EvalBinaryBitwise(TokenKind op, Logic4Vec lhs, Logic4Vec rhs,
                                   Arena& arena) {
  uint32_t width = (lhs.width > rhs.width) ? lhs.width : rhs.width;
  auto result = MakeLogic4Vec(arena, width);
  uint32_t words = result.nwords;

  for (uint32_t i = 0; i < words; ++i) {
    auto lw = (i < lhs.nwords) ? lhs.words[i] : Logic4Word{};
    auto rw = (i < rhs.nwords) ? rhs.words[i] : Logic4Word{};
    switch (op) {
      case TokenKind::kAmp:
        result.words[i] = Logic4And(lw, rw);
        break;
      case TokenKind::kPipe:
        result.words[i] = Logic4Or(lw, rw);
        break;
      case TokenKind::kCaret:
        result.words[i] = Logic4Xor(lw, rw);
        break;
      default:
        break;
    }
  }
  return result;
}

// --- Binary comparison and shifts ---

static Logic4Vec EvalBinaryCompare(TokenKind op, Logic4Vec lhs, Logic4Vec rhs,
                                   Arena& arena) {
  uint64_t lv = lhs.ToUint64();
  uint64_t rv = rhs.ToUint64();
  uint64_t result = 0;

  switch (op) {
    case TokenKind::kEqEq:
    case TokenKind::kEqEqEq:
      result = static_cast<uint64_t>(lv == rv);
      break;
    case TokenKind::kBangEq:
    case TokenKind::kBangEqEq:
      result = static_cast<uint64_t>(lv != rv);
      break;
    case TokenKind::kLt:
      result = static_cast<uint64_t>(lv < rv);
      break;
    case TokenKind::kGt:
      result = static_cast<uint64_t>(lv > rv);
      break;
    case TokenKind::kLtEq:
      result = static_cast<uint64_t>(lv <= rv);
      break;
    case TokenKind::kGtEq:
      result = static_cast<uint64_t>(lv >= rv);
      break;
    case TokenKind::kLtLt:
    case TokenKind::kLtLtLt:
      return MakeLogic4VecVal(arena, lhs.width, lv << rv);
    case TokenKind::kGtGt:
    case TokenKind::kGtGtGt:
      return MakeLogic4VecVal(arena, lhs.width, lv >> rv);
    case TokenKind::kAmpAmp:
      result = static_cast<uint64_t>(lv != 0 && rv != 0);
      break;
    case TokenKind::kPipePipe:
      result = static_cast<uint64_t>(lv != 0 || rv != 0);
      break;
    default:
      break;
  }
  return MakeLogic4VecVal(arena, 1, result);
}

// --- Binary dispatch ---

static Logic4Vec EvalBinaryOp(TokenKind op, Logic4Vec lhs, Logic4Vec rhs,
                              Arena& arena) {
  switch (op) {
    case TokenKind::kPlus:
    case TokenKind::kMinus:
    case TokenKind::kStar:
    case TokenKind::kSlash:
    case TokenKind::kPercent:
      return EvalBinaryArith(op, lhs, rhs, arena);
    case TokenKind::kAmp:
    case TokenKind::kPipe:
    case TokenKind::kCaret:
      return EvalBinaryBitwise(op, lhs, rhs, arena);
    default:
      return EvalBinaryCompare(op, lhs, rhs, arena);
  }
}

// --- System call formatting ---

static std::string FormatArg(const Logic4Vec& val, char spec) {
  uint64_t v = val.ToUint64();
  char buf[64];
  switch (spec) {
    case 'd':
      std::snprintf(buf, sizeof(buf), "%llu",
                    static_cast<unsigned long long>(v));
      return buf;
    case 'h':
    case 'x':
      std::snprintf(buf, sizeof(buf), "%llx",
                    static_cast<unsigned long long>(v));
      return buf;
    case 'b':
      return val.ToString();
    case 't':
      std::snprintf(buf, sizeof(buf), "%llu",
                    static_cast<unsigned long long>(v));
      return buf;
    default:
      return val.ToString();
  }
}

static std::string FormatDisplay(const std::string& fmt,
                                 const std::vector<Logic4Vec>& vals) {
  std::string out;
  size_t vi = 0;
  for (size_t i = 0; i < fmt.size(); ++i) {
    if (fmt[i] == '%' && i + 1 < fmt.size()) {
      char spec = fmt[i + 1];
      if (vi < vals.size()) {
        out += FormatArg(vals[vi++], spec);
      }
      ++i;
    } else if (fmt[i] == '\\' && i + 1 < fmt.size()) {
      if (fmt[i + 1] == 'n') {
        out += '\n';
      } else {
        out += fmt[i + 1];
      }
      ++i;
    } else {
      out += fmt[i];
    }
  }
  return out;
}

// --- PRNG system calls ---

static Logic4Vec EvalPrngCall(const Expr* expr, SimContext& ctx, Arena& arena,
                              std::string_view name) {
  if (name == "$random") {
    return MakeLogic4VecVal(arena, 32, ctx.Random32());
  }
  if (name == "$urandom") {
    return MakeLogic4VecVal(arena, 32, ctx.Urandom32());
  }
  if (name == "$urandom_range") {
    uint32_t max_val = 0;
    uint32_t min_val = 0;
    if (!expr->args.empty()) {
      max_val =
          static_cast<uint32_t>(EvalExpr(expr->args[0], ctx, arena).ToUint64());
    }
    if (expr->args.size() > 1) {
      min_val =
          static_cast<uint32_t>(EvalExpr(expr->args[1], ctx, arena).ToUint64());
    }
    return MakeLogic4VecVal(arena, 32, ctx.UrandomRange(min_val, max_val));
  }
  return MakeLogic4VecVal(arena, 1, 0);
}

// --- System call evaluation ---

static std::string ExtractFormatString(const Expr* first_arg) {
  auto text = first_arg->text;
  if (text.size() >= 2 && text.front() == '"') {
    return std::string(text.substr(1, text.size() - 2));
  }
  return std::string(text);
}

static void ExecDisplayWrite(const Expr* expr, SimContext& ctx, Arena& arena) {
  std::string fmt;
  std::vector<Logic4Vec> arg_vals;
  for (size_t i = 0; i < expr->args.size(); ++i) {
    auto val = EvalExpr(expr->args[i], ctx, arena);
    if (i == 0 && expr->args[i]->kind == ExprKind::kStringLiteral) {
      fmt = ExtractFormatString(expr->args[i]);
    } else {
      arg_vals.push_back(val);
    }
  }
  std::string output = fmt.empty() ? "" : FormatDisplay(fmt, arg_vals);
  std::cout << output;
  if (expr->callee == "$display") std::cout << "\n";
}

static void ExecSeverityTask(const Expr* expr, SimContext& ctx, Arena& arena,
                             const char* prefix, std::ostream& os) {
  std::string fmt;
  std::vector<Logic4Vec> arg_vals;
  size_t start_idx = 0;

  // $fatal's first arg may be a numeric finish_number — skip it.
  if (std::string_view(prefix) == "FATAL" && !expr->args.empty()) {
    if (expr->args[0]->kind != ExprKind::kStringLiteral) {
      EvalExpr(expr->args[0], ctx, arena);
      start_idx = 1;
    }
  }

  for (size_t i = start_idx; i < expr->args.size(); ++i) {
    auto val = EvalExpr(expr->args[i], ctx, arena);
    if (i == start_idx && expr->args[i]->kind == ExprKind::kStringLiteral) {
      fmt = ExtractFormatString(expr->args[i]);
    } else {
      arg_vals.push_back(val);
    }
  }
  std::string msg = fmt.empty() ? "" : FormatDisplay(fmt, arg_vals);
  os << prefix << ": " << msg << "\n";
}

static Logic4Vec EvalSystemCall(const Expr* expr, SimContext& ctx,
                                Arena& arena) {
  auto name = expr->callee;

  if (name == "$display" || name == "$write") {
    ExecDisplayWrite(expr, ctx, arena);
    return MakeLogic4VecVal(arena, 1, 0);
  }

  if (name == "$finish" || name == "$stop") {
    ctx.RequestStop();
    return MakeLogic4VecVal(arena, 1, 0);
  }

  if (name == "$time") {
    return MakeLogic4VecVal(arena, 64, ctx.CurrentTime().ticks);
  }

  if (name == "$fatal") {
    ExecSeverityTask(expr, ctx, arena, "FATAL", std::cerr);
    ctx.RequestStop();
    return MakeLogic4VecVal(arena, 1, 0);
  }
  if (name == "$error") {
    ExecSeverityTask(expr, ctx, arena, "ERROR", std::cerr);
    return MakeLogic4VecVal(arena, 1, 0);
  }
  if (name == "$warning") {
    ExecSeverityTask(expr, ctx, arena, "WARNING", std::cout);
    return MakeLogic4VecVal(arena, 1, 0);
  }
  if (name == "$info") {
    ExecSeverityTask(expr, ctx, arena, "INFO", std::cout);
    return MakeLogic4VecVal(arena, 1, 0);
  }

  return EvalPrngCall(expr, ctx, arena, name);
}

// --- Concatenation ---

static Logic4Vec EvalConcat(const Expr* expr, SimContext& ctx, Arena& arena) {
  uint32_t total_width = 0;
  std::vector<Logic4Vec> parts;
  for (auto* elem : expr->elements) {
    parts.push_back(EvalExpr(elem, ctx, arena));
    total_width += parts.back().width;
  }
  if (total_width == 0) return MakeLogic4Vec(arena, 1);

  auto result = MakeLogic4Vec(arena, total_width);
  uint32_t bit_pos = 0;
  for (auto it = parts.rbegin(); it != parts.rend(); ++it) {
    uint64_t val = it->ToUint64();
    uint32_t word = bit_pos / 64;
    uint32_t bit = bit_pos % 64;
    if (word < result.nwords) {
      result.words[word].aval |= val << bit;
    }
    bit_pos += it->width;
  }
  return result;
}

// --- Select (bit/part) ---

static Logic4Vec EvalSelect(const Expr* expr, SimContext& ctx, Arena& arena) {
  auto base_val = EvalExpr(expr->base, ctx, arena);
  auto idx_val = EvalExpr(expr->index, ctx, arena);
  uint64_t idx = idx_val.ToUint64();

  if (expr->index_end) {
    auto end_val = EvalExpr(expr->index_end, ctx, arena);
    uint64_t end_idx = end_val.ToUint64();
    uint32_t lo = (idx < end_idx) ? static_cast<uint32_t>(idx)
                                  : static_cast<uint32_t>(end_idx);
    uint32_t hi = (idx > end_idx) ? static_cast<uint32_t>(idx)
                                  : static_cast<uint32_t>(end_idx);
    uint32_t width = hi - lo + 1;
    uint64_t val = base_val.ToUint64() >> lo;
    uint64_t mask = (width >= 64) ? ~uint64_t{0} : (uint64_t{1} << width) - 1;
    return MakeLogic4VecVal(arena, width, val & mask);
  }

  // Single bit select.
  uint64_t bit = (base_val.ToUint64() >> idx) & 1;
  return MakeLogic4VecVal(arena, 1, bit);
}

// --- Ternary ---

static Logic4Vec EvalTernary(const Expr* expr, SimContext& ctx, Arena& arena) {
  auto cond = EvalExpr(expr->condition, ctx, arena);
  if (cond.ToUint64() != 0) {
    return EvalExpr(expr->true_expr, ctx, arena);
  }
  return EvalExpr(expr->false_expr, ctx, arena);
}

// --- Function call ---

static void BindFunctionArgs(const ModuleItem* func, const Expr* expr,
                             SimContext& ctx, Arena& arena) {
  for (size_t i = 0; i < func->func_args.size() && i < expr->args.size(); ++i) {
    auto arg_val = EvalExpr(expr->args[i], ctx, arena);
    auto* var = ctx.CreateLocalVariable(func->func_args[i].name, arg_val.width);
    var->value = arg_val;
  }
}

static void ExecFunctionBody(const ModuleItem* func, Variable* ret_var,
                             SimContext& ctx, Arena& arena) {
  for (auto* stmt : func->func_body_stmts) {
    if (stmt->kind == StmtKind::kReturn) {
      if (stmt->expr) ret_var->value = EvalExpr(stmt->expr, ctx, arena);
      return;
    }
    if (stmt->kind == StmtKind::kBlockingAssign && stmt->lhs) {
      auto rhs_val = EvalExpr(stmt->rhs, ctx, arena);
      auto* var = ctx.FindVariable(stmt->lhs->text);
      if (var) var->value = rhs_val;
    } else if (stmt->kind == StmtKind::kExprStmt) {
      EvalExpr(stmt->expr, ctx, arena);
    }
  }
}

static Logic4Vec EvalFunctionCall(const Expr* expr, SimContext& ctx,
                                  Arena& arena) {
  auto* func = ctx.FindFunction(expr->callee);
  if (!func) return MakeLogic4VecVal(arena, 1, 0);

  ctx.PushScope();
  BindFunctionArgs(func, expr, ctx, arena);
  auto* ret_var = ctx.CreateLocalVariable(func->name, 32);
  ExecFunctionBody(func, ret_var, ctx, arena);
  auto result = ret_var->value;
  ctx.PopScope();
  return result;
}

// --- Main dispatch ---

Logic4Vec EvalExpr(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (!expr) return MakeLogic4Vec(arena, 1);

  switch (expr->kind) {
    case ExprKind::kIntegerLiteral:
    case ExprKind::kUnbasedUnsizedLiteral:
      return EvalIntLiteral(expr, arena);
    case ExprKind::kStringLiteral:
      return EvalStringLiteral(expr, arena);
    case ExprKind::kRealLiteral:
      return MakeLogic4VecVal(arena, 64, 0);
    case ExprKind::kIdentifier:
      return EvalIdentifier(expr, ctx, arena);
    case ExprKind::kUnary:
      return EvalUnaryOp(expr->op, EvalExpr(expr->lhs, ctx, arena), arena);
    case ExprKind::kBinary:
      return EvalBinaryOp(expr->op, EvalExpr(expr->lhs, ctx, arena),
                          EvalExpr(expr->rhs, ctx, arena), arena);
    case ExprKind::kTernary:
      return EvalTernary(expr, ctx, arena);
    case ExprKind::kConcatenation:
      return EvalConcat(expr, ctx, arena);
    case ExprKind::kSelect:
      return EvalSelect(expr, ctx, arena);
    case ExprKind::kSystemCall:
      return EvalSystemCall(expr, ctx, arena);
    case ExprKind::kCall:
      return EvalFunctionCall(expr, ctx, arena);
    default:
      return MakeLogic4Vec(arena, 1);
  }
}

}  // namespace delta
