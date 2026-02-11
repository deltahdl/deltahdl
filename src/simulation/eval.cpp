#include "simulation/eval.h"

#include <cstdlib>
#include <cstring>
#include <iostream>
#include <string>
#include <vector>

#include "common/arena.h"
#include "elaboration/type_eval.h"
#include "lexer/token.h"
#include "parser/ast.h"
#include "simulation/class_object.h"
#include "simulation/dpi.h"
#include "simulation/eval_array.h"
#include "simulation/sim_context.h"
#include "simulation/vcd_writer.h"

namespace delta {

// --- Literal evaluation ---

static uint32_t LiteralWidth(std::string_view text, uint64_t val) {
  auto tick = text.find('\'');
  if (tick != std::string_view::npos && tick > 0) {
    uint32_t w = 0;
    for (size_t i = 0; i < tick; ++i) {
      if (text[i] >= '0' && text[i] <= '9') w = w * 10 + (text[i] - '0');
    }
    if (w > 0) return w;
  }
  return (val > UINT32_MAX) ? 64 : 32;
}

static Logic4Vec EvalUnbasedUnsized(const Expr* expr, Arena& arena) {
  // §5.7.1: '0, '1, 'x, 'z — single-bit unbased unsized literal.
  auto text = expr->text;
  if (text.size() >= 2 && text[0] == '\'') {
    char c = text[1];
    if (c == '1') return MakeLogic4VecVal(arena, 1, 1);
    if (c == '0') return MakeLogic4VecVal(arena, 1, 0);
    // 'x and 'z: set bval to indicate unknown.
    auto vec = MakeLogic4Vec(arena, 1);
    if (c == 'x' || c == 'X') vec.words[0] = {1, 1};
    if (c == 'z' || c == 'Z' || c == '?') vec.words[0] = {0, 1};
    return vec;
  }
  return MakeLogic4VecVal(arena, 1, expr->int_val);
}

// Check if a based literal's digit string contains x/z characters.
static bool TextHasXZ(std::string_view text) {
  auto tick = text.find('\'');
  if (tick == std::string_view::npos) return false;
  for (size_t i = tick + 1; i < text.size(); ++i) {
    char c = text[i];
    if (c == 'x' || c == 'X' || c == 'z' || c == 'Z' || c == '?') return true;
  }
  return false;
}

// Bits per digit for each base letter.
static int BitsPerDigit(char base_letter) {
  switch (base_letter) {
    case 'h':
    case 'H':
      return 4;
    case 'o':
    case 'O':
      return 3;
    case 'b':
    case 'B':
      return 1;
    default:
      return 0;
  }
}

// Parse a digit's numeric value (0-15), or -1 for x/z.
static int DigitValue(char c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'a' && c <= 'f') return c - 'a' + 10;
  if (c >= 'A' && c <= 'F') return c - 'A' + 10;
  return -1;
}

// Set bit_count bits starting at bit_pos in vec for an x/z/normal digit.
static void SetDigitBits(Logic4Vec& vec, uint32_t& bit_pos, int bit_count,
                         char digit, uint32_t width) {
  bool is_x = (digit == 'x' || digit == 'X');
  bool is_z = (digit == 'z' || digit == 'Z' || digit == '?');
  int dval = DigitValue(digit);
  for (int b = 0; b < bit_count && bit_pos < width; ++b, ++bit_pos) {
    uint32_t word = bit_pos / 64;
    uint64_t mask = uint64_t{1} << (bit_pos % 64);
    if (is_x) {
      vec.words[word].aval |= mask;
      vec.words[word].bval |= mask;
    } else if (is_z) {
      vec.words[word].bval |= mask;
    } else if (dval >= 0 && (dval & (1 << b))) {
      vec.words[word].aval |= mask;
    }
  }
}

// Parse a based literal with x/z digits into a Logic4Vec.
static Logic4Vec ParseBasedXZLiteral(std::string_view text, uint32_t width,
                                     Arena& arena) {
  auto vec = MakeLogic4Vec(arena, width);
  std::string buf;
  buf.reserve(text.size());
  for (char c : text)
    if (c != '_') buf.push_back(c);
  auto tick = buf.find('\'');
  if (tick == std::string::npos) return vec;
  size_t i = tick + 1;
  if (i < buf.size() && (buf[i] == 's' || buf[i] == 'S')) ++i;
  int bpd = (i < buf.size()) ? BitsPerDigit(buf[i]) : 0;
  if (bpd == 0) return vec;  // Decimal x/z: leave as zero.
  ++i;
  uint32_t bit_pos = 0;
  for (auto j = buf.size(); j > i && bit_pos < width; --j)
    SetDigitBits(vec, bit_pos, bpd, buf[j - 1], width);
  return vec;
}

static Logic4Vec EvalIntLiteral(const Expr* expr, Arena& arena) {
  uint32_t width = LiteralWidth(expr->text, expr->int_val);
  if (TextHasXZ(expr->text))
    return ParseBasedXZLiteral(expr->text, width, arena);
  return MakeLogic4VecVal(arena, width, expr->int_val);
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
  if (var) {
    auto val = var->value;
    if (ctx.IsRealVariable(expr->text)) val.is_real = true;
    if (var->is_signed) val.is_signed = true;
    return val;
  }
  return MakeLogic4Vec(arena, 1);  // X for unknown
}

// --- Reduction operations (§11.4.9) ---

static uint64_t ReduceBits(uint64_t val, uint32_t width) {
  uint64_t mask = (width >= 64) ? ~uint64_t{0} : (uint64_t{1} << width) - 1;
  return val & mask;
}

static Logic4Vec EvalReductionOp(TokenKind op, Logic4Vec operand,
                                 Arena& arena) {
  uint64_t val = ReduceBits(operand.ToUint64(), operand.width);
  uint64_t all_ones =
      (operand.width >= 64) ? ~uint64_t{0} : (uint64_t{1} << operand.width) - 1;
  uint64_t bit_count = __builtin_popcountll(val);
  switch (op) {
    case TokenKind::kAmp:
      return MakeLogic4VecVal(arena, 1, (val == all_ones) ? 1 : 0);
    case TokenKind::kPipe:
      return MakeLogic4VecVal(arena, 1, (val != 0) ? 1 : 0);
    case TokenKind::kCaret:
      return MakeLogic4VecVal(arena, 1, bit_count & 1);
    case TokenKind::kTildeAmp:
      return MakeLogic4VecVal(arena, 1, (val == all_ones) ? 0 : 1);
    case TokenKind::kTildePipe:
      return MakeLogic4VecVal(arena, 1, (val != 0) ? 0 : 1);
    case TokenKind::kTildeCaret:
    case TokenKind::kCaretTilde:
      return MakeLogic4VecVal(arena, 1, (bit_count & 1) ? 0 : 1);
    default:
      return operand;
  }
}

// --- Unary operations ---

static bool IsReductionOp(TokenKind op) {
  switch (op) {
    case TokenKind::kAmp:
    case TokenKind::kPipe:
    case TokenKind::kCaret:
    case TokenKind::kTildeAmp:
    case TokenKind::kTildePipe:
    case TokenKind::kTildeCaret:
    case TokenKind::kCaretTilde:
      return true;
    default:
      return false;
  }
}

static Logic4Vec EvalUnaryOp(TokenKind op, Logic4Vec operand, Arena& arena) {
  if (operand.nwords == 0) return operand;
  if (IsReductionOp(op)) return EvalReductionOp(op, operand, arena);
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

static uint64_t IntPow(uint64_t base, uint64_t exp) {
  uint64_t result = 1;
  while (exp > 0) {
    if (exp & 1) result *= base;
    base *= base;
    exp >>= 1;
  }
  return result;
}

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
    case TokenKind::kPower:
      result = IntPow(lv, rv);
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

// --- Case equality (compares both aval and bval) ---

static bool EvalCaseEquality(Logic4Vec lhs, Logic4Vec rhs) {
  if (lhs.width != rhs.width) return false;
  for (uint32_t i = 0; i < lhs.nwords; ++i) {
    if (lhs.words[i].aval != rhs.words[i].aval) return false;
    if (lhs.words[i].bval != rhs.words[i].bval) return false;
  }
  return true;
}

// --- Shift operations ---

static Logic4Vec MakeSignedResult(Arena& arena, uint32_t width, uint64_t val,
                                  bool is_signed) {
  auto result = MakeLogic4VecVal(arena, width, val);
  result.is_signed = is_signed;
  return result;
}

static Logic4Vec EvalArithShiftRight(Logic4Vec lhs, uint64_t rv, Arena& arena) {
  uint64_t lv = lhs.ToUint64();
  uint32_t w = lhs.width;
  if (w > 0 && w < 64 && ((lv >> (w - 1)) & 1)) {
    auto sv = static_cast<int64_t>(lv | (~uint64_t{0} << w));
    auto shifted = static_cast<uint64_t>(sv >> rv);
    uint64_t mask = (w >= 64) ? ~uint64_t{0} : (uint64_t{1} << w) - 1;
    return MakeSignedResult(arena, w, shifted & mask, lhs.is_signed);
  }
  return MakeSignedResult(arena, lhs.width, lv >> rv, lhs.is_signed);
}

static Logic4Vec EvalShift(TokenKind op, Logic4Vec lhs, uint64_t rv,
                           Arena& arena) {
  uint64_t lv = lhs.ToUint64();
  if (op == TokenKind::kLtLt || op == TokenKind::kLtLtLt) {
    return MakeSignedResult(arena, lhs.width, lv << rv, lhs.is_signed);
  }
  if (op == TokenKind::kGtGt) {
    return MakeSignedResult(arena, lhs.width, lv >> rv, lhs.is_signed);
  }
  return EvalArithShiftRight(lhs, rv, arena);
}

// --- Wildcard equality ---

static uint64_t EvalWildcardEq(Logic4Vec lhs, Logic4Vec rhs) {
  uint64_t rhs_dc = rhs.nwords > 0 ? rhs.words[0].bval : 0;
  return (((lhs.ToUint64() ^ rhs.ToUint64()) & ~rhs_dc) == 0) ? 1 : 0;
}

// --- Equality operations (§11.4.5, §11.4.6) ---

static uint64_t EvalEqualityOp(TokenKind op, Logic4Vec lhs, Logic4Vec rhs) {
  uint64_t lv = lhs.ToUint64();
  uint64_t rv = rhs.ToUint64();
  switch (op) {
    case TokenKind::kEqEq:
      return (lv == rv) ? 1 : 0;
    case TokenKind::kEqEqEq:
      return EvalCaseEquality(lhs, rhs) ? 1 : 0;
    case TokenKind::kBangEq:
      return (lv != rv) ? 1 : 0;
    case TokenKind::kBangEqEq:
      return EvalCaseEquality(lhs, rhs) ? 0 : 1;
    case TokenKind::kEqEqQuestion:
      return EvalWildcardEq(lhs, rhs);
    case TokenKind::kBangEqQuestion:
      return EvalWildcardEq(lhs, rhs) ^ 1;
    default:
      return 0;
  }
}

// --- Relational and logical operations (§11.4.4, §11.4.7) ---

static uint64_t EvalRelationalOp(TokenKind op, uint64_t lv, uint64_t rv) {
  switch (op) {
    case TokenKind::kLt:
      return (lv < rv) ? 1 : 0;
    case TokenKind::kGt:
      return (lv > rv) ? 1 : 0;
    case TokenKind::kLtEq:
      return (lv <= rv) ? 1 : 0;
    case TokenKind::kGtEq:
      return (lv >= rv) ? 1 : 0;
    case TokenKind::kAmpAmp:
      return (lv != 0 && rv != 0) ? 1 : 0;
    case TokenKind::kPipePipe:
      return (lv != 0 || rv != 0) ? 1 : 0;
    default:
      return 0;
  }
}

// --- Binary comparison dispatch ---

static bool IsEqualityOp(TokenKind op) {
  return op == TokenKind::kEqEq || op == TokenKind::kEqEqEq ||
         op == TokenKind::kBangEq || op == TokenKind::kBangEqEq ||
         op == TokenKind::kEqEqQuestion || op == TokenKind::kBangEqQuestion;
}

static Logic4Vec EvalBinaryCompare(TokenKind op, Logic4Vec lhs, Logic4Vec rhs,
                                   Arena& arena) {
  if (op == TokenKind::kLtLt || op == TokenKind::kLtLtLt ||
      op == TokenKind::kGtGt || op == TokenKind::kGtGtGt) {
    return EvalShift(op, lhs, rhs.ToUint64(), arena);
  }
  if (IsEqualityOp(op)) {
    return MakeLogic4VecVal(arena, 1, EvalEqualityOp(op, lhs, rhs));
  }
  return MakeLogic4VecVal(arena, 1,
                          EvalRelationalOp(op, lhs.ToUint64(), rhs.ToUint64()));
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
    case TokenKind::kPower:
      return EvalBinaryArith(op, lhs, rhs, arena);
    case TokenKind::kAmp:
    case TokenKind::kPipe:
    case TokenKind::kCaret:
      return EvalBinaryBitwise(op, lhs, rhs, arena);
    default:
      return EvalBinaryCompare(op, lhs, rhs, arena);
  }
}

// --- Compound assignment operators (§11.4.1) ---

static TokenKind CompoundAssignBaseOp(TokenKind op) {
  switch (op) {
    case TokenKind::kPlusEq:
      return TokenKind::kPlus;
    case TokenKind::kMinusEq:
      return TokenKind::kMinus;
    case TokenKind::kStarEq:
      return TokenKind::kStar;
    case TokenKind::kSlashEq:
      return TokenKind::kSlash;
    case TokenKind::kPercentEq:
      return TokenKind::kPercent;
    case TokenKind::kAmpEq:
      return TokenKind::kAmp;
    case TokenKind::kPipeEq:
      return TokenKind::kPipe;
    case TokenKind::kCaretEq:
      return TokenKind::kCaret;
    case TokenKind::kLtLtEq:
      return TokenKind::kLtLt;
    case TokenKind::kGtGtEq:
      return TokenKind::kGtGt;
    case TokenKind::kLtLtLtEq:
      return TokenKind::kLtLtLt;
    case TokenKind::kGtGtGtEq:
      return TokenKind::kGtGtGt;
    default:
      return TokenKind::kEof;
  }
}

static bool IsCompoundAssignOp(TokenKind op) {
  return CompoundAssignBaseOp(op) != TokenKind::kEof;
}

static Logic4Vec EvalCompoundAssign(const Expr* expr, SimContext& ctx,
                                    Arena& arena) {
  auto lhs_val = EvalExpr(expr->lhs, ctx, arena);
  auto rhs_val = EvalExpr(expr->rhs, ctx, arena);
  auto base_op = CompoundAssignBaseOp(expr->op);
  auto result = EvalBinaryOp(base_op, lhs_val, rhs_val, arena);
  if (expr->lhs->kind == ExprKind::kIdentifier) {
    auto* var = ctx.FindVariable(expr->lhs->text);
    if (var) var->value = result;
  }
  return result;
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

static Logic4Vec EvalDeferredPrint(const Expr* expr, SimContext& ctx,
                                   Arena& arena) {
  auto* event = ctx.GetScheduler().GetEventPool().Acquire();
  event->callback = [expr, &ctx, &arena]() {
    ExecDisplayWrite(expr, ctx, arena);
    std::cout << "\n";
  };
  ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime(), Region::kPostponed,
                                   event);
  return MakeLogic4VecVal(arena, 1, 0);
}

static Logic4Vec EvalVcdSysCall(SimContext& ctx, Arena& arena,
                                std::string_view name) {
  auto* vcd = ctx.GetVcdWriter();
  if (name == "$dumpvars" || name == "$dumpall") {
    if (vcd) vcd->DumpAllValues();
  } else if (name == "$dumpoff") {
    if (vcd) vcd->SetEnabled(false);
  } else if (name == "$dumpon") {
    if (vcd) vcd->SetEnabled(true);
  }
  return MakeLogic4VecVal(arena, 1, 0);
}

static bool IsMathSysCall(std::string_view n) {
  return n == "$ln" || n == "$log10" || n == "$exp" || n == "$sqrt" ||
         n == "$pow" || n == "$floor" || n == "$ceil" || n == "$sin" ||
         n == "$cos" || n == "$tan" || n == "$asin" || n == "$acos" ||
         n == "$atan" || n == "$atan2" || n == "$hypot" || n == "$sinh" ||
         n == "$cosh" || n == "$tanh" || n == "$asinh" || n == "$acosh" ||
         n == "$atanh" || n == "$dist_uniform" || n == "$dist_normal" ||
         n == "$dist_exponential" || n == "$dist_poisson" ||
         n == "$dist_chi_square" || n == "$dist_t" || n == "$dist_erlang";
}

static bool IsExtFileIOSysCall(std::string_view n) {
  return n == "$fgets" || n == "$fgetc" || n == "$fflush" || n == "$feof" ||
         n == "$ferror" || n == "$fseek" || n == "$ftell" || n == "$rewind" ||
         n == "$ungetc" || n == "$fscanf" || n == "$fread";
}

static Logic4Vec EvalTimeSysCall(SimContext& ctx, Arena& arena,
                                 std::string_view name) {
  if (name == "$stime") {
    auto ticks = ctx.CurrentTime().ticks & 0xFFFFFFFF;
    return MakeLogic4VecVal(arena, 32, ticks);
  }
  return MakeLogic4VecVal(arena, 64, ctx.CurrentTime().ticks);
}

static Logic4Vec EvalSystemCommand(const Expr* expr, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 32, 0);
  auto text = expr->args[0]->text;
  std::string cmd;
  if (text.size() >= 2 && text.front() == '"') {
    cmd = std::string(text.substr(1, text.size() - 2));
  } else {
    cmd = std::string(text);
  }
  int ret = std::system(cmd.c_str());
  return MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(ret));
}

static bool IsUtilitySysCall(std::string_view n) {
  return n == "$clog2" || n == "$bits" || n == "$unsigned" || n == "$signed" ||
         n == "$countones" || n == "$onehot" || n == "$onehot0" ||
         n == "$isunknown" || n == "$test$plusargs" || n == "$value$plusargs" ||
         n == "$typename" || n == "$sformatf" || n == "$itor" || n == "$rtoi" ||
         n == "$bitstoreal" || n == "$realtobits" || n == "$countbits" ||
         n == "$shortrealtobits" || n == "$bitstoshortreal";
}

static bool IsArrayQuerySysCall(std::string_view n) {
  return n == "$dimensions" || n == "$unpacked_dimensions" || n == "$left" ||
         n == "$right" || n == "$low" || n == "$high" || n == "$increment" ||
         n == "$size";
}

static bool IsVerifSysCall(std::string_view n) {
  return n == "$sampled" || n == "$rose" || n == "$fell" || n == "$stable" ||
         n == "$past" || n == "$changed" || n.starts_with("$assert") ||
         n.starts_with("$coverage") || n.starts_with("$q_") ||
         n.starts_with("$async$") || n.starts_with("$sync$");
}

static bool IsIOSysCall(std::string_view n) {
  return n == "$fopen" || n == "$fclose" || n == "$fwrite" ||
         n == "$fdisplay" || n == "$readmemh" || n == "$readmemb" ||
         n == "$writememh" || n == "$writememb" || n == "$sscanf";
}

static bool IsNoOpSysCall(std::string_view n) {
  return n == "$monitoron" || n == "$monitoroff" || n == "$printtimescale" ||
         n == "$timeformat";
}

static Logic4Vec EvalMiscSysCall(const Expr* expr, SimContext& ctx,
                                 Arena& arena, std::string_view name) {
  if (name == "$time" || name == "$stime" || name == "$realtime") {
    return EvalTimeSysCall(ctx, arena, name);
  }
  if (name == "$strobe" || name == "$monitor") {
    return EvalDeferredPrint(expr, ctx, arena);
  }
  if (IsNoOpSysCall(name)) return MakeLogic4VecVal(arena, 1, 0);
  if (name == "$system") return EvalSystemCommand(expr, arena);
  if (name == "$stacktrace") {
    std::cerr << "stacktrace not available\n";
    return MakeLogic4VecVal(arena, 1, 0);
  }
  if (name.starts_with("$dump")) return EvalVcdSysCall(ctx, arena, name);
  if (IsMathSysCall(name)) return EvalMathSysCall(expr, ctx, arena, name);
  if (IsUtilitySysCall(name)) return EvalUtilitySysCall(expr, ctx, arena, name);
  if (IsIOSysCall(name)) return EvalIOSysCall(expr, ctx, arena, name);
  if (IsExtFileIOSysCall(name))
    return EvalFileIOSysCall(expr, ctx, arena, name);
  if (IsArrayQuerySysCall(name))
    return EvalArrayQuerySysCall(expr, ctx, arena, name);
  if (IsVerifSysCall(name)) return EvalVerifSysCall(expr, ctx, arena, name);
  return EvalPrngCall(expr, ctx, arena, name);
}

static Logic4Vec EvalSeveritySysCall(const Expr* expr, SimContext& ctx,
                                     Arena& arena, std::string_view name) {
  if (name == "$fatal") {
    ExecSeverityTask(expr, ctx, arena, "FATAL", std::cerr);
    ctx.RequestStop();
  } else if (name == "$error") {
    ExecSeverityTask(expr, ctx, arena, "ERROR", std::cerr);
  } else if (name == "$warning") {
    ExecSeverityTask(expr, ctx, arena, "WARNING", std::cout);
  } else if (name == "$info") {
    ExecSeverityTask(expr, ctx, arena, "INFO", std::cout);
  }
  return MakeLogic4VecVal(arena, 1, 0);
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
  if (name == "$fatal" || name == "$error" || name == "$warning" ||
      name == "$info") {
    return EvalSeveritySysCall(expr, ctx, arena, name);
  }
  return EvalMiscSysCall(expr, ctx, arena, name);
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
    uint32_t w = it->width;
    if (w > 64) w = 64;
    uint32_t word = bit_pos / 64;
    uint32_t bit = bit_pos % 64;
    if (word < result.nwords) {
      result.words[word].aval |= val << bit;
      if (bit + w > 64 && word + 1 < result.nwords) {
        result.words[word + 1].aval |= val >> (64 - bit);
      }
    }
    bit_pos += it->width;
  }
  return result;
}

// --- Select (bit/part) ---

// §7.10: Resolve a queue index with $ = last element index.
static uint64_t ResolveQueueIdx(const Expr* idx_expr, QueueObject* q,
                                SimContext& ctx, Arena& arena) {
  ctx.PushScope();
  auto* dv = ctx.CreateLocalVariable("$", 32);
  uint64_t last = q->elements.empty() ? 0 : q->elements.size() - 1;
  dv->value = MakeLogic4VecVal(arena, 32, last);
  auto val = EvalExpr(idx_expr, ctx, arena);
  ctx.PopScope();
  return val.ToUint64();
}

// §7.10: Try queue indexed access with $ support. Returns true if handled.
static bool TryQueueSelect(const Expr* expr, SimContext& ctx, Arena& arena,
                           Logic4Vec& out) {
  if (!expr->base || expr->base->kind != ExprKind::kIdentifier) return false;
  if (expr->index_end) return false;
  auto* q = ctx.FindQueue(expr->base->text);
  if (!q) return false;
  auto idx = ResolveQueueIdx(expr->index, q, ctx, arena);
  out = (idx < q->elements.size()) ? q->elements[idx]
                                   : MakeLogic4VecVal(arena, q->elem_width, 0);
  return true;
}

// §7.4: Try unpacked array element access. Returns true if handled.
static bool TryArrayElementSelect(const Expr* expr, uint64_t idx,
                                  SimContext& ctx, Logic4Vec& out) {
  if (!expr->base || expr->base->kind != ExprKind::kIdentifier) return false;
  if (expr->index_end) return false;
  auto elem_name =
      std::string(expr->base->text) + "[" + std::to_string(idx) + "]";
  auto* elem = ctx.FindVariable(elem_name);
  if (!elem) return false;
  out = elem->value;
  return true;
}

// §7.4: Build a compound variable name from chained selects (e.g., mem[i][j]).
static bool BuildCompoundName(const Expr* expr, SimContext& ctx, Arena& arena,
                              std::string& name) {
  if (expr->kind == ExprKind::kIdentifier) {
    name = expr->text;
    return true;
  }
  if (expr->kind != ExprKind::kSelect || expr->index_end) return false;
  if (!BuildCompoundName(expr->base, ctx, arena, name)) return false;
  auto idx = EvalExpr(expr->index, ctx, arena).ToUint64();
  name += "[" + std::to_string(idx) + "]";
  return true;
}

// §7.4: Try multi-dimensional array element access (e.g., mem[i][j]).
static bool TryCompoundArraySelect(const Expr* expr, SimContext& ctx,
                                   Arena& arena, Logic4Vec& out) {
  if (!expr->base || expr->base->kind != ExprKind::kSelect) return false;
  if (expr->index_end) return false;
  std::string compound;
  if (!BuildCompoundName(expr, ctx, arena, compound)) return false;
  auto* elem = ctx.FindVariable(compound);
  if (!elem) return false;
  out = elem->value;
  return true;
}

// Evaluate a packed part-select: base[hi:lo].
static Logic4Vec EvalPartSelect(const Logic4Vec& base_val, uint64_t idx,
                                uint64_t end_idx, Arena& arena) {
  uint32_t lo = static_cast<uint32_t>(std::min(idx, end_idx));
  uint32_t hi = static_cast<uint32_t>(std::max(idx, end_idx));
  uint32_t width = hi - lo + 1;
  uint64_t val = base_val.ToUint64() >> lo;
  uint64_t mask = (width >= 64) ? ~uint64_t{0} : (uint64_t{1} << width) - 1;
  return MakeLogic4VecVal(arena, width, val & mask);
}

// §7.8: Try associative array indexed access. Returns true if handled.
static bool TryAssocSelect(const Expr* expr, SimContext& ctx, Arena& arena,
                           Logic4Vec& out) {
  if (!expr->base || expr->base->kind != ExprKind::kIdentifier) return false;
  if (expr->index_end) return false;
  auto* aa = ctx.FindAssocArray(expr->base->text);
  if (!aa) return false;
  if (aa->is_string_key) {
    auto key = EvalExpr(expr->index, ctx, arena);
    uint32_t nb = key.width / 8;
    std::string s;
    s.reserve(nb);
    for (uint32_t i = nb; i > 0; --i) {
      uint32_t bi = i - 1;
      auto ch = static_cast<char>(
          (key.words[(bi * 8) / 64].aval >> ((bi * 8) % 64)) & 0xFF);
      if (ch != 0) s.push_back(ch);
    }
    auto it = aa->str_data.find(s);
    out = (it != aa->str_data.end())
              ? it->second
              : MakeLogic4VecVal(arena, aa->elem_width, 0);
  } else {
    auto key =
        static_cast<int64_t>(EvalExpr(expr->index, ctx, arena).ToUint64());
    auto it = aa->int_data.find(key);
    out = (it != aa->int_data.end())
              ? it->second
              : MakeLogic4VecVal(arena, aa->elem_width, 0);
  }
  return true;
}

static Logic4Vec EvalSelect(const Expr* expr, SimContext& ctx, Arena& arena) {
  Logic4Vec result;
  if (TryQueueSelect(expr, ctx, arena, result)) return result;
  if (TryAssocSelect(expr, ctx, arena, result)) return result;

  auto idx_val = EvalExpr(expr->index, ctx, arena);
  uint64_t idx = idx_val.ToUint64();

  if (TryArrayElementSelect(expr, idx, ctx, result)) return result;
  if (TryCompoundArraySelect(expr, ctx, arena, result)) return result;

  auto base_val = EvalExpr(expr->base, ctx, arena);
  if (expr->index_end) {
    auto end_val = EvalExpr(expr->index_end, ctx, arena).ToUint64();
    if (expr->is_part_select_plus) {
      // §7.4.5: base[idx +: width] → extract `width` bits from bit `idx`.
      auto w = static_cast<uint32_t>(end_val);
      return EvalPartSelect(base_val, idx, idx + w - 1, arena);
    }
    if (expr->is_part_select_minus) {
      // §7.4.5: base[idx -: width] → extract `width` bits ending at `idx`.
      auto w = static_cast<uint32_t>(end_val);
      uint64_t lo = (idx >= w - 1) ? idx - w + 1 : 0;
      return EvalPartSelect(base_val, lo, idx, arena);
    }
    return EvalPartSelect(base_val, idx, end_val, arena);
  }
  // Single bit select.
  return MakeLogic4VecVal(arena, 1, (base_val.ToUint64() >> idx) & 1);
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

// §13.5.4: Resolve the call-site arg index for a given parameter index.
static int ResolveArgIndex(const ModuleItem* func, const Expr* expr,
                           size_t param_idx) {
  if (expr->arg_names.empty()) {
    return (param_idx < expr->args.size()) ? static_cast<int>(param_idx) : -1;
  }
  auto param_name = func->func_args[param_idx].name;
  for (size_t j = 0; j < expr->arg_names.size(); ++j) {
    if (expr->arg_names[j] == param_name) return static_cast<int>(j);
  }
  return -1;
}

// §13.5.2: Try to pass by reference. Returns true if aliased successfully.
static bool TryBindRefArg(const Expr* expr, int arg_index,
                          std::string_view param_name, SimContext& ctx) {
  if (arg_index < 0) return false;
  auto* call_arg = expr->args[static_cast<size_t>(arg_index)];
  if (call_arg->kind != ExprKind::kIdentifier) return false;
  auto* target = ctx.FindVariable(call_arg->text);
  if (!target) return false;
  ctx.AliasLocalVariable(param_name, target);
  return true;
}

// §13.5.3: Evaluate call-site arg, use default value, or X.
static Logic4Vec ResolveArgValue(const FunctionArg& param, const Expr* expr,
                                 int arg_index, SimContext& ctx, Arena& arena) {
  if (arg_index >= 0) {
    return EvalExpr(expr->args[static_cast<size_t>(arg_index)], ctx, arena);
  }
  if (param.default_value) return EvalExpr(param.default_value, ctx, arena);
  return MakeLogic4Vec(arena, 32);
}

// §7.8: Copy associative array data when passing to a subroutine.
static bool TryBindAssocArg(const Expr* call_arg, std::string_view param_name,
                            SimContext& ctx) {
  if (!call_arg || call_arg->kind != ExprKind::kIdentifier) return false;
  auto* src = ctx.FindAssocArray(call_arg->text);
  if (!src) return false;
  auto* dst =
      ctx.CreateAssocArray(param_name, src->elem_width, src->is_string_key);
  dst->int_data = src->int_data;
  dst->str_data = src->str_data;
  return true;
}

// §13.4: Copy array elements when passing an unpacked array to a subroutine.
static bool TryBindArrayArg(const Expr* call_arg, std::string_view param_name,
                            SimContext& ctx, Arena& arena) {
  if (!call_arg || call_arg->kind != ExprKind::kIdentifier) return false;
  if (TryBindAssocArg(call_arg, param_name, ctx)) return true;
  auto* info = ctx.FindArrayInfo(call_arg->text);
  if (!info) return false;
  ctx.RegisterArray(param_name, *info);
  for (uint32_t j = 0; j < info->size; ++j) {
    uint32_t idx = info->lo + j;
    auto src = std::string(call_arg->text) + "[" + std::to_string(idx) + "]";
    auto dst = std::string(param_name) + "[" + std::to_string(idx) + "]";
    auto* src_var = ctx.FindVariable(src);
    auto val =
        src_var ? src_var->value : MakeLogic4VecVal(arena, info->elem_width, 0);
    auto* dst_var = ctx.CreateLocalVariable(
        *arena.Create<std::string>(std::move(dst)), val.width);
    dst_var->value = val;
  }
  return true;
}

// §13.5: Bind function arguments with named, default, and ref support.
static void BindFunctionArgs(const ModuleItem* func, const Expr* expr,
                             SimContext& ctx, Arena& arena) {
  for (size_t i = 0; i < func->func_args.size(); ++i) {
    int ai = ResolveArgIndex(func, expr, i);
    auto dir = func->func_args[i].direction;
    if (dir == Direction::kRef &&
        TryBindRefArg(expr, ai, func->func_args[i].name, ctx)) {
      continue;
    }
    if (ai >= 0 && TryBindArrayArg(expr->args[static_cast<size_t>(ai)],
                                   func->func_args[i].name, ctx, arena)) {
      continue;
    }
    auto val = ResolveArgValue(func->func_args[i], expr, ai, ctx, arena);
    auto* var = ctx.CreateLocalVariable(func->func_args[i].name, val.width);
    var->value = val;
  }
}

// Write back output/inout args, respecting named binding (§13.5.4).
static void WritebackOutputArgs(const ModuleItem* func, const Expr* expr,
                                SimContext& ctx) {
  for (size_t i = 0; i < func->func_args.size(); ++i) {
    auto dir = func->func_args[i].direction;
    if (dir != Direction::kOutput && dir != Direction::kInout) continue;
    auto* local = ctx.FindLocalVariable(func->func_args[i].name);
    if (!local) continue;
    int ai = ResolveArgIndex(func, expr, i);
    if (ai < 0) continue;
    auto* call_arg = expr->args[static_cast<size_t>(ai)];
    if (call_arg->kind != ExprKind::kIdentifier) continue;
    auto* target = ctx.FindVariable(call_arg->text);
    if (target) target->value = local->value;
  }
}

// §13: Handle blocking assignment inside function/task body.
// Write to an indexed LHS inside a function body (array/assoc element).
static void ExecFuncSelectAssign(const Expr* lhs, const Logic4Vec& val,
                                 SimContext& ctx, Arena& arena) {
  if (!lhs->base || lhs->base->kind != ExprKind::kIdentifier) return;
  auto* aa = ctx.FindAssocArray(lhs->base->text);
  if (aa && lhs->index) {
    if (aa->is_string_key) {
      aa->str_data[FormatValueAsString(EvalExpr(lhs->index, ctx, arena))] = val;
    } else {
      auto key =
          static_cast<int64_t>(EvalExpr(lhs->index, ctx, arena).ToUint64());
      aa->int_data[key] = val;
    }
    return;
  }
  auto idx = EvalExpr(lhs->index, ctx, arena).ToUint64();
  auto name = std::string(lhs->base->text) + "[" + std::to_string(idx) + "]";
  auto* elem = ctx.FindVariable(name);
  if (elem) elem->value = val;
}

static void ExecFuncBlockingAssign(const Stmt* stmt, SimContext& ctx,
                                   Arena& arena) {
  if (!stmt->lhs) return;
  auto val = EvalExpr(stmt->rhs, ctx, arena);
  // Simple identifier LHS.
  if (stmt->lhs->kind == ExprKind::kIdentifier) {
    auto* var = ctx.FindVariable(stmt->lhs->text);
    if (var) {
      var->value = val;
      return;
    }
    // §8.7: Inside constructor, write to class property via `this`.
    auto* self = ctx.CurrentThis();
    if (self) self->SetProperty(std::string(stmt->lhs->text), val);
    return;
  }
  if (stmt->lhs->kind == ExprKind::kSelect) {
    ExecFuncSelectAssign(stmt->lhs, val, ctx, arena);
  }
}

// Forward declarations for mutually recursive function body execution.
static bool ExecFuncStmt(const Stmt* stmt, Variable* ret_var, SimContext& ctx,
                         Arena& arena);
static bool ExecFuncBlock(const Stmt* stmt, Variable* ret_var, SimContext& ctx,
                          Arena& arena);

static bool ExecFuncIf(const Stmt* stmt, Variable* ret_var, SimContext& ctx,
                       Arena& arena) {
  auto cond = EvalExpr(stmt->condition, ctx, arena);
  bool taken = cond.ToUint64() != 0;
  if (taken) return ExecFuncStmt(stmt->then_branch, ret_var, ctx, arena);
  if (stmt->else_branch) {
    return ExecFuncStmt(stmt->else_branch, ret_var, ctx, arena);
  }
  return false;
}

static bool ExecFuncBlock(const Stmt* stmt, Variable* ret_var, SimContext& ctx,
                          Arena& arena) {
  for (auto* c : stmt->stmts) {
    if (ExecFuncStmt(c, ret_var, ctx, arena)) return true;
  }
  return false;
}

// Execute a single statement in a function body; returns true on 'return'.
static bool ExecFuncStmt(const Stmt* stmt, Variable* ret_var, SimContext& ctx,
                         Arena& arena) {
  if (!stmt) return false;
  switch (stmt->kind) {
    case StmtKind::kReturn:
      if (stmt->expr) ret_var->value = EvalExpr(stmt->expr, ctx, arena);
      return true;
    case StmtKind::kBlockingAssign:
      ExecFuncBlockingAssign(stmt, ctx, arena);
      return false;
    case StmtKind::kExprStmt:
      EvalExpr(stmt->expr, ctx, arena);
      return false;
    case StmtKind::kVarDecl: {
      uint32_t w = EvalTypeWidth(stmt->var_decl_type);
      if (w == 0) w = 32;
      auto* v = ctx.CreateVariable(stmt->var_name, w);
      if (stmt->var_init) v->value = EvalExpr(stmt->var_init, ctx, arena);
      return false;
    }
    case StmtKind::kIf:
      return ExecFuncIf(stmt, ret_var, ctx, arena);
    case StmtKind::kBlock:
      return ExecFuncBlock(stmt, ret_var, ctx, arena);
    default:
      return false;
  }
}

static void ExecFunctionBody(const ModuleItem* func, Variable* ret_var,
                             SimContext& ctx, Arena& arena) {
  for (auto* s : func->func_body_stmts) {
    if (ExecFuncStmt(s, ret_var, ctx, arena)) return;
  }
}

// §8.7: Allocate a new class object, execute constructor, return handle.
Logic4Vec EvalClassNew(std::string_view class_type, const Expr* new_expr,
                       SimContext& ctx, Arena& arena) {
  auto* info = ctx.FindClassType(class_type);
  if (!info) return MakeLogic4VecVal(arena, 64, kNullClassHandle);
  auto* obj = arena.Create<ClassObject>();
  obj->type = info;
  // Initialize properties with default zero values.
  for (const auto& prop : info->properties) {
    obj->properties[std::string(prop.name)] =
        MakeLogic4VecVal(arena, prop.width, 0);
  }
  auto handle = ctx.AllocateClassObject(obj);
  // Execute constructor if present.
  auto it = info->methods.find("new");
  if (it != info->methods.end() && it->second) {
    ctx.PushScope();
    ctx.PushThis(obj);
    // Bind constructor arguments.
    if (new_expr) BindFunctionArgs(it->second, new_expr, ctx, arena);
    Variable dummy;
    ExecFunctionBody(it->second, &dummy, ctx, arena);
    ctx.PopThis();
    ctx.PopScope();
  }
  return MakeLogic4VecVal(arena, 64, handle);
}

static Logic4Vec EvalDpiCall(const Expr* expr, SimContext& ctx, Arena& arena) {
  auto* dpi = ctx.GetDpiContext();
  if (!dpi || !dpi->HasImport(expr->callee)) {
    return MakeLogic4VecVal(arena, 1, 0);
  }
  std::vector<uint64_t> args;
  args.reserve(expr->args.size());
  for (auto* arg : expr->args) {
    args.push_back(EvalExpr(arg, ctx, arena).ToUint64());
  }
  uint64_t result = dpi->Call(expr->callee, args);
  return MakeLogic4VecVal(arena, 32, result);
}

// Try dispatching to built-in type methods (enum, string, array, queue).
static bool TryBuiltinMethodCall(const Expr* expr, SimContext& ctx,
                                 Arena& arena, Logic4Vec& out) {
  if (TryEvalEnumMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalStringMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalArrayMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalQueueMethodCall(expr, ctx, arena, out)) return true;
  return TryEvalAssocMethodCall(expr, ctx, arena, out);
}

// §13: Dispatch function calls with lifetime and void support.
static Logic4Vec EvalFunctionCall(const Expr* expr, SimContext& ctx,
                                  Arena& arena) {
  Logic4Vec method_result;
  if (TryBuiltinMethodCall(expr, ctx, arena, method_result)) {
    return method_result;
  }

  auto* func = ctx.FindFunction(expr->callee);
  if (!func) return EvalDpiCall(expr, ctx, arena);

  bool is_static = func->is_static && !func->is_automatic;
  bool is_void = (func->return_type.kind == DataTypeKind::kVoid);

  // §13.3.1: Static functions reuse their variable frame across calls.
  if (is_static) {
    ctx.PushStaticScope(func->name);
  } else {
    ctx.PushScope();
  }

  BindFunctionArgs(func, expr, ctx, arena);

  // §13.4.1: Void functions have no implicit return variable.
  // For static functions, reuse the existing return variable if present.
  Variable dummy_ret;
  Variable* ret_var = &dummy_ret;
  if (!is_void) {
    auto* existing = is_static ? ctx.FindLocalVariable(func->name) : nullptr;
    ret_var = existing ? existing : ctx.CreateLocalVariable(func->name, 32);
  }

  ExecFunctionBody(func, ret_var, ctx, arena);
  WritebackOutputArgs(func, expr, ctx);
  auto result = is_void ? MakeLogic4VecVal(arena, 1, 0) : ret_var->value;

  if (is_static) {
    ctx.PopStaticScope(func->name);
  } else {
    ctx.PopScope();
  }
  return result;
}

// --- Binary expression with short-circuit ---

// §10.3: Assignment within expression — evaluate RHS, store in LHS, return.
static Logic4Vec EvalAssignInExpr(const Expr* expr, SimContext& ctx,
                                  Arena& arena) {
  auto rhs_val = EvalExpr(expr->rhs, ctx, arena);
  if (expr->lhs->kind == ExprKind::kIdentifier) {
    auto* var = ctx.FindVariable(expr->lhs->text);
    if (var) var->value = rhs_val;
  }
  return rhs_val;
}

static Logic4Vec EvalBinaryExpr(const Expr* expr, SimContext& ctx,
                                Arena& arena) {
  if (expr->op == TokenKind::kEq) return EvalAssignInExpr(expr, ctx, arena);
  if (expr->op == TokenKind::kAmpAmp) {
    auto l = EvalExpr(expr->lhs, ctx, arena);
    if (l.ToUint64() == 0) return MakeLogic4VecVal(arena, 1, 0);
    auto r = EvalExpr(expr->rhs, ctx, arena);
    return MakeLogic4VecVal(arena, 1, r.ToUint64() != 0 ? 1 : 0);
  }
  if (expr->op == TokenKind::kPipePipe) {
    auto l = EvalExpr(expr->lhs, ctx, arena);
    if (l.ToUint64() != 0) return MakeLogic4VecVal(arena, 1, 1);
    auto r = EvalExpr(expr->rhs, ctx, arena);
    return MakeLogic4VecVal(arena, 1, r.ToUint64() != 0 ? 1 : 0);
  }
  return EvalBinaryOp(expr->op, EvalExpr(expr->lhs, ctx, arena),
                      EvalExpr(expr->rhs, ctx, arena), arena);
}

// --- Main dispatch ---

Logic4Vec EvalExpr(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (!expr) return MakeLogic4Vec(arena, 1);

  switch (expr->kind) {
    case ExprKind::kIntegerLiteral:
      return EvalIntLiteral(expr, arena);
    case ExprKind::kUnbasedUnsizedLiteral:
      return EvalUnbasedUnsized(expr, arena);
    case ExprKind::kStringLiteral:
      return EvalStringLiteral(expr, arena);
    case ExprKind::kRealLiteral: {
      uint64_t bits = 0;
      std::memcpy(&bits, &expr->real_val, sizeof(double));
      return MakeLogic4VecVal(arena, 64, bits);
    }
    case ExprKind::kIdentifier:
      return EvalIdentifier(expr, ctx, arena);
    case ExprKind::kUnary:
      if (expr->op == TokenKind::kPlusPlus ||
          expr->op == TokenKind::kMinusMinus) {
        return EvalPrefixUnary(expr, ctx, arena);
      }
      return EvalUnaryOp(expr->op, EvalExpr(expr->lhs, ctx, arena), arena);
    case ExprKind::kBinary:
      if (IsCompoundAssignOp(expr->op)) {
        return EvalCompoundAssign(expr, ctx, arena);
      }
      if (expr->op == TokenKind::kKwMatches) {
        return EvalMatches(expr, ctx, arena);
      }
      return EvalBinaryExpr(expr, ctx, arena);
    case ExprKind::kTernary:
      return EvalTernary(expr, ctx, arena);
    case ExprKind::kConcatenation:
      return EvalConcat(expr, ctx, arena);
    case ExprKind::kReplicate:
      return EvalReplicate(expr, ctx, arena);
    case ExprKind::kSelect:
      return EvalSelect(expr, ctx, arena);
    case ExprKind::kSystemCall:
      return EvalSystemCall(expr, ctx, arena);
    case ExprKind::kCall:
      return EvalFunctionCall(expr, ctx, arena);
    case ExprKind::kPostfixUnary:
      return EvalPostfixUnary(expr, ctx, arena);
    case ExprKind::kMemberAccess:
      return EvalMemberAccess(expr, ctx, arena);
    case ExprKind::kCast:
      return EvalCast(expr, ctx, arena);
    case ExprKind::kInside:
      return EvalInside(expr, ctx, arena);
    case ExprKind::kStreamingConcat:
      return EvalStreamingConcat(expr, ctx, arena);
    case ExprKind::kAssignmentPattern:
      return EvalAssignmentPattern(expr, ctx, arena);
    default:
      return MakeLogic4Vec(arena, 1);
  }
}

}  // namespace delta
