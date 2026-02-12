#include <bit>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iostream>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "parser/ast.h"
#include "simulation/eval.h"
#include "simulation/sim_context.h"

namespace delta {

// ============================================================================
// Helpers
// ============================================================================

static uint32_t CountOnesInVec(const Logic4Vec& val) {
  uint32_t count = 0;
  for (uint32_t i = 0; i < val.nwords; ++i) {
    // Count known-1 bits: aval set AND bval clear.
    uint64_t known_ones = val.words[i].aval & ~val.words[i].bval;
    count += static_cast<uint32_t>(std::popcount(known_ones));
  }
  return count;
}

static bool HasUnknownBits(const Logic4Vec& val) {
  for (uint32_t i = 0; i < val.nwords; ++i) {
    if (val.words[i].bval != 0) return true;
  }
  return false;
}

// ============================================================================
// §20 — $clog2
// ============================================================================

static Logic4Vec EvalClog2(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 32, 0);
  uint64_t v = EvalExpr(expr->args[0], ctx, arena).ToUint64();
  if (v <= 1) return MakeLogic4VecVal(arena, 32, 0);
  int result = 0;
  uint64_t shifted = v - 1;
  while (shifted > 0) {
    shifted >>= 1;
    ++result;
  }
  return MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(result));
}

// ============================================================================
// §20 — $bits
// ============================================================================

static Logic4Vec EvalBits(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 32, 0);
  // §20.6.2: $bits can accept a type name or an expression.
  auto* arg = expr->args[0];
  if (arg->kind == ExprKind::kIdentifier) {
    uint32_t tw = ctx.FindTypeWidth(arg->text);
    if (tw > 0) return MakeLogic4VecVal(arena, 32, tw);
  }
  auto val = EvalExpr(arg, ctx, arena);
  return MakeLogic4VecVal(arena, 32, val.width);
}

// ============================================================================
// §20 — $unsigned, $signed
// ============================================================================

static Logic4Vec EvalSignCast(const Expr* expr, SimContext& ctx, Arena& arena,
                              bool make_signed) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 32, 0);
  auto val = EvalExpr(expr->args[0], ctx, arena);
  val.is_signed = make_signed;
  return val;
}

// ============================================================================
// §20 — $countones, $onehot, $onehot0, $isunknown
// ============================================================================

static Logic4Vec EvalCountones(const Expr* expr, SimContext& ctx,
                               Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 32, 0);
  auto val = EvalExpr(expr->args[0], ctx, arena);
  return MakeLogic4VecVal(arena, 32, CountOnesInVec(val));
}

static Logic4Vec EvalOnehot(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 1, 0);
  auto val = EvalExpr(expr->args[0], ctx, arena);
  uint64_t result = (CountOnesInVec(val) == 1) ? 1 : 0;
  return MakeLogic4VecVal(arena, 1, result);
}

static Logic4Vec EvalOnehot0(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 1, 1);
  auto val = EvalExpr(expr->args[0], ctx, arena);
  uint64_t result = (CountOnesInVec(val) <= 1) ? 1 : 0;
  return MakeLogic4VecVal(arena, 1, result);
}

static Logic4Vec EvalIsunknown(const Expr* expr, SimContext& ctx,
                               Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 1, 0);
  auto val = EvalExpr(expr->args[0], ctx, arena);
  return MakeLogic4VecVal(arena, 1, HasUnknownBits(val) ? 1 : 0);
}

// ============================================================================
// §20 — $test$plusargs, $value$plusargs
// ============================================================================

static std::string ExtractStrArg(const Expr* arg) {
  auto text = arg->text;
  if (text.size() >= 2 && text.front() == '"') {
    return std::string(text.substr(1, text.size() - 2));
  }
  return std::string(text);
}

static Logic4Vec EvalTestPlusargs(const Expr* expr, SimContext& ctx,
                                  Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 1, 0);
  std::string prefix = ExtractStrArg(expr->args[0]);
  for (const auto& arg : ctx.GetPlusArgs()) {
    if (arg.substr(0, prefix.size()) == prefix) {
      return MakeLogic4VecVal(arena, 1, 1);
    }
  }
  return MakeLogic4VecVal(arena, 1, 0);
}

static Logic4Vec EvalValuePlusargs(const Expr* expr, SimContext& ctx,
                                   Arena& arena) {
  if (expr->args.size() < 2) return MakeLogic4VecVal(arena, 1, 0);
  std::string pattern = ExtractStrArg(expr->args[0]);

  // Split pattern at '%' to get prefix and format spec.
  auto pct_pos = pattern.find('%');
  std::string prefix =
      (pct_pos != std::string::npos) ? pattern.substr(0, pct_pos) : pattern;

  for (const auto& arg : ctx.GetPlusArgs()) {
    if (arg.substr(0, prefix.size()) != prefix) continue;
    std::string value_str = arg.substr(prefix.size());
    // Remove leading '=' if present.
    if (!value_str.empty() && value_str[0] == '=') {
      value_str = value_str.substr(1);
    }
    uint64_t parsed_val = std::strtoull(value_str.c_str(), nullptr, 10);
    // Write to the destination variable.
    if (expr->args[1]->kind == ExprKind::kIdentifier) {
      auto* var = ctx.FindVariable(expr->args[1]->text);
      if (var)
        var->value = MakeLogic4VecVal(arena, var->value.width, parsed_val);
    }
    return MakeLogic4VecVal(arena, 1, 1);
  }
  return MakeLogic4VecVal(arena, 1, 0);
}

// ============================================================================
// §20 — $typename
// ============================================================================

static Logic4Vec EvalTypename(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) {
    return StringToLogic4Vec(arena, "logic");
  }
  auto val = EvalExpr(expr->args[0], ctx, arena);
  if (val.width <= 1) return StringToLogic4Vec(arena, "logic");
  std::string name = "logic[" + std::to_string(val.width - 1) + ":0]";
  return StringToLogic4Vec(arena, name);
}

// ============================================================================
// §21.3.3 — $sformatf
// ============================================================================

static Logic4Vec EvalSformatf(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return StringToLogic4Vec(arena, "");
  std::string fmt = ExtractFormatString(expr->args[0]);
  std::vector<Logic4Vec> arg_vals;
  for (size_t i = 1; i < expr->args.size(); ++i) {
    arg_vals.push_back(EvalExpr(expr->args[i], ctx, arena));
  }
  std::string result = FormatDisplay(fmt, arg_vals);
  return StringToLogic4Vec(arena, result);
}

// ============================================================================
// §20.5 — Type conversion functions
// ============================================================================

static Logic4Vec EvalItor(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 64, 0);
  auto val = EvalExpr(expr->args[0], ctx, arena);
  auto d = static_cast<double>(static_cast<int64_t>(val.ToUint64()));
  uint64_t bits = 0;
  std::memcpy(&bits, &d, sizeof(double));
  return MakeLogic4VecVal(arena, 64, bits);
}

static Logic4Vec EvalRtoi(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 32, 0);
  auto val = EvalExpr(expr->args[0], ctx, arena);
  uint64_t raw_bits = val.ToUint64();
  double d = 0.0;
  std::memcpy(&d, &raw_bits, sizeof(double));
  auto truncated = static_cast<int64_t>(d);
  return MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(truncated));
}

static Logic4Vec EvalBitstoreal(const Expr* expr, SimContext& ctx,
                                Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 64, 0);
  auto val = EvalExpr(expr->args[0], ctx, arena);
  return MakeLogic4VecVal(arena, 64, val.ToUint64());
}

static Logic4Vec EvalRealtobits(const Expr* expr, SimContext& ctx,
                                Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 64, 0);
  auto val = EvalExpr(expr->args[0], ctx, arena);
  uint64_t raw_bits = val.ToUint64();
  // If argument is a real literal, convert from double directly.
  if (expr->args[0]->kind == ExprKind::kRealLiteral) {
    double d = expr->args[0]->real_val;
    std::memcpy(&raw_bits, &d, sizeof(double));
  }
  return MakeLogic4VecVal(arena, 64, raw_bits);
}

// ============================================================================
// §20.9 — $countbits
// ============================================================================

static uint32_t CountMatchingBits(const Logic4Vec& val, const bool match[4]) {
  uint32_t count = 0;
  for (uint32_t i = 0; i < val.nwords; ++i) {
    uint64_t a = val.words[i].aval;
    uint64_t b = val.words[i].bval;
    if (match[1]) count += static_cast<uint32_t>(std::popcount(a & ~b));
    if (match[0]) count += static_cast<uint32_t>(std::popcount(~a & ~b));
    if (match[3]) count += static_cast<uint32_t>(std::popcount(a & b));
    if (match[2]) count += static_cast<uint32_t>(std::popcount(~a & b));
  }
  if (match[0] && val.width < val.nwords * 64) {
    count -= val.nwords * 64 - val.width;
  }
  return count;
}

static Logic4Vec EvalCountbits(const Expr* expr, SimContext& ctx,
                               Arena& arena) {
  if (expr->args.size() < 2) return MakeLogic4VecVal(arena, 32, 0);
  auto val = EvalExpr(expr->args[0], ctx, arena);
  bool match[4] = {};
  for (size_t i = 1; i < expr->args.size(); ++i) {
    auto pat = EvalExpr(expr->args[i], ctx, arena);
    uint64_t a = pat.nwords > 0 ? pat.words[0].aval & 1 : 0;
    uint64_t b = pat.nwords > 0 ? pat.words[0].bval & 1 : 0;
    match[a + b * 2] = true;
  }
  return MakeLogic4VecVal(arena, 32, CountMatchingBits(val, match));
}

// ============================================================================
// §20.7 Array query functions
// ============================================================================

// §7.11/§20.7: Determine whether the argument names an aggregate object.
static bool HasUnpackedDim(const Expr* arg, SimContext& ctx) {
  if (!arg || arg->kind != ExprKind::kIdentifier) return false;
  if (ctx.FindArrayInfo(arg->text)) return true;
  if (ctx.FindQueue(arg->text)) return true;
  if (ctx.FindAssocArray(arg->text)) return true;
  return false;
}

Logic4Vec EvalArrayQuerySysCall(const Expr* expr, SimContext& ctx, Arena& arena,
                                std::string_view name) {
  uint32_t width = 32;
  if (!expr->args.empty()) {
    auto val = EvalExpr(expr->args[0], ctx, arena);
    width = val.width;
  }
  bool has_unpacked = !expr->args.empty() && HasUnpackedDim(expr->args[0], ctx);
  uint32_t unpacked_dims = has_unpacked ? 1 : 0;
  uint32_t packed_dims = (width > 0) ? 1 : 0;
  if (name == "$dimensions")
    return MakeLogic4VecVal(arena, 32, packed_dims + unpacked_dims);
  if (name == "$unpacked_dimensions")
    return MakeLogic4VecVal(arena, 32, unpacked_dims);
  if (name == "$left") return MakeLogic4VecVal(arena, 32, width - 1);
  if (name == "$right") return MakeLogic4VecVal(arena, 32, 0);
  if (name == "$low") return MakeLogic4VecVal(arena, 32, 0);
  if (name == "$high") return MakeLogic4VecVal(arena, 32, width - 1);
  if (name == "$increment") {
    uint64_t inc = (width > 1) ? 1 : static_cast<uint64_t>(-1);
    return MakeLogic4VecVal(arena, 32, inc);
  }
  return MakeLogic4VecVal(arena, 32, width);
}

// ============================================================================
// §20.11-20.16 Verification system calls
// ============================================================================

Logic4Vec EvalVerifSysCall(const Expr* expr, SimContext& ctx, Arena& arena,
                           std::string_view name) {
  // §20.12 sampled value functions.
  if (name == "$sampled") {
    if (expr->args.empty()) return MakeLogic4VecVal(arena, 1, 0);
    return EvalExpr(expr->args[0], ctx, arena);
  }
  if (name == "$past") {
    if (expr->args.empty()) return MakeLogic4VecVal(arena, 32, 0);
    return EvalExpr(expr->args[0], ctx, arena);
  }
  if (name == "$rose" || name == "$fell" || name == "$stable" ||
      name == "$changed") {
    return MakeLogic4VecVal(arena, 1, 0);
  }
  // §20.11 assertion control.
  if (name.starts_with("$assert")) return MakeLogic4VecVal(arena, 1, 0);
  // §20.13 coverage.
  if (name.starts_with("$coverage")) return MakeLogic4VecVal(arena, 32, 0);
  // §20.15 stochastic analysis.
  if (name.starts_with("$q_")) return MakeLogic4VecVal(arena, 32, 0);
  // §20.16 PLA modeling.
  return MakeLogic4VecVal(arena, 32, 0);
}

// ============================================================================
// §20 dispatch
// ============================================================================

// §20.5 type conversion sub-dispatch.
static Logic4Vec EvalConversionSysCall(const Expr* expr, SimContext& ctx,
                                       Arena& arena, std::string_view name) {
  if (name == "$itor") return EvalItor(expr, ctx, arena);
  if (name == "$rtoi") return EvalRtoi(expr, ctx, arena);
  if (name == "$bitstoreal") return EvalBitstoreal(expr, ctx, arena);
  if (name == "$realtobits") return EvalRealtobits(expr, ctx, arena);
  if (name == "$shortrealtobits") {
    if (expr->args.empty()) return MakeLogic4VecVal(arena, 32, 0);
    auto val = EvalExpr(expr->args[0], ctx, arena);
    double d = 0.0;
    uint64_t bits = val.ToUint64();
    std::memcpy(&d, &bits, sizeof(double));
    auto f = static_cast<float>(d);
    uint32_t fbits = 0;
    std::memcpy(&fbits, &f, sizeof(float));
    return MakeLogic4VecVal(arena, 32, fbits);
  }
  if (name == "$bitstoshortreal") {
    if (expr->args.empty()) return MakeLogic4VecVal(arena, 64, 0);
    auto val = EvalExpr(expr->args[0], ctx, arena);
    auto fbits = static_cast<uint32_t>(val.ToUint64());
    float f = 0.0f;
    std::memcpy(&f, &fbits, sizeof(float));
    auto d = static_cast<double>(f);
    uint64_t dbits = 0;
    std::memcpy(&dbits, &d, sizeof(double));
    auto result = MakeLogic4VecVal(arena, 64, dbits);
    result.is_real = true;
    return result;
  }
  if (name == "$countbits") return EvalCountbits(expr, ctx, arena);
  return MakeLogic4VecVal(arena, 1, 0);
}

// §6.20.7: $isunbounded(param) — returns 1 if parameter has $ value.
static Logic4Vec EvalIsunbounded(const Expr* expr, SimContext& ctx,
                                 Arena& arena) {
  if (!expr->args.empty() && expr->args[0]->kind == ExprKind::kIdentifier) {
    bool ub = ctx.IsUnboundedParam(expr->args[0]->text);
    return MakeLogic4VecVal(arena, 1, ub ? 1 : 0);
  }
  return MakeLogic4VecVal(arena, 1, 0);
}

// §6.24.2: $cast(dest, source) — dynamic cast, returns 1 on success.
static Logic4Vec EvalCastSysFunc(const Expr* expr, SimContext& ctx,
                                 Arena& arena) {
  if (expr->args.size() < 2 || !expr->args[0]) {
    return MakeLogic4VecVal(arena, 32, 0);
  }
  auto* dest_expr = expr->args[0];
  auto src = EvalExpr(expr->args[1], ctx, arena);
  uint64_t src_val = src.ToUint64();
  if (dest_expr->kind != ExprKind::kIdentifier) {
    return MakeLogic4VecVal(arena, 32, 0);
  }
  auto dest_name = dest_expr->text;
  // §6.24.2 enum cast: check if source value is a valid enum member.
  auto* enum_info = ctx.GetVariableEnumType(dest_name);
  if (enum_info) {
    for (const auto& m : enum_info->members) {
      if (m.value != src_val) continue;
      auto* var = ctx.FindVariable(dest_name);
      if (var) var->value = MakeLogic4VecVal(arena, var->value.width, src_val);
      return MakeLogic4VecVal(arena, 32, 1);
    }
    return MakeLogic4VecVal(arena, 32, 0);
  }
  // Non-enum: simple assignment (always succeeds).
  auto* var = ctx.FindVariable(dest_name);
  if (var) var->value = MakeLogic4VecVal(arena, var->value.width, src_val);
  return MakeLogic4VecVal(arena, 32, 1);
}

Logic4Vec EvalUtilitySysCall(const Expr* expr, SimContext& ctx, Arena& arena,
                             std::string_view name) {
  if (name == "$clog2") return EvalClog2(expr, ctx, arena);
  if (name == "$bits") return EvalBits(expr, ctx, arena);
  if (name == "$signed") return EvalSignCast(expr, ctx, arena, true);
  if (name == "$unsigned") return EvalSignCast(expr, ctx, arena, false);
  if (name == "$countones") return EvalCountones(expr, ctx, arena);
  if (name == "$onehot") return EvalOnehot(expr, ctx, arena);
  if (name == "$onehot0") return EvalOnehot0(expr, ctx, arena);
  if (name == "$isunknown") return EvalIsunknown(expr, ctx, arena);
  if (name == "$isunbounded") return EvalIsunbounded(expr, ctx, arena);
  if (name == "$cast") return EvalCastSysFunc(expr, ctx, arena);
  if (name == "$test$plusargs") return EvalTestPlusargs(expr, ctx, arena);
  if (name == "$value$plusargs") return EvalValuePlusargs(expr, ctx, arena);
  if (name == "$typename") return EvalTypename(expr, ctx, arena);
  if (name == "$sformatf") return EvalSformatf(expr, ctx, arena);
  return EvalConversionSysCall(expr, ctx, arena, name);
}

// ============================================================================
// §21 — $fopen
// ============================================================================

static Logic4Vec EvalFopen(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.size() < 2) return MakeLogic4VecVal(arena, 32, 0);
  std::string filename = ExtractStrArg(expr->args[0]);
  std::string mode = ExtractStrArg(expr->args[1]);
  int fd = ctx.OpenFile(filename, mode);
  return MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(fd));
}

// ============================================================================
// §21 — $fclose
// ============================================================================

static Logic4Vec EvalFclose(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 1, 0);
  int fd = static_cast<int>(EvalExpr(expr->args[0], ctx, arena).ToUint64());
  ctx.CloseFile(fd);
  return MakeLogic4VecVal(arena, 1, 0);
}

// ============================================================================
// §21 — $fdisplay, $fwrite
// ============================================================================

static Logic4Vec EvalFdisplayWrite(const Expr* expr, SimContext& ctx,
                                   Arena& arena, std::string_view name) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 1, 0);
  int fd = static_cast<int>(EvalExpr(expr->args[0], ctx, arena).ToUint64());
  FILE* fp = ctx.GetFileHandle(fd);
  if (!fp) return MakeLogic4VecVal(arena, 1, 0);

  std::string fmt;
  std::vector<Logic4Vec> arg_vals;
  for (size_t i = 1; i < expr->args.size(); ++i) {
    auto val = EvalExpr(expr->args[i], ctx, arena);
    if (i == 1 && expr->args[i]->kind == ExprKind::kStringLiteral) {
      fmt = ExtractFormatString(expr->args[i]);
    } else {
      arg_vals.push_back(val);
    }
  }
  std::string output = fmt.empty() ? "" : FormatDisplay(fmt, arg_vals);
  std::fputs(output.c_str(), fp);
  if (name == "$fdisplay") std::fputc('\n', fp);
  std::fflush(fp);
  return MakeLogic4VecVal(arena, 1, 0);
}

// ============================================================================
// §21 — $readmemh, $readmemb
// ============================================================================

static uint64_t ParseHexLine(const std::string& line) {
  return std::strtoull(line.c_str(), nullptr, 16);
}

static uint64_t ParseBinLine(const std::string& line) {
  return std::strtoull(line.c_str(), nullptr, 2);
}

static Logic4Vec EvalReadmem(const Expr* expr, SimContext& ctx, Arena& arena,
                             bool is_hex) {
  if (expr->args.size() < 2) return MakeLogic4VecVal(arena, 1, 0);
  std::string filename = ExtractStrArg(expr->args[0]);

  std::ifstream ifs(filename);
  if (!ifs.is_open()) {
    std::cerr << "WARNING: $readmem" << (is_hex ? "h" : "b")
              << ": cannot open file: " << filename << "\n";
    return MakeLogic4VecVal(arena, 1, 0);
  }

  // Find the target variable.
  Variable* target = nullptr;
  if (expr->args[1]->kind == ExprKind::kIdentifier) {
    target = ctx.FindVariable(expr->args[1]->text);
  }
  if (!target) return MakeLogic4VecVal(arena, 1, 0);

  // Read the first value and store it into the variable.
  std::string line;
  while (std::getline(ifs, line)) {
    // Skip blank lines and comments.
    if (line.empty() || line[0] == '/' || line[0] == '#') continue;
    uint64_t val = is_hex ? ParseHexLine(line) : ParseBinLine(line);
    target->value = MakeLogic4VecVal(arena, target->value.width, val);
    break;  // For flat variable, store only first value.
  }
  return MakeLogic4VecVal(arena, 1, 0);
}

// ============================================================================
// §21 — $writememh, $writememb
// ============================================================================

static Logic4Vec EvalWritemem(const Expr* expr, SimContext& ctx, Arena& arena,
                              bool is_hex) {
  if (expr->args.size() < 2) return MakeLogic4VecVal(arena, 1, 0);
  std::string filename = ExtractStrArg(expr->args[0]);

  Variable* target = nullptr;
  if (expr->args[1]->kind == ExprKind::kIdentifier) {
    target = ctx.FindVariable(expr->args[1]->text);
  }
  if (!target) return MakeLogic4VecVal(arena, 1, 0);

  std::ofstream ofs(filename);
  if (!ofs.is_open()) {
    std::cerr << "WARNING: $writemem" << (is_hex ? "h" : "b")
              << ": cannot open file: " << filename << "\n";
    return MakeLogic4VecVal(arena, 1, 0);
  }

  if (is_hex) {
    char buf[32];
    std::snprintf(buf, sizeof(buf), "%llx",
                  static_cast<unsigned long long>(target->value.ToUint64()));
    ofs << buf << "\n";
  } else {
    ofs << target->value.ToString() << "\n";
  }
  return MakeLogic4VecVal(arena, 1, 0);
}

// ============================================================================
// §21 — $sscanf
// ============================================================================

static int SpecToBase(char spec) {
  if (spec == 'd') return 10;
  if (spec == 'h' || spec == 'x') return 16;
  if (spec == 'b') return 2;
  return 0;
}

struct ScanResult {
  uint64_t value = 0;
  size_t new_pos = 0;
  bool ok = false;
};

static ScanResult ScanOneValue(const std::string& input, size_t pos, int base) {
  ScanResult sr;
  while (pos < input.size() && input[pos] == ' ') ++pos;
  char* end = nullptr;
  sr.value = std::strtoull(input.c_str() + pos, &end, base);
  sr.ok = (end != input.c_str() + pos);
  sr.new_pos = sr.ok ? static_cast<size_t>(end - input.c_str()) : pos;
  return sr;
}

// Extract a runtime string value from an expression.
static std::string EvalStringArg(const Expr* arg, SimContext& ctx,
                                 Arena& arena) {
  if (arg->kind == ExprKind::kStringLiteral) return ExtractStrArg(arg);
  auto val = EvalExpr(arg, ctx, arena);
  uint32_t nbytes = val.width / 8;
  std::string result;
  for (uint32_t i = nbytes; i > 0; --i) {
    uint32_t byte_idx = i - 1;
    uint32_t word = (byte_idx * 8) / 64;
    uint32_t bit = (byte_idx * 8) % 64;
    if (word >= val.nwords) continue;
    auto ch = static_cast<char>((val.words[word].aval >> bit) & 0xFF);
    if (ch != 0) result += ch;
  }
  return result;
}

static Logic4Vec EvalSscanf(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.size() < 3) return MakeLogic4VecVal(arena, 32, 0);
  std::string input = EvalStringArg(expr->args[0], ctx, arena);
  std::string fmt = ExtractStrArg(expr->args[1]);

  uint32_t matched = 0;
  size_t arg_idx = 2;
  size_t input_pos = 0;

  for (size_t fi = 0; fi < fmt.size(); ++fi) {
    if (fmt[fi] != '%' || fi + 1 >= fmt.size()) continue;
    int base = SpecToBase(fmt[++fi]);
    if (base == 0 || arg_idx >= expr->args.size()) break;

    auto sr = ScanOneValue(input, input_pos, base);
    if (!sr.ok) break;
    input_pos = sr.new_pos;

    if (expr->args[arg_idx]->kind == ExprKind::kIdentifier) {
      auto* var = ctx.FindVariable(expr->args[arg_idx]->text);
      if (var) var->value = MakeLogic4VecVal(arena, var->value.width, sr.value);
    }
    ++matched;
    ++arg_idx;
  }
  return MakeLogic4VecVal(arena, 32, matched);
}

// ============================================================================
// §21 dispatch
// ============================================================================

Logic4Vec EvalIOSysCall(const Expr* expr, SimContext& ctx, Arena& arena,
                        std::string_view name) {
  if (name == "$fopen") return EvalFopen(expr, ctx, arena);
  if (name == "$fclose") return EvalFclose(expr, ctx, arena);
  if (name == "$fdisplay" || name == "$fwrite") {
    return EvalFdisplayWrite(expr, ctx, arena, name);
  }
  if (name == "$readmemh") return EvalReadmem(expr, ctx, arena, true);
  if (name == "$readmemb") return EvalReadmem(expr, ctx, arena, false);
  if (name == "$writememh") return EvalWritemem(expr, ctx, arena, true);
  if (name == "$writememb") return EvalWritemem(expr, ctx, arena, false);
  if (name == "$sscanf") return EvalSscanf(expr, ctx, arena);
  return MakeLogic4VecVal(arena, 1, 0);
}

}  // namespace delta
