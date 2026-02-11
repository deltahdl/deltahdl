#include <bit>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
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
  auto val = EvalExpr(expr->args[0], ctx, arena);
  return MakeLogic4VecVal(arena, 32, val.width);
}

// ============================================================================
// §20 — $unsigned, $signed (pass-through for now)
// ============================================================================

static Logic4Vec EvalSignCast(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 32, 0);
  return EvalExpr(expr->args[0], ctx, arena);
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
// §20 dispatch
// ============================================================================

Logic4Vec EvalUtilitySysCall(const Expr* expr, SimContext& ctx, Arena& arena,
                             std::string_view name) {
  if (name == "$clog2") return EvalClog2(expr, ctx, arena);
  if (name == "$bits") return EvalBits(expr, ctx, arena);
  if (name == "$unsigned" || name == "$signed") {
    return EvalSignCast(expr, ctx, arena);
  }
  if (name == "$countones") return EvalCountones(expr, ctx, arena);
  if (name == "$onehot") return EvalOnehot(expr, ctx, arena);
  if (name == "$onehot0") return EvalOnehot0(expr, ctx, arena);
  if (name == "$isunknown") return EvalIsunknown(expr, ctx, arena);
  if (name == "$test$plusargs") return EvalTestPlusargs(expr, ctx, arena);
  if (name == "$value$plusargs") return EvalValuePlusargs(expr, ctx, arena);
  if (name == "$typename") return EvalTypename(expr, ctx, arena);
  if (name == "$sformatf") return EvalSformatf(expr, ctx, arena);
  return MakeLogic4VecVal(arena, 1, 0);
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

static Logic4Vec EvalSscanf(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.size() < 3) return MakeLogic4VecVal(arena, 32, 0);
  std::string input = ExtractStrArg(expr->args[0]);
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
