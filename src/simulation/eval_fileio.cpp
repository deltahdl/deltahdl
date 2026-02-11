#include <cerrno>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast.h"
#include "simulation/eval.h"
#include "simulation/sim_context.h"

namespace delta {

// ============================================================================
// Helpers
// ============================================================================

static int FdFromArg(const Expr* arg, SimContext& ctx, Arena& arena) {
  return static_cast<int>(EvalExpr(arg, ctx, arena).ToUint64());
}

static Logic4Vec StringToVec(Arena& arena, const std::string& str,
                             uint32_t width) {
  auto vec = MakeLogic4VecVal(arena, width, 0);
  for (size_t i = 0; i < str.size() && i * 8 < width; ++i) {
    auto byte_idx = static_cast<uint32_t>(str.size() - 1 - i);
    uint32_t word = (byte_idx * 8) / 64;
    uint32_t bit = (byte_idx * 8) % 64;
    if (word < vec.nwords) {
      vec.words[word].aval |= static_cast<uint64_t>(str[i]) << bit;
    }
  }
  return vec;
}

// ============================================================================
// section 21.3 -- $fgets(str, fd)
// ============================================================================

static Logic4Vec EvalFgets(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.size() < 2) return MakeLogic4VecVal(arena, 32, 0);
  int fd = FdFromArg(expr->args[1], ctx, arena);
  FILE* fp = ctx.GetFileHandle(fd);
  if (!fp) return MakeLogic4VecVal(arena, 32, 0);

  char buf[4096];
  char* result = std::fgets(buf, sizeof(buf), fp);
  if (!result) return MakeLogic4VecVal(arena, 32, 0);

  std::string line(buf);
  auto nchars = static_cast<uint64_t>(line.size());

  // Write the string into the destination variable.
  if (expr->args[0]->kind == ExprKind::kIdentifier) {
    auto* var = ctx.FindVariable(expr->args[0]->text);
    if (var) var->value = StringToVec(arena, line, var->value.width);
  }
  return MakeLogic4VecVal(arena, 32, nchars);
}

// ============================================================================
// section 21.3 -- $fgetc(fd)
// ============================================================================

static Logic4Vec EvalFgetc(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 32, 0xFFFFFFFF);
  int fd = FdFromArg(expr->args[0], ctx, arena);
  FILE* fp = ctx.GetFileHandle(fd);
  if (!fp) return MakeLogic4VecVal(arena, 32, 0xFFFFFFFF);

  int ch = std::fgetc(fp);
  if (ch == EOF) return MakeLogic4VecVal(arena, 32, 0xFFFFFFFF);
  return MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(ch));
}

// ============================================================================
// section 21.3 -- $fflush(fd)
// ============================================================================

static Logic4Vec EvalFflush(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) {
    std::fflush(nullptr);  // Flush all open streams.
    return MakeLogic4VecVal(arena, 1, 0);
  }
  int fd = FdFromArg(expr->args[0], ctx, arena);
  FILE* fp = ctx.GetFileHandle(fd);
  if (fp) std::fflush(fp);
  return MakeLogic4VecVal(arena, 1, 0);
}

// ============================================================================
// section 21.3 -- $feof(fd)
// ============================================================================

static Logic4Vec EvalFeof(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 32, 1);
  int fd = FdFromArg(expr->args[0], ctx, arena);
  FILE* fp = ctx.GetFileHandle(fd);
  if (!fp) return MakeLogic4VecVal(arena, 32, 1);
  int result = std::feof(fp);
  return MakeLogic4VecVal(arena, 32, result != 0 ? 1 : 0);
}

// ============================================================================
// section 21.3 -- $ferror(fd, str)
// ============================================================================

static Logic4Vec EvalFerror(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 32, 0);
  int fd = FdFromArg(expr->args[0], ctx, arena);
  FILE* fp = ctx.GetFileHandle(fd);
  if (!fp) return MakeLogic4VecVal(arena, 32, 0);

  int err = std::ferror(fp);
  // Optionally write error string to second arg variable.
  if (err != 0 && expr->args.size() >= 2) {
    if (expr->args[1]->kind == ExprKind::kIdentifier) {
      auto* var = ctx.FindVariable(expr->args[1]->text);
      if (var) {
        std::string msg = std::strerror(errno);
        var->value = StringToVec(arena, msg, var->value.width);
      }
    }
  }
  return MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(err));
}

// ============================================================================
// section 21.3 -- $fseek(fd, offset, whence)
// ============================================================================

static Logic4Vec EvalFseek(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.size() < 3) return MakeLogic4VecVal(arena, 32, 0);
  int fd = FdFromArg(expr->args[0], ctx, arena);
  FILE* fp = ctx.GetFileHandle(fd);
  if (!fp) return MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(-1));

  auto offset =
      static_cast<long>(EvalExpr(expr->args[1], ctx, arena).ToUint64());
  auto whence =
      static_cast<int>(EvalExpr(expr->args[2], ctx, arena).ToUint64());
  int result = std::fseek(fp, offset, whence);
  return MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(result));
}

// ============================================================================
// section 21.3 -- $ftell(fd)
// ============================================================================

static Logic4Vec EvalFtell(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 64, 0);
  int fd = FdFromArg(expr->args[0], ctx, arena);
  FILE* fp = ctx.GetFileHandle(fd);
  if (!fp) return MakeLogic4VecVal(arena, 64, static_cast<uint64_t>(-1));
  long pos = std::ftell(fp);
  return MakeLogic4VecVal(arena, 64, static_cast<uint64_t>(pos));
}

// ============================================================================
// section 21.3 -- $rewind(fd)
// ============================================================================

static Logic4Vec EvalRewind(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 32, 0);
  int fd = FdFromArg(expr->args[0], ctx, arena);
  FILE* fp = ctx.GetFileHandle(fd);
  if (fp) std::fseek(fp, 0, SEEK_SET);
  return MakeLogic4VecVal(arena, 32, 0);
}

// ============================================================================
// section 21.3 -- $ungetc(char, fd)
// ============================================================================

static Logic4Vec EvalUngetc(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.size() < 2) return MakeLogic4VecVal(arena, 32, 0);
  auto ch = static_cast<int>(EvalExpr(expr->args[0], ctx, arena).ToUint64());
  int fd = FdFromArg(expr->args[1], ctx, arena);
  FILE* fp = ctx.GetFileHandle(fd);
  if (!fp) return MakeLogic4VecVal(arena, 32, 0);
  int result = std::ungetc(ch, fp);
  return MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(result));
}

// ============================================================================
// section 21.3 -- $fscanf(fd, format, args...)
// ============================================================================

static int SpecToBase(char spec) {
  if (spec == 'd') return 10;
  if (spec == 'h' || spec == 'x') return 16;
  if (spec == 'b') return 2;
  if (spec == 'o') return 8;
  return 0;
}

static std::string ReadFileContent(FILE* fp) {
  std::string content;
  int c = 0;
  while ((c = std::fgetc(fp)) != EOF) {
    content += static_cast<char>(c);
  }
  return content;
}

static std::string ExtractFmtStr(std::string_view text) {
  if (text.size() >= 2 && text.front() == '"') {
    return std::string(text.substr(1, text.size() - 2));
  }
  return std::string(text);
}

struct ScanState {
  size_t input_pos = 0;
  uint32_t matched = 0;
};

static bool ScanOneField(const std::string& input, ScanState& state, int base,
                         Variable* var, Arena& arena) {
  while (state.input_pos < input.size() && input[state.input_pos] == ' ') {
    ++state.input_pos;
  }
  char* end = nullptr;
  auto val = std::strtoull(input.c_str() + state.input_pos, &end, base);
  if (end == input.c_str() + state.input_pos) return false;
  state.input_pos = static_cast<size_t>(end - input.c_str());
  if (var) var->value = MakeLogic4VecVal(arena, var->value.width, val);
  ++state.matched;
  return true;
}

static Logic4Vec EvalFscanf(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.size() < 3) return MakeLogic4VecVal(arena, 32, 0);
  int fd = FdFromArg(expr->args[0], ctx, arena);
  FILE* fp = ctx.GetFileHandle(fd);
  if (!fp) return MakeLogic4VecVal(arena, 32, 0);

  long start = std::ftell(fp);
  std::string input = ReadFileContent(fp);
  std::fseek(fp, start, SEEK_SET);

  std::string fmt = ExtractFmtStr(expr->args[1]->text);
  ScanState state;
  size_t arg_idx = 2;

  for (size_t fi = 0; fi < fmt.size(); ++fi) {
    if (fmt[fi] != '%' || fi + 1 >= fmt.size()) continue;
    int base = SpecToBase(fmt[++fi]);
    if (base == 0 || arg_idx >= expr->args.size()) break;
    Variable* var = nullptr;
    if (expr->args[arg_idx]->kind == ExprKind::kIdentifier) {
      var = ctx.FindVariable(expr->args[arg_idx]->text);
    }
    if (!ScanOneField(input, state, base, var, arena)) break;
    ++arg_idx;
  }
  std::fseek(fp, start + static_cast<long>(state.input_pos), SEEK_SET);
  return MakeLogic4VecVal(arena, 32, state.matched);
}

// ============================================================================
// section 21.3 -- $fread(variable, fd [, start [, count]])
// ============================================================================

static Logic4Vec EvalFread(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.size() < 2) return MakeLogic4VecVal(arena, 32, 0);
  int fd = FdFromArg(expr->args[1], ctx, arena);
  FILE* fp = ctx.GetFileHandle(fd);
  if (!fp) return MakeLogic4VecVal(arena, 32, 0);

  Variable* var = nullptr;
  if (expr->args[0]->kind == ExprKind::kIdentifier) {
    var = ctx.FindVariable(expr->args[0]->text);
  }
  if (!var) return MakeLogic4VecVal(arena, 32, 0);

  // Read width/8 bytes (rounded up) to fill the variable.
  uint32_t nbytes = (var->value.width + 7) / 8;
  auto* buf = new uint8_t[nbytes];
  size_t nread = std::fread(buf, 1, nbytes, fp);

  // Pack bytes into the variable (big-endian as per LRM).
  uint64_t val = 0;
  for (size_t i = 0; i < nread && i < 8; ++i) {
    val = (val << 8) | buf[i];
  }
  var->value = MakeLogic4VecVal(arena, var->value.width, val);
  delete[] buf;
  return MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(nread));
}

// ============================================================================
// Public dispatch: EvalFileIOSysCall
// ============================================================================

Logic4Vec EvalFileIOSysCall(const Expr* expr, SimContext& ctx, Arena& arena,
                            std::string_view name) {
  if (name == "$fgets") return EvalFgets(expr, ctx, arena);
  if (name == "$fgetc") return EvalFgetc(expr, ctx, arena);
  if (name == "$fflush") return EvalFflush(expr, ctx, arena);
  if (name == "$feof") return EvalFeof(expr, ctx, arena);
  if (name == "$ferror") return EvalFerror(expr, ctx, arena);
  if (name == "$fseek") return EvalFseek(expr, ctx, arena);
  if (name == "$ftell") return EvalFtell(expr, ctx, arena);
  if (name == "$rewind") return EvalRewind(expr, ctx, arena);
  if (name == "$ungetc") return EvalUngetc(expr, ctx, arena);
  if (name == "$fscanf") return EvalFscanf(expr, ctx, arena);
  if (name == "$fread") return EvalFread(expr, ctx, arena);
  return MakeLogic4VecVal(arena, 1, 0);
}

}  // namespace delta
