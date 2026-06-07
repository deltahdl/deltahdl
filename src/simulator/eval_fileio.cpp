#include <cerrno>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

namespace delta {

static uint32_t FdFromArg(const Expr* arg, SimContext& ctx, Arena& arena) {
  return static_cast<uint32_t>(EvalExpr(arg, ctx, arena).ToUint64());
}

// §21.3.4: a file descriptor may be read from only when it was opened with a
// read or read-update type. Returning a null handle for a write/append channel
// makes each read function fall through to its normal failure result.
static FILE* ReadableHandle(uint32_t fd, SimContext& ctx) {
  if (!ctx.IsFdReadable(fd)) return nullptr;
  return ctx.GetFileHandle(fd);
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

static Logic4Vec EvalFgets(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.size() < 2) return MakeLogic4VecVal(arena, 32, 0);
  uint32_t fd = FdFromArg(expr->args[1], ctx, arena);
  FILE* fp = ReadableHandle(fd, ctx);
  if (!fp) return MakeLogic4VecVal(arena, 32, 0);

  // §21.3.4.2: the destination variable bounds how much one line can hold. Its
  // capacity is its number of whole bytes -- a most-significant partial byte
  // (a width that is not a multiple of eight) does not count toward the size.
  Variable* var = nullptr;
  if (expr->args[0]->kind == ExprKind::kIdentifier)
    var = ctx.FindVariable(expr->args[0]->text);
  uint32_t capacity = var ? var->value.width / 8 : 0;
  if (capacity == 0) return MakeLogic4VecVal(arena, 32, 0);

  // §21.3.4.2: characters are read until the variable is filled, a newline is
  // read (the newline itself is kept), or end-of-file is reached.
  std::string line;
  line.reserve(capacity);
  while (line.size() < capacity) {
    int ch = std::fgetc(fp);
    if (ch == EOF) break;
    line.push_back(static_cast<char>(ch));
    if (ch == '\n') break;
  }

  // §21.3.4.2: a read that returns no characters (error/EOF) yields a count of
  // zero; otherwise the count of characters read is returned.
  if (line.empty()) return MakeLogic4VecVal(arena, 32, 0);

  if (var) var->value = StringToVec(arena, line, var->value.width);
  return MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(line.size()));
}

static Logic4Vec EvalFgetc(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 32, 0xFFFFFFFF);
  uint32_t fd = FdFromArg(expr->args[0], ctx, arena);
  FILE* fp = ReadableHandle(fd, ctx);
  if (!fp) return MakeLogic4VecVal(arena, 32, 0xFFFFFFFF);

  int ch = std::fgetc(fp);
  if (ch == EOF) return MakeLogic4VecVal(arena, 32, 0xFFFFFFFF);
  return MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(ch));
}

static Logic4Vec EvalFflush(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) {
    std::fflush(nullptr);
    return MakeLogic4VecVal(arena, 1, 0);
  }
  uint32_t fd = FdFromArg(expr->args[0], ctx, arena);
  FILE* fp = ctx.GetFileHandle(fd);
  if (fp) std::fflush(fp);
  return MakeLogic4VecVal(arena, 1, 0);
}

static Logic4Vec EvalFeof(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 32, 1);
  uint32_t fd = FdFromArg(expr->args[0], ctx, arena);
  FILE* fp = ctx.GetFileHandle(fd);
  if (!fp) return MakeLogic4VecVal(arena, 32, 1);
  int result = std::feof(fp);
  return MakeLogic4VecVal(arena, 32, result != 0 ? 1 : 0);
}

static Logic4Vec EvalFerror(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 32, 0);
  uint32_t fd = FdFromArg(expr->args[0], ctx, arena);
  FILE* fp = ctx.GetFileHandle(fd);
  if (!fp) return MakeLogic4VecVal(arena, 32, 0);

  int err = std::ferror(fp);

  // §21.3.7: the str argument receives a textual description of the error
  // raised by the most recent file I/O operation. When the most recent
  // operation did not fail, the standard requires the returned code to be zero
  // and the str variable to be cleared rather than left holding a stale value.
  if (expr->args.size() >= 2 &&
      expr->args[1]->kind == ExprKind::kIdentifier) {
    auto* var = ctx.FindVariable(expr->args[1]->text);
    if (var) {
      std::string msg = err != 0 ? std::strerror(errno) : std::string();
      var->value = StringToVec(arena, msg, var->value.width);
    }
  }
  return MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(err));
}

// §21.3.5: the new position is the signed distance "offset" from the chosen
// origin. The argument is read as a signed quantity of its own width, so a
// narrow negative value (e.g. a 32-bit -2) seeks backward rather than being
// zero-extended into a huge forward offset.
static long SignedOffset(const Logic4Vec& vec) {
  uint64_t raw = vec.ToUint64();
  uint32_t width = vec.width;
  if (width > 0 && width < 64) {
    uint64_t sign_bit = uint64_t{1} << (width - 1);
    if (raw & sign_bit) raw |= ~((uint64_t{1} << width) - 1);
  }
  return static_cast<long>(raw);
}

static Logic4Vec EvalFseek(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.size() < 3) return MakeLogic4VecVal(arena, 32, 0);
  uint32_t fd = FdFromArg(expr->args[0], ctx, arena);
  FILE* fp = ctx.GetFileHandle(fd);
  // §21.3.5: a failed reposition reports the error code -1.
  if (!fp) return MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(-1));

  long offset = SignedOffset(EvalExpr(expr->args[1], ctx, arena));

  // §21.3.5: the operation argument selects the origin -- 0 is the start of
  // the file, 1 the current position, and 2 the end of file. Map these to the
  // host's seek constants explicitly rather than assuming the platform's
  // SEEK_* macros share those numeric values.
  auto operation =
      static_cast<int>(EvalExpr(expr->args[2], ctx, arena).ToUint64());
  int whence = SEEK_SET;
  if (operation == 1) {
    whence = SEEK_CUR;
  } else if (operation == 2) {
    whence = SEEK_END;
  } else if (operation != 0) {
    return MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(-1));
  }

  // §21.3.5: a successful $fseek cancels any $ungetc push-back; the host's
  // std::fseek discards pushed-back characters for the stream as required.
  int result = std::fseek(fp, offset, whence);
  return MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(result));
}

static Logic4Vec EvalFtell(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 64, 0);
  uint32_t fd = FdFromArg(expr->args[0], ctx, arena);
  FILE* fp = ctx.GetFileHandle(fd);
  if (!fp) return MakeLogic4VecVal(arena, 64, static_cast<uint64_t>(-1));
  long pos = std::ftell(fp);
  return MakeLogic4VecVal(arena, 64, static_cast<uint64_t>(pos));
}

static Logic4Vec EvalRewind(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 32, 0);
  uint32_t fd = FdFromArg(expr->args[0], ctx, arena);
  FILE* fp = ctx.GetFileHandle(fd);
  // §21.3.5: $rewind is equivalent to $fseek(fd, 0, 0) and, like $fseek,
  // reports -1 when the reposition fails. The host reposition also discards
  // any $ungetc push-back, satisfying the cancellation requirement.
  if (!fp) return MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(-1));
  int result = std::fseek(fp, 0, SEEK_SET);
  return MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(result));
}

static Logic4Vec EvalUngetc(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.size() < 2) return MakeLogic4VecVal(arena, 32, 0);
  auto ch = static_cast<int>(EvalExpr(expr->args[0], ctx, arena).ToUint64());
  uint32_t fd = FdFromArg(expr->args[1], ctx, arena);
  FILE* fp = ReadableHandle(fd, ctx);
  if (!fp) return MakeLogic4VecVal(arena, 32, 0);
  // §21.3.4.1: the result of a push back is zero on success and EOF when the
  // character could not be pushed onto the descriptor. The host library returns
  // the pushed character (not zero) on success, so normalize the codes here.
  int result = std::ungetc(ch, fp);
  if (result == EOF) return MakeLogic4VecVal(arena, 32, 0xFFFFFFFF);
  return MakeLogic4VecVal(arena, 32, 0);
}

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
  uint32_t fd = FdFromArg(expr->args[0], ctx, arena);
  FILE* fp = ReadableHandle(fd, ctx);
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

static Logic4Vec EvalFread(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.size() < 2) return MakeLogic4VecVal(arena, 32, 0);
  uint32_t fd = FdFromArg(expr->args[1], ctx, arena);
  FILE* fp = ReadableHandle(fd, ctx);
  if (!fp) return MakeLogic4VecVal(arena, 32, 0);

  Variable* var = nullptr;
  if (expr->args[0]->kind == ExprKind::kIdentifier) {
    var = ctx.FindVariable(expr->args[0]->text);
  }
  if (!var) return MakeLogic4VecVal(arena, 32, 0);

  uint32_t nbytes = (var->value.width + 7) / 8;
  auto* buf = new uint8_t[nbytes];
  size_t nread = std::fread(buf, 1, nbytes, fp);

  uint64_t val = 0;
  for (size_t i = 0; i < nread && i < 8; ++i) {
    val = (val << 8) | buf[i];
  }
  var->value = MakeLogic4VecVal(arena, var->value.width, val);
  delete[] buf;
  return MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(nread));
}

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

}
