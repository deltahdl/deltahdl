#include <cerrno>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "simulator/eval_expr_internal.h"
#include "simulator/eval_string.h"
#include "simulator/eval_systask_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"

namespace delta {

static uint32_t FdFromArg(const Expr* arg, SimContext& ctx, Arena& arena) {
  return static_cast<uint32_t>(EvalExpr(arg, ctx, arena).ToUint64());
}

static FILE* ReadableHandle(uint32_t fd, SimContext& ctx) {
  if (!ctx.IsFdReadable(fd)) {
    ctx.SetFileIoError(fd, EBADF, "file descriptor is not open for reading");
    return nullptr;
  }
  FILE* fp = ctx.GetFileHandle(fd);
  if (fp != nullptr) ctx.ClearFileIoError(fd);
  return fp;
}

static std::string ReadFgetsLine(FILE* fp, bool string_dest,
                                 uint32_t capacity) {
  std::string line;
  line.reserve(string_dest ? 0 : capacity);
  while (string_dest || line.size() < capacity) {
    int ch = std::fgetc(fp);
    if (ch == EOF) break;
    line.push_back(static_cast<char>(ch));
    if (ch == '\n') break;
  }
  return line;
}

static Logic4Vec EvalFgets(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.size() < 2) return MakeLogic4VecVal(arena, 32, 0);
  uint32_t fd = FdFromArg(expr->args[1], ctx, arena);
  FILE* fp = ReadableHandle(fd, ctx);
  if (!fp) return MakeLogic4VecVal(arena, 32, 0);

  const Expr* dest = expr->args[0];
  Variable* var = nullptr;
  if (dest->kind == ExprKind::kIdentifier) var = ctx.FindVariable(dest->text);
  bool string_dest = var != nullptr && ctx.IsStringVariable(dest->text);
  uint32_t capacity = var ? var->value.width / 8 : 0;
  bool assign_dest = var == nullptr;
  if (assign_dest) {
    Logic4Vec held = EvalExpr(dest, ctx, arena);
    string_dest = held.is_string || NamesStringProperty(dest, ctx);
    capacity = held.width / 8;
  }
  if (!string_dest && capacity == 0) return MakeLogic4VecVal(arena, 32, 0);

  std::string line = ReadFgetsLine(fp, string_dest, capacity);

  if (line.empty()) return MakeLogic4VecVal(arena, 32, 0);

  uint32_t width = string_dest ? static_cast<uint32_t>(line.size()) * 8
                               : (var ? var->value.width : capacity * 8);
  Logic4Vec value = ScanStringToVec(arena, line, width);
  value.is_string = string_dest;
  if (assign_dest) {
    PerformBlockingAssign(dest, value, ctx, arena);
    return MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(line.size()));
  }
  var->value = value;
  var->NotifyWatchers();
  return MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(line.size()));
}

static Logic4Vec EvalFgetc(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 32, 0xFFFFFFFF);
  uint32_t fd = FdFromArg(expr->args[0], ctx, arena);
  std::string& pushed = ctx.FdPushback(fd);
  if (!pushed.empty()) {
    auto ch = static_cast<unsigned char>(pushed.back());
    pushed.pop_back();
    ctx.ClearFileIoError(fd);
    return MakeLogic4VecVal(arena, 32, ch);
  }
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
  uint32_t descriptor = FdFromArg(expr->args[0], ctx, arena);
  if ((descriptor & SimContext::kFdMsb) != 0) {
    if (FILE* fp = ctx.GetFileHandle(descriptor)) std::fflush(fp);
  } else {
    for (FILE* fp : ctx.GetMcdFiles(descriptor)) std::fflush(fp);
  }
  return MakeLogic4VecVal(arena, 1, 0);
}

static Logic4Vec EvalFeof(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 32, 1);
  uint32_t fd = FdFromArg(expr->args[0], ctx, arena);
  FILE* fp = ctx.GetFileHandle(fd);
  if (!fp) return MakeLogic4VecVal(arena, 32, 1);
  bool detected = std::feof(fp) != 0 || ctx.FdEofDetected(fd);
  return MakeLogic4VecVal(arena, 32, detected ? 1 : 0);
}

static Logic4Vec EvalFerror(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 32, 0);
  uint32_t fd = FdFromArg(expr->args[0], ctx, arena);

  int32_t code = 0;
  std::string msg;
  if (const auto* err = ctx.GetFileIoError(fd)) {
    code = err->code;
    msg = err->msg;
  } else if (FILE* fp = ctx.GetFileHandle(fd); fp && std::ferror(fp) != 0) {
    code = errno != 0 ? errno : EIO;
    msg = std::strerror(code);
  }

  if (expr->args.size() >= 2 && expr->args[1]->kind == ExprKind::kIdentifier) {
    auto* var = ctx.FindVariable(expr->args[1]->text);
    if (var) {
      Logic4Vec packed = StringToLogic4Vec(arena, msg);
      var->value = ctx.IsStringVariable(expr->args[1]->text)
                       ? StripStringZeros(packed, arena)
                       : ResizeToWidth(packed, var->value.width, arena);
      var->NotifyWatchers();
    }
  }
  return MakeLogic4VecVal(arena, 32, static_cast<uint32_t>(code));
}

static long SignedOffset(const Logic4Vec& vec) {
  uint64_t raw = vec.ToUint64();
  uint32_t width = vec.width;
  if (width > 0 && width < 64) {
    uint64_t sign_bit = uint64_t{1} << (width - 1);
    if (raw & sign_bit) raw |= ~((uint64_t{1} << width) - 1);
  }
  return static_cast<long>(raw);
}

static Logic4Vec PositioningFailure(uint32_t fd, int32_t code, const char* what,
                                    SimContext& ctx, Arena& arena) {
  ctx.SetFileIoError(fd, code, what);
  return MakeLogic4VecVal(arena, 64, static_cast<uint64_t>(-1));
}

static Logic4Vec EvalFseek(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.size() < 3) return MakeLogic4VecVal(arena, 64, 0);
  uint32_t fd = FdFromArg(expr->args[0], ctx, arena);
  FILE* fp = ctx.GetFileHandle(fd);
  if (!fp) {
    return PositioningFailure(
        fd, EBADF, "reposition on an invalid file descriptor", ctx, arena);
  }

  long offset = SignedOffset(EvalExpr(expr->args[1], ctx, arena));

  auto operation =
      static_cast<int>(EvalExpr(expr->args[2], ctx, arena).ToUint64());
  int whence = SEEK_SET;
  if (operation == 1) {
    whence = SEEK_CUR;
  } else if (operation == 2) {
    whence = SEEK_END;
  } else if (operation != 0) {
    return PositioningFailure(fd, EINVAL, "invalid $fseek operation value", ctx,
                              arena);
  }

  int result = std::fseek(fp, offset, whence);
  if (result != 0) {
    return PositioningFailure(fd, errno != 0 ? errno : EIO,
                              std::strerror(errno), ctx, arena);
  }
  ctx.ClearFileIoError(fd);
  ctx.SetFdEofDetected(fd, false);
  ctx.FdPushback(fd).clear();
  return MakeLogic4VecVal(arena, 64, 0);
}

static Logic4Vec EvalFtell(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 64, 0);
  uint32_t fd = FdFromArg(expr->args[0], ctx, arena);
  FILE* fp = ctx.GetFileHandle(fd);
  if (!fp) {
    return PositioningFailure(
        fd, EBADF, "position query on an invalid file descriptor", ctx, arena);
  }
  long pos = std::ftell(fp);
  if (pos < 0) {
    return PositioningFailure(fd, errno != 0 ? errno : EIO,
                              std::strerror(errno), ctx, arena);
  }
  ctx.ClearFileIoError(fd);
  return MakeLogic4VecVal(arena, 64, static_cast<uint64_t>(pos));
}

static Logic4Vec EvalRewind(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 64, 0);
  uint32_t fd = FdFromArg(expr->args[0], ctx, arena);
  FILE* fp = ctx.GetFileHandle(fd);
  if (!fp) {
    return PositioningFailure(
        fd, EBADF, "reposition on an invalid file descriptor", ctx, arena);
  }
  int result = std::fseek(fp, 0, SEEK_SET);
  if (result != 0) {
    return PositioningFailure(fd, errno != 0 ? errno : EIO,
                              std::strerror(errno), ctx, arena);
  }
  ctx.ClearFileIoError(fd);
  ctx.SetFdEofDetected(fd, false);
  ctx.FdPushback(fd).clear();
  return MakeLogic4VecVal(arena, 64, 0);
}

static Logic4Vec PushBackOntoUnreadableFd(int ch, uint32_t fd, SimContext& ctx,
                                          Arena& arena) {
  if (ctx.GetFileHandle(fd) == nullptr) {
    ctx.SetFileIoError(fd, EBADF, "file descriptor is not open");
    return MakeLogic4VecVal(arena, 32, 0xFFFFFFFF);
  }
  if (ch == EOF) {
    ctx.SetFileIoError(fd, EINVAL, "character push back was refused");
    return MakeLogic4VecVal(arena, 32, 0xFFFFFFFF);
  }
  ctx.FdPushback(fd).push_back(
      static_cast<char>(static_cast<unsigned char>(ch)));
  ctx.ClearFileIoError(fd);
  ctx.SetFdEofDetected(fd, false);
  return MakeLogic4VecVal(arena, 32, 0);
}

static Logic4Vec EvalUngetc(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.size() < 2) return MakeLogic4VecVal(arena, 32, 0);
  auto ch = static_cast<int>(EvalExpr(expr->args[0], ctx, arena).ToUint64());
  uint32_t fd = FdFromArg(expr->args[1], ctx, arena);
  if (!ctx.IsFdReadable(fd)) {
    return PushBackOntoUnreadableFd(ch, fd, ctx, arena);
  }
  FILE* fp = ReadableHandle(fd, ctx);
  if (!fp) return MakeLogic4VecVal(arena, 32, 0xFFFFFFFF);
  int result = std::ungetc(ch, fp);
  if (result == EOF) {
    ctx.SetFileIoError(fd, EINVAL, "character push back was refused");
    return MakeLogic4VecVal(arena, 32, 0xFFFFFFFF);
  }
  ctx.SetFdEofDetected(fd, false);
  return MakeLogic4VecVal(arena, 32, 0);
}

static std::string ReadFileContent(FILE* fp) {
  std::string content;
  int c = 0;
  while ((c = std::fgetc(fp)) != EOF) {
    content += static_cast<char>(c);
  }
  return content;
}

static bool ScanArgHasUnknownBits(const Expr* arg, SimContext& ctx,
                                  Arena& arena) {
  if (!arg || arg->kind == ExprKind::kStringLiteral) return false;
  Logic4Vec v = EvalExpr(arg, ctx, arena);
  for (uint32_t w = 0; w < v.nwords; ++w) {
    if (v.words[w].bval != 0) return true;
  }
  return false;
}

static bool IsScanSpace(char c) {
  return c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\f' ||
         c == '\v';
}

static Logic4Vec EvalFscanf(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.size() < 3) return MakeLogic4VecVal(arena, 32, 0);

  if (ScanArgHasUnknownBits(expr->args[1], ctx, arena)) {
    return MakeLogic4VecVal(arena, 32, 0xFFFFFFFF);
  }

  uint32_t fd = FdFromArg(expr->args[0], ctx, arena);
  FILE* fp = ReadableHandle(fd, ctx);
  if (!fp) return MakeLogic4VecVal(arena, 32, 0);

  long start = std::ftell(fp);
  std::string input = ReadFileContent(fp);
  std::fseek(fp, start, SEEK_SET);

  std::string fmt = ResolveFormatArg(expr->args[1], ctx, arena);
  size_t consumed = 0;
  bool hit_end = false;
  ScanRequest req{input,
                  fmt,
                  expr->args.data() + 2,
                  expr->args.size() - 2,
                  consumed,
                  expr->range.start,
                  &hit_end};
  uint32_t matched = RunScanf(req, ctx, arena);

  std::fseek(fp, start + static_cast<long>(consumed), SEEK_SET);

  ctx.SetFdEofDetected(fd, hit_end);

  if (matched == 0) {
    size_t p = consumed;
    while (p < input.size() && IsScanSpace(input[p])) ++p;
    if (p >= input.size()) return MakeLogic4VecVal(arena, 32, 0xFFFFFFFF);
  }
  return MakeLogic4VecVal(arena, 32, matched);
}

static Logic4Vec PackWordBigEndian(Arena& arena, const uint8_t* buf,
                                   size_t nread, uint32_t bytes_per_word,
                                   uint32_t width) {
  Logic4Vec vec = MakeLogic4Vec(arena, width);
  for (size_t i = 0; i < nread; ++i) {
    uint32_t off = 8 * (bytes_per_word - 1 - static_cast<uint32_t>(i));
    if (off >= width) continue;
    uint64_t byte = buf[i];
    if (width - off < 8) byte &= (uint64_t{1} << (width - off)) - 1;
    vec.words[off / 64].aval |= byte << (off % 64);
  }
  return vec;
}

static Logic4Vec FreadUnpackedStruct(const StructTypeInfo* sinfo, Variable* var,
                                     FILE* fp, Arena& arena) {
  size_t count = sinfo->is_union ? 1 : sinfo->fields.size();
  uint64_t total_bytes = 0;
  for (size_t i = 0; i < count; ++i) {
    const StructFieldInfo& fld = sinfo->fields[i];
    uint32_t fbytes = (fld.width + 7) / 8;
    if (fbytes == 0) fbytes = 1;
    auto* fbuf = new uint8_t[fbytes];
    size_t fread_n = std::fread(fbuf, 1, fbytes, fp);
    Logic4Vec fv = PackWordBigEndian(arena, fbuf, fread_n, fbytes, fld.width);
    delete[] fbuf;

    DepositBitField(var->value, fld.bit_offset, fv, fld.width);
    total_bytes += fread_n;
    if (fread_n < fbytes) break;
  }
  var->NotifyWatchers();
  return MakeLogic4VecVal(arena, 32, total_bytes);
}

static Logic4Vec FreadIntegralVar(Variable* var, FILE* fp, Arena& arena) {
  uint32_t nbytes = (var->value.width + 7) / 8;
  if (nbytes == 0) nbytes = 1;
  auto* buf = new uint8_t[nbytes];
  size_t nread = std::fread(buf, 1, nbytes, fp);
  var->value = PackWordBigEndian(arena, buf, nread, nbytes, var->value.width);
  delete[] buf;
  var->NotifyWatchers();
  return MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(nread));
}

static int64_t FreadStartAddr(const Expr* expr, int64_t low_addr,
                              SimContext& ctx, Arena& arena) {
  bool has_start = expr->args.size() >= 3 && expr->args[2] != nullptr;
  if (!has_start) return low_addr;
  return static_cast<int64_t>(EvalExpr(expr->args[2], ctx, arena).ToUint64());
}

static uint64_t FreadMaxWords(const Expr* expr, bool& has_count,
                              SimContext& ctx, Arena& arena) {
  has_count = expr->args.size() >= 4 && expr->args[3] != nullptr;
  if (!has_count) return 0;
  return EvalExpr(expr->args[3], ctx, arena).ToUint64();
}

struct FreadMemory {
  std::string mem_name;
  int64_t low_addr;
  int64_t high_addr;
  uint32_t bytes_per_word;
};

struct FreadWindow {
  int64_t start_addr;
  bool has_count;
  uint64_t max_words;
};

static uint64_t FreadLoadWords(const FreadMemory& mem, const FreadWindow& win,
                               FILE* fp, SimContext& ctx, Arena& arena) {
  uint64_t total_bytes = 0;
  uint64_t words_done = 0;
  auto* buf = new uint8_t[mem.bytes_per_word];
  for (int64_t addr = win.start_addr;
       addr <= mem.high_addr && (!win.has_count || words_done < win.max_words);
       ++addr) {
    if (addr < mem.low_addr) continue;
    size_t nread = std::fread(buf, 1, mem.bytes_per_word, fp);
    if (nread == 0) break;
    std::string elem = mem.mem_name + "[" + std::to_string(addr) + "]";
    if (auto* v = ctx.FindVariable(elem)) {
      v->value = PackWordBigEndian(arena, buf, nread, mem.bytes_per_word,
                                   v->value.width);
      v->NotifyWatchers();
    }
    total_bytes += nread;
    ++words_done;
    if (nread < mem.bytes_per_word) break;
  }
  delete[] buf;
  return total_bytes;
}

static Logic4Vec FreadMemoryArray(const Expr* expr, const ArrayInfo* ai,
                                  FILE* fp, SimContext& ctx, Arena& arena) {
  const Expr* dst = expr->args[0];
  std::string mem_name(dst->text);
  int64_t low_addr = ai->lo;
  int64_t high_addr = ai->lo + static_cast<int64_t>(ai->size) - 1;
  uint32_t elem_width = ai->elem_width;
  uint32_t bytes_per_word = (elem_width + 7) / 8;
  if (bytes_per_word == 0) bytes_per_word = 1;

  int64_t start_addr = FreadStartAddr(expr, low_addr, ctx, arena);
  bool has_count = false;
  uint64_t max_words = FreadMaxWords(expr, has_count, ctx, arena);

  FreadMemory mem{mem_name, low_addr, high_addr, bytes_per_word};
  FreadWindow win{start_addr, has_count, max_words};
  uint64_t total_bytes = FreadLoadWords(mem, win, fp, ctx, arena);
  return MakeLogic4VecVal(arena, 32, total_bytes);
}

static Logic4Vec FreadNonArray(const Expr* dst, FILE* fp, SimContext& ctx,
                               Arena& arena) {
  const StructTypeInfo* sinfo = (dst->kind == ExprKind::kIdentifier)
                                    ? StructLayoutOfName(dst->text, ctx)
                                    : nullptr;
  if (sinfo && !sinfo->is_packed && !sinfo->fields.empty()) {
    Variable* var = ctx.FindVariable(dst->text);
    if (!var) return MakeLogic4VecVal(arena, 32, 0);
    return FreadUnpackedStruct(sinfo, var, fp, arena);
  }

  Variable* var = (dst->kind == ExprKind::kIdentifier)
                      ? ctx.FindVariable(dst->text)
                      : nullptr;
  if (!var) return MakeLogic4VecVal(arena, 32, 0);
  return FreadIntegralVar(var, fp, arena);
}

static Logic4Vec EvalFread(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.size() < 2) return MakeLogic4VecVal(arena, 32, 0);
  uint32_t fd = FdFromArg(expr->args[1], ctx, arena);
  FILE* fp = ReadableHandle(fd, ctx);
  if (!fp) return MakeLogic4VecVal(arena, 32, 0);

  const Expr* dst = expr->args[0];
  const ArrayInfo* ai = (dst->kind == ExprKind::kIdentifier)
                            ? ctx.FindArrayInfo(dst->text)
                            : nullptr;

  if (!ai) return FreadNonArray(dst, fp, ctx, arena);
  return FreadMemoryArray(expr, ai, fp, ctx, arena);
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

}  // namespace delta
