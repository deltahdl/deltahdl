#include <cerrno>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
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
  // §21.3.6: with no argument every open file is flushed.
  if (expr->args.empty()) {
    std::fflush(nullptr);
    return MakeLogic4VecVal(arena, 1, 0);
  }
  // §21.3.6: the single argument is either a multi-channel descriptor, whose
  // every selected channel is flushed, or a single file descriptor. A real fd
  // carries the reserved high bit; anything else is treated as an mcd.
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

// §21.3.4.3: the integer conversion codes are case-insensitive (%d or %D, and
// so on). Returns the numeric base for an integer code, or 0 for a code this
// reader does not treat as an integer field.
static int SpecToBase(char spec) {
  char c = (spec >= 'A' && spec <= 'Z') ? static_cast<char>(spec - 'A' + 'a')
                                        : spec;
  if (c == 'd') return 10;
  if (c == 'h' || c == 'x') return 16;
  if (c == 'b') return 2;
  if (c == 'o') return 8;
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

// §21.3.4.3: the control string is parsed as ASCII, so a four-state value with
// any unknown bit (x or z) cannot be interpreted. Only a non-literal argument
// can carry such bits; a string literal never does.
static bool ScanArgHasUnknownBits(const Expr* arg, SimContext& ctx,
                                  Arena& arena) {
  if (!arg || arg->kind == ExprKind::kStringLiteral) return false;
  Logic4Vec v = EvalExpr(arg, ctx, arena);
  for (uint32_t w = 0; w < v.nwords; ++w) {
    if (v.words[w].bval != 0) return true;
  }
  return false;
}

// §21.3.4.3: leading white space in front of an input field is ignored. The
// set covers blanks, tabs, newlines, and formfeeds (plus the related vertical
// tab and carriage return).
static bool IsScanSpace(char c) {
  return c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\f' ||
         c == '\v';
}

// §21.3.4.3: store the converted real value (its IEEE-754 bit pattern) into a
// real destination variable.
static void StoreRealField(Variable* var, Arena& arena, double d) {
  if (!var) return;
  uint64_t bits = 0;
  std::memcpy(&bits, &d, sizeof(double));
  uint32_t width = var->value.width ? var->value.width : 64;
  auto vec = MakeLogic4VecVal(arena, width, bits);
  vec.is_real = true;
  var->value = vec;
}

// §21.3.4.3 scan engine shared by $fscanf (here) and $sscanf. Interprets the
// control string `fmt` against `input`, assigning converted fields to the
// destination arguments. Returns the number of items assigned and reports, via
// `consumed`, how many input characters were used.
static uint32_t RunScanf(const std::string& input, const std::string& fmt,
                         Expr* const* dest, size_t ndest, SimContext& ctx,
                         Arena& arena, size_t& consumed) {
  size_t pos = 0;  // input cursor
  size_t ai = 0;   // next destination argument
  uint32_t matched = 0;

  auto field_var = [&](bool suppress) -> Variable* {
    if (suppress || ai >= ndest) return nullptr;
    const Expr* a = dest[ai];
    if (a->kind == ExprKind::kIdentifier) return ctx.FindVariable(a->text);
    return nullptr;
  };
  auto upper_limit = [&](int width) -> size_t {
    if (width > 0 && pos + static_cast<size_t>(width) < input.size())
      return pos + static_cast<size_t>(width);
    return input.size();
  };

  for (size_t fi = 0; fi < fmt.size(); ++fi) {
    char fc = fmt[fi];

    // §21.3.4.3 (a): white space in the control string skips a run of input
    // white space.
    if (IsScanSpace(fc)) {
      while (pos < input.size() && IsScanSpace(input[pos])) ++pos;
      continue;
    }

    // §21.3.4.3 (b): an ordinary character must match the next input character;
    // a mismatch ends the scan with the offending character left unread.
    if (fc != '%') {
      if (pos >= input.size() || input[pos] != fc) break;
      ++pos;
      continue;
    }

    if (fi + 1 >= fmt.size()) break;
    ++fi;
    // §21.3.4.3 (c): optional assignment-suppression character.
    bool suppress = false;
    if (fmt[fi] == '*') {
      suppress = true;
      if (++fi >= fmt.size()) break;
    }
    // §21.3.4.3 (c): optional maximum field width.
    int width = 0;
    while (fi < fmt.size() && fmt[fi] >= '0' && fmt[fi] <= '9') {
      width = width * 10 + (fmt[fi] - '0');
      ++fi;
    }
    if (fi >= fmt.size()) break;
    char code = fmt[fi];
    char lc = (code >= 'A' && code <= 'Z') ? static_cast<char>(code - 'A' + 'a')
                                           : code;

    if (lc == '%') {
      if (pos >= input.size() || input[pos] != '%') break;
      ++pos;
      continue;
    }

    if (lc == 'c') {
      // §21.3.4.3: the character conversion does not skip leading white space;
      // it takes the next character(s) verbatim.
      int cnt = width > 0 ? width : 1;
      if (pos >= input.size()) break;
      std::string chars;
      for (int k = 0; k < cnt && pos < input.size(); ++k) chars += input[pos++];
      Variable* var = field_var(suppress);
      if (var) {
        if (chars.size() == 1) {
          var->value = MakeLogic4VecVal(arena, var->value.width,
                                        static_cast<uint8_t>(chars[0]));
        } else {
          var->value = StringToVec(arena, chars, var->value.width);
        }
      }
      if (!suppress) {
        ++matched;
        ++ai;
      }
      continue;
    }

    // §21.3.4.3: every remaining conversion ignores white space leading the
    // input field.
    while (pos < input.size() && IsScanSpace(input[pos])) ++pos;

    if (lc == 's') {
      size_t limit = upper_limit(width);
      std::string s;
      while (pos < limit && !IsScanSpace(input[pos])) s += input[pos++];
      if (s.empty()) break;
      Variable* var = field_var(suppress);
      if (var) var->value = StringToVec(arena, s, var->value.width);
      if (!suppress) {
        ++matched;
        ++ai;
      }
      continue;
    }

    if (lc == 'f' || lc == 'e' || lc == 'g' || lc == 't') {
      size_t limit = upper_limit(width);
      std::string sub = input.substr(pos, limit - pos);
      const char* c = sub.c_str();
      char* end = nullptr;
      double d = std::strtod(c, &end);
      if (end == c) break;
      pos += static_cast<size_t>(end - c);
      StoreRealField(field_var(suppress), arena, d);
      if (!suppress) {
        ++matched;
        ++ai;
      }
      continue;
    }

    int base = SpecToBase(lc);
    if (base == 0) break;  // unsupported conversion code: stop scanning
    size_t limit = upper_limit(width);
    std::string sub = input.substr(pos, limit - pos);
    const char* c = sub.c_str();
    char* end = nullptr;
    unsigned long long v = std::strtoull(c, &end, base);
    if (end == c) break;
    pos += static_cast<size_t>(end - c);
    Variable* var = field_var(suppress);
    if (var) {
      var->value =
          MakeLogic4VecVal(arena, var->value.width, static_cast<uint64_t>(v));
    }
    if (!suppress) {
      ++matched;
      ++ai;
    }
  }

  consumed = pos;
  return matched;
}

static Logic4Vec EvalFscanf(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.size() < 3) return MakeLogic4VecVal(arena, 32, 0);

  // §21.3.4.3: an unknown bit (x or z) in the format string makes the function
  // report EOF (-1).
  if (ScanArgHasUnknownBits(expr->args[1], ctx, arena)) {
    return MakeLogic4VecVal(arena, 32, 0xFFFFFFFF);
  }

  uint32_t fd = FdFromArg(expr->args[0], ctx, arena);
  FILE* fp = ReadableHandle(fd, ctx);
  if (!fp) return MakeLogic4VecVal(arena, 32, 0);

  long start = std::ftell(fp);
  std::string input = ReadFileContent(fp);
  std::fseek(fp, start, SEEK_SET);

  std::string fmt = ExtractFmtStr(expr->args[1]->text);
  size_t consumed = 0;
  uint32_t matched = RunScanf(input, fmt, expr->args.data() + 2,
                              expr->args.size() - 2, ctx, arena, consumed);

  // §21.3.4.3: leave the descriptor positioned just past the consumed input so
  // a later read continues where the scan stopped.
  std::fseek(fp, start + static_cast<long>(consumed), SEEK_SET);

  // §21.3.4.3: a return of zero means an input character failed to match the
  // control string, whereas EOF (-1) is reported when the input runs out before
  // any field could be converted.
  if (matched == 0) {
    size_t p = consumed;
    while (p < input.size() && IsScanSpace(input[p])) ++p;
    if (p >= input.size()) return MakeLogic4VecVal(arena, 32, 0xFFFFFFFF);
  }
  return MakeLogic4VecVal(arena, 32, matched);
}

// §21.3.4.4: pack the bytes of one memory word big-endian -- the first byte
// read occupies the most significant byte position of the element. When the
// file runs out before a full word is read, the bytes that were read still sit
// in the most significant positions, so the partial value is shifted up to
// align. The loaded data are 2-value (each set bit becomes 1, each clear bit 0;
// x and z can never be read), which MakeLogic4VecVal yields directly.
static Logic4Vec PackWordBigEndian(Arena& arena, const uint8_t* buf,
                                   size_t nread, uint32_t bytes_per_word,
                                   uint32_t width) {
  uint64_t val = 0;
  for (size_t i = 0; i < nread && i < 8; ++i) val = (val << 8) | buf[i];
  if (nread < bytes_per_word) val <<= 8 * (bytes_per_word - nread);
  return MakeLogic4VecVal(arena, width, val);
}

static Logic4Vec EvalFread(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.size() < 2) return MakeLogic4VecVal(arena, 32, 0);
  // §21.3.4.4: the file descriptor is the second argument in every form.
  uint32_t fd = FdFromArg(expr->args[1], ctx, arena);
  FILE* fp = ReadableHandle(fd, ctx);
  if (!fp) return MakeLogic4VecVal(arena, 32, 0);

  const Expr* dst = expr->args[0];
  // §21.3.4.4: a destination that names an unpacked array selects the memory
  // form; anything else is the integral-variable form, which the standard
  // defines as the one applied for all packed data.
  const ArrayInfo* ai = (dst->kind == ExprKind::kIdentifier)
                            ? ctx.FindArrayInfo(dst->text)
                            : nullptr;

  if (!ai) {
    // §21.3.4.4: an unpacked struct is read as though a separate $fread were
    // performed on each member in declaration order; an unpacked union reads
    // only its first member. Each member therefore takes its own whole number
    // of bytes. A packed aggregate is not handled here -- it falls through to
    // the integral-variable form, which loads the whole value at once.
    const StructTypeInfo* sinfo = (dst->kind == ExprKind::kIdentifier)
                                      ? ctx.GetVariableStructType(dst->text)
                                      : nullptr;
    if (sinfo && !sinfo->is_packed && !sinfo->fields.empty()) {
      Variable* var = ctx.FindVariable(dst->text);
      if (!var) return MakeLogic4VecVal(arena, 32, 0);

      size_t count = sinfo->is_union ? 1 : sinfo->fields.size();
      uint64_t whole = var->value.ToUint64();
      uint64_t total_bytes = 0;
      for (size_t i = 0; i < count; ++i) {
        const StructFieldInfo& fld = sinfo->fields[i];
        uint32_t fbytes = (fld.width + 7) / 8;
        if (fbytes == 0) fbytes = 1;
        auto* fbuf = new uint8_t[fbytes];
        size_t fread_n = std::fread(fbuf, 1, fbytes, fp);
        Logic4Vec fv =
            PackWordBigEndian(arena, fbuf, fread_n, fbytes, fld.width);
        delete[] fbuf;

        uint64_t fmask = (fld.width >= 64) ? ~uint64_t{0}
                                           : (uint64_t{1} << fld.width) - 1;
        whole &= ~(fmask << fld.bit_offset);
        whole |= (fv.ToUint64() & fmask) << fld.bit_offset;
        total_bytes += fread_n;
        if (fread_n < fbytes) break;  // file ran out mid-member
      }
      var->value = MakeLogic4VecVal(arena, var->value.width, whole);
      return MakeLogic4VecVal(arena, 32, total_bytes);
    }

    // Integral-variable variant: $fread(integral_var, fd). Any start/count
    // arguments are ignored when loading a single packed value.
    Variable* var = (dst->kind == ExprKind::kIdentifier)
                        ? ctx.FindVariable(dst->text)
                        : nullptr;
    if (!var) return MakeLogic4VecVal(arena, 32, 0);

    uint32_t nbytes = (var->value.width + 7) / 8;
    if (nbytes == 0) nbytes = 1;
    auto* buf = new uint8_t[nbytes];
    size_t nread = std::fread(buf, 1, nbytes, fp);
    var->value = PackWordBigEndian(arena, buf, nread, nbytes, var->value.width);
    delete[] buf;
    return MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(nread));
  }

  // Memory variant: $fread(mem, fd [, start [, count]]), including the
  // $fread(mem, fd, , count) form whose start argument is omitted (a null arg).
  std::string mem_name(dst->text);
  int64_t low_addr = ai->lo;
  int64_t high_addr = ai->lo + static_cast<int64_t>(ai->size) - 1;
  // §21.3.4.4: the data are read byte by byte; the number of bytes that fill a
  // word is the word width rounded up to a whole number of bytes (an 8-bit word
  // uses one byte, a 9-bit word two).
  uint32_t elem_width = ai->elem_width;
  uint32_t bytes_per_word = (elem_width + 7) / 8;
  if (bytes_per_word == 0) bytes_per_word = 1;

  // §21.3.4.4: start, when present, is the address of the first element loaded;
  // otherwise the lowest-numbered location is used. The omitted-start form
  // (`, ,`) reaches here as a null third argument and likewise defaults.
  bool has_start = expr->args.size() >= 3 && expr->args[2] != nullptr;
  int64_t start_addr =
      has_start
          ? static_cast<int64_t>(EvalExpr(expr->args[2], ctx, arena).ToUint64())
          : low_addr;

  // §21.3.4.4: count, when present, caps how many locations are loaded;
  // otherwise the memory is filled with whatever data are available.
  bool has_count = expr->args.size() >= 4 && expr->args[3] != nullptr;
  uint64_t max_words =
      has_count ? EvalExpr(expr->args[3], ctx, arena).ToUint64() : 0;

  // §21.3.4.4: consecutive words are loaded toward the highest address
  // (increasing index), regardless of the array's declared direction, until the
  // memory is full, the count is reached, or the file is exhausted.
  uint64_t total_bytes = 0;
  uint64_t words_done = 0;
  auto* buf = new uint8_t[bytes_per_word];
  for (int64_t addr = start_addr;
       addr <= high_addr && (!has_count || words_done < max_words); ++addr) {
    if (addr < low_addr) continue;
    size_t nread = std::fread(buf, 1, bytes_per_word, fp);
    if (nread == 0) break;
    std::string elem = mem_name + "[" + std::to_string(addr) + "]";
    if (auto* v = ctx.FindVariable(elem)) {
      v->value =
          PackWordBigEndian(arena, buf, nread, bytes_per_word, v->value.width);
    }
    total_bytes += nread;
    ++words_done;
    if (nread < bytes_per_word) break;  // file ran out mid-word
  }
  delete[] buf;
  return MakeLogic4VecVal(arena, 32, total_bytes);
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
