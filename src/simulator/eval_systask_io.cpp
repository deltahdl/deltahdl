#include <fcntl.h>

#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "parser/ast.h"
#include "simulator/eval_string.h"
#include "simulator/eval_systask_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/variable.h"

namespace delta {

// §21.3.3: shared output-string builder used by $swrite{,b,h,o} and $sformat.
// `args` are the unevaluated argument expressions following the output
// variable; `default_radix` is the format-specifier letter applied to any
// bare expression argument when no embedded format string drives it.
static std::string BuildStringTaskOutput(const std::vector<Expr*>& args,
                                         char default_radix, SimContext& ctx,
                                         Arena& arena) {
  std::string out;
  for (size_t i = 0; i < args.size(); ++i) {
    const Expr* a = args[i];
    if (a == nullptr) {
      out += ' ';
      continue;
    }
    if (a->kind == ExprKind::kStringLiteral) {
      std::string fmt = ExtractFormatString(a);
      std::vector<Logic4Vec> vals;
      while (i + 1 < args.size() && args[i + 1] != nullptr &&
             args[i + 1]->kind != ExprKind::kStringLiteral) {
        vals.push_back(EvalExpr(args[++i], ctx, arena));
      }
      out += FormatDisplay(fmt, vals, {.ctx = &ctx});
      continue;
    }
    auto val = EvalExpr(a, ctx, arena);
    char spec = val.is_string ? 's' : default_radix;
    char fmt_buf[3] = {'%', spec, 0};
    out += FormatDisplay(fmt_buf, {val}, {.ctx = &ctx});
  }
  return out;
}

// §21.3.3 N7 (and §5.9): store the formatted output into the destination
// variable using the string-literal assignment-to-variable rules. A
// `string`-typed destination is variable-width and holds exactly the packed
// characters (leading NULs dropped, as any string assignment does). A
// fixed-width integral destination is coerced to its declared width: the
// leftmost character lands in the highest byte (left-bound to right-bound
// ordering), so a wider destination is zero-padded on the left (right-
// justified) and a narrower one is truncated from the left, discarding the
// earliest characters. Previously the write ignored the destination width and
// silently redefined it to the string length, violating §5.9 for fixed-width
// targets.
// §21.3.3: the destination may be an unpacked array of byte, which is lowered
// to one variable per element. Distributes the formatted characters across
// those elements from the array's left bound to its right bound -- the leftmost
// character lands in the left-bound element. §5.9 assigns a string literal to
// an unpacked byte array left justified, so elements past the end of the string
// are cleared, and characters past the end of the array are dropped. Returns
// false when `name` does not denote such an array.
static bool TryStoreIntoByteArray(std::string_view name,
                                  const std::string& output, SimContext& ctx,
                                  Arena& arena) {
  const ArrayInfo* ai = ctx.FindArrayInfo(name);
  if (ai == nullptr || ai->is_dynamic || ai->is_queue ||
      ai->elem_type_kind != DataTypeKind::kByte) {
    return false;
  }
  for (uint32_t i = 0; i < ai->size; ++i) {
    uint32_t idx =
        ai->is_descending ? (ai->lo + ai->size - 1 - i) : (ai->lo + i);
    std::string ename = std::string(name) + "[" + std::to_string(idx) + "]";
    Variable* elem = ctx.FindVariable(ename);
    if (elem == nullptr) continue;
    uint8_t byte = i < output.size() ? static_cast<uint8_t>(output[i]) : 0;
    elem->value = MakeLogic4VecVal(arena, ai->elem_width, byte);
  }
  return true;
}

static void StoreStringResult(Variable* dst, std::string_view name,
                              const std::string& output, SimContext& ctx,
                              Arena& arena) {
  // An unpacked byte array is recognised before the plain-variable case.
  // Lowering gives such an array a variable under its own name as well as one
  // per element, so testing the destination variable first would send every
  // character into that base variable, which no read of the array consults.
  if (TryStoreIntoByteArray(name, output, ctx, arena)) return;
  if (dst == nullptr) return;
  Logic4Vec packed = StringToLogic4Vec(arena, output);
  if (ctx.IsStringVariable(name)) {
    dst->value = StripStringZeros(packed, arena);
  } else {
    dst->value = ResizeToWidth(packed, dst->value.width, arena);
  }
}

// §21.3.3 N6: $swrite/$swriteb/$swriteh/$swriteo take an output variable as
// the first argument and write the formatted result into it under string-
// literal assignment-to-variable rules. The b/h/o suffix selects the default
// radix for bare expression arguments per §21.3.2.
static Logic4Vec EvalSwriteFamily(const Expr* expr, SimContext& ctx,
                                  Arena& arena, std::string_view name) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 1, 0);
  Variable* dst = nullptr;
  std::string_view dst_name;
  if (expr->args[0] && expr->args[0]->kind == ExprKind::kIdentifier) {
    dst_name = expr->args[0]->text;
    dst = ctx.FindVariable(dst_name);
  }

  // The suffix character ('\0' / b / h / o) becomes the default radix letter
  // for bare expression arguments. Without a suffix, decimal is the default.
  char default_radix = 'd';
  if (name.size() >= 1) {
    char back = name.back();
    if (back == 'b' || back == 'h' || back == 'o') default_radix = back;
  }

  std::vector<Expr*> rest(expr->args.begin() + 1, expr->args.end());
  std::string output = BuildStringTaskOutput(rest, default_radix, ctx, arena);
  StoreStringResult(dst, dst_name, output, ctx, arena);
  return MakeLogic4VecVal(arena, 1, 0);
}

// §21.3.3 N9: $sformat always interprets its second argument, and only its
// second argument, as the format string; following arguments fill its
// specifiers in order and are never re-interpreted as format strings.
static Logic4Vec EvalSformatTask(const Expr* expr, SimContext& ctx,
                                 Arena& arena) {
  if (expr->args.size() < 2) return MakeLogic4VecVal(arena, 1, 0);
  Variable* dst = nullptr;
  std::string_view dst_name;
  if (expr->args[0] && expr->args[0]->kind == ExprKind::kIdentifier) {
    dst_name = expr->args[0]->text;
    dst = ctx.FindVariable(dst_name);
  }
  std::string fmt = ResolveFormatArg(expr->args[1], ctx, arena);
  std::vector<Logic4Vec> vals;
  for (size_t i = 2; i < expr->args.size(); ++i) {
    vals.push_back(EvalExpr(expr->args[i], ctx, arena));
  }
  WarnIfArgCountMismatch(ctx, "$sformat", fmt, vals.size());
  std::string out = FormatDisplay(fmt, vals, {.ctx = &ctx});
  StoreStringResult(dst, dst_name, out, ctx, arena);
  return MakeLogic4VecVal(arena, 1, 0);
}

static Logic4Vec EvalFopen(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 32, 0);
  // §21.3.1 admits a filename / type argument that is a string literal, a
  // string-typed variable, or an integral value whose bytes encode the
  // characters; EvalStringArg handles all three forms.
  std::string filename = EvalStringArg(expr->args[0], ctx, arena);
  // §21.3.1: omitting the type argument requests a multichannel descriptor;
  // supplying it requests a single 32-bit file descriptor.
  if (expr->args.size() < 2) {
    uint32_t mcd = ctx.OpenMcd(filename);
    return MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(mcd));
  }
  std::string mode = EvalStringArg(expr->args[1], ctx, arena);
  uint32_t fd = ctx.OpenFile(filename, mode);
  return MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(fd));
}

static Logic4Vec EvalFclose(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 1, 0);
  auto descriptor =
      static_cast<uint32_t>(EvalExpr(expr->args[0], ctx, arena).ToUint64());
  ctx.CloseFile(descriptor);
  return MakeLogic4VecVal(arena, 1, 0);
}

// Determines whether a system-task name names a §21.3.2 file-output task and,
// if so, returns the radix character for any base-specific suffix (b/h/o).
// Returns '\0' for the default ($fdisplay, $fwrite, $fstrobe, $fmonitor),
// 'b'/'h'/'o' for the suffixed variants, and '?' if the name is not in the set.
static char FileOutputSuffix(std::string_view name) {
  auto match = [&](std::string_view base) -> char {
    if (name == base) return '\0';
    if (name.size() == base.size() + 1 && name.substr(0, base.size()) == base) {
      char c = name.back();
      if (c == 'b' || c == 'h' || c == 'o') return c;
    }
    return '?';
  };
  for (auto base : {"$fdisplay", "$fwrite", "$fstrobe", "$fmonitor"}) {
    char s = match(base);
    if (s != '?') return s;
  }
  return '?';
}

static bool IsFileOutputTask(std::string_view name) {
  return FileOutputSuffix(name) != '?';
}

// Routes formatted output to every FILE* selected by a descriptor argument.
// An fd has its MSB set and refers to a single open file (or to STDIN/STDOUT/
// STDERR); an mcd has its MSB clear and may select multiple channels at once
// by setting their channel bits (§21.3.1, §21.3.2).
static std::vector<FILE*> ResolveOutputTargets(uint32_t descriptor,
                                               SimContext& ctx) {
  if ((descriptor & SimContext::kFdMsb) != 0) {
    FILE* fp = ctx.GetFileHandle(descriptor);
    if (fp == nullptr) return {};
    return {fp};
  }
  return ctx.GetMcdFiles(descriptor);
}

// §21.3.2: render the text one file-output task writes. The first argument is
// the descriptor; a string literal directly after it is the format string and
// every other argument is a value. With no format string the b/h/o radix is
// derived from the task-name suffix.
static std::string RenderFileOutputText(const Expr* expr, SimContext& ctx,
                                        Arena& arena, char suffix) {
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
  if (!fmt.empty()) return FormatDisplay(fmt, arg_vals, {.ctx = &ctx});
  if (suffix == '\0') return {};
  char fmt_buf[3] = {'%', suffix, 0};
  return FormatDisplay(fmt_buf, arg_vals, {.ctx = &ctx});
}

// Write the rendered text to one target stream. It is written by size, not as a
// C string: the unformatted %u / %z renderings (§21.2.1.1) legitimately contain
// NUL bytes, which must reach the file intact for a §21.3.4.3 $fscanf round
// trip to recover the value.
//
// §21.3.6: output to a regular file stays in the stream buffer until a $fflush
// publishes it or the descriptor is closed -- flushing here would leave the
// flush task nothing to do. The console streams are pushed through immediately
// so their text interleaves with $display output, and an append-type stream is
// too: §21.3.5 requires every append write to land at the end of the file and
// reposition the pointer there, which the host only performs at the actual
// write, so it must not be deferred.
static void WriteFileOutputText(FILE* fp, const std::string& output,
                                bool is_display_family) {
  std::fwrite(output.data(), 1, output.size(), fp);
  if (is_display_family) std::fputc('\n', fp);
  int fd_flags = fcntl(fileno(fp), F_GETFL);
  bool is_append = fd_flags != -1 && (fd_flags & O_APPEND) != 0;
  if (fp == stdout || fp == stderr || is_append) std::fflush(fp);
}

static Logic4Vec EvalFdisplayWrite(const Expr* expr, SimContext& ctx,
                                   Arena& arena, std::string_view name) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 1, 0);
  auto descriptor =
      static_cast<uint32_t>(EvalExpr(expr->args[0], ctx, arena).ToUint64());
  auto targets = ResolveOutputTargets(descriptor, ctx);
  if (targets.empty()) return MakeLogic4VecVal(arena, 1, 0);

  char suffix = FileOutputSuffix(name);
  bool is_display_family = name.rfind("$fdisplay", 0) == 0 ||
                           name.rfind("$fstrobe", 0) == 0 ||
                           name.rfind("$fmonitor", 0) == 0;

  std::string output = RenderFileOutputText(expr, ctx, arena, suffix);
  for (FILE* fp : targets) WriteFileOutputText(fp, output, is_display_family);
  return MakeLogic4VecVal(arena, 1, 0);
}

Logic4Vec EvalIOSysCall(const Expr* expr, SimContext& ctx, Arena& arena,
                        std::string_view name) {
  if (name == "$fopen") return EvalFopen(expr, ctx, arena);
  if (name == "$fclose") return EvalFclose(expr, ctx, arena);
  if (IsFileOutputTask(name)) {
    return EvalFdisplayWrite(expr, ctx, arena, name);
  }
  if (name == "$readmemh") return EvalReadmem(expr, ctx, arena, true);
  if (name == "$readmemb") return EvalReadmem(expr, ctx, arena, false);
  // §D.14: the string-loading counterparts of $readmemh / $readmemb.
  if (name == "$sreadmemh") return EvalSreadmem(expr, ctx, arena, true);
  if (name == "$sreadmemb") return EvalSreadmem(expr, ctx, arena, false);
  if (name == "$writememh") return EvalWritemem(expr, ctx, arena, true);
  if (name == "$writememb") return EvalWritemem(expr, ctx, arena, false);
  if (name == "$sscanf") return EvalSscanf(expr, ctx, arena);
  // §21.3.3: the $swrite family and $sformat target a variable rather than a
  // file descriptor but otherwise mirror their $fwrite / $fdisplay
  // counterparts.
  if (name == "$swrite" || name == "$swriteb" || name == "$swriteh" ||
      name == "$swriteo") {
    return EvalSwriteFamily(expr, ctx, arena, name);
  }
  if (name == "$sformat") return EvalSformatTask(expr, ctx, arena);
  return MakeLogic4VecVal(arena, 1, 0);
}

}  // namespace delta
