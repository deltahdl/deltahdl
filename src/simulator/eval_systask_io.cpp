#include <fcntl.h>
#include <stdio.h>

#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/eval_function_internal.h"
#include "simulator/eval_string.h"
#include "simulator/eval_systask_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/variable.h"

namespace delta {

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
      const size_t kTaken = CountFormatConversions(fmt);
      while (i + 1 < args.size() && args[i + 1] != nullptr &&
             vals.size() < kTaken) {
        vals.push_back(EvalExpr(args[++i], ctx, arena));
      }
      out += FormatDisplay(fmt, vals, {.ctx = &ctx, .loc = a->range.start});
      continue;
    }
    auto val = EvalExpr(a, ctx, arena);
    char spec = val.is_string ? 's' : default_radix;
    char fmt_buf[3] = {'%', spec, 0};
    out += FormatDisplay(fmt_buf, {val}, {.ctx = &ctx, .loc = a->range.start});
  }
  return out;
}

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
    elem->NotifyWatchers();
  }
  return true;
}

static void AssignStringResult(const Expr* dest, const std::string& output,
                               SimContext& ctx, Arena& arena) {
  Logic4Vec packed = StringToLogic4Vec(arena, output);
  if (NamesStringProperty(dest, ctx)) {
    packed = StripStringZeros(packed, arena);
    packed.is_string = true;
  } else {
    packed = ResizeToWidth(packed, EvalExpr(dest, ctx, arena).width, arena);
  }
  PerformBlockingAssign(dest, packed, ctx, arena);
}

static void StoreStringResult(const Expr* dest, const std::string& output,
                              SimContext& ctx, Arena& arena) {
  Variable* dst = nullptr;
  std::string_view name;
  if (dest != nullptr && dest->kind == ExprKind::kIdentifier) {
    name = dest->text;
    dst = ctx.FindVariable(name);
  }
  if (TryStoreIntoByteArray(name, output, ctx, arena)) return;
  if (dst == nullptr) {
    if (dest != nullptr) AssignStringResult(dest, output, ctx, arena);
    return;
  }
  Logic4Vec packed = StringToLogic4Vec(arena, output);
  if (ctx.IsStringVariable(name)) {
    dst->value = StripStringZeros(packed, arena);
  } else {
    dst->value = ResizeToWidth(packed, dst->value.width, arena);
  }
  dst->NotifyWatchers();
}

static Logic4Vec EvalSwriteFamily(const Expr* expr, SimContext& ctx,
                                  Arena& arena, std::string_view name) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 1, 0);

  char default_radix = 'd';
  if (name.size() >= 1) {
    char back = name.back();
    if (back == 'b' || back == 'h' || back == 'o') default_radix = back;
  }

  std::vector<Expr*> rest(expr->args.begin() + 1, expr->args.end());
  std::string output = BuildStringTaskOutput(rest, default_radix, ctx, arena);
  StoreStringResult(expr->args[0], output, ctx, arena);
  return MakeLogic4VecVal(arena, 1, 0);
}

static Logic4Vec EvalSformatTask(const Expr* expr, SimContext& ctx,
                                 Arena& arena) {
  if (expr->args.size() < 2) return MakeLogic4VecVal(arena, 1, 0);
  std::string fmt = ResolveFormatArg(expr->args[1], ctx, arena);
  WarnIfArgCountMismatch(ctx, "$sformat", fmt, expr->args.size() - 2,
                         expr->range.start);
  std::string out = FormatDisplayArgs(expr, 1, fmt, ctx, arena);
  StoreStringResult(expr->args[0], out, ctx, arena);
  return MakeLogic4VecVal(arena, 1, 0);
}

static Logic4Vec EvalFopen(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 32, 0);
  std::string filename = EvalStringArg(expr->args[0], ctx, arena);
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

static std::vector<FILE*> ResolveOutputTargets(uint32_t descriptor,
                                               SimContext& ctx) {
  if ((descriptor & SimContext::kFdMsb) != 0) {
    FILE* fp = ctx.GetFileHandle(descriptor);
    if (fp == nullptr) return {};
    return {fp};
  }
  return ctx.GetMcdFiles(descriptor);
}

static std::string RenderFileOutputText(const Expr* expr, SimContext& ctx,
                                        Arena& arena, char suffix) {
  return RenderDisplayArgList(expr, 1, suffix == '\0' ? 'd' : suffix, ctx,
                              arena);
}

static void WriteFileOutputText(FILE* fp, const std::string& output,
                                bool is_display_family, SimContext& ctx) {
  std::fwrite(output.data(), 1, output.size(), fp);
  if (is_display_family) std::fputc('\n', fp);
  if (fp == stdout) {
    ctx.Log().Copy(output);
    if (is_display_family) ctx.Log().Copy("\n");
  }
  int fd_flags = fcntl(fileno(fp), F_GETFL);
  bool is_append = fd_flags != -1 && (fd_flags & O_APPEND) != 0;
  if (fp == stdout || fp == stderr || is_append) std::fflush(fp);
}

void WriteFileOutputTask(const Expr* expr, uint32_t descriptor,
                         std::string_view name, SimContext& ctx, Arena& arena) {
  auto targets = ResolveOutputTargets(descriptor, ctx);
  if (targets.empty()) return;

  char suffix = FileOutputSuffix(name);
  bool is_display_family = name.rfind("$fdisplay", 0) == 0 ||
                           name.rfind("$fstrobe", 0) == 0 ||
                           name.rfind("$fmonitor", 0) == 0;

  std::string output = RenderFileOutputText(expr, ctx, arena, suffix);
  for (FILE* fp : targets) {
    WriteFileOutputText(fp, output, is_display_family, ctx);
  }
}

static Logic4Vec EvalFdisplayWrite(const Expr* expr, SimContext& ctx,
                                   Arena& arena, std::string_view name) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 1, 0);
  auto descriptor =
      static_cast<uint32_t>(EvalExpr(expr->args[0], ctx, arena).ToUint64());
  if (name.rfind("$fmonitor", 0) == 0) {
    return EvalFmonitor(expr, descriptor, name, ctx, arena);
  }
  if (name.rfind("$fstrobe", 0) == 0) {
    return EvalFstrobe(expr, descriptor, name, ctx, arena);
  }
  WriteFileOutputTask(expr, descriptor, name, ctx, arena);
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
  if (name == "$sreadmemh") return EvalSreadmem(expr, ctx, arena, true);
  if (name == "$sreadmemb") return EvalSreadmem(expr, ctx, arena, false);
  if (name == "$writememh") return EvalWritemem(expr, ctx, arena, true);
  if (name == "$writememb") return EvalWritemem(expr, ctx, arena, false);
  if (name == "$sscanf") return EvalSscanf(expr, ctx, arena);
  if (name == "$swrite" || name == "$swriteb" || name == "$swriteh" ||
      name == "$swriteo") {
    return EvalSwriteFamily(expr, ctx, arena, name);
  }
  if (name == "$sformat") return EvalSformatTask(expr, ctx, arena);
  return MakeLogic4VecVal(arena, 1, 0);
}

}  // namespace delta
