#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <memory>
#include <optional>
#include <ostream>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/packed_range.h"
#include "common/source_loc.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "simulator/deferred_caller.h"
#include "simulator/eval_expr_internal.h"
#include "simulator/eval_function_internal.h"
#include "simulator/eval_systask_internal.h"
#include "simulator/evaluation.h"
#include "simulator/net.h"
#include "simulator/probabilistic_distribution.h"
#include "simulator/process.h"
#include "simulator/scope_hier_name.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/variable.h"
#include "simulator/vcd_writer.h"

namespace delta {

bool IsPrngSysCall(std::string_view name) {
  return name == "$random" || name == "$urandom" || name == "$urandom_range";
}

Logic4Vec EvalPrngCall(const Expr* expr, SimContext& ctx, Arena& arena,
                       std::string_view name) {
  if (name == "$random") {
    int32_t* seed = ctx.RandomSeed();
    if (!expr->args.empty()) {
      *seed =
          static_cast<int32_t>(EvalExpr(expr->args[0], ctx, arena).ToUint64());
    }
    int32_t result = RtlDistRandom(seed);
    if (!expr->args.empty()) {
      WriteBackDistributionSeed(expr->args[0], *seed, ctx, arena);
    }
    return MakeLogic4VecVal(
        arena, 32, static_cast<uint64_t>(static_cast<uint32_t>(result)));
  }
  if (name == "$urandom") {
    if (!expr->args.empty()) {
      ctx.SeedUrandom(static_cast<uint32_t>(
          EvalExpr(expr->args[0], ctx, arena).ToUint64()));
    }
    return MakeLogic4VecVal(arena, 32, ctx.Urandom32());
  }
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

static bool IsScalarNet(const Variable& var) {
  return !var.has_packed_range && var.value.width == 1;
}

enum class PercentVArgKind : uint8_t {
  kNoStrength,
  kNetBit,
  kVectorNet,
  kNetMultibitSelect,
};

struct PercentVArg {
  PercentVArgKind kind = PercentVArgKind::kNoStrength;
  const Net* net = nullptr;
  uint32_t bit = 0;
};

static bool IsRepeatableIndex(const Expr* e) {
  if (e == nullptr) return true;
  switch (e->kind) {
    case ExprKind::kIntegerLiteral:
    case ExprKind::kIdentifier:
      return true;
    case ExprKind::kUnary:
      if (e->op == TokenKind::kPlusPlus || e->op == TokenKind::kMinusMinus)
        return false;
      return IsRepeatableIndex(e->lhs);
    case ExprKind::kBinary:
      return IsRepeatableIndex(e->lhs) && IsRepeatableIndex(e->rhs);
    case ExprKind::kTernary:
      return IsRepeatableIndex(e->condition) &&
             IsRepeatableIndex(e->true_expr) &&
             IsRepeatableIndex(e->false_expr);
    case ExprKind::kSelect:
      return IsRepeatableIndex(e->base) && IsRepeatableIndex(e->index) &&
             IsRepeatableIndex(e->index_end);
    default:
      return false;
  }
}

static PercentVArg ClassifyNetBitSelect(const Expr* arg, const Net* net,
                                        SimContext& ctx, Arena& arena) {
  if (net->resolved->packed_elem_width > 1)
    return {PercentVArgKind::kNetMultibitSelect};
  if (!IsRepeatableIndex(arg->index)) return {};
  auto idx = EvalExpr(arg->index, ctx, arena);
  if (!idx.IsKnown()) return {};
  PackedRange range = net->resolved->BitSelectRange();
  auto declared = static_cast<int64_t>(idx.ToUint64());
  if (!range.Contains(declared)) return {};
  return {PercentVArgKind::kNetBit, net,
          static_cast<uint32_t>(range.OffsetOf(declared))};
}

static bool IsNetName(const Expr* e) {
  return e->kind == ExprKind::kIdentifier || e->kind == ExprKind::kMemberAccess;
}

static const Net* FindNamedNet(const Expr* e, SimContext& ctx) {
  if (e->kind == ExprKind::kIdentifier) return ctx.FindNet(e->text);
  return FindHierarchicalNet(e, ctx);
}

static PercentVArg ClassifyPercentVArg(const Expr* arg, SimContext& ctx,
                                       Arena& arena) {
  if (IsNetName(arg)) {
    const Net* net = FindNamedNet(arg, ctx);
    if (net == nullptr || net->resolved == nullptr) return {};
    if (!IsScalarNet(*net->resolved)) return {PercentVArgKind::kVectorNet};
    return {PercentVArgKind::kNetBit, net, 0};
  }
  if (arg->kind != ExprKind::kSelect || arg->base == nullptr ||
      !IsNetName(arg->base))
    return {};
  const Net* net = FindNamedNet(arg->base, ctx);
  if (net == nullptr || net->resolved == nullptr) return {};
  if (arg->index_end != nullptr) return {PercentVArgKind::kNetMultibitSelect};
  return ClassifyNetBitSelect(arg, net, ctx, arena);
}

static std::string BuildFormatV(const PercentVArg& v) {
  if (v.kind != PercentVArgKind::kNetBit) return "";
  return FormatStrength(v.net->BitStrength(v.bit));
}

static char NonScalarNetArgFlag(const PercentVArg& v) {
  if (v.kind == PercentVArgKind::kVectorNet) return 1;
  if (v.kind == PercentVArgKind::kNetMultibitSelect) return 2;
  return 0;
}

bool IsDisplayOrWriteTask(std::string_view name) {
  return name == "$display" || name == "$displayb" || name == "$displayo" ||
         name == "$displayh" || name == "$write" || name == "$writeb" ||
         name == "$writeo" || name == "$writeh";
}

static char DefaultRadixForDisplayWriteTask(std::string_view callee) {
  if (callee.empty()) return 'd';
  switch (callee.back()) {
    case 'b':
      return 'b';
    case 'o':
      return 'o';
    case 'h':
      return 'h';
    default:
      return 'd';
  }
}

static std::string ByteArrayText(std::string_view name, SimContext& ctx) {
  std::string out;
  auto add = [&out](const Logic4Vec& v) {
    char c = static_cast<char>(v.ToUint64() & 0xFF);
    if (c != 0) out += c;
  };
  if (const QueueObject* q = ctx.FindQueue(name)) {
    for (const Logic4Vec& v : q->elements) add(v);
    return out;
  }
  const ArrayInfo& ai = *ctx.FindArrayInfo(name);
  for (uint32_t i = 0; i < ai.size; ++i) {
    uint32_t idx = ai.is_descending ? ai.lo + ai.size - 1 - i : ai.lo + i;
    std::string elem_name = std::string(name) + "[" + std::to_string(idx) + "]";
    if (Variable* elem = ctx.FindVariable(elem_name)) add(elem->value);
  }
  return out;
}

UnpackedAggregateKind ClassifyUnpackedAggregate(const Expr* arg,
                                                SimContext& ctx) {
  if (arg == nullptr || arg->kind != ExprKind::kIdentifier)
    return UnpackedAggregateKind::kNone;
  auto of_elements = [](DataTypeKind kind) {
    return kind == DataTypeKind::kByte ? UnpackedAggregateKind::kByteArray
                                       : UnpackedAggregateKind::kArray;
  };
  if (const QueueObject* q = ctx.FindQueue(arg->text))
    return of_elements(q->elem_type_kind);
  if (ctx.FindAssocArray(arg->text) != nullptr)
    return UnpackedAggregateKind::kArray;
  if (const ArrayInfo* ai = ctx.FindArrayInfo(arg->text))
    return of_elements(ai->elem_type_kind);
  const StructTypeInfo* st = StructLayoutOfName(arg->text, ctx);
  return st != nullptr && !st->is_packed ? UnpackedAggregateKind::kStruct
                                         : UnpackedAggregateKind::kNone;
}

static char UnpackedAggregateMark(UnpackedAggregateKind kind) {
  switch (kind) {
    case UnpackedAggregateKind::kArray:
      return 1;
    case UnpackedAggregateKind::kByteArray:
      return 2;
    case UnpackedAggregateKind::kStruct:
      return 3;
    default:
      return 0;
  }
}

static Logic4Vec UnformattedLayout(const Logic4Vec& val,
                                   const StructTypeInfo& st, Arena& arena) {
  size_t count =
      st.is_union ? std::min<size_t>(1, st.fields.size()) : st.fields.size();
  auto units_of = [](uint32_t width) { return (width + 31) / 32 * 32; };
  uint32_t total = 0;
  for (size_t m = 0; m < count; ++m) total += units_of(st.fields[m].width);
  Logic4Vec out = MakeLogic4Vec(arena, std::max<uint32_t>(total, 1));
  uint32_t base = 0;
  for (size_t m = 0; m < count; ++m) {
    const StructFieldInfo& field = st.fields[m];
    for (uint32_t k = 0; k < field.width; ++k) {
      uint32_t from = field.bit_offset + k;
      uint32_t to = base + k;
      if (from / 64 >= val.nwords) break;
      uint64_t bit = uint64_t{1} << (to % 64);
      if ((val.words[from / 64].aval >> (from % 64)) & 1)
        out.words[to / 64].aval |= bit;
      if ((val.words[from / 64].bval >> (from % 64)) & 1)
        out.words[to / 64].bval |= bit;
    }
    base += units_of(field.width);
  }
  return out;
}

struct DisplayArgRenderings {
  std::vector<Logic4Vec> vals;
  std::vector<std::string> p_fmts;
  std::vector<std::string> v_fmts;
  std::vector<char> nonscalar_nets;
  std::vector<char> agg_flags;
  std::vector<std::string> byte_strings;
};

static DisplayArgRenderings CollectDisplayArgs(const Expr* expr, size_t& i,
                                               const std::string& fmt,
                                               SimContext& ctx, Arena& arena) {
  DisplayArgRenderings r;
  const size_t kN = expr->args.size();
  const size_t kTaken = CountFormatConversions(fmt);
  while (i + 1 < kN && expr->args[i + 1] != nullptr && r.vals.size() < kTaken) {
    const Expr* val_arg = expr->args[++i];
    auto v = EvalExpr(val_arg, ctx, arena);
    r.vals.push_back(v);
    r.p_fmts.push_back(BuildFormatP(val_arg, v, ctx));
    PercentVArg pv = ClassifyPercentVArg(val_arg, ctx, arena);
    r.v_fmts.push_back(BuildFormatV(pv));
    r.nonscalar_nets.push_back(NonScalarNetArgFlag(pv));
    UnpackedAggregateKind agg = ClassifyUnpackedAggregate(val_arg, ctx);
    r.agg_flags.push_back(UnpackedAggregateMark(agg));
    if (agg == UnpackedAggregateKind::kStruct) {
      r.vals.back() =
          UnformattedLayout(v, *StructLayoutOfName(val_arg->text, ctx), arena);
    }
    r.byte_strings.push_back(agg == UnpackedAggregateKind::kByteArray
                                 ? ByteArrayText(val_arg->text, ctx)
                                 : std::string());
  }
  return r;
}

static bool AppendUnpackedArrayArg(const Expr* arg, SimContext& ctx,
                                   std::string& output) {
  UnpackedAggregateKind agg = ClassifyUnpackedAggregate(arg, ctx);
  if (agg == UnpackedAggregateKind::kNone) return false;
  if (agg == UnpackedAggregateKind::kByteArray) {
    output += ByteArrayText(arg->text, ctx);
  } else {
    ctx.GetDiag().Error(
        arg->range.start,
        "unformatted unpacked argument to a display or write task is illegal "
        "unless it is an unpacked array of byte",
        Subclause("21.2.1.1"));
  }
  return true;
}

struct DisplayText {
  std::string& text;
  char default_radix;
};

static void AppendDisplayArg(const Expr* expr, size_t& i, SimContext& ctx,
                             Arena& arena, DisplayText out) {
  const Expr* arg = expr->args[i];
  if (arg == nullptr) {
    out.text += ' ';
    return;
  }
  if (arg->kind == ExprKind::kStringLiteral) {
    std::string fmt = ExtractFormatString(arg);
    DisplayArgRenderings r = CollectDisplayArgs(expr, i, fmt, ctx, arena);
    if (r.vals.size() < CountFormatConversions(fmt)) {
      ctx.GetDiag().Warning(arg->range.start,
                            std::string(expr->callee) +
                                ": a string literal has more format "
                                "specifications than arguments after it",
                            Subclause("21.2.1"));
    }
    out.text += FormatDisplay(fmt, r.vals,
                              {.p_fmts = &r.p_fmts,
                               .v_fmts = &r.v_fmts,
                               .arg_nonscalar_net = &r.nonscalar_nets,
                               .ctx = &ctx,
                               .arg_unpacked_agg = &r.agg_flags,
                               .arg_byte_strings = &r.byte_strings,
                               .loc = arg->range.start});
    return;
  }
  if (AppendUnpackedArrayArg(arg, ctx, out.text)) return;
  auto val = EvalExpr(arg, ctx, arena);
  char spec = val.is_string ? 's' : out.default_radix;
  out.text += FormatArgAutoSized(val, spec);
}

std::string RenderDisplayArgList(const Expr* expr, size_t first,
                                 char default_radix, SimContext& ctx,
                                 Arena& arena) {
  std::string output;
  DisplayText out{output, default_radix};
  for (size_t i = first; i < expr->args.size(); ++i)
    AppendDisplayArg(expr, i, ctx, arena, out);
  return output;
}

std::string FormatDisplayArgs(const Expr* expr, size_t fmt_index,
                              const std::string& fmt, SimContext& ctx,
                              Arena& arena) {
  size_t i = fmt_index;
  DisplayArgRenderings r = CollectDisplayArgs(expr, i, fmt, ctx, arena);
  return FormatDisplay(fmt, r.vals,
                       {.p_fmts = &r.p_fmts,
                        .v_fmts = &r.v_fmts,
                        .arg_nonscalar_net = &r.nonscalar_nets,
                        .ctx = &ctx,
                        .arg_unpacked_agg = &r.agg_flags,
                        .arg_byte_strings = &r.byte_strings,
                        .loc = expr->range.start});
}

void ExecDisplayWrite(const Expr* expr, SimContext& ctx, Arena& arena) {
  ctx.Out() << RenderDisplayArgList(
      expr, 0, DefaultRadixForDisplayWriteTask(expr->callee), ctx, arena);
  if (expr->callee.starts_with("$display")) ctx.Out() << "\n";
}

void EmitSeverityHeader(SimContext& ctx, std::string_view prefix,
                        std::string_view msg, std::ostream& os, SourceLoc loc) {
  std::string scope = ScopeHierName(ctx);
  const SourceManager& sources = ctx.GetDiag().Sources();
  SourceLoc origin = sources.ResolveToOrigin(loc);
  uint32_t line = origin.line;
  os << "[" << ctx.CurrentTime().ticks << "] " << prefix;
  if (!scope.empty()) os << " " << scope;
  if (line != 0) {
    os << " (" << sources.FilePath(origin.file_id) << ":" << line << ")";
  }
  if (!msg.empty()) os << ": " << msg;
  os << "\n";
  ctx.SetLastSeverity(prefix, msg, ctx.CurrentTime(), scope, line);
  if (prefix == "ERROR" || prefix == "FATAL") ctx.NoteRuntimeError();
}

void ExecSeverityTask(const Expr* expr, SimContext& ctx, Arena& arena,
                      const char* prefix, std::ostream& os) {
  size_t start_idx = 0;
  if (std::string_view(prefix) == "FATAL" && !expr->args.empty()) {
    if (expr->args[0]->kind != ExprKind::kStringLiteral) {
      EvalExpr(expr->args[0], ctx, arena);
      start_idx = 1;
    }
  }
  std::string msg;
  DisplayText out{msg, 'd'};
  for (size_t i = start_idx; i < expr->args.size(); ++i) {
    AppendDisplayArg(expr, i, ctx, arena, out);
  }
  EmitSeverityHeader(ctx, prefix, msg, os, expr->range.start);
}

Logic4Vec EvalDeferredPrint(const Expr* expr, SimContext& ctx, Arena& arena) {
  auto* event = ctx.GetScheduler().GetEventPool().Acquire();
  std::shared_ptr<Process> caller = SnapshotCallingProcess(ctx);
  std::string scope = caller ? caller->inst_prefix : std::string();
  event->callback = [expr, caller, scope, &ctx, &arena]() {
    CallerStandIn stand_in(caller.get(), ctx);
    ctx.SetDeferredBindingScope(scope);
    ExecDisplayWrite(expr, ctx, arena);
    ctx.SetDeferredBindingScope(std::nullopt);
    ctx.Out() << "\n";
  };
  ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime(), Region::kPostponed,
                                   event);
  return MakeLogic4VecVal(arena, 1, 0);
}

bool IsStrobeTask(std::string_view name) {
  return name == "$strobe" || name == "$strobeb" || name == "$strobeo" ||
         name == "$strobeh";
}

}  // namespace delta
