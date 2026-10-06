
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
#include "common/types.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "simulator/deferred_caller.h"
#include "simulator/eval_function_internal.h"
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
    // §20.14 with Table N.1: $random is rtl_dist_uniform(seed, LONG_MIN,
    // LONG_MAX), the §N.2 algorithm drawn over the whole 32-bit range, so its
    // values are the standard's and not a generator of this tool's choosing;
    // it drew from the $urandom stream, which no seed of the annex's selects.
    // §20.14.1: the seed argument selects the stream, so different seeds yield
    // different sequences and a given seed replays identically; the seed the
    // draw advanced goes back to the variable, and the seedless form continues
    // from the stream the last seed selected.
    int32_t* seed = ctx.RandomSeed();
    if (!expr->args.empty()) {
      *seed =
          static_cast<int32_t>(EvalExpr(expr->args[0], ctx, arena).ToUint64());
    }
    // The returned 32-bit number is a signed integer (it may be negative).
    int32_t result = RtlDistRandom(seed);
    if (!expr->args.empty()) {
      WriteBackDistributionSeed(expr->args[0], *seed, ctx, arena);
    }
    return MakeLogic4VecVal(
        arena, 32, static_cast<uint64_t>(static_cast<uint32_t>(result)));
  }
  if (name == "$urandom") {
    // An optional seed (any integral expression) selects the sequence; the
    // same seed must replay identically.
    if (!expr->args.empty()) {
      ctx.SeedUrandom(static_cast<uint32_t>(
          EvalExpr(expr->args[0], ctx, arena).ToUint64()));
    }
    return MakeLogic4VecVal(arena, 32, ctx.Urandom32());
  }
  // $urandom_range is the only name IsPrngSysCall admits that is left, and
  // this function is reached through that predicate alone. It used to end in a
  // one-bit zero for every other name instead, which made it the accidental
  // end of the whole dispatch chain: an unrecognised $name was answered here
  // rather than reported.
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

// §6.9: a data object "declared ... without a range specification shall be
// considered 1-bit wide and is known as a scalar", and one declared with a
// range is a vector. The declaration is what that definition keys on, not the
// width, so `wire [0:0] w` is a vector here: it is one bit wide and yet carries
// the range the sentence turns on. Reading the width as well as the range
// covers the net whose declared bounds this scope could not fold, which
// RecordPackedRange leaves unrecorded while the storage it sized still says the
// net is multibit.
static bool IsScalarNet(const Variable& var) {
  return !var.has_packed_range && var.value.width == 1;
}

// What §21.2.1.4 makes of one argument a display task rendered a %v for.
//
// The clause gives each %v a scalar reference of its own and reports a scalar
// net's strength, so an argument is one of three things: a reference to a
// scalar of a net, whose strength there is to render; a reference to a net that
// is not a scalar, which the clause admits no rendering for and which is
// reported; or neither, which carries no strength model and so has nothing to
// render and nothing to report against. The second of those is two kinds rather
// than one so that a report can name which shape it was.
enum class PercentVArgKind : uint8_t {
  kNoStrength,
  kNetBit,
  kVectorNet,
  kNetMultibitSelect,
};

// One %v argument classified, with the net bit it names where it names one.
// `bit` counts from the least significant end of the net's storage, which is
// where Net::BitStrength indexes from.
struct PercentVArg {
  PercentVArgKind kind = PercentVArgKind::kNoStrength;
  const Net* net = nullptr;
  uint32_t bit = 0;
};

// Whether evaluating `e` again yields what evaluating it once did, and changes
// nothing on the way.
//
// The display task evaluates every argument it takes, a bit-select's index
// along with the rest of it, before the strength renderings are built; reading
// the index here to find which bit was named evaluates that index a second
// time. So the forms below are the ones a bit-select's index may take and still
// be a %v operand: a literal is a literal, reading a name changes nothing, and
// an operator is as repeatable as its operands. Everything else -- a call, a
// system call, an increment -- is refused, and the operand then names no bit of
// a net rather than naming one twice.
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

// §11.5.1: the bit of `net` that a bit-select's index names, resolved against
// the declaration, since which bit an address reaches depends in part on the
// declaration. An index carrying x or z names no bit
// -- §11.5.1 has `vect[expression that returns x]` return x -- and neither does
// one outside the declared bounds, which reads as x for the same reason. Both
// are still the scalar reference §21.2.1.4 asks for, so neither is reported;
// there is simply no bit of a net whose strength could be named.
static PercentVArg ClassifyNetBitSelect(const Expr* arg, const Net* net,
                                        SimContext& ctx, Arena& arena) {
  // §7.4.1: one index of a packed multidimensional array addresses an element
  // rather than a bit, and an element of more than one bit is no more a scalar
  // than a part-select is.
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

// Whether `e` is a name a net can stand under: an identifier, or a dotted
// name reaching one declared elsewhere (§23.6).
static bool IsNetName(const Expr* e) {
  return e->kind == ExprKind::kIdentifier || e->kind == ExprKind::kMemberAccess;
}

// The net such a name stands for, if any.
static const Net* FindNamedNet(const Expr* e, SimContext& ctx) {
  if (e->kind == ExprKind::kIdentifier) return ctx.FindNet(e->text);
  return FindHierarchicalNet(e, ctx);
}

// §21.2.1.4's operand, classified. A net declared without a range is a scalar
// (§6.9) and names its only bit. A bit-select of a vector net is a scalar
// reference too: §11.5.1 has it address one bit of the vector, and one bit of a
// net is the scalar whose strength the clause reports. A select that still
// names more than one bit is not, being no more a single bit than the vector it
// selects from.
//
// §23.6: a net named hierarchically, `s.y` of an instance or `b.y` of an
// interface instance, is the net declared there, with the drivers and the
// strength it has there, so it is looked up by the name the read of it resolves
// by. Asked for by an identifier alone, it named no net and printed nothing.
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

// §21.2.1.4: the three-character group reporting the strength of the scalar the
// argument names. An argument that names no scalar of a net renders nothing,
// whether because it names no net at all or because it names one the clause
// does not admit -- the flag threaded beside this is what reports the latter.
static std::string BuildFormatV(const PercentVArg& v) {
  if (v.kind != PercentVArgKind::kNetBit) return "";
  return FormatStrength(v.net->BitStrength(v.bit));
}

// §21.2.1.4: each %v in a string literal is matched by a scalar reference
// among the arguments that follow the literal. Whether this argument breaks
// that is settled here, where the net is in reach, and reported by the
// formatter, where it is known whether a %v is what consumed the argument:
// the renderings are built for every argument a template takes, so reporting
// here would report a vector net passed to %h. The two shapes that break it
// are told apart so that each is named by what it is: a net reference naming
// the whole net, or a select of it that still names more than one bit. Zero
// is every argument that does not break it.
static char NonScalarNetArgFlag(const PercentVArg& v) {
  if (v.kind == PercentVArgKind::kVectorNet) return 1;
  if (v.kind == PercentVArgKind::kNetMultibitSelect) return 2;
  return 0;
}

// The eight display and write system tasks named in Syntax 21-1. The b/o/h
// suffixed forms differ from the plain ones only in the default radix used for
// unformatted expression arguments; that radix is applied elsewhere.
bool IsDisplayOrWriteTask(std::string_view name) {
  return name == "$display" || name == "$displayb" || name == "$displayo" ||
         name == "$displayh" || name == "$write" || name == "$writeb" ||
         name == "$writeo" || name == "$writeh";
}

// Maps a display- or write-family task name to the specifier letter that
// renders an unformatted expression argument: $displayb/$writeb use binary,
// $displayo/$writeo octal, $displayh/$writeh hexadecimal, and the plain
// $display/$write pair use decimal.
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

// §21.2.1.1: a bare argument (one with no governing format specifier) that is
// an unpacked array of byte is displayed as the character string its element
// bytes spell out, taken in index order. Each element's low byte contributes
// one character; a zero byte carries no character, matching the way a string
// value renders. The per-element variables are named "arr[idx]" by the lowerer,
// the same layout the %p renderer walks.
static std::string FormatUnpackedByteArrayAsString(std::string_view name,
                                                   const ArrayInfo& ai,
                                                   SimContext& ctx) {
  std::string out;
  for (uint32_t i = 0; i < ai.size; ++i) {
    uint32_t idx = ai.lo + i;
    std::string elem_name = std::string(name) + "[" + std::to_string(idx) + "]";
    Variable* elem = ctx.FindVariable(elem_name);
    if (elem == nullptr) continue;
    char c = static_cast<char>(elem->value.ToUint64() & 0xFF);
    if (c != 0) out += c;
  }
  return out;
}

// §21.2.1.7: render an unpacked array of byte as the character string its
// elements spell, ordered from the left bound of the declaration to the right
// bound. An ascending range [0:3] walks index 0 upward; a descending range
// [3:0] has its left bound at the highest index, so the walk runs downward.
// A zero element carries no character, the same way a zero byte in a
// string-typed value carries none.
static std::string FormatByteArrayLeftBoundFirst(std::string_view name,
                                                 const ArrayInfo& ai,
                                                 SimContext& ctx) {
  std::string out;
  for (uint32_t i = 0; i < ai.size; ++i) {
    uint32_t idx = ai.is_descending ? ai.lo + ai.size - 1 - i : ai.lo + i;
    std::string elem_name = std::string(name) + "[" + std::to_string(idx) + "]";
    Variable* elem = ctx.FindVariable(elem_name);
    if (elem == nullptr) continue;
    char c = static_cast<char>(elem->value.ToUint64() & 0xFF);
    if (c != 0) out += c;
  }
  return out;
}

// §21.2.1.1 / §21.2.1.7: classify a display/write argument that names a
// fixed-size unpacked aggregate (an unpacked array). The integer format
// specifiers may not be applied to such an argument; %s admits it only when
// its elements are of type byte. Returns 0 for anything else, 1 for an
// aggregate of non-byte elements, and 2 for an unpacked array of byte.
// Queues, dynamic, and associative arrays are handled by their own machinery
// and are left out here.
static char ClassifyUnpackedAggregateArg(const Expr* arg, SimContext& ctx) {
  if (arg == nullptr || arg->kind != ExprKind::kIdentifier) return 0;
  const ArrayInfo* ai = ctx.FindArrayInfo(arg->text);
  if (ai == nullptr || ai->is_queue || ai->is_dynamic) return 0;
  return ai->elem_type_kind == DataTypeKind::kByte ? 2 : 1;
}

// §21.2: the per-argument renderings a format template consumes alongside the
// values -- the %p and %v forms of each argument, its unpacked-aggregate
// classification, and, for an unpacked array of byte, the character string %s
// prints.
struct DisplayArgRenderings {
  std::vector<Logic4Vec> vals;
  std::vector<std::string> p_fmts;
  std::vector<std::string> v_fmts;
  std::vector<char> nonscalar_nets;
  std::vector<char> agg_flags;
  std::vector<std::string> byte_strings;
};

// Evaluate the arguments a format template's conversions take: §21.2.1.1 has
// each conversion take the expression argument that follows the template, so
// as many arguments as `fmt` has conversions are taken, a string literal among
// them being the §5.9 integer its characters make. The argument after the
// last one taken, whether a string literal starting a template of its own or an
// expression printed under the default radix, is left to the caller; `i` is
// advanced past those taken.
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
    char agg = ClassifyUnpackedAggregateArg(val_arg, ctx);
    r.agg_flags.push_back(agg);
    // §21.2.1.7: an unpacked array of byte governed by %s prints its element
    // characters from the left bound to the right bound. The element variables
    // live here, so the string is precomputed and threaded to the formatter
    // alongside the value.
    r.byte_strings.push_back(
        agg == 2 ? FormatByteArrayLeftBoundFirst(
                       val_arg->text, *ctx.FindArrayInfo(val_arg->text), ctx)
                 : std::string());
  }
  return r;
}

// §21.2.1.1: a bare argument that is a fixed-size unpacked array is handled by
// its element type. An unpacked array of byte prints as a character string; any
// other unpacked aggregate has no unformatted rendering and is illegal.
// (Queues, dynamic, and associative arrays are left to their own handling.)
// False means the argument is not such an array and renders normally.
static bool AppendUnpackedArrayArg(const Expr* arg, SimContext& ctx,
                                   std::string& output) {
  if (arg->kind != ExprKind::kIdentifier) return false;
  const ArrayInfo* ai = ctx.FindArrayInfo(arg->text);
  if (ai == nullptr || ai->is_queue || ai->is_dynamic) return false;
  if (ai->elem_type_kind == DataTypeKind::kByte) {
    output += FormatUnpackedByteArrayAsString(arg->text, *ai, ctx);
  } else {
    ctx.GetDiag().Error(
        arg->range.start,
        "unformatted unpacked-array argument to a display or write task "
        "is illegal unless its elements are of type byte",
        Subclause("21.2.1.1"));
  }
  return true;
}

// Render one argument of a display or write task, consuming any expression
// arguments a format template takes with it.
// The text a display-syntax argument list is rendered into, and the
// specifier a bare expression argument is rendered under: the task's own for
// the display and write families, decimal for a severity task, whose name
// says nothing of a radix ($info ends in the letter the octal family does).
struct DisplayText {
  std::string& text;
  char default_radix;
};

static void AppendDisplayArg(const Expr* expr, size_t& i, SimContext& ctx,
                             Arena& arena, DisplayText out) {
  const Expr* arg = expr->args[i];
  // An omitted argument -- a leading, trailing, or doubled comma in the call --
  // carries no expression and is rendered as a single space.
  if (arg == nullptr) {
    out.text += ' ';
    return;
  }
  if (arg->kind == ExprKind::kStringLiteral) {
    std::string fmt = ExtractFormatString(arg);
    DisplayArgRenderings r = CollectDisplayArgs(expr, i, fmt, ctx, arena);
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
  // A bare expression renders under the task's default radix; a value carrying
  // string-typed data is always rendered as its character sequence regardless
  // of the task name. The rendering carries the §21.2.1.2 automatic sizing, so
  // a plain $display pads its default decimal exactly as an explicit %d would.
  auto val = EvalExpr(arg, ctx, arena);
  char spec = val.is_string ? 's' : out.default_radix;
  out.text += FormatArgAutoSized(val, spec);
}

std::string RenderDisplayArgList(const Expr* expr, size_t first,
                                 char default_radix, SimContext& ctx,
                                 Arena& arena) {
  // The arguments are processed in the order they appear. A string literal acts
  // as a format template whose specifiers are filled by the expression
  // arguments that immediately follow it.
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
  // The display family ($display, $displayb, $displayo, $displayh) terminates
  // its output with a newline; the write family does not.
  if (expr->callee.starts_with("$display")) ctx.Out() << "\n";
}

void EmitSeverityHeader(SimContext& ctx, std::string_view prefix,
                        std::string_view msg, std::ostream& os, uint32_t line) {
  // §20.10: the tool-specific message reports the severity plus the required
  // call-site information -- the simulation time, the hierarchical scope of the
  // call, and its source line (the `__LINE__ equivalent, see §22.13). A line of
  // 0 marks a call site with no recorded source location.
  std::string scope = ScopeHierName(ctx);
  os << "[" << ctx.CurrentTime().ticks << "] " << prefix;
  if (!scope.empty()) os << " " << scope;
  if (line != 0) os << " (line " << line << ")";
  if (!msg.empty()) os << ": " << msg;
  os << "\n";
  ctx.SetLastSeverity(prefix, msg, ctx.CurrentTime(), scope, line);
  // §20.10: an error or a fatal report is a run-time error of the run, the
  // tool's own -- an assertion's default action (§16.14.1), wait_order's
  // (§15.5.4) -- as much as a $error or $fatal the source calls, and the
  // run's exit status reports it (RunSimulation in src/main.cpp). Noted for
  // the two calls alone, test/src/e2e/assert_statement.sv's failing no_else
  // assertion left the status 0.
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
  // §20.10 (printed page 635): the user-defined message uses the syntax of
  // $display, and the tool's message shall include it, so the arguments are
  // rendered as ExecDisplayWrite renders $display's -- a string literal a
  // format for the arguments after it, a string-typed value its text, any
  // other value in the default radix. Read for a format string alone,
  // `$error($sformatf("property check failed"))`, the action block of the
  // suite's chapter-16 -fail assertions, printed the header and no message.
  std::string msg;
  DisplayText out{msg, 'd'};
  for (size_t i = start_idx; i < expr->args.size(); ++i) {
    AppendDisplayArg(expr, i, ctx, arena, out);
  }
  // §20.10: report the source line of the call, matching the `__LINE__ the
  // preprocessor would produce here (§22.13).
  EmitSeverityHeader(ctx, prefix, msg, os, expr->range.start.line);
}

Logic4Vec EvalDeferredPrint(const Expr* expr, SimContext& ctx, Arena& arena) {
  auto* event = ctx.GetScheduler().GetEventPool().Acquire();
  // §21.2.2 with §33.7: the text is produced after the calling process has run
  // to completion, yet it is the call's arguments as the calling scope sees
  // them -- a method's object and locals among them -- and the binding %l/%L
  // reports is that of the instance the call was written in. Both are recorded
  // now and reinstated for the span of the output. Without them a property
  // named in a class method read 0, the call having no object by then.
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

// The four strobed-monitoring task names listed in Syntax 21-2. They differ
// only in the default radix used for unformatted expression arguments; that
// radix is applied by the shared display machinery.
bool IsStrobeTask(std::string_view name) {
  return name == "$strobe" || name == "$strobeb" || name == "$strobeo" ||
         name == "$strobeh";
}

}  // namespace delta
