#include <algorithm>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <optional>
#include <string>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "parser/ast.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/vcd_writer.h"

namespace delta {

Logic4Vec EvalPrngCall(const Expr* expr, SimContext& ctx, Arena& arena,
                       std::string_view name) {
  if (name == "$random") {
    // §20.14.1: an optional seed selects the stream, so different seeds yield
    // different sequences and a given seed replays identically. Reseed the
    // active generator from the argument before drawing, mirroring $urandom.
    if (!expr->args.empty()) {
      ctx.SeedUrandom(static_cast<uint32_t>(
          EvalExpr(expr->args[0], ctx, arena).ToUint64()));
    }
    // The returned 32-bit number is a signed integer (it may be negative).
    return MakeLogic4VecVal(arena, 32, ctx.Random32());
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
  if (name == "$urandom_range") {
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
  return MakeLogic4VecVal(arena, 1, 0);
}

// The integer kinds whose unformatted decimal rendering is signed, so a member
// or element holding a negative value shows its sign.
static bool IsSignedIntegerKind(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kByte:
    case DataTypeKind::kShortint:
    case DataTypeKind::kInt:
    case DataTypeKind::kLongint:
    case DataTypeKind::kInteger:
      return true;
    default:
      return false;
  }
}

// §21.2.1.6: render a singular value the way it appears as one element of an
// assignment pattern. A string-typed element is enclosed in quotes (C7c); every
// other singular type prints as it would unformatted (C7e) -- the default
// decimal form, with x/z status characters carried through by FormatArg and the
// sign shown for the signed integer kinds.
static std::string FormatSingularForP(const Logic4Vec& val, DataTypeKind kind) {
  if (kind == DataTypeKind::kString || val.is_string) {
    return "\"" + FormatValueAsString(val) + "\"";
  }
  Logic4Vec v = val;
  if (IsSignedIntegerKind(kind)) v.is_signed = true;
  return FormatArg(v, 'd');
}

// §21.2.1.6: copy the [offset, offset+width) bit field out of a packed
// aggregate into its own vector, preserving unknown/high-impedance bits so a
// member that holds x or z renders as such.
static Logic4Vec SliceField(const Logic4Vec& val, uint32_t offset,
                            uint32_t width, DataTypeKind kind, Arena& arena) {
  Logic4Vec out = MakeLogic4Vec(arena, width == 0 ? 1 : width);
  for (uint32_t i = 0; i < width; ++i) {
    uint32_t src = offset + i;
    uint32_t sw = src / 64, sb = src % 64;
    if (sw >= val.nwords) continue;
    uint32_t dw = i / 64, db = i % 64;
    if ((val.words[sw].aval >> sb) & 1) out.words[dw].aval |= uint64_t{1} << db;
    if ((val.words[sw].bval >> sb) & 1) out.words[dw].bval |= uint64_t{1} << db;
  }
  out.is_signed = IsSignedIntegerKind(kind);
  return out;
}

// §21.2.1.6 (C2/C7a): render one struct or union member as "name:value", its
// value formatted by the singular rules.
static std::string FormatMember(const StructFieldInfo& f, const Logic4Vec& val,
                                Arena& arena) {
  Logic4Vec slice = SliceField(val, f.bit_offset, f.width, f.type_kind, arena);
  return std::string(f.name) + ":" + FormatSingularForP(slice, f.type_kind);
}

// §21.2.1.6 (C4): a tagged union prints its currently valid member as
// "tag:value". The active member's width and type come from the union type.
// Returns the formatted text, or no value when the variable is not a tagged
// union (the caller falls through to the next aggregate form).
static std::optional<std::string> BuildFormatPTaggedUnion(std::string_view name,
                                                          const Logic4Vec& val,
                                                          SimContext& ctx,
                                                          Arena& arena) {
  auto tag = ctx.GetVariableTag(name);
  if (tag.empty()) return std::nullopt;
  DataTypeKind kind = DataTypeKind::kImplicit;
  uint32_t width = val.width;
  if (auto* st = ctx.GetVariableStructType(name)) {
    for (const auto& f : st->fields) {
      if (f.name == tag) {
        kind = f.type_kind;
        width = f.width;
        break;
      }
    }
  }
  Logic4Vec slice = SliceField(val, 0, width, kind, arena);
  return "'{" + std::string(tag) + ":" + FormatSingularForP(slice, kind) + "}";
}

// §21.2.1.6 (C2/C3/C7a): a struct prints every member as "name:value"; a
// plain (untagged) union prints only its first declared member. Returns no
// value when the variable is not a struct/union type.
static std::optional<std::string> BuildFormatPStruct(std::string_view name,
                                                     const Logic4Vec& val,
                                                     SimContext& ctx,
                                                     Arena& arena) {
  auto* st = ctx.GetVariableStructType(name);
  if (st == nullptr) return std::nullopt;
  std::string out = "'{";
  size_t count =
      st->is_union ? std::min<size_t>(1, st->fields.size()) : st->fields.size();
  for (size_t i = 0; i < count; ++i) {
    if (i) out += ", ";
    out += FormatMember(st->fields[i], val, arena);
  }
  out += "}";
  return out;
}

// §21.2.1.6 (C5): an unpacked array prints as an assignment pattern of its
// elements in index order. Elements live as their own variables, named
// "arr[idx]" by the lowerer. Returns no value when the variable is not a
// non-empty unpacked array.
static std::optional<std::string> BuildFormatPArray(std::string_view name,
                                                    SimContext& ctx,
                                                    Arena& arena) {
  auto* ai = ctx.FindArrayInfo(name);
  if (ai == nullptr || ai->size == 0) return std::nullopt;
  std::string out = "'{";
  for (uint32_t i = 0; i < ai->size; ++i) {
    if (i) out += ", ";
    uint32_t idx = ai->lo + i;
    std::string elem_name = std::string(name) + "[" + std::to_string(idx) + "]";
    Variable* elem = ctx.FindVariable(elem_name);
    Logic4Vec ev =
        elem ? elem->value : MakeLogic4VecVal(arena, ai->elem_width, 0);
    out += FormatSingularForP(ev, ai->elem_type_kind);
  }
  out += "}";
  return out;
}

// §21.2.1.6 (C7d): a class handle prints in an implementation-dependent form,
// except that a null handle prints the word "null". A null handle is the known
// zero value. Returns no value when the variable is not a class handle.
static std::optional<std::string> BuildFormatPClassHandle(std::string_view name,
                                                          const Logic4Vec& val,
                                                          SimContext& ctx) {
  if (ctx.GetVariableClassType(name).empty()) return std::nullopt;
  if (val.IsKnown() && val.ToUint64() == 0) return "null";
  return FormatArg(val, 'd');
}

// §21.2.1.6 (C7b): an enumerated value prints as the matching member name when
// the value is one named by the type; otherwise it prints in the base type's
// (decimal) form. Returns no value when the variable is not an enum type.
static std::optional<std::string> BuildFormatPEnum(std::string_view name,
                                                   const Logic4Vec& val,
                                                   SimContext& ctx) {
  auto* et = ctx.GetVariableEnumType(name);
  if (et == nullptr) return std::nullopt;
  if (val.IsKnown()) {
    uint64_t v = val.ToUint64();
    for (const auto& m : et->members) {
      if (m.value == v) return std::string(m.name);
    }
  }
  return FormatArg(val, 'd');
}

// §21.2.1.6: build the text the %p (and %0p) format specifier substitutes for
// an argument. An aggregate operand prints as an assignment pattern; a singular
// operand prints as a single element of one. The use of white space is left to
// the implementation, but the result is a legal assignment-pattern form (C6).
static std::string BuildFormatP(const Expr* arg, const Logic4Vec& val,
                                SimContext& ctx) {
  Arena& arena = ctx.GetArena();
  std::string_view name = (arg->kind == ExprKind::kIdentifier)
                              ? std::string_view(arg->text)
                              : std::string_view{};

  if (!name.empty()) {
    if (auto r = BuildFormatPTaggedUnion(name, val, ctx, arena)) return *r;
    if (auto r = BuildFormatPStruct(name, val, ctx, arena)) return *r;
    if (auto r = BuildFormatPArray(name, ctx, arena)) return *r;
    if (auto r = BuildFormatPClassHandle(name, val, ctx)) return *r;
    if (auto r = BuildFormatPEnum(name, val, ctx)) return *r;
  }

  // §21.2.1.6 (C10): %p on a singular expression formats it as one element of
  // an aggregate would be formatted.
  return FormatSingularForP(val, DataTypeKind::kImplicit);
}

// §21.2.1.4: %v reports the strength of a scalar net, so the operand is looked
// up as a net and rendered from its resolved strength. An operand that does
// not name a net carries no strength model and yields an empty string.
static std::string BuildFormatV(const Expr* arg, SimContext& ctx) {
  if (arg->kind != ExprKind::kIdentifier) return "";
  Net* net = ctx.FindNet(arg->text);
  if (net == nullptr) return "";
  return FormatStrength(net->resolved_strength);
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

void ExecDisplayWrite(const Expr* expr, SimContext& ctx, Arena& arena) {
  // The arguments are processed in the order they appear. A string literal
  // acts as a format template whose specifiers are filled by the expression
  // arguments that immediately follow it. An omitted argument -- a leading,
  // trailing, or doubled comma in the call -- carries no expression and is
  // rendered as a single space.
  std::string output;
  const size_t kN = expr->args.size();
  for (size_t i = 0; i < kN; ++i) {
    const Expr* arg = expr->args[i];
    if (arg == nullptr) {
      output += ' ';
      continue;
    }
    if (arg->kind == ExprKind::kStringLiteral) {
      std::string fmt = ExtractFormatString(arg);
      std::vector<Logic4Vec> arg_vals;
      std::vector<std::string> p_fmts;
      std::vector<std::string> v_fmts;
      while (i + 1 < kN && expr->args[i + 1] != nullptr &&
             expr->args[i + 1]->kind != ExprKind::kStringLiteral) {
        const Expr* val_arg = expr->args[++i];
        auto v = EvalExpr(val_arg, ctx, arena);
        arg_vals.push_back(v);
        p_fmts.push_back(BuildFormatP(val_arg, v, ctx));
        v_fmts.push_back(BuildFormatV(val_arg, ctx));
      }
      output += FormatDisplay(
          fmt, arg_vals, {.p_fmts = &p_fmts, .v_fmts = &v_fmts, .ctx = &ctx});
      continue;
    }
    // A bare expression renders under the task's default radix; a value
    // carrying string-typed data is always rendered as its character
    // sequence regardless of the task name.
    auto val = EvalExpr(arg, ctx, arena);
    char spec =
        val.is_string ? 's' : DefaultRadixForDisplayWriteTask(expr->callee);
    output += FormatArg(val, spec);
  }
  std::cout << output;
  // The display family ($display, $displayb, $displayo, $displayh) terminates
  // its output with a newline; the write family does not.
  if (expr->callee.starts_with("$display")) std::cout << "\n";
}

void EmitSeverityHeader(SimContext& ctx, std::string_view prefix,
                        std::string_view msg, std::ostream& os) {
  os << "[" << ctx.CurrentTime().ticks << "] " << prefix;
  if (!msg.empty()) os << ": " << msg;
  os << "\n";
  ctx.SetLastSeverity(prefix, msg, ctx.CurrentTime());
}

void ExecSeverityTask(const Expr* expr, SimContext& ctx, Arena& arena,
                      const char* prefix, std::ostream& os) {
  std::string fmt;
  std::vector<Logic4Vec> arg_vals;
  size_t start_idx = 0;

  if (std::string_view(prefix) == "FATAL" && !expr->args.empty()) {
    if (expr->args[0]->kind != ExprKind::kStringLiteral) {
      EvalExpr(expr->args[0], ctx, arena);
      start_idx = 1;
    }
  }

  for (size_t i = start_idx; i < expr->args.size(); ++i) {
    auto val = EvalExpr(expr->args[i], ctx, arena);
    if (i == start_idx && expr->args[i]->kind == ExprKind::kStringLiteral) {
      fmt = ExtractFormatString(expr->args[i]);
    } else {
      arg_vals.push_back(val);
    }
  }
  std::string msg =
      fmt.empty() ? "" : FormatDisplay(fmt, arg_vals, {.ctx = &ctx});
  EmitSeverityHeader(ctx, prefix, msg, os);
}

Logic4Vec EvalDeferredPrint(const Expr* expr, SimContext& ctx, Arena& arena) {
  auto* event = ctx.GetScheduler().GetEventPool().Acquire();
  event->callback = [expr, &ctx, &arena]() {
    ExecDisplayWrite(expr, ctx, arena);
    std::cout << "\n";
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

// The four monitor task names listed in Syntax 21-3. They differ only in the
// default radix used for unformatted expression arguments; that radix is
// applied by the shared display machinery, so all four monitor identically.
bool IsMonitorTask(std::string_view name) {
  return name == "$monitor" || name == "$monitorb" || name == "$monitoro" ||
         name == "$monitorh";
}

// Gathers the simple signal names referenced anywhere in a monitor argument.
// $time, $stime, and $realtime are system calls rather than identifiers, so
// they are never collected and their advance does not trigger the monitor.
static void CollectMonitorSignals(const Expr* e,
                                  std::vector<std::string_view>& out) {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kIdentifier) {
    out.push_back(e->text);
    return;
  }
  CollectMonitorSignals(e->lhs, out);
  CollectMonitorSignals(e->rhs, out);
  CollectMonitorSignals(e->condition, out);
  CollectMonitorSignals(e->true_expr, out);
  CollectMonitorSignals(e->false_expr, out);
  CollectMonitorSignals(e->base, out);
  CollectMonitorSignals(e->index, out);
  CollectMonitorSignals(e->index_end, out);
  for (auto* a : e->args) CollectMonitorSignals(a, out);
  for (auto* el : e->elements) CollectMonitorSignals(el, out);
}

static Logic4Vec CloneLogic4Vec(const Logic4Vec& v, Arena& arena) {
  Logic4Vec copy = MakeLogic4Vec(arena, v.width);
  copy.is_signed = v.is_signed;
  uint32_t n = std::min(copy.nwords, v.nwords);
  for (uint32_t i = 0; i < n; ++i) copy.words[i] = v.words[i];
  return copy;
}

static bool SameBits(const Logic4Vec& a, const Logic4Vec& b) {
  if (a.nwords != b.nwords) return false;
  for (uint32_t i = 0; i < a.nwords; ++i) {
    if (a.words[i].aval != b.words[i].aval ||
        a.words[i].bval != b.words[i].bval)
      return false;
  }
  return true;
}

// Queues the active monitor's display into the postponed region of the current
// time step, coalescing so that simultaneous changes produce a single line.
static void ScheduleMonitorDisplay(SimContext& ctx, Arena& arena) {
  if (ctx.MonitorDisplayPending()) return;
  ctx.SetMonitorDisplayPending(true);
  auto* event = ctx.GetScheduler().GetEventPool().Acquire();
  event->callback = [&ctx, &arena]() {
    ctx.SetMonitorDisplayPending(false);
    const Expr* monitor = ctx.ActiveMonitor();
    if (monitor == nullptr || !ctx.MonitorEnabled()) return;
    ExecDisplayWrite(monitor, ctx, arena);
    std::cout << "\n";
  };
  ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime(), Region::kPostponed,
                                   event);
}

// Installs a persistent watcher that redisplays the active monitor whenever the
// signal takes on a new value. The captured generation deactivates the watcher
// once a later $monitor has replaced the display list.
static void AddMonitorWatcher(Variable* var, SimContext& ctx, Arena& arena,
                              uint64_t generation) {
  var->AddWatcher([var, &ctx, &arena, generation]() -> bool {
    if (generation != ctx.MonitorGeneration()) return true;  // superseded
    const Logic4Vec* last = ctx.MonitorLastValue(var);
    if (last != nullptr && SameBits(*last, var->value)) return false;
    ctx.SetMonitorLastValue(var, CloneLogic4Vec(var->value, arena));
    if (ctx.MonitorEnabled()) ScheduleMonitorDisplay(ctx, arena);
    return false;
  });
}

Logic4Vec EvalMonitor(const Expr* expr, SimContext& ctx, Arena& arena) {
  // A fresh $monitor call becomes the one active display list and supersedes
  // any earlier one.
  ctx.SetActiveMonitor(expr);
  std::vector<std::string_view> names;
  for (auto* arg : expr->args) CollectMonitorSignals(arg, names);
  uint64_t generation = ctx.MonitorGeneration();
  for (auto name : names) {
    Variable* var = ctx.FindVariable(name);
    if (var == nullptr) continue;
    ctx.SetMonitorLastValue(var, CloneLogic4Vec(var->value, arena));
    AddMonitorWatcher(var, ctx, arena, generation);
  }
  // The initial values are displayed at the end of the current time step.
  if (ctx.MonitorEnabled()) ScheduleMonitorDisplay(ctx, arena);
  return MakeLogic4VecVal(arena, 1, 0);
}

Logic4Vec EvalMonitorFlag(SimContext& ctx, Arena& arena,
                          std::string_view name) {
  if (name == "$monitoroff") {
    ctx.SetMonitorEnabled(false);
  } else {  // $monitoron
    ctx.SetMonitorEnabled(true);
    // Turning the flag on produces a display immediately, regardless of
    // whether a watched value has changed.
    ScheduleMonitorDisplay(ctx, arena);
  }
  return MakeLogic4VecVal(arena, 1, 0);
}

static std::string ResolveDumpFileName(const Expr* expr, SimContext& ctx,
                                       Arena& arena) {
  if (expr->args.empty()) return "dump.vcd";
  const Expr* arg = expr->args[0];
  if (arg->kind == ExprKind::kStringLiteral) {
    auto text = arg->text;
    if (text.size() >= 2 && text.front() == '"') {
      return std::string(text.substr(1, text.size() - 2));
    }
    return std::string(text);
  }
  return FormatValueAsString(EvalExpr(arg, ctx, arena));
}

// Reduces a $dumpvars scope argument to the simple name a registered signal
// carries: a string literal loses its quotes and a hierarchical path keeps
// only its trailing component (e.g. top.mod2.net1 -> net1).
static std::string_view DumpvarsScopeName(const Expr* arg) {
  std::string_view text = arg->text;
  if (arg->kind == ExprKind::kStringLiteral && text.size() >= 2 &&
      text.front() == '"') {
    text = text.substr(1, text.size() - 2);
  }
  auto dot = text.rfind('.');
  if (dot != std::string_view::npos) text = text.substr(dot + 1);
  return text;
}

// Resolves the $dumpports output filename (§21.7.3.1). The filename is the
// trailing argument when it is given as a string literal; when no filename is
// supplied the output defaults to dumpports.vcd in the working directory.
static std::string ResolveDumpportsFileName(const Expr* expr) {
  if (!expr->args.empty()) {
    const Expr* last = expr->args.back();
    if (last && last->kind == ExprKind::kStringLiteral) {
      auto text = last->text;
      if (text.size() >= 2 && text.front() == '"') {
        return std::string(text.substr(1, text.size() - 2));
      }
      return std::string(text);
    }
  }
  return "dumpports.vcd";
}

// §21.7.3.7: the extended VCD control tasks each act on a $dumpports dump and
// share the general rules for filename matching and no-argument default
// actions.
static bool IsDumpportsControlTask(std::string_view name) {
  return name == "$dumpportsoff" || name == "$dumpportson" ||
         name == "$dumpportsall" || name == "$dumpportslimit" ||
         name == "$dumpportsflush";
}

// §21.7.3.7: a control task's optional filename is its trailing string-literal
// argument and names which $dumpports output the task targets. Returns the
// unquoted filename, or an empty string when the call carries no such argument
// (for $dumpportslimit the trailing argument is the filesize, not a literal).
static std::string DumpportsControlFileArg(const Expr* expr) {
  if (expr->args.empty()) return {};
  const Expr* last = expr->args.back();
  if (!last || last->kind != ExprKind::kStringLiteral) return {};
  auto text = last->text;
  if (text.size() >= 2 && text.front() == '"') {
    return std::string(text.substr(1, text.size() - 2));
  }
  return std::string(text);
}

// §21.7.1.2: dump the variables named by a $dumpvars call. With no arguments
// every variable in the model is dumped. When arguments are present the first
// is the level count and the remaining arguments name the scopes (modules or
// individual variables) to dump.
static void ExecDumpvars(const Expr* expr, VcdWriter* vcd) {
  if (!vcd) return;
  std::vector<std::string_view> scopes;
  for (size_t i = 1; i < expr->args.size(); ++i) {
    auto scope = DumpvarsScopeName(expr->args[i]);
    if (!scope.empty()) scopes.push_back(scope);
  }
  if (scopes.empty()) {
    vcd->DumpAllValues();
  } else {
    vcd->DumpSelectedValues(scopes);
  }
}

// §21.7.3.1: gather the unique module scopes named in a $dumpports scope_list.
// scope_end excludes a trailing filename argument. A string-literal entry is
// not a valid module_identifier and is rejected; duplicate scopes within this
// call and across earlier $dumpports calls are reported rather than dumped.
static std::vector<std::string_view> CollectDumpportsScopes(const Expr* expr,
                                                            size_t scope_end,
                                                            SimContext& ctx) {
  std::vector<std::string_view> scopes;
  for (size_t i = 0; i < scope_end; ++i) {
    if (!expr->args[i]) continue;
    // §21.7.3.1: scope_list entries name modules; a string literal is not a
    // valid module_identifier, so reject it rather than treating it as a
    // scope name.
    if (expr->args[i]->kind == ExprKind::kStringLiteral) {
      ctx.GetDiag().Error(
          {},
          "$dumpports scope_list entry must be a module, not a string "
          "literal");
      continue;
    }
    auto scope = DumpvarsScopeName(expr->args[i]);
    if (scope.empty()) continue;
    // §21.7.3.1: each scope named in a $dumpports scope_list shall be
    // unique; a repeated scope is reported rather than dumped twice.
    if (std::find(scopes.begin(), scopes.end(), scope) != scopes.end()) {
      ctx.GetDiag().Error({}, "$dumpports scope_list entries must be unique");
      continue;
    }
    // §21.7.3.1: scope names must also be unique across separate $dumpports
    // calls, not just within one call.
    if (!ctx.RegisterDumpportsScope(std::string(scope))) {
      ctx.GetDiag().Error({},
                          "$dumpports scope already named by an earlier call");
      continue;
    }
    scopes.push_back(scope);
  }
  return scopes;
}

// §21.7.3.1: name the (extended) VCD output and start dumping the ports in
// scope. A trailing string-literal argument names the file, defaulting to
// dumpports.vcd when omitted. The leading arguments form the scope_list naming
// the modules whose ports are dumped; with no scope_list the scope is the
// calling module, so every port registered from the point of the call is
// treated as a primary I/O pin and dumped. Dumping reuses the 4-state VCD
// machinery, which the extended VCD file inherits unless otherwise stated.
static void ExecDumpports(const Expr* expr, SimContext& ctx, VcdWriter* vcd) {
  ctx.SetDumpFileName(ResolveDumpportsFileName(expr));
  bool last_is_file = !expr->args.empty() && expr->args.back() &&
                      expr->args.back()->kind == ExprKind::kStringLiteral;
  // §21.7.3.1: a file name spelled out in the call may not be reused by a
  // later $dumpports call. A defaulted name is not "specified", so repeated
  // default calls are allowed.
  if (last_is_file && !ctx.RegisterDumpportsFile(ctx.GetDumpFileName())) {
    ctx.GetDiag().Error(
        {}, "$dumpports may not name the same output file more than once");
  }
  if (!vcd) return;
  // $dumpports produces an extended VCD file, which closes with the
  // $vcdclose keyword command (§21.7.3.6.1).
  vcd->SetExtended();
  size_t scope_end = expr->args.size() - (last_is_file ? 1 : 0);
  std::vector<std::string_view> scopes =
      CollectDumpportsScopes(expr, scope_end, ctx);
  if (scopes.empty()) {
    vcd->DumpAllValues();
  } else {
    vcd->DumpSelectedValues(scopes);
  }
}

// §21.7.3.7: an extended VCD control task that names a file no $dumpports call
// opened is ignored. The match is against the files explicitly named by
// $dumpports; with no filename argument the default action runs against every
// such file. Under this single-writer model, when no $dumpports call has named
// a file there is nothing to mismatch, so the lone dump is the implicit target
// and the task proceeds. Returns true when the task should be skipped.
static bool DumpportsControlTaskTargetsUnknownFile(const Expr* expr,
                                                   SimContext& ctx,
                                                   std::string_view name) {
  if (!IsDumpportsControlTask(name) || !ctx.HasDumpportsFiles()) return false;
  std::string file = DumpportsControlFileArg(expr);
  return !file.empty() && !ctx.IsDumpportsFile(file);
}

// §21.7.1.5 / §21.7.3.4: bound the VCD file size in bytes. The single (leading)
// argument gives the maximum byte budget; the extended-VCD form reuses the same
// 4-state size-limit machinery the file inherits.
static void ExecDumpLimit(const Expr* expr, SimContext& ctx, Arena& arena,
                          VcdWriter* vcd) {
  if (vcd && !expr->args.empty()) {
    uint64_t limit = EvalExpr(expr->args[0], ctx, arena).ToUint64();
    vcd->SetSizeLimit(limit);
  }
}

// §21.7.1.x: the basic four-state VCD control tasks ($dumpall/$dumpoff/$dumpon/
// $dumpflush) act directly on the writer. Returns true when name named one of
// them (whether or not a writer is present) so the caller stops dispatching.
static bool ExecBasicVcdControl(std::string_view name, VcdWriter* vcd) {
  if (name == "$dumpall") {
    // Emit a checkpoint of every selected variable's current value (§21.7.1.4).
    if (vcd) vcd->DumpAll();
  } else if (name == "$dumpoff") {
    // Suspend dumping with an all-x checkpoint (§21.7.1.3).
    if (vcd) vcd->DumpOff();
  } else if (name == "$dumpon") {
    // Resume dumping with a checkpoint of current values (§21.7.1.3).
    if (vcd) vcd->DumpOn();
  } else if (name == "$dumpflush") {
    // §21.7.1.6: flush buffered output to the dump file, then continue dumping
    // as before so no value changes are lost.
    if (vcd) vcd->Flush();
  } else {
    return false;
  }
  return true;
}

// §21.7.3.x: the writer-acting extended-VCD ($dumpports) port control tasks.
// Each reuses the 4-state machinery the extended VCD file inherits and treats
// its optional trailing filename as selecting this single-file writer (already
// validated by DumpportsControlTaskTargetsUnknownFile). Returns true when name
// named one of them (whether or not a writer is present) so the caller stops
// dispatching.
static bool ExecDumpportsWriterAction(std::string_view name, VcdWriter* vcd) {
  if (name == "$dumpportsoff") {
    // §21.7.3.2: suspend the extended VCD port dump. A checkpoint marking every
    // selected port as x is written and recording stops from this simulation
    // time forward. The optional filename argument denotes the $dumpports
    // output file; with this single-file writer it selects that one dump, and
    // with no argument every $dumpports file is suspended. The suspend
    // checkpoint reuses the 4-state machinery the extended VCD file inherits
    // (§21.7.1.3). If port dumping is already suspended for the file the task
    // is ignored, so no second checkpoint is written.
    if (vcd && vcd->IsEnabled()) vcd->DumpOff();
  } else if (name == "$dumpportson") {
    // §21.7.3.2: resume the extended VCD port dump, emitting a checkpoint of
    // every selected port's current value. The optional filename argument names
    // the $dumpports file to resume; with no argument every stopped $dumpports
    // file resumes. The resume checkpoint reuses the inherited 4-state
    // machinery (§21.7.1.3). If the ports are already being dumped the task is
    // ignored, so no checkpoint is written.
    if (vcd && !vcd->IsEnabled()) vcd->DumpOn();
  } else if (name == "$dumpportsall") {
    // §21.7.3.3: write an extended-VCD checkpoint recording the current value
    // of every selected port at this simulation time, regardless of whether the
    // values changed since the previous time step. The optional filename names
    // the $dumpports output to checkpoint; with this single-file writer it
    // selects that one dump, and with no filename the checkpoint covers every
    // file opened by $dumpports. The checkpoint reuses the 4-state machinery
    // the extended VCD file inherits (§21.7.1.4).
    if (vcd) vcd->DumpAll();
  } else if (name == "$dumpportsflush") {
    // §21.7.3.5: push the buffered extended-VCD port values out to the dump
    // file, clearing the simulator's VCD buffer so a reader sees everything
    // dumped so far while the simulation keeps running. The optional filename
    // argument denotes the $dumpports output to flush; with this single-file
    // writer it selects that one dump, and with no filename the buffers for
    // every file opened by $dumpports are flushed. Either way the one writer is
    // flushed, so the filename is parsed but does not change which dump is
    // emptied. The flush reuses the buffer-flushing machinery the extended VCD
    // file inherits (§21.7.1.6): no VCD command is written and the dump state
    // is left untouched so dumping continues exactly as before.
    if (vcd) vcd->Flush();
  } else {
    return false;
  }
  return true;
}

// §21.7.3.x: the extended-VCD ($dumpports) port control tasks. The
// writer-acting tasks are handled by ExecDumpportsWriterAction; $dumpportslimit
// additionally needs the call expression to read its byte budget. Returns true
// when name named one of these tasks so the caller stops dispatching.
static bool ExecDumpportsControl(const Expr* expr, SimContext& ctx,
                                 Arena& arena, VcdWriter* vcd,
                                 std::string_view name) {
  if (name == "$dumpportslimit") {
    // §21.7.3.4: bound the extended VCD file size. The required leading
    // filesize argument gives the maximum number of bytes; once the dump
    // reaches it, recording stops and a comment noting the limit is inserted. A
    // trailing filename argument may denote which $dumpports output the limit
    // applies to; with no filename the limit covers every file opened by
    // $dumpports. With this single-file writer both cases bound the one dump,
    // so the optional filename is parsed but does not change which dump is
    // limited. The byte budget reuses the 4-state size-limit machinery the
    // extended VCD file inherits (§21.7.1.5).
    ExecDumpLimit(expr, ctx, arena, vcd);
    return true;
  }
  return ExecDumpportsWriterAction(name, vcd);
}

Logic4Vec EvalVcdSysCall(const Expr* expr, SimContext& ctx, Arena& arena,
                         std::string_view name) {
  auto* vcd = ctx.GetVcdWriter();
  if (DumpportsControlTaskTargetsUnknownFile(expr, ctx, name)) {
    return MakeLogic4VecVal(arena, 1, 0);
  }
  if (name == "$dumpfile") {
    ctx.SetDumpFileName(ResolveDumpFileName(expr, ctx, arena));
  } else if (name == "$dumpvars") {
    ExecDumpvars(expr, vcd);
  } else if (name == "$dumplimit") {
    // §21.7.1.5: the single argument bounds the VCD file size in bytes.
    ExecDumpLimit(expr, ctx, arena, vcd);
  } else if (name == "$dumpports") {
    ExecDumpports(expr, ctx, vcd);
  } else if (!ExecBasicVcdControl(name, vcd)) {
    ExecDumpportsControl(expr, ctx, arena, vcd, name);
  }
  return MakeLogic4VecVal(arena, 1, 0);
}

}  // namespace delta
