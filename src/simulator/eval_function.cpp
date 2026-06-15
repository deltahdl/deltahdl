#include <algorithm>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <string>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/dpi.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/vcd_writer.h"

namespace delta {

static Logic4Vec EvalPrngCall(const Expr* expr, SimContext& ctx, Arena& arena,
                              std::string_view name) {
  if (name == "$random") {
    // §20.14.1: an optional seed selects the stream, so different seeds yield
    // different sequences and a given seed replays identically. Reseed the
    // active generator from the argument before drawing, mirroring $urandom.
    if (!expr->args.empty()) {
      ctx.SeedUrandom(
          static_cast<uint32_t>(EvalExpr(expr->args[0], ctx, arena).ToUint64()));
    }
    // The returned 32-bit number is a signed integer (it may be negative).
    return MakeLogic4VecVal(arena, 32, ctx.Random32());
  }
  if (name == "$urandom") {
    // An optional seed (any integral expression) selects the sequence; the
    // same seed must replay identically.
    if (!expr->args.empty()) {
      ctx.SeedUrandom(
          static_cast<uint32_t>(EvalExpr(expr->args[0], ctx, arena).ToUint64()));
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

// §21.2.1.6: copy the [offset, offset+width) bit field out of a packed aggregate
// into its own vector, preserving unknown/high-impedance bits so a member that
// holds x or z renders as such.
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
    // §21.2.1.6 (C4): a tagged union prints its currently valid member as
    // "tag:value". The active member's width and type come from the union type.
    auto tag = ctx.GetVariableTag(name);
    if (!tag.empty()) {
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
      return "'{" + std::string(tag) + ":" + FormatSingularForP(slice, kind) +
             "}";
    }

    // §21.2.1.6 (C2/C3/C7a): a struct prints every member as "name:value"; a
    // plain (untagged) union prints only its first declared member.
    if (auto* st = ctx.GetVariableStructType(name)) {
      std::string out = "'{";
      size_t count = st->is_union ? std::min<size_t>(1, st->fields.size())
                                  : st->fields.size();
      for (size_t i = 0; i < count; ++i) {
        if (i) out += ", ";
        out += FormatMember(st->fields[i], val, arena);
      }
      out += "}";
      return out;
    }

    // §21.2.1.6 (C5): an unpacked array prints as an assignment pattern of its
    // elements in index order. Elements live as their own variables, named
    // "arr[idx]" by the lowerer.
    if (auto* ai = ctx.FindArrayInfo(name); ai != nullptr && ai->size > 0) {
      std::string out = "'{";
      for (uint32_t i = 0; i < ai->size; ++i) {
        if (i) out += ", ";
        uint32_t idx = ai->lo + i;
        std::string elem_name =
            std::string(name) + "[" + std::to_string(idx) + "]";
        Variable* elem = ctx.FindVariable(elem_name);
        Logic4Vec ev = elem ? elem->value
                            : MakeLogic4VecVal(arena, ai->elem_width, 0);
        out += FormatSingularForP(ev, ai->elem_type_kind);
      }
      out += "}";
      return out;
    }

    // §21.2.1.6 (C7d): a class handle prints in an implementation-dependent
    // form, except that a null handle prints the word "null". A null handle is
    // the known zero value.
    if (!ctx.GetVariableClassType(name).empty()) {
      if (val.IsKnown() && val.ToUint64() == 0) return "null";
      return FormatArg(val, 'd');
    }

    // §21.2.1.6 (C7b): an enumerated value prints as the matching member name
    // when the value is one named by the type; otherwise it prints in the base
    // type's (decimal) form.
    if (auto* et = ctx.GetVariableEnumType(name)) {
      if (val.IsKnown()) {
        uint64_t v = val.ToUint64();
        for (const auto& m : et->members) {
          if (m.value == v) return std::string(m.name);
        }
      }
      return FormatArg(val, 'd');
    }
  }

  // §21.2.1.6 (C10): %p on a singular expression formats it as one element of an
  // aggregate would be formatted.
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
static bool IsDisplayOrWriteTask(std::string_view name) {
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

static void ExecDisplayWrite(const Expr* expr, SimContext& ctx, Arena& arena) {
  // The arguments are processed in the order they appear. A string literal
  // acts as a format template whose specifiers are filled by the expression
  // arguments that immediately follow it. An omitted argument -- a leading,
  // trailing, or doubled comma in the call -- carries no expression and is
  // rendered as a single space.
  std::string output;
  const size_t n = expr->args.size();
  for (size_t i = 0; i < n; ++i) {
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
      while (i + 1 < n && expr->args[i + 1] != nullptr &&
             expr->args[i + 1]->kind != ExprKind::kStringLiteral) {
        const Expr* val_arg = expr->args[++i];
        auto v = EvalExpr(val_arg, ctx, arena);
        arg_vals.push_back(v);
        p_fmts.push_back(BuildFormatP(val_arg, v, ctx));
        v_fmts.push_back(BuildFormatV(val_arg, ctx));
      }
      output += FormatDisplay(fmt, arg_vals, p_fmts, nullptr, v_fmts, &ctx);
      continue;
    }
    // A bare expression renders under the task's default radix; a value
    // carrying string-typed data is always rendered as its character
    // sequence regardless of the task name.
    auto val = EvalExpr(arg, ctx, arena);
    char spec = val.is_string ? 's'
                              : DefaultRadixForDisplayWriteTask(expr->callee);
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

static void ExecSeverityTask(const Expr* expr, SimContext& ctx, Arena& arena,
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
      fmt.empty() ? "" : FormatDisplay(fmt, arg_vals, {}, nullptr, {}, &ctx);
  EmitSeverityHeader(ctx, prefix, msg, os);
}

static Logic4Vec EvalDeferredPrint(const Expr* expr, SimContext& ctx,
                                   Arena& arena) {
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
static bool IsStrobeTask(std::string_view name) {
  return name == "$strobe" || name == "$strobeb" || name == "$strobeo" ||
         name == "$strobeh";
}

// The four monitor task names listed in Syntax 21-3. They differ only in the
// default radix used for unformatted expression arguments; that radix is
// applied by the shared display machinery, so all four monitor identically.
static bool IsMonitorTask(std::string_view name) {
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

static Logic4Vec EvalMonitor(const Expr* expr, SimContext& ctx, Arena& arena) {
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

static Logic4Vec EvalMonitorFlag(SimContext& ctx, Arena& arena,
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
// share the general rules for filename matching and no-argument default actions.
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

static Logic4Vec EvalVcdSysCall(const Expr* expr, SimContext& ctx, Arena& arena,
                                std::string_view name) {
  auto* vcd = ctx.GetVcdWriter();
  // §21.7.3.7: if an extended VCD control task names a file that no $dumpports
  // call opened, the task is ignored. The match is against the files explicitly
  // named by $dumpports; with no filename argument the default action runs
  // against every such file. Under this single-writer model, when no $dumpports
  // call has named a file there is nothing to mismatch, so the lone dump is the
  // implicit target and the task proceeds.
  if (IsDumpportsControlTask(name) && ctx.HasDumpportsFiles()) {
    std::string file = DumpportsControlFileArg(expr);
    if (!file.empty() && !ctx.IsDumpportsFile(file)) {
      return MakeLogic4VecVal(arena, 1, 0);
    }
  }
  if (name == "$dumpfile") {
    ctx.SetDumpFileName(ResolveDumpFileName(expr, ctx, arena));
  } else if (name == "$dumpvars") {
    // With no arguments every variable in the model is dumped. When
    // arguments are present the first is the level count and the remaining
    // arguments name the scopes (modules or individual variables) to dump.
    if (vcd) {
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
  } else if (name == "$dumpall") {
    // Emit a checkpoint of every selected variable's current value (§21.7.1.4).
    if (vcd) vcd->DumpAll();
  } else if (name == "$dumpoff") {
    // Suspend dumping with an all-x checkpoint (§21.7.1.3).
    if (vcd) vcd->DumpOff();
  } else if (name == "$dumpon") {
    // Resume dumping with a checkpoint of current values (§21.7.1.3).
    if (vcd) vcd->DumpOn();
  } else if (name == "$dumplimit") {
    // §21.7.1.5: the single argument bounds the VCD file size in bytes.
    if (vcd && !expr->args.empty()) {
      uint64_t limit = EvalExpr(expr->args[0], ctx, arena).ToUint64();
      vcd->SetSizeLimit(limit);
    }
  } else if (name == "$dumpflush") {
    // §21.7.1.6: flush buffered output to the dump file, then continue dumping
    // as before so no value changes are lost.
    if (vcd) vcd->Flush();
  } else if (name == "$dumpports") {
    // §21.7.3.1: name the (extended) VCD output and start dumping the ports in
    // scope. A trailing string-literal argument names the file, defaulting to
    // dumpports.vcd when omitted. The leading arguments form the scope_list
    // naming the modules whose ports are dumped; with no scope_list the scope
    // is the calling module, so every port registered from the point of the
    // call is treated as a primary I/O pin and dumped. Dumping reuses the
    // 4-state VCD machinery, which the extended VCD file inherits unless
    // otherwise stated.
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
    if (vcd) {
      // $dumpports produces an extended VCD file, which closes with the
      // $vcdclose keyword command (§21.7.3.6.1).
      vcd->SetExtended();
      size_t scope_end = expr->args.size() - (last_is_file ? 1 : 0);
      std::vector<std::string_view> scopes;
      for (size_t i = 0; i < scope_end; ++i) {
        if (!expr->args[i]) continue;
        // §21.7.3.1: scope_list entries name modules; a string literal is not a
        // valid module_identifier, so reject it rather than treating it as a
        // scope name.
        if (expr->args[i]->kind == ExprKind::kStringLiteral) {
          ctx.GetDiag().Error(
              {}, "$dumpports scope_list entry must be a module, not a string "
                  "literal");
          continue;
        }
        auto scope = DumpvarsScopeName(expr->args[i]);
        if (scope.empty()) continue;
        // §21.7.3.1: each scope named in a $dumpports scope_list shall be
        // unique; a repeated scope is reported rather than dumped twice.
        if (std::find(scopes.begin(), scopes.end(), scope) != scopes.end()) {
          ctx.GetDiag().Error(
              {}, "$dumpports scope_list entries must be unique");
          continue;
        }
        // §21.7.3.1: scope names must also be unique across separate $dumpports
        // calls, not just within one call.
        if (!ctx.RegisterDumpportsScope(std::string(scope))) {
          ctx.GetDiag().Error(
              {}, "$dumpports scope already named by an earlier call");
          continue;
        }
        scopes.push_back(scope);
      }
      if (scopes.empty()) {
        vcd->DumpAllValues();
      } else {
        vcd->DumpSelectedValues(scopes);
      }
    }
  } else if (name == "$dumpportsoff") {
    // §21.7.3.2: suspend the extended VCD port dump. A checkpoint marking every
    // selected port as x is written and recording stops from this simulation
    // time forward. The optional filename argument denotes the $dumpports output
    // file; with this single-file writer it selects that one dump, and with no
    // argument every $dumpports file is suspended. The suspend checkpoint reuses
    // the 4-state machinery the extended VCD file inherits (§21.7.1.3). If port
    // dumping is already suspended for the file the task is ignored, so no
    // second checkpoint is written.
    if (vcd && vcd->IsEnabled()) vcd->DumpOff();
  } else if (name == "$dumpportson") {
    // §21.7.3.2: resume the extended VCD port dump, emitting a checkpoint of
    // every selected port's current value. The optional filename argument names
    // the $dumpports file to resume; with no argument every stopped $dumpports
    // file resumes. The resume checkpoint reuses the inherited 4-state machinery
    // (§21.7.1.3). If the ports are already being dumped the task is ignored, so
    // no checkpoint is written.
    if (vcd && !vcd->IsEnabled()) vcd->DumpOn();
  } else if (name == "$dumpportsall") {
    // §21.7.3.3: write an extended-VCD checkpoint recording the current value of
    // every selected port at this simulation time, regardless of whether the
    // values changed since the previous time step. The optional filename names
    // the $dumpports output to checkpoint; with this single-file writer it
    // selects that one dump, and with no filename the checkpoint covers every
    // file opened by $dumpports. The checkpoint reuses the 4-state machinery the
    // extended VCD file inherits (§21.7.1.4).
    if (vcd) vcd->DumpAll();
  } else if (name == "$dumpportslimit") {
    // §21.7.3.4: bound the extended VCD file size. The required leading filesize
    // argument gives the maximum number of bytes; once the dump reaches it,
    // recording stops and a comment noting the limit is inserted. A trailing
    // filename argument may denote which $dumpports output the limit applies to;
    // with no filename the limit covers every file opened by $dumpports. With
    // this single-file writer both cases bound the one dump, so the optional
    // filename is parsed but does not change which dump is limited. The byte
    // budget reuses the 4-state size-limit machinery the extended VCD file
    // inherits (§21.7.1.5).
    if (vcd && !expr->args.empty()) {
      uint64_t limit = EvalExpr(expr->args[0], ctx, arena).ToUint64();
      vcd->SetSizeLimit(limit);
    }
  } else if (name == "$dumpportsflush") {
    // §21.7.3.5: push the buffered extended-VCD port values out to the dump
    // file, clearing the simulator's VCD buffer so a reader sees everything
    // dumped so far while the simulation keeps running. The optional filename
    // argument denotes the $dumpports output to flush; with this single-file
    // writer it selects that one dump, and with no filename the buffers for
    // every file opened by $dumpports are flushed. Either way the one writer is
    // flushed, so the filename is parsed but does not change which dump is
    // emptied. The flush reuses the buffer-flushing machinery the extended VCD
    // file inherits (§21.7.1.6): no VCD command is written and the dump state is
    // left untouched so dumping continues exactly as before.
    if (vcd) vcd->Flush();
  }
  return MakeLogic4VecVal(arena, 1, 0);
}

static bool IsMathSysCall(std::string_view n) {
  return n == "$ln" || n == "$log10" || n == "$exp" || n == "$sqrt" ||
         n == "$pow" || n == "$floor" || n == "$ceil" || n == "$sin" ||
         n == "$cos" || n == "$tan" || n == "$asin" || n == "$acos" ||
         n == "$atan" || n == "$atan2" || n == "$hypot" || n == "$sinh" ||
         n == "$cosh" || n == "$tanh" || n == "$asinh" || n == "$acosh" ||
         n == "$atanh" || n == "$dist_uniform" || n == "$dist_normal" ||
         n == "$dist_exponential" || n == "$dist_poisson" ||
         n == "$dist_chi_square" || n == "$dist_t" || n == "$dist_erlang";
}

static bool IsExtFileIOSysCall(std::string_view n) {
  return n == "$fgets" || n == "$fgetc" || n == "$fflush" || n == "$feof" ||
         n == "$ferror" || n == "$fseek" || n == "$ftell" || n == "$rewind" ||
         n == "$ungetc" || n == "$fscanf" || n == "$fread";
}

// §20.3.1: $time reports the current simulation time as a 64-bit integer
// expressed in the time unit of the module that invoked it. The scheduler
// keeps time in ticks of the global precision (the finest precision in the
// design), so converting to the invoking module's unit divides the tick count
// by the number of precision steps that make up one unit. Because $time has an
// integer return type, the quotient is rounded to the nearest integer; the
// design's time precision itself plays no part in that rounding.
static uint64_t CurrentTimeInModuleUnits(SimContext& ctx) {
  uint64_t ticks = ctx.CurrentTime().ticks;
  const TimeScale& scale = ctx.CurrentTimeScale();
  int unit_order = EffectiveTimeOrder(scale.unit, scale.magnitude);
  int prec_order = static_cast<int>(ctx.StepTimeUnit());
  int exp = unit_order - prec_order;  // >= 0: the unit is no finer than a tick
  if (exp <= 0) return ticks;
  uint64_t steps_per_unit = 1;
  for (int i = 0; i < exp; ++i) steps_per_unit *= 10;
  return (ticks + steps_per_unit / 2) / steps_per_unit;  // round to nearest
}

// §20.3.3: $realtime reports the current simulation time scaled to the
// invoking module's time unit just as $time does, but the result is a real
// number rather than an integer. Because the return type is real, the scaled
// value keeps its fractional part instead of being rounded to the nearest
// integer (e.g. a 16 ns time under a 10 ns unit yields 1.6, not 2).
static double CurrentTimeInModuleUnitsReal(SimContext& ctx) {
  uint64_t ticks = ctx.CurrentTime().ticks;
  const TimeScale& scale = ctx.CurrentTimeScale();
  int unit_order = EffectiveTimeOrder(scale.unit, scale.magnitude);
  int prec_order = static_cast<int>(ctx.StepTimeUnit());
  int exp = unit_order - prec_order;  // >= 0: the unit is no finer than a tick
  if (exp <= 0) return static_cast<double>(ticks);
  double steps_per_unit = 1.0;
  for (int i = 0; i < exp; ++i) steps_per_unit *= 10.0;
  return static_cast<double>(ticks) / steps_per_unit;
}

static Logic4Vec EvalTimeSysCall(SimContext& ctx, Arena& arena,
                                 std::string_view name) {
  if (name == "$stime") {
    // §20.3.2: $stime reports the current time scaled to the invoking module's
    // time unit just as $time does, but as an unsigned 32-bit value. When the
    // scaled time does not fit in 32 bits, only its low-order 32 bits are
    // returned; the 32-bit result width performs that truncation.
    return MakeLogic4VecVal(arena, 32, CurrentTimeInModuleUnits(ctx));
  }
  if (name == "$realtime") {
    double scaled = CurrentTimeInModuleUnitsReal(ctx);
    uint64_t bits = 0;
    std::memcpy(&bits, &scaled, sizeof(double));
    auto result = MakeLogic4VecVal(arena, 64, bits);
    result.is_real = true;
    return result;
  }
  if (name == "$time") {
    return MakeLogic4VecVal(arena, 64, CurrentTimeInModuleUnits(ctx));
  }
  return MakeLogic4VecVal(arena, 64, ctx.CurrentTime().ticks);
}

// Extract the design-element name an argument to $timeunit/$timeprecision
// refers to. Bare $root/$unit are modeled by the parser as argument-less
// system calls; an ordinary hierarchical reference is an identifier.
static std::string_view TimescaleArgName(const Expr* arg) {
  if (arg->kind == ExprKind::kSystemCall) return arg->callee;
  if (arg->kind == ExprKind::kIdentifier) {
    return arg->scope_prefix.empty() ? arg->text : arg->scope_prefix;
  }
  return {};
}

// §20.4.1: $timeunit and $timeprecision return the time unit or precision of a
// design element, encoded as the base-10 order from Table 20-2 (an integer in
// the range 2 to -15). With no argument the current scope is reported; an
// argument names the design element, $unit names the compilation unit, and
// $root yields the simulation time unit for both functions (see 3.14.3).
static Logic4Vec EvalTimescaleQuery(const Expr* expr, SimContext& ctx,
                                    Arena& arena, std::string_view name) {
  bool want_precision = (name == "$timeprecision");
  const TimeScale* scale = &ctx.CurrentTimeScale();
  bool use_sim_time_unit = false;
  if (!expr->args.empty() && expr->args[0] != nullptr) {
    std::string_view target = TimescaleArgName(expr->args[0]);
    if (target == "$root") {
      use_sim_time_unit = true;
    } else if (target == "$unit") {
      scale = &ctx.CompUnitTimeScale();
    } else if (const TimeScale* found = ctx.FindScopeTimeScale(target)) {
      scale = found;
    }
  }
  int order;
  if (use_sim_time_unit) {
    order = static_cast<int>(ctx.StepTimeUnit());
  } else if (want_precision) {
    order = EffectiveTimeOrder(scale->precision, scale->prec_magnitude);
  } else {
    order = EffectiveTimeOrder(scale->unit, scale->magnitude);
  }
  auto result = MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(order));
  result.is_signed = true;
  return result;
}

static Logic4Vec EvalSystemCommand(const Expr* expr, Arena& arena) {
  int ret;
  if (expr->args.empty()) {
    // §20.17.1: invoked with no string argument, $system calls the C system()
    // with the NULL string rather than executing any command.
    ret = std::system(nullptr);
  } else {
    auto text = expr->args[0]->text;
    std::string cmd;
    if (text.size() >= 2 && text.front() == '"') {
      cmd = std::string(text.substr(1, text.size() - 2));
    } else {
      cmd = std::string(text);
    }
    // §20.17.1: the argument is handed to C system() as if executed from the
    // terminal.
    ret = std::system(cmd.c_str());
  }
  // §20.17.1: as a function, $system returns the system() result with the
  // signed data type int.
  auto result = MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(ret));
  result.is_signed = true;
  return result;
}

// §20.17.2: build the call-stack text reported by $stacktrace. The chain runs
// from the context that invoked $stacktrace up to the top-level process, so the
// innermost active subroutine is listed first and each enclosing caller follows
// on its own line. The exact content is implementation dependent; here it is
// the names of the subroutine frames currently on the call stack.
std::string BuildStackTraceReport(const SimContext& ctx) {
  const auto& frames = ctx.FuncNameStack();
  std::string report;
  for (auto it = frames.rbegin(); it != frames.rend(); ++it) {
    if (!report.empty()) report += '\n';
    report += std::string(*it);
  }
  return report;
}

static bool IsUtilitySysCall(std::string_view n) {
  return n == "$clog2" || n == "$bits" || n == "$unsigned" || n == "$signed" ||
         n == "$countones" || n == "$onehot" || n == "$onehot0" ||
         n == "$isunknown" || n == "$isunbounded" || n == "$cast" ||
         n == "$test$plusargs" || n == "$value$plusargs" || n == "$typename" ||
         n == "$sformatf" || n == "$itor" || n == "$rtoi" ||
         n == "$bitstoreal" || n == "$realtobits" || n == "$countbits" ||
         n == "$shortrealtobits" || n == "$bitstoshortreal";
}

static bool IsArrayQuerySysCall(std::string_view n) {
  return n == "$dimensions" || n == "$unpacked_dimensions" || n == "$left" ||
         n == "$right" || n == "$low" || n == "$high" || n == "$increment" ||
         n == "$size";
}

static bool IsVerifSysCall(std::string_view n) {
  // §16.9.4: the global clocking sampled value functions all carry the `_gclk`
  // suffix ($past_gclk, $rose_gclk, …, $changing_gclk).
  return n == "$sampled" || n == "$rose" || n == "$fell" || n == "$stable" ||
         n == "$past" || n == "$changed" || n.ends_with("_gclk") ||
         n.starts_with("$assert") || n.starts_with("$coverage") ||
         n.starts_with("$q_") || n.starts_with("$async$") ||
         n.starts_with("$sync$");
}

static bool IsIOSysCall(std::string_view n) {
  if (n == "$fopen" || n == "$fclose" || n == "$readmemh" ||
      n == "$readmemb" || n == "$writememh" || n == "$writememb" ||
      n == "$sscanf") {
    return true;
  }
  // §21.3.3: the variable-targeted output tasks share the IO syscall path
  // with their $fwrite / $fdisplay counterparts.
  if (n == "$swrite" || n == "$swriteb" || n == "$swriteh" || n == "$swriteo" ||
      n == "$sformat") {
    return true;
  }
  // §21.3.2 file-output tasks: $fdisplay, $fwrite, $fstrobe, $fmonitor and
  // their b/h/o radix variants.
  for (auto base : {"$fdisplay", "$fwrite", "$fstrobe", "$fmonitor"}) {
    if (n == base) return true;
    std::string_view base_view = base;
    if (n.size() == base_view.size() + 1 &&
        n.substr(0, base_view.size()) == base_view) {
      char c = n.back();
      if (c == 'b' || c == 'h' || c == 'o') return true;
    }
  }
  return false;
}

// Render a Table 20-2 base-10 order (in the range 2 .. -15) as the
// magnitude-and-unit text used in $printtimescale output, e.g. -7 -> "100ns",
// -12 -> "1ps", -15 -> "1fs". The SI unit comes from the nearest multiple of
// three at or below the order; the remainder selects the 1/10/100 mantissa.
static std::string TimeOrderToUnitString(int order) {
  int base = (order >= 0) ? (order / 3) * 3 : -(((-order) + 2) / 3) * 3;
  int diff = order - base;  // 0, 1, or 2
  const char* mantissa = diff == 2 ? "100" : (diff == 1 ? "10" : "1");
  const char* unit;
  switch (base) {
    case 0: unit = "s"; break;
    case -3: unit = "ms"; break;
    case -6: unit = "us"; break;
    case -9: unit = "ns"; break;
    case -12: unit = "ps"; break;
    default: unit = "fs"; break;  // -15
  }
  return std::string(mantissa) + unit;
}

// §20.4.2: assemble the line $printtimescale displays for `expr`, reading the
// timescale model in `ctx`. The output names the targeted design element and
// reports its time unit and precision in the fixed format
// "Time scale of (<name>) is <unit> / <precision>". With no argument the
// current scope is described; a named argument selects that element; the
// special $unit and $root arguments select the compilation unit and the
// simulation time unit, and in those two cases the literal "$unit"/"$root" is
// shown in place of a design-element name.
std::string BuildPrinttimescaleReport(const Expr* expr, SimContext& ctx) {
  std::string name;
  const TimeScale* scale = &ctx.CurrentTimeScale();
  bool use_sim_time_unit = false;
  if (!expr->args.empty() && expr->args[0] != nullptr) {
    std::string_view target = TimescaleArgName(expr->args[0]);
    if (target == "$root") {
      use_sim_time_unit = true;
      name = "$root";
    } else if (target == "$unit") {
      scale = &ctx.CompUnitTimeScale();
      name = "$unit";
    } else {
      name = std::string(target);
      if (const TimeScale* found = ctx.FindScopeTimeScale(target)) scale = found;
    }
  } else {
    name = ctx.CurrentScopeName();
  }
  int unit_order;
  int prec_order;
  if (use_sim_time_unit) {
    // The simulation time unit and the global precision are synonymous, so
    // $root reports the same value for both fields (see 3.14.3).
    unit_order = static_cast<int>(ctx.StepTimeUnit());
    prec_order = unit_order;
  } else {
    unit_order = EffectiveTimeOrder(scale->unit, scale->magnitude);
    prec_order = EffectiveTimeOrder(scale->precision, scale->prec_magnitude);
  }
  return "Time scale of (" + name + ") is " + TimeOrderToUnitString(unit_order) +
         " / " + TimeOrderToUnitString(prec_order);
}

static Logic4Vec EvalPrinttimescaleTask(const Expr* expr, SimContext& ctx,
                                        Arena& arena) {
  std::cout << BuildPrinttimescaleReport(expr, ctx) << "\n";
  return MakeLogic4VecVal(arena, 1, 0);
}

// $timeformat (20.4.3) shall accept units_number and precision_number values
// in the Table 20-2 range from 2 to -15; out-of-range integers are rejected
// and the configured state is left untouched.
static bool TimeformatRangeOk(int64_t v) { return v <= 2 && v >= -15; }

static std::string ExtractStringArg(const Expr* arg) {
  if (!arg) return {};
  auto text = arg->text;
  if (text.size() >= 2 && text.front() == '"' && text.back() == '"') {
    return std::string(text.substr(1, text.size() - 2));
  }
  return std::string(text);
}

static Logic4Vec EvalTimeformatTask(const Expr* expr, SimContext& ctx,
                                    Arena& arena) {
  // Bare $timeformat with no parens block leaves the configured state alone.
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 1, 0);

  TimeFormatSpec spec = ctx.GetTimeFormat();
  if (expr->args.size() >= 1 && expr->args[0]) {
    auto v = static_cast<int64_t>(
        EvalExpr(expr->args[0], ctx, arena).ToUint64());
    // The value arrives as an unsigned 64-bit word, so widen the negative
    // 32-bit pattern back into a signed integer for the range check.
    int32_t units = static_cast<int32_t>(v);
    if (!TimeformatRangeOk(units)) {
      ctx.GetDiag().Error(
          {}, "$timeformat units_number out of range [2 .. -15]");
      return MakeLogic4VecVal(arena, 1, 0);
    }
    spec.units_number = units;
  }
  if (expr->args.size() >= 2 && expr->args[1]) {
    auto v = static_cast<int64_t>(
        EvalExpr(expr->args[1], ctx, arena).ToUint64());
    int32_t prec = static_cast<int32_t>(v);
    if (!TimeformatRangeOk(prec)) {
      ctx.GetDiag().Error(
          {}, "$timeformat precision_number out of range [2 .. -15]");
      return MakeLogic4VecVal(arena, 1, 0);
    }
    spec.precision_number = prec;
  }
  if (expr->args.size() >= 3 && expr->args[2]) {
    if (expr->args[2]->kind == ExprKind::kStringLiteral) {
      spec.suffix_string = ExtractStringArg(expr->args[2]);
    } else {
      spec.suffix_string =
          FormatValueAsString(EvalExpr(expr->args[2], ctx, arena));
    }
  }
  if (expr->args.size() >= 4 && expr->args[3]) {
    auto v = static_cast<int64_t>(
        EvalExpr(expr->args[3], ctx, arena).ToUint64());
    spec.minimum_field_width = static_cast<int>(v);
  }
  ctx.SetTimeFormat(spec);
  return MakeLogic4VecVal(arena, 1, 0);
}

static Logic4Vec EvalMiscSysCall(const Expr* expr, SimContext& ctx,
                                 Arena& arena, std::string_view name) {
  if (name == "$time" || name == "$stime" || name == "$realtime") {
    return EvalTimeSysCall(ctx, arena, name);
  }
  if (name == "$timeunit" || name == "$timeprecision") {
    return EvalTimescaleQuery(expr, ctx, arena, name);
  }
  if (IsStrobeTask(name)) {
    return EvalDeferredPrint(expr, ctx, arena);
  }
  if (IsMonitorTask(name)) return EvalMonitor(expr, ctx, arena);
  if (name == "$monitoron" || name == "$monitoroff") {
    return EvalMonitorFlag(ctx, arena, name);
  }
  if (name == "$timeformat") return EvalTimeformatTask(expr, ctx, arena);
  if (name == "$printtimescale")
    return EvalPrinttimescaleTask(expr, ctx, arena);
  if (name == "$system") return EvalSystemCommand(expr, arena);
  // §20.17.2: called as a function, $stacktrace returns a string holding the
  // call stack of the invoking context. (The task form, which displays the
  // same information, is handled where statements execute.)
  if (name == "$stacktrace") {
    return StringToLogic4Vec(arena, BuildStackTraceReport(ctx));
  }
  if (name.starts_with("$dump")) return EvalVcdSysCall(expr, ctx, arena, name);
  if (IsMathSysCall(name)) return EvalMathSysCall(expr, ctx, arena, name);
  if (IsUtilitySysCall(name)) return EvalUtilitySysCall(expr, ctx, arena, name);
  if (IsIOSysCall(name)) return EvalIOSysCall(expr, ctx, arena, name);
  if (IsExtFileIOSysCall(name))
    return EvalFileIOSysCall(expr, ctx, arena, name);
  if (IsArrayQuerySysCall(name))
    return EvalArrayQuerySysCall(expr, ctx, arena, name);
  if (IsVerifSysCall(name)) return EvalVerifSysCall(expr, ctx, arena, name);
  return EvalPrngCall(expr, ctx, arena, name);
}

static Logic4Vec EvalSeveritySysCall(const Expr* expr, SimContext& ctx,
                                     Arena& arena, std::string_view name) {
  if (name == "$fatal") {
    ExecSeverityTask(expr, ctx, arena, "FATAL", std::cerr);
    ctx.RequestStop();
  } else if (name == "$error") {
    ExecSeverityTask(expr, ctx, arena, "ERROR", std::cerr);
  } else if (name == "$warning") {
    ExecSeverityTask(expr, ctx, arena, "WARNING", std::cout);
  } else if (name == "$info") {
    ExecSeverityTask(expr, ctx, arena, "INFO", std::cout);
  }
  return MakeLogic4VecVal(arena, 1, 0);
}

// Annex D.11: the argument to $scope is a complete hierarchical name. Rebuild
// that name as a string from its expression form (a bare or scoped identifier,
// or a dotted member-access chain) without evaluating it, since it names a
// level of hierarchy rather than a readable object.
static std::string HierarchicalScopeName(const Expr* e) {
  if (!e) return {};
  switch (e->kind) {
    case ExprKind::kIdentifier: {
      std::string s;
      if (!e->scope_prefix.empty()) {
        s += std::string(e->scope_prefix);
        s += (e->scope_prefix == "$unit") ? "::" : ".";
      }
      s += std::string(e->text);
      return s;
    }
    case ExprKind::kMemberAccess:
      return HierarchicalScopeName(e->lhs) + "." +
             (e->rhs ? std::string(e->rhs->text) : std::string());
    default:
      return std::string(e->text);
  }
}

// Annex D.13: each entry in the $showvars variable list names a variable, or a
// bit-select or part-select of one. Because the status of every bit of a
// selected vector is displayed, a selection is reduced to the name of the
// vector it selects from; a plain reference keeps its own name. Either way the
// name is rebuilt from the expression without evaluating it.
static std::string ShowVarsVariableName(const Expr* e) {
  if (!e) return {};
  if (e->kind == ExprKind::kSelect) {
    return ShowVarsVariableName(e->base);
  }
  return HierarchicalScopeName(e);
}

// Annex D.10: $scale converts a time value held in one module into the time
// unit of the module that invokes $scale. The argument is the complete
// hierarchical name of the source value: the hierarchy above the final
// component names the source module, whose time unit applies to the raw value,
// and the final component names the value itself. The result is that value
// rescaled by the ratio of the source time unit to the invoking module's time
// unit, so a value expressed in a coarser unit grows and one expressed in a
// finer unit shrinks. A bare name carries no enclosing module of its own, so
// the invoking module's unit applies on both sides and the value passes through
// unchanged.
static Logic4Vec EvalScale(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty() || expr->args[0] == nullptr) {
    return MakeLogic4VecVal(arena, 64, 0);
  }
  const Expr* arg = expr->args[0];
  uint64_t raw = EvalExpr(arg, ctx, arena).ToUint64();

  const TimeScale& dst = ctx.CurrentTimeScale();
  const TimeScale* src = &dst;
  if (arg->kind == ExprKind::kMemberAccess) {
    std::string source_scope = HierarchicalScopeName(arg->lhs);
    if (const TimeScale* found = ctx.FindScopeTimeScale(source_scope)) {
      src = found;
    }
  }

  // EffectiveTimeOrder yields the base-10 order of each unit (Table 20-2), so
  // their difference is the power of ten relating the two units.
  int order_diff = EffectiveTimeOrder(src->unit, src->magnitude) -
                   EffectiveTimeOrder(dst.unit, dst.magnitude);
  uint64_t result = raw;
  if (order_diff > 0) {
    for (int i = 0; i < order_diff; ++i) result *= 10;
  } else if (order_diff < 0) {
    for (int i = 0; i < -order_diff; ++i) result /= 10;
  }
  return MakeLogic4VecVal(arena, 64, result);
}

// §20.2 / Table 20-1: $stop and $finish accept an optional diagnostic level
// argument (0, 1, or 2) that selects how much information accompanies the
// control action. Level 0 prints nothing; level 1 reports the simulation time
// and the controlling task (its location); level 2 additionally summarizes the
// memory and CPU time used by the run. When no argument is supplied the level
// defaults to 1.
static void EmitSimControlDiagnostic(const Expr* expr, SimContext& ctx,
                                     Arena& arena, std::string_view task,
                                     std::ostream& os) {
  int64_t level = 1;
  if (!expr->args.empty() && expr->args[0]) {
    level =
        static_cast<int64_t>(EvalExpr(expr->args[0], ctx, arena).ToUint64());
  }
  if (level <= 0) return;
  os << task << " at time " << ctx.CurrentTime().ticks << "\n";
  if (level >= 2) {
    os << task << ": memory and CPU time statistics unavailable\n";
  }
}

Logic4Vec EvalSystemCall(const Expr* expr, SimContext& ctx, Arena& arena) {
  auto name = expr->callee;

  // §20.16.1: a PLA modeling system task evaluates the array and drives its
  // output terms; it produces no value of its own.
  if (TryEvalPlaSystemTask(expr, ctx, arena)) {
    return MakeLogic4VecVal(arena, 1, 0);
  }

  if (IsDisplayOrWriteTask(name)) {
    ExecDisplayWrite(expr, ctx, arena);
    return MakeLogic4VecVal(arena, 1, 0);
  }
  // §20.2: $stop suspends the run and $finish ends it, returning control to the
  // host; both honor the Table 20-1 diagnostic level before halting.
  if (name == "$finish" || name == "$stop") {
    EmitSimControlDiagnostic(expr, ctx, arena, name, std::cout);
    ctx.RequestStop();
    return MakeLogic4VecVal(arena, 1, 0);
  }
  // Optional $reset family (Annex D.8). $reset tallies a reset of the tool and
  // captures its reset_value argument (the second argument, after stop_value)
  // so that the value can be communicated to after the reset; the other
  // arguments are accepted but carry no observable state here.
  if (name == "$reset") {
    int64_t reset_value = 0;
    if (expr->args.size() > 1 && expr->args[1]) {
      reset_value =
          static_cast<int64_t>(EvalExpr(expr->args[1], ctx, arena).ToUint64());
    }
    ctx.RecordReset(reset_value);
    return MakeLogic4VecVal(arena, 1, 0);
  }
  // $reset_count reports how many times the tool has been reset.
  if (name == "$reset_count") {
    return MakeLogic4VecVal(arena, 32, ctx.ResetCount());
  }
  // $reset_value returns the reset_value argument supplied to the last $reset.
  if (name == "$reset_value") {
    return MakeLogic4VecVal(arena, 32,
                            static_cast<uint64_t>(ctx.ResetValue()));
  }
  // Optional $scope system task (Annex D.11). It selects a level of hierarchy as
  // the interactive scope used to identify objects. Its single argument is the
  // complete hierarchical name of a module, task, function, or named block;
  // record that name as the new interactive scope.
  if (name == "$scope") {
    if (!expr->args.empty() && expr->args[0]) {
      ctx.SetInteractiveScope(HierarchicalScopeName(expr->args[0]));
    }
    return MakeLogic4VecVal(arena, 1, 0);
  }
  // Optional $list system task (Annex D.6). It produces a listing of a module,
  // task, function, or named block. With no argument the object listed is the
  // current scope setting (the interactive scope established by $scope); with an
  // argument, the argument is the complete hierarchical name of the specific
  // scope to list. Resolve which scope is selected and record it.
  if (name == "$list") {
    std::string target = (!expr->args.empty() && expr->args[0])
                             ? HierarchicalScopeName(expr->args[0])
                             : ctx.InteractiveScope();
    ctx.RecordListing(target);
    return MakeLogic4VecVal(arena, 1, 0);
  }
  // Optional $showscopes system task (Annex D.12). It produces a complete list
  // of the modules, tasks, functions, and named blocks defined at the current
  // scope level (the interactive scope established by $scope). An optional
  // integer argument widens the listing: a nonzero value lists every such object
  // in or below the current hierarchical scope, while no argument or a zero
  // value lists only the objects at the current scope level itself. Evaluate the
  // optional argument to decide the depth and record the request.
  if (name == "$showscopes") {
    bool recursive = false;
    if (!expr->args.empty() && expr->args[0]) {
      recursive = EvalExpr(expr->args[0], ctx, arena).ToUint64() != 0;
    }
    ctx.RecordShowScopes(ctx.InteractiveScope(), recursive);
    return MakeLogic4VecVal(arena, 1, 0);
  }
  // Optional $showvars system task (Annex D.13). It produces status information
  // for the reg and net variables, scalar and vector, in the current scope (the
  // interactive scope established by $scope). With no argument every variable in
  // that scope is reported; with a list of variables only the named ones are. A
  // bit-select or part-select of a vector reports the status of all bits of that
  // vector, so such a selection is reduced to the name of its underlying vector.
  // Collect the requested variable names and record the request against the
  // current scope.
  if (name == "$showvars") {
    std::vector<std::string> vars;
    for (const Expr* arg : expr->args) {
      if (arg) vars.push_back(ShowVarsVariableName(arg));
    }
    ctx.RecordShowVars(ctx.InteractiveScope(), std::move(vars));
    return MakeLogic4VecVal(arena, 1, 0);
  }
  // Optional $nolog and $log system tasks (Annex D.7). The log file holds a
  // copy of everything printed to standard output. $nolog disables that copy;
  // $log reenables it. An optional filename argument to $log closes the current
  // log file and starts a new one, directing subsequent output there.
  if (name == "$nolog") {
    ctx.DisableLogging();
    return MakeLogic4VecVal(arena, 1, 0);
  }
  if (name == "$log") {
    if (!expr->args.empty() && expr->args[0]) {
      ctx.SetLogFile(ExtractStringArg(expr->args[0]));
    } else {
      ctx.EnableLogging();
    }
    return MakeLogic4VecVal(arena, 1, 0);
  }
  // Optional $scale function (Annex D.10). It reads the time value named by a
  // hierarchical reference and converts it from the time unit of the module
  // that holds it to the time unit of the module that invokes $scale.
  if (name == "$scale") {
    return EvalScale(expr, ctx, arena);
  }
  if (name == "$exit") {

    auto* cur = ctx.CurrentProcess();
    if (cur && cur->program_block_id != 0) {
      ctx.ExitProgramBlock(cur->program_block_id);
    }
    return MakeLogic4VecVal(arena, 1, 0);
  }
  if (name == "$fatal" || name == "$error" || name == "$warning" ||
      name == "$info") {
    return EvalSeveritySysCall(expr, ctx, arena, name);
  }
  return EvalMiscSysCall(expr, ctx, arena, name);
}

static int ResolveArgIndex(const ModuleItem* func, const Expr* expr,
                           size_t param_idx) {
  if (expr->arg_names.empty()) {
    return (param_idx < expr->args.size()) ? static_cast<int>(param_idx) : -1;
  }

  size_t positional_count = expr->args.size() - expr->arg_names.size();
  if (param_idx < positional_count) {
    return static_cast<int>(param_idx);
  }
  auto param_name = func->func_args[param_idx].name;
  for (size_t j = 0; j < expr->arg_names.size(); ++j) {
    if (expr->arg_names[j] == param_name)
      return static_cast<int>(positional_count + j);
  }
  return -1;
}

static bool TryBindRefArg(const Expr* expr, int arg_index,
                          std::string_view param_name, SimContext& ctx) {
  if (arg_index < 0) return false;
  auto* call_arg = expr->args[static_cast<size_t>(arg_index)];
  if (!call_arg) return false;
  if (call_arg->kind != ExprKind::kIdentifier) return false;
  auto* target = ctx.FindVariable(call_arg->text);
  if (!target) return false;
  ctx.AliasLocalVariable(param_name, target);
  return true;
}

static bool TryBindQueueElementRef(const Expr* expr, int arg_index,
                                   const FunctionArg& param, SimContext& ctx,
                                   Arena& arena) {
  if (arg_index < 0) return false;
  auto* call_arg = expr->args[static_cast<size_t>(arg_index)];
  if (!call_arg) return false;
  if (call_arg->kind != ExprKind::kSelect) return false;
  if (!call_arg->base || call_arg->base->kind != ExprKind::kIdentifier)
    return false;
  auto* q = ctx.FindQueue(call_arg->base->text);
  if (!q || !call_arg->index) return false;
  auto idx = EvalExpr(call_arg->index, ctx, arena).ToUint64();
  if (idx >= q->elements.size()) return false;

  if (param.data_type.kind != DataTypeKind::kImplicit) {
    uint32_t param_width = EvalTypeWidth(param.data_type);
    if (param_width != q->elem_width) return false;
  }

  auto* var = ctx.CreateLocalVariable(param.name, q->elem_width);
  var->value = q->elements[idx];

  if (idx < q->element_ids.size()) {
    ctx.RecordQueueRef({q, q->element_ids[idx], var});
  }
  return true;
}

static void WritebackQueueRefs(SimContext& ctx) {
  auto bindings = ctx.PopQueueRefFrame();
  for (const auto& b : bindings) {
    auto& ids = b.queue->element_ids;
    auto it = std::find(ids.begin(), ids.end(), b.element_id);
    if (it == ids.end()) continue;
    auto pos = static_cast<size_t>(it - ids.begin());
    if (pos < b.queue->elements.size()) {
      b.queue->elements[pos] = b.local_var->value;
    }
  }
}

static bool TryBindAssocElementRef(const Expr* expr, int arg_index,
                                   const FunctionArg& param, SimContext& ctx,
                                   Arena& arena) {
  if (arg_index < 0) return false;
  auto* call_arg = expr->args[static_cast<size_t>(arg_index)];
  if (!call_arg) return false;
  if (call_arg->kind != ExprKind::kSelect) return false;
  if (!call_arg->base || call_arg->base->kind != ExprKind::kIdentifier)
    return false;
  auto* aa = ctx.FindAssocArray(call_arg->base->text);
  if (!aa || !call_arg->index) return false;

  auto* var = ctx.CreateLocalVariable(param.name, aa->elem_width);

  AssocRefBinding binding;
  binding.assoc = aa;
  binding.is_string_key = aa->is_string_key;
  binding.local_var = var;
  if (aa->is_string_key) {
    binding.str_key = FormatValueAsString(EvalExpr(call_arg->index, ctx, arena));
    auto it = aa->str_data.find(binding.str_key);
    if (it == aa->str_data.end()) {
      aa->str_data[binding.str_key] = MakeLogic4Vec(arena, aa->elem_width);
      it = aa->str_data.find(binding.str_key);
    }
    var->value = it->second;
  } else {
    binding.int_key =
        static_cast<int64_t>(EvalExpr(call_arg->index, ctx, arena).ToUint64());
    auto it = aa->int_data.find(binding.int_key);
    if (it == aa->int_data.end()) {
      aa->int_data[binding.int_key] = MakeLogic4Vec(arena, aa->elem_width);
      it = aa->int_data.find(binding.int_key);
    }
    var->value = it->second;
  }
  ctx.RecordAssocRef(binding);
  return true;
}

static void WritebackAssocRefs(SimContext& ctx) {
  auto bindings = ctx.PopAssocRefFrame();
  for (const auto& b : bindings) {
    if (b.is_string_key) {
      b.assoc->str_data[b.str_key] = b.local_var->value;
    } else {
      b.assoc->int_data[b.int_key] = b.local_var->value;
    }
  }
}

static Logic4Vec ResolveArgValue(const FunctionArg& param, const Expr* expr,
                                 int arg_index, SimContext& ctx, Arena& arena) {
  if (arg_index >= 0 && expr->args[static_cast<size_t>(arg_index)] != nullptr) {
    return EvalExpr(expr->args[static_cast<size_t>(arg_index)], ctx, arena);
  }
  if (param.default_value) return EvalExpr(param.default_value, ctx, arena);
  return MakeLogic4Vec(arena, 32);
}

static bool TryBindAssocArg(const Expr* call_arg, std::string_view param_name,
                            SimContext& ctx) {
  if (!call_arg || call_arg->kind != ExprKind::kIdentifier) return false;
  auto* src = ctx.FindAssocArray(call_arg->text);
  if (!src) return false;
  auto* dst =
      ctx.CreateAssocArray(param_name, src->elem_width, src->is_string_key);
  dst->int_data = src->int_data;
  dst->str_data = src->str_data;
  dst->has_default = src->has_default;
  dst->default_value = src->default_value;
  dst->index_width = src->index_width;
  dst->is_wildcard = src->is_wildcard;
  dst->is_4state = src->is_4state;
  return true;
}

static bool TryBindArrayArg(const Expr* call_arg, const FunctionArg& formal,
                            SimContext& ctx, Arena& arena) {
  if (!call_arg || call_arg->kind != ExprKind::kIdentifier) return false;
  if (TryBindAssocArg(call_arg, formal.name, ctx)) return true;

  // Dynamic arrays and queues hold their elements in a QueueObject rather than
  // as per-element variables, so a by-value bind copies through that object;
  // the formal becomes a fresh, independent copy of the actual.
  if (auto* src_q = ctx.FindQueue(call_arg->text)) {
    if (formal.unpacked_dims.empty()) return false;
    if (formal.unpacked_dims[0] != nullptr) {
      // A fixed-size formal accepts a dynamic array or queue only when the
      // sizes are equal; this can only be verified at the time of the call.
      auto formal_size =
          EvalExpr(formal.unpacked_dims[0], ctx, arena).ToUint64();
      if (src_q->elements.size() != formal_size) {
        ctx.GetDiag().Error(
            {}, "array size mismatch: formal expects " +
                    std::to_string(formal_size) + " elements, actual has " +
                    std::to_string(src_q->elements.size()));
        return true;
      }
      ArrayInfo finfo;
      finfo.size = static_cast<uint32_t>(formal_size);
      finfo.elem_width = src_q->elem_width;
      finfo.is_4state = src_q->is_4state;
      ctx.RegisterArray(formal.name, finfo);
      for (uint32_t j = 0; j < finfo.size; ++j) {
        auto dst = std::string(formal.name) + "[" + std::to_string(j) + "]";
        auto* dst_var = ctx.CreateLocalVariable(
            *arena.Create<std::string>(std::move(dst)),
            src_q->elements[j].width);
        dst_var->value = src_q->elements[j];
      }
      return true;
    }
    // An unsized formal keeps the dynamic-array/queue representation, so the
    // callee reads the copy through the same queue-backed select path.
    auto* dst_q = ctx.CreateQueue(formal.name, src_q->elem_width,
                                  src_q->max_size, src_q->is_4state);
    dst_q->elements = src_q->elements;
    dst_q->AssignFreshIds();
    return true;
  }

  auto* info = ctx.FindArrayInfo(call_arg->text);
  if (!info) return false;

  ctx.RegisterArray(formal.name, *info);
  for (uint32_t j = 0; j < info->size; ++j) {
    uint32_t idx = info->lo + j;
    auto src = std::string(call_arg->text) + "[" + std::to_string(idx) + "]";
    auto dst = std::string(formal.name) + "[" + std::to_string(idx) + "]";
    auto* src_var = ctx.FindVariable(src);
    auto val =
        src_var ? src_var->value : MakeLogic4VecVal(arena, info->elem_width, 0);
    auto* dst_var = ctx.CreateLocalVariable(
        *arena.Create<std::string>(std::move(dst)), val.width);
    dst_var->value = val;
  }
  return true;
}

static void BindFunctionArgs(const ModuleItem* func, const Expr* expr,
                             SimContext& ctx, Arena& arena) {
  for (size_t i = 0; i < func->func_args.size(); ++i) {
    int ai = ResolveArgIndex(func, expr, i);
    auto dir = func->func_args[i].direction;
    if (dir == Direction::kRef) {
      if (TryBindRefArg(expr, ai, func->func_args[i].name, ctx)) continue;
      if (TryBindQueueElementRef(expr, ai, func->func_args[i], ctx, arena))
        continue;
      if (TryBindAssocElementRef(expr, ai, func->func_args[i], ctx, arena))
        continue;
    }
    if (ai >= 0 && TryBindArrayArg(expr->args[static_cast<size_t>(ai)],
                                   func->func_args[i], ctx, arena)) {
      continue;
    }
    auto val = ResolveArgValue(func->func_args[i], expr, ai, ctx, arena);
    const auto& dt = func->func_args[i].data_type;
    if (dt.kind != DataTypeKind::kImplicit) {
      uint32_t formal_width = EvalTypeWidth(dt);
      if (formal_width > 0 && formal_width != val.width)
        val = ResizeToWidth(val, formal_width, arena);
    }
    auto* var = ctx.CreateLocalVariable(func->func_args[i].name, val.width);
    var->value = val;
  }
}

static void WritebackOutputArgs(const ModuleItem* func, const Expr* expr,
                                SimContext& ctx, Arena& arena) {
  for (size_t i = 0; i < func->func_args.size(); ++i) {
    auto dir = func->func_args[i].direction;
    if (dir != Direction::kOutput && dir != Direction::kInout) continue;
    auto* local = ctx.FindLocalVariable(func->func_args[i].name);
    if (!local) continue;
    int ai = ResolveArgIndex(func, expr, i);
    const Expr* wb_target = nullptr;
    if (ai >= 0) wb_target = expr->args[static_cast<size_t>(ai)];
    if (!wb_target) wb_target = func->func_args[i].default_value;
    if (!wb_target) continue;
    PerformBlockingAssign(wb_target, local->value, ctx, arena);
  }
}

static void ExecFuncSelectAssign(const Expr* lhs, const Logic4Vec& val,
                                 SimContext& ctx, Arena& arena) {
  if (!lhs->base || lhs->base->kind != ExprKind::kIdentifier) return;
  auto* aa = ctx.FindAssocArray(lhs->base->text);
  if (aa && lhs->index) {
    if (aa->is_string_key) {
      aa->str_data[FormatValueAsString(EvalExpr(lhs->index, ctx, arena))] = val;
    } else {
      auto key =
          static_cast<int64_t>(EvalExpr(lhs->index, ctx, arena).ToUint64());
      aa->int_data[key] = val;
    }
    return;
  }
  auto idx = EvalExpr(lhs->index, ctx, arena).ToUint64();
  auto name = std::string(lhs->base->text) + "[" + std::to_string(idx) + "]";
  auto* elem = ctx.FindVariable(name);
  if (elem) elem->value = val;
}

static void ExecFuncBlockingAssign(const Stmt* stmt, SimContext& ctx,
                                   Arena& arena) {
  if (!stmt->lhs) return;
  auto val = EvalExpr(stmt->rhs, ctx, arena);
  if (stmt->lhs->kind == ExprKind::kIdentifier) {
    auto* var = ctx.FindVariable(stmt->lhs->text);
    if (var) {
      var->value = val;
      return;
    }
    auto* self = ctx.CurrentThis();
    if (self) self->SetProperty(std::string(stmt->lhs->text), val);
    return;
  }
  if (stmt->lhs->kind == ExprKind::kSelect) {
    ExecFuncSelectAssign(stmt->lhs, val, ctx, arena);
    return;
  }

  if (stmt->lhs->kind == ExprKind::kMemberAccess && stmt->lhs->lhs &&
      stmt->lhs->lhs->kind == ExprKind::kIdentifier &&
      stmt->lhs->lhs->text == "this" && stmt->lhs->rhs &&
      stmt->lhs->rhs->kind == ExprKind::kIdentifier) {
    auto* self = ctx.CurrentThis();
    if (self) self->SetProperty(std::string(stmt->lhs->rhs->text), val);
    return;
  }

  if (stmt->lhs->kind == ExprKind::kMemberAccess && stmt->lhs->lhs &&
      stmt->lhs->lhs->kind == ExprKind::kIdentifier &&
      stmt->lhs->lhs->text == "super" && stmt->lhs->rhs &&
      stmt->lhs->rhs->kind == ExprKind::kIdentifier) {
    auto* self = ctx.CurrentThis();
    if (self && self->type && self->type->parent) {
      self->SetPropertyForType(std::string(stmt->lhs->rhs->text),
                               self->type->parent, val);
    }
  }
}

static bool ExecFuncStmt(const Stmt* stmt, Variable* ret_var,
                         std::string_view func_name, SimContext& ctx,
                         Arena& arena);
static bool ExecFuncBlock(const Stmt* stmt, Variable* ret_var,
                          std::string_view func_name, SimContext& ctx,
                          Arena& arena);

// Returns the trailing unconditional else of an if/else-if chain, or null when
// the chain has no final else.
static const Stmt* FuncFindFinalElse(const Stmt* stmt) {
  const Stmt* cur = stmt;
  while (cur->else_branch && cur->else_branch->kind == StmtKind::kIf) {
    cur = cur->else_branch;
  }
  return cur->else_branch;
}

// A unique/unique0/priority if encountered while running a function or task body
// performs the same violation checks as one in a process body (§12.4.2). Because
// the report queue is keyed on the calling process (§12.4.2.2), routing the
// report through AddPendingViolation attributes it to whichever process invoked
// the subroutine; separate callers therefore accumulate and flush independently.
static bool ExecFuncUniqueIf(const Stmt* stmt, CaseQualifier qual,
                             Variable* ret_var, std::string_view func_name,
                             SimContext& ctx, Arena& arena) {
  int match_count = 0;
  const Stmt* first_match = nullptr;
  bool has_final_else = false;
  for (const Stmt* cur = stmt; cur && cur->kind == StmtKind::kIf;
       cur = cur->else_branch) {
    if (EvalExpr(cur->condition, ctx, arena).IsTruthy()) {
      match_count++;
      if (!first_match) first_match = cur;
    }
    if (cur->else_branch && cur->else_branch->kind != StmtKind::kIf) {
      has_final_else = true;
    }
  }
  if (match_count > 1) {
    ctx.AddPendingViolation("unique if: multiple conditions matched");
  }
  if (first_match) {
    return ExecFuncStmt(first_match->then_branch, ret_var, func_name, ctx,
                        arena);
  }
  if (has_final_else) {
    const Stmt* final_else = FuncFindFinalElse(stmt);
    if (final_else)
      return ExecFuncStmt(final_else, ret_var, func_name, ctx, arena);
  } else if (qual == CaseQualifier::kUnique) {
    ctx.AddPendingViolation("unique if: no condition matched");
  }
  return false;
}

static bool ExecFuncPriorityIf(const Stmt* stmt, Variable* ret_var,
                               std::string_view func_name, SimContext& ctx,
                               Arena& arena) {
  bool has_final_else = false;
  for (const Stmt* cur = stmt; cur && cur->kind == StmtKind::kIf;
       cur = cur->else_branch) {
    if (EvalExpr(cur->condition, ctx, arena).IsTruthy()) {
      return ExecFuncStmt(cur->then_branch, ret_var, func_name, ctx, arena);
    }
    if (cur->else_branch && cur->else_branch->kind != StmtKind::kIf) {
      has_final_else = true;
    }
  }
  if (has_final_else) {
    const Stmt* final_else = FuncFindFinalElse(stmt);
    if (final_else)
      return ExecFuncStmt(final_else, ret_var, func_name, ctx, arena);
  } else {
    ctx.AddPendingViolation("priority if: no condition matched");
  }
  return false;
}

static bool ExecFuncIf(const Stmt* stmt, Variable* ret_var,
                       std::string_view func_name, SimContext& ctx,
                       Arena& arena) {
  bool labeled = !stmt->label.empty();
  if (labeled) ctx.PushStaticScope(stmt->label);

  auto qual = stmt->qualifier;
  bool r;
  if (qual == CaseQualifier::kUnique || qual == CaseQualifier::kUnique0) {
    r = ExecFuncUniqueIf(stmt, qual, ret_var, func_name, ctx, arena);
  } else if (qual == CaseQualifier::kPriority) {
    r = ExecFuncPriorityIf(stmt, ret_var, func_name, ctx, arena);
  } else {
    auto cond = EvalExpr(stmt->condition, ctx, arena);
    if (cond.ToUint64() != 0) {
      r = ExecFuncStmt(stmt->then_branch, ret_var, func_name, ctx, arena);
    } else if (stmt->else_branch) {
      r = ExecFuncStmt(stmt->else_branch, ret_var, func_name, ctx, arena);
    } else {
      r = false;
    }
  }

  if (labeled) ctx.PopStaticScope(stmt->label);
  return r;
}

static bool ExecFuncBlock(const Stmt* stmt, Variable* ret_var,
                          std::string_view func_name, SimContext& ctx,
                          Arena& arena) {
  bool named = !stmt->label.empty();
  if (named) ctx.PushStaticScope(stmt->label);
  for (auto* c : stmt->stmts) {
    if (ExecFuncStmt(c, ret_var, func_name, ctx, arena)) {
      if (named) ctx.PopStaticScope(stmt->label);
      return true;
    }
  }
  if (named) ctx.PopStaticScope(stmt->label);
  return false;
}

static bool ExecFuncFor(const Stmt* stmt, Variable* ret_var,
                        std::string_view func_name, SimContext& ctx,
                        Arena& arena) {
  bool labeled = !stmt->label.empty();
  if (labeled) ctx.PushStaticScope(stmt->label);
  bool scoped = false;
  for (const auto& t : stmt->for_init_types) {
    if (t.kind != DataTypeKind::kImplicit) { scoped = true; break; }
  }
  if (scoped) ctx.PushScope();
  for (size_t i = 0; i < stmt->for_inits.size(); ++i) {
    auto* init = stmt->for_inits[i];
    if (i < stmt->for_init_types.size() &&
        stmt->for_init_types[i].kind != DataTypeKind::kImplicit && init &&
        init->lhs && init->lhs->kind == ExprKind::kIdentifier) {
      uint32_t w = EvalTypeWidth(stmt->for_init_types[i]);
      if (w == 0) w = 32;
      auto* v = ctx.CreateLocalVariable(init->lhs->text, w);
      if (init->rhs) v->value = EvalExpr(init->rhs, ctx, arena);
    } else if (init) {
      ExecFuncStmt(init, ret_var, func_name, ctx, arena);
    }
  }
  while (stmt->for_cond &&
         EvalExpr(stmt->for_cond, ctx, arena).IsTruthy()) {
    if (stmt->for_body &&
        ExecFuncStmt(stmt->for_body, ret_var, func_name, ctx, arena)) {
      if (scoped) ctx.PopScope();
      if (labeled) ctx.PopStaticScope(stmt->label);
      return true;
    }
    for (auto* step : stmt->for_steps)
      ExecFuncStmt(step, ret_var, func_name, ctx, arena);
  }
  if (scoped) ctx.PopScope();
  if (labeled) ctx.PopStaticScope(stmt->label);
  return false;
}

static Variable* CreateFuncLocalVar(std::string_view name, const DataType& type,
                                    const Expr* init, SimContext& ctx,
                                    Arena& arena) {
  uint32_t w = EvalTypeWidth(type);
  if (w == 0) w = 32;
  auto* v = ctx.CreateLocalVariable(name, w);
  if (init) v->value = EvalExpr(init, ctx, arena);
  return v;
}

static void ExecFuncVarDeclAutomatic(const Stmt* stmt, SimContext& ctx,
                                     Arena& arena) {
  CreateFuncLocalVar(stmt->var_name, stmt->var_decl_type, stmt->var_init, ctx,
                     arena);
}

static void ExecFuncVarDeclStatic(const Stmt* stmt, std::string_view func_name,
                                  SimContext& ctx, Arena& arena) {
  auto* existing = ctx.FindStaticFuncVar(func_name, stmt->var_name);
  if (existing) {
    ctx.AliasLocalVariable(stmt->var_name, existing);
    return;
  }
  auto* v = CreateFuncLocalVar(stmt->var_name, stmt->var_decl_type,
                               stmt->var_init, ctx, arena);
  ctx.SaveStaticFuncVar(func_name, stmt->var_name, v);
}

static void ExecFuncVarDecl(const Stmt* stmt, std::string_view func_name,
                            SimContext& ctx, Arena& arena) {
  if (stmt->var_is_automatic) {
    ExecFuncVarDeclAutomatic(stmt, ctx, arena);
    return;
  }
  if (stmt->var_is_static) {
    ExecFuncVarDeclStatic(stmt, func_name, ctx, arena);
    return;
  }
  if (ctx.FindLocalVariable(stmt->var_name)) return;
  CreateFuncLocalVar(stmt->var_name, stmt->var_decl_type, stmt->var_init, ctx,
                     arena);
}

static std::string GetForeachArrayName(const Expr* expr) {
  if (!expr) return {};
  if (expr->kind == ExprKind::kIdentifier) return std::string(expr->text);
  if (expr->kind == ExprKind::kMemberAccess) {
    std::string name;
    BuildLhsName(expr, name);
    return name;
  }
  return {};
}

static bool ExecFuncWhile(const Stmt* stmt, Variable* ret_var,
                          std::string_view func_name, SimContext& ctx,
                          Arena& arena) {
  bool labeled = !stmt->label.empty();
  if (labeled) ctx.PushStaticScope(stmt->label);
  while (stmt->condition &&
         EvalExpr(stmt->condition, ctx, arena).IsTruthy()) {
    if (stmt->body &&
        ExecFuncStmt(stmt->body, ret_var, func_name, ctx, arena)) {
      if (labeled) ctx.PopStaticScope(stmt->label);
      return true;
    }
  }
  if (labeled) ctx.PopStaticScope(stmt->label);
  return false;
}

static bool ExecFuncDoWhile(const Stmt* stmt, Variable* ret_var,
                            std::string_view func_name, SimContext& ctx,
                            Arena& arena) {
  bool labeled = !stmt->label.empty();
  if (labeled) ctx.PushStaticScope(stmt->label);
  do {
    if (stmt->body &&
        ExecFuncStmt(stmt->body, ret_var, func_name, ctx, arena)) {
      if (labeled) ctx.PopStaticScope(stmt->label);
      return true;
    }
  } while (stmt->condition &&
           EvalExpr(stmt->condition, ctx, arena).IsTruthy());
  if (labeled) ctx.PopStaticScope(stmt->label);
  return false;
}

static bool ExecFuncForever(const Stmt* stmt, Variable* ret_var,
                            std::string_view func_name, SimContext& ctx,
                            Arena& arena) {
  bool labeled = !stmt->label.empty();
  if (labeled) ctx.PushStaticScope(stmt->label);
  for (;;) {
    if (stmt->body &&
        ExecFuncStmt(stmt->body, ret_var, func_name, ctx, arena)) {
      if (labeled) ctx.PopStaticScope(stmt->label);
      return true;
    }
  }
  if (labeled) ctx.PopStaticScope(stmt->label);
  return false;
}

static bool ExecFuncForeach(const Stmt* stmt, Variable* ret_var,
                            std::string_view func_name, SimContext& ctx,
                            Arena& arena) {
  bool labeled = !stmt->label.empty();
  if (labeled) ctx.PushStaticScope(stmt->label);
  std::string name = GetForeachArrayName(stmt->expr);
  if (name.empty()) {
    if (labeled) ctx.PopStaticScope(stmt->label);
    return false;
  }
  uint32_t size = 0;
  auto* info = ctx.FindArrayInfo(name);
  if (info) {
    size = info->size;
  } else {
    auto* var = ctx.FindVariable(name);
    if (var) size = var->value.width;
  }
  if (size == 0) {
    if (labeled) ctx.PopStaticScope(stmt->label);
    return false;
  }

  std::string_view iter_name;
  if (!stmt->foreach_vars.empty() && !stmt->foreach_vars[0].empty()) {
    iter_name = stmt->foreach_vars[0];
  }

  ctx.PushScope();
  Variable* iter_var = nullptr;
  if (!iter_name.empty()) {
    iter_var = ctx.CreateLocalVariable(iter_name, 32);
  }

  for (uint32_t i = 0; i < size; ++i) {
    if (iter_var) {
      iter_var->value = MakeLogic4VecVal(arena, 32, i);
    }
    if (stmt->body &&
        ExecFuncStmt(stmt->body, ret_var, func_name, ctx, arena)) {
      ctx.PopScope();
      if (labeled) ctx.PopStaticScope(stmt->label);
      return true;
    }
  }

  ctx.PopScope();
  if (labeled) ctx.PopStaticScope(stmt->label);
  return false;
}

static bool ExecFuncStmt(const Stmt* stmt, Variable* ret_var,
                         std::string_view func_name, SimContext& ctx,
                         Arena& arena) {
  if (!stmt) return false;
  switch (stmt->kind) {
    case StmtKind::kReturn:
      if (stmt->expr)
        ret_var->value =
            EvalExpr(stmt->expr, ctx, arena, ret_var->value.width);
      return true;
    case StmtKind::kBlockingAssign:
      ExecFuncBlockingAssign(stmt, ctx, arena);
      return false;
    case StmtKind::kExprStmt:
      EvalExpr(stmt->expr, ctx, arena);
      return false;
    case StmtKind::kVarDecl:
      ExecFuncVarDecl(stmt, func_name, ctx, arena);
      return false;
    case StmtKind::kIf:
      return ExecFuncIf(stmt, ret_var, func_name, ctx, arena);
    case StmtKind::kBlock:
      return ExecFuncBlock(stmt, ret_var, func_name, ctx, arena);
    case StmtKind::kFor:
      return ExecFuncFor(stmt, ret_var, func_name, ctx, arena);
    case StmtKind::kForeach:
      return ExecFuncForeach(stmt, ret_var, func_name, ctx, arena);
    case StmtKind::kWhile:
      return ExecFuncWhile(stmt, ret_var, func_name, ctx, arena);
    case StmtKind::kDoWhile:
      return ExecFuncDoWhile(stmt, ret_var, func_name, ctx, arena);
    case StmtKind::kForever:
      return ExecFuncForever(stmt, ret_var, func_name, ctx, arena);
    default:
      return false;
  }
}

static void ExecFunctionBody(const ModuleItem* func, Variable* ret_var,
                             SimContext& ctx, Arena& arena) {
  for (auto* s : func->func_body_stmts) {
    if (ExecFuncStmt(s, ret_var, func->name, ctx, arena)) return;
  }
}

static void InitClassPropertyDefaults(const ClassTypeInfo* info,
                                      ClassObject* obj, SimContext& ctx,
                                      Arena& arena) {
  for (const auto& prop : info->properties) {
    Logic4Vec val = prop.init_expr ? EvalExpr(prop.init_expr, ctx, arena)
                                  : MakeLogic4VecVal(arena, prop.width, 0);
    obj->properties[std::string(prop.name)] = val;
    std::string scoped = std::string(info->name) + "::" + std::string(prop.name);
    obj->properties[scoped] = val;
  }

  if (info->decl) {
    for (const auto& [pname, pexpr] : info->decl->params) {
      if (pexpr) {
        auto val = EvalExpr(pexpr, ctx, arena);
        obj->properties[std::string(pname)] = val;
        std::string scoped = std::string(info->name) + "::" + std::string(pname);
        obj->properties[scoped] = val;
      }
    }
  }
}

static void RunConstructorForLevel(const ClassTypeInfo* info, ClassObject* obj,
                                   const Expr* args_expr, SimContext& ctx,
                                   Arena& arena) {
  auto it = info->methods.find("new");
  if (it == info->methods.end() || !it->second) return;
  ctx.PushScope();
  if (args_expr) BindFunctionArgs(it->second, args_expr, ctx, arena);
  Variable dummy;
  ExecFunctionBody(it->second, &dummy, ctx, arena);
  ctx.PopScope();
}

Logic4Vec EvalClassNew(std::string_view class_type, const Expr* new_expr,
                       SimContext& ctx, Arena& arena) {
  auto* info = ctx.FindClassType(class_type);
  if (!info) return MakeLogic4VecVal(arena, 64, kNullClassHandle);
  if (info->is_abstract) {
    ctx.GetDiag().Error(
        {}, "cannot construct object of abstract class '" +
                std::string(class_type) + "'");
    return MakeLogic4VecVal(arena, 64, kNullClassHandle);
  }
  if (info->is_interface) {
    ctx.GetDiag().Error(
        {}, "cannot construct object of interface class '" +
                std::string(class_type) + "'");
    return MakeLogic4VecVal(arena, 64, kNullClassHandle);
  }
  auto* obj = arena.Create<ClassObject>();
  obj->type = info;

  std::vector<const ClassTypeInfo*> chain;
  for (auto* cur = info; cur; cur = cur->parent) chain.push_back(cur);
  std::reverse(chain.begin(), chain.end());

  auto handle = ctx.AllocateClassObject(obj);
  ctx.PushThis(obj);

  for (size_t i = 0; i < chain.size(); ++i) {
    InitClassPropertyDefaults(chain[i], obj, ctx, arena);
    const Expr* args = (i == chain.size() - 1) ? new_expr : nullptr;

    if (!args && i + 1 < chain.size() && chain[i + 1]->decl) {
      const auto* child_decl = chain[i + 1]->decl;
      if (!child_decl->extends_args.empty()) {
        auto* synth = arena.Create<Expr>();
        synth->kind = ExprKind::kCall;
        synth->args = child_decl->extends_args;
        args = synth;
      } else if (child_decl->extends_has_default && new_expr) {

        size_t default_pos = 0;
        for (const auto* m : child_decl->members) {
          if (m->kind == ClassMemberKind::kMethod && m->method &&
              m->method->name == "new") {
            for (size_t j = 0; j < m->method->func_args.size(); ++j) {
              if (m->method->func_args[j].is_default) {
                default_pos = j;
                break;
              }
            }
            break;
          }
        }

        size_t base_argc = 0;
        auto base_it = chain[i]->methods.find("new");
        if (base_it != chain[i]->methods.end() && base_it->second) {
          base_argc = base_it->second->func_args.size();
        }
        auto* synth = arena.Create<Expr>();
        synth->kind = ExprKind::kCall;
        for (size_t j = 0; j < base_argc &&
                           default_pos + j < new_expr->args.size();
             ++j) {
          synth->args.push_back(new_expr->args[default_pos + j]);
        }
        args = synth;
      }
    }
    RunConstructorForLevel(chain[i], obj, args, ctx, arena);
  }

  ctx.PopThis();
  return MakeLogic4VecVal(arena, 64, handle);
}

void ApplyClassParamOverrides(std::string_view var_name, uint64_t handle,
                              SimContext& ctx, Arena& arena) {
  auto* obj = ctx.GetClassObject(handle);
  if (!obj || !obj->type || !obj->type->decl) return;
  const auto& param_exprs = ctx.GetVariableClassParamExprs(var_name);
  if (param_exprs.empty()) return;
  const auto& params = obj->type->decl->params;
  for (size_t i = 0; i < params.size() && i < param_exprs.size(); ++i) {
    if (param_exprs[i]) {
      auto val = EvalExpr(param_exprs[i], ctx, arena);
      obj->properties[std::string(params[i].first)] = val;
      std::string scoped =
          std::string(obj->type->name) + "::" + std::string(params[i].first);
      obj->properties[scoped] = val;
    }
  }
}

static Logic4Vec EvalDpiCall(const Expr* expr, SimContext& ctx, Arena& arena) {
  auto* dpi = ctx.GetDpiContext();
  if (!dpi || !dpi->HasImport(expr->callee)) {
    return MakeLogic4VecVal(arena, 1, 0);
  }
  // §35.6: calling an imported function uses the same usage and syntax as a
  // native function call. When the import's formals are known, resolve the
  // call-site actuals against them so that named-argument binding and omitted
  // arguments backed by defaults behave exactly as for native subroutine calls.
  const DpiFunction* import = dpi->FindImport(expr->callee);
  std::vector<uint64_t> args;
  if (import && !import->args.empty()) {
    size_t positional_count = expr->args.size() - expr->arg_names.size();
    args.reserve(import->args.size());
    for (size_t i = 0; i < import->args.size(); ++i) {
      int ai = -1;
      if (i < positional_count) {
        ai = static_cast<int>(i);
      } else {
        for (size_t j = 0; j < expr->arg_names.size(); ++j) {
          if (expr->arg_names[j] == import->args[i].name) {
            ai = static_cast<int>(positional_count + j);
            break;
          }
        }
      }
      if (ai >= 0 && expr->args[static_cast<size_t>(ai)] != nullptr) {
        args.push_back(
            EvalExpr(expr->args[static_cast<size_t>(ai)], ctx, arena).ToUint64());
      } else if (import->args[i].default_value) {
        args.push_back(
            EvalExpr(import->args[i].default_value, ctx, arena).ToUint64());
      } else {
        args.push_back(0);
      }
    }
  } else {
    args.reserve(expr->args.size());
    for (auto* arg : expr->args) {
      args.push_back(EvalExpr(arg, ctx, arena).ToUint64());
    }
  }
  uint64_t result = dpi->Call(expr->callee, args);
  return MakeLogic4VecVal(arena, 32, result);
}

static void ExecClassMethod(ModuleItem* method, const Expr* expr,
                            SimContext& ctx, Arena& arena, Logic4Vec& out);

struct InstanceMethodInfo {
  ClassObject* obj = nullptr;
  ModuleItem* method = nullptr;
};

static bool ResolveInstanceMethod(const MethodCallParts& parts, SimContext& ctx,
                                  InstanceMethodInfo& info) {
  auto class_type = ctx.GetVariableClassType(parts.var_name);
  if (class_type.empty()) return false;
  auto* var = ctx.FindVariable(parts.var_name);
  if (!var) return false;
  auto handle = var->value.ToUint64();
  if (handle == kNullClassHandle) return false;
  info.obj = ctx.GetClassObject(handle);
  if (!info.obj) return false;
  info.method = info.obj->ResolveVirtualMethod(parts.method_name);
  if (!info.method) {

    auto* declared_type = ctx.FindClassType(class_type);
    if (declared_type) {
      info.method =
          info.obj->ResolveMethodForType(parts.method_name, declared_type);
    } else {
      info.method = info.obj->ResolveMethod(parts.method_name);
    }
  }
  return info.method != nullptr;
}

static Logic4Vec ExecInstanceMethodCall(ModuleItem* method, ClassObject* obj,
                                        const Expr* expr, SimContext& ctx,
                                        Arena& arena) {
  Logic4Vec out;
  ctx.PushScope();
  ctx.PushThis(obj);
  ctx.PushQueueRefFrame();
  ctx.PushAssocRefFrame();
  ExecClassMethod(method, expr, ctx, arena, out);
  WritebackOutputArgs(method, expr, ctx, arena);
  WritebackQueueRefs(ctx);
  WritebackAssocRefs(ctx);
  ctx.PopThis();
  ctx.PopScope();
  return out;
}

static bool TryEvalSuperMethodCall(const Expr* expr, SimContext& ctx,
                                   Arena& arena, Logic4Vec& out) {
  MethodCallParts parts;
  if (!ExtractMethodCallParts(expr, parts)) return false;
  if (parts.var_name != "super") return false;
  auto* self = ctx.CurrentThis();
  if (!self || !self->type || !self->type->parent) return false;
  auto* method =
      self->ResolveMethodForType(parts.method_name, self->type->parent);
  if (!method) return false;
  out = ExecInstanceMethodCall(method, self, expr, ctx, arena);
  return true;
}

static bool TryEvalClassMethodCall(const Expr* expr, SimContext& ctx,
                                   Arena& arena, Logic4Vec& out) {
  MethodCallParts parts;
  if (!ExtractMethodCallParts(expr, parts)) return false;
  InstanceMethodInfo info;
  if (!ResolveInstanceMethod(parts, ctx, info)) return false;
  out = ExecInstanceMethodCall(info.method, info.obj, expr, ctx, arena);
  return true;
}

static void BindClassParams(const ClassTypeInfo* cls, const Expr* base_id,
                            SimContext& ctx, Arena& arena) {
  if (!cls->decl) return;
  const auto& params = cls->decl->params;
  const auto& values = base_id->elements;
  for (size_t i = 0; i < params.size(); ++i) {
    Logic4Vec val;
    if (i < values.size()) {
      val = EvalExpr(values[i], ctx, arena);
    } else if (params[i].second) {
      val = EvalExpr(params[i].second, ctx, arena);
    } else {
      val = MakeLogic4VecVal(arena, 32, 0);
    }
    auto* v = ctx.CreateLocalVariable(params[i].first, val.width);
    v->value = val;
  }
}

struct ClassScopeInfo {
  const Expr* access;
  ClassTypeInfo* cls;
  ModuleItem* method;
  bool is_void;
};

static bool ResolveClassScope(const Expr* expr, SimContext& ctx,
                              ClassScopeInfo& info) {
  if (!expr->lhs || expr->lhs->kind != ExprKind::kMemberAccess) return false;
  info.access = expr->lhs;
  if (!info.access->lhs || info.access->lhs->kind != ExprKind::kIdentifier)
    return false;
  if (!info.access->rhs || info.access->rhs->kind != ExprKind::kIdentifier)
    return false;
  info.cls = ctx.FindClassType(info.access->lhs->text);
  if (!info.cls) return false;
  auto it = info.cls->methods.find(std::string(info.access->rhs->text));
  if (it == info.cls->methods.end()) return false;
  info.method = it->second;
  info.is_void = (info.method->return_type.kind == DataTypeKind::kVoid);
  return true;
}

static void ExecClassMethod(ModuleItem* method, const Expr* expr,
                            SimContext& ctx, Arena& arena, Logic4Vec& out) {
  bool is_void = (method->return_type.kind == DataTypeKind::kVoid);
  BindFunctionArgs(method, expr, ctx, arena);
  Variable dummy_ret;
  Variable* ret_var = &dummy_ret;
  if (!is_void) ret_var = ctx.CreateLocalVariable(method->name, 32);
  ExecFunctionBody(method, ret_var, ctx, arena);
  out = is_void ? MakeLogic4VecVal(arena, 1, 0) : ret_var->value;
}

static bool TryEvalClassScopeCall(const Expr* expr, SimContext& ctx,
                                  Arena& arena, Logic4Vec& out) {
  ClassScopeInfo info;
  if (!ResolveClassScope(expr, ctx, info)) return false;
  if (!info.access->lhs->elements.empty()) return false;

  if (info.access->rhs->text == "new") {
    out = EvalClassNew(info.access->lhs->text, expr, ctx, arena);
    return true;
  }
  ctx.PushScope();
  ExecClassMethod(info.method, expr, ctx, arena, out);
  ctx.PopScope();
  return true;
}

static bool TryEvalParameterizedScopeCall(const Expr* expr, SimContext& ctx,
                                          Arena& arena, Logic4Vec& out) {
  ClassScopeInfo info;
  if (!ResolveClassScope(expr, ctx, info)) return false;
  if (info.access->lhs->elements.empty()) return false;
  ctx.PushScope();
  BindClassParams(info.cls, info.access->lhs, ctx, arena);

  if (info.access->rhs->text == "new") {
    out = EvalClassNew(info.access->lhs->text, expr, ctx, arena);
    ctx.PopScope();
    return true;
  }
  ExecClassMethod(info.method, expr, ctx, arena, out);
  ctx.PopScope();
  return true;
}

static bool TryEvalWeakRefMethodCall(const Expr* expr, SimContext& ctx,
                                     Arena& arena, Logic4Vec& out) {
  MethodCallParts parts;
  if (!ExtractMethodCallParts(expr, parts)) return false;
  if (ctx.GetVariableClassType(parts.var_name) != "weak_reference") return false;
  auto* var = ctx.FindVariable(parts.var_name);
  if (!var) return false;
  auto wr_handle = var->value.ToUint64();
  auto* wr = ctx.FindWeakReferenceByHandle(wr_handle);
  if (parts.method_name == "get") {
    uint64_t referent = (wr != nullptr) ? wr->Get() : kNullClassHandle;
    out = MakeLogic4VecVal(arena, 64, referent);
    return true;
  }
  if (parts.method_name == "clear") {
    if (wr != nullptr) wr->Clear();
    out = MakeLogic4VecVal(arena, 1, 0);
    return true;
  }
  return false;
}

static bool TryEvalWeakRefStaticCall(const Expr* expr, SimContext& ctx,
                                     Arena& arena, Logic4Vec& out) {
  if (!expr->lhs || expr->lhs->kind != ExprKind::kMemberAccess) return false;
  auto* access = expr->lhs;
  if (!access->lhs || access->lhs->kind != ExprKind::kIdentifier) return false;
  if (access->lhs->text != "weak_reference") return false;
  if (!access->rhs || access->rhs->kind != ExprKind::kIdentifier) return false;
  if (access->rhs->text != "get_id") return false;
  if (expr->args.empty()) return false;
  uint64_t obj_handle = EvalExpr(expr->args[0], ctx, arena).ToUint64();
  int64_t id = WeakReference::GetId(obj_handle);
  out = MakeLogic4VecVal(arena, 64, static_cast<uint64_t>(id));
  return true;
}

static bool TryEvalProcessStaticCall(const Expr* expr, SimContext& ctx,
                                     Arena& arena, Logic4Vec& out) {
  if (!expr->lhs || expr->lhs->kind != ExprKind::kMemberAccess) return false;
  auto* access = expr->lhs;
  if (!access->lhs || access->lhs->kind != ExprKind::kIdentifier) return false;
  if (access->lhs->text != "process") return false;
  if (!access->rhs || access->rhs->kind != ExprKind::kIdentifier) return false;
  if (access->rhs->text != "self") return false;
  auto* proc = ctx.CurrentProcess();
  if (!proc) {
    out = MakeLogic4VecVal(arena, 64, 0);
    return true;
  }
  uint64_t handle = ctx.RegisterProcessHandle(proc);
  out = MakeLogic4VecVal(arena, 64, handle);
  return true;
}

static bool IsRestrictedTarget(const Process* proc) {
  if (!proc) return false;
  return proc->kind == ProcessKind::kFinal ||
         proc->kind == ProcessKind::kContAssign;
}

static bool TryEvalProcessMethodCall(const Expr* expr, SimContext& ctx,
                                     Arena& arena, Logic4Vec& out) {
  MethodCallParts parts;
  if (!ExtractMethodCallParts(expr, parts)) return false;
  if (ctx.GetVariableClassType(parts.var_name) != "process") return false;
  auto* var = ctx.FindVariable(parts.var_name);
  if (!var) return false;
  auto proc_handle = var->value.ToUint64();
  auto* proc = ctx.FindProcessByHandle(proc_handle);
  if (parts.method_name == "status") {
    uint64_t state_val = 0;
    if (proc) {
      state_val = static_cast<uint64_t>(proc->sv_state);
    }
    out = MakeLogic4VecVal(arena, 32, state_val);
    return true;
  }
  if (parts.method_name == "kill") {
    if (IsRestrictedTarget(proc)) {
      ctx.GetDiag().Error(
          {}, "kill() shall only target a process created by an initial "
              "procedure, always procedure, or fork block");
      out = MakeLogic4VecVal(arena, 1, 0);
      return true;
    }
    if (proc && proc->sv_state != ProcessState::kFinished &&
        proc->sv_state != ProcessState::kKilled) {
      proc->active = false;
      proc->sv_state = ProcessState::kKilled;

      std::vector<Process*> stack(proc->children.begin(), proc->children.end());
      while (!stack.empty()) {
        auto* child = stack.back();
        stack.pop_back();
        if (child->sv_state != ProcessState::kFinished &&
            child->sv_state != ProcessState::kKilled) {
          child->active = false;
          child->sv_state = ProcessState::kKilled;
          for (auto* gc : child->children) stack.push_back(gc);
        }
      }

      for (auto& w : proc->await_waiters) {
        if (w) w.resume();
      }
      proc->await_waiters.clear();
    }
    out = MakeLogic4VecVal(arena, 1, 0);
    return true;
  }
  if (parts.method_name == "suspend") {
    if (IsRestrictedTarget(proc)) {
      ctx.GetDiag().Error(
          {}, "suspend() shall only target a process created by an initial "
              "procedure, always procedure, or fork block");
      out = MakeLogic4VecVal(arena, 1, 0);
      return true;
    }

    if (proc && proc == ctx.CurrentProcess() && ctx.InFunction()) {
      ctx.GetDiag().Error(
          {}, "function cannot suspend its own execution");
      out = MakeLogic4VecVal(arena, 1, 0);
      return true;
    }
    if (proc && proc->sv_state != ProcessState::kFinished &&
        proc->sv_state != ProcessState::kKilled) {
      proc->is_suspended = true;
      proc->sv_state = ProcessState::kSuspended;
    }
    out = MakeLogic4VecVal(arena, 1, 0);
    return true;
  }
  if (parts.method_name == "srandom") {

    if (proc && !expr->args.empty()) {
      auto seed_val = EvalExpr(expr->args[0], ctx, arena);
      auto seed = static_cast<uint32_t>(seed_val.ToUint64());
      proc->rng_seed = seed;
      // Reset the per-thread stream now so subsequent draws from this thread
      // replay the sequence keyed by the requested seed.
      proc->rng.seed(seed);
      proc->rng_initialized = true;
    }
    out = MakeLogic4VecVal(arena, 1, 0);
    return true;
  }
  if (parts.method_name == "resume") {
    if (IsRestrictedTarget(proc)) {
      ctx.GetDiag().Error(
          {}, "resume() shall only target a process created by an initial "
              "procedure, always procedure, or fork block");
      out = MakeLogic4VecVal(arena, 1, 0);
      return true;
    }
    if (proc && proc->is_suspended) {
      proc->is_suspended = false;
      if (proc->sv_state == ProcessState::kSuspended) {
        proc->sv_state = ProcessState::kRunning;
      }

      auto* event = ctx.GetScheduler().GetEventPool().Acquire();
      Process* target = proc;
      event->callback = [target, &ctx]() {
        if (target->active && !target->Done()) {
          ctx.SetCurrentProcess(target);
          target->Resume();
        }
      };
      ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime(), Region::kActive,
                                       event);
    }
    out = MakeLogic4VecVal(arena, 1, 0);
    return true;
  }
  return false;
}

static bool TryBuiltinMethodCall(const Expr* expr, SimContext& ctx,
                                 Arena& arena, Logic4Vec& out) {
  if (TryEvalProcessMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalWeakRefMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalEnumMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalStringMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalArrayMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalQueueMethodCall(expr, ctx, arena, out)) return true;
  return TryEvalAssocMethodCall(expr, ctx, arena, out);
}

static thread_local std::unordered_set<std::string_view> expanding_lets;

static std::vector<Logic4Vec> EvalLetActuals(ModuleItem* decl, const Expr* call,
                                             SimContext& ctx, Arena& arena) {
  auto& formals = decl->func_args;
  size_t positional_count = call->args.size() - call->arg_names.size();
  std::vector<Logic4Vec> vals;
  vals.reserve(formals.size());
  for (size_t i = 0; i < formals.size(); ++i) {
    Logic4Vec val;
    if (i < positional_count) {
      val = EvalExpr(call->args[i], ctx, arena);
    } else {
      int found = -1;
      for (size_t j = 0; j < call->arg_names.size(); ++j) {
        if (call->arg_names[j] == formals[i].name) {
          found = static_cast<int>(positional_count + j);
          break;
        }
      }
      if (found >= 0 && call->args[static_cast<size_t>(found)]) {
        val = EvalExpr(call->args[static_cast<size_t>(found)], ctx, arena);
      } else if (formals[i].default_value) {
        val = EvalExpr(formals[i].default_value, ctx, arena);
      } else {
        val = MakeLogic4Vec(arena, 32);
      }
    }

    const auto& dt = formals[i].data_type;
    if (dt.kind != DataTypeKind::kImplicit && dt.packed_dim_left &&
        dt.packed_dim_right) {
      uint32_t formal_width = EvalTypeWidth(dt);
      if (formal_width > 0 && formal_width != val.width) {
        val = ResizeToWidth(val, formal_width, arena);
      }
    }
    vals.push_back(val);
  }
  return vals;
}

static void BindLetArgs(ModuleItem* decl, const std::vector<Logic4Vec>& vals,
                        SimContext& ctx) {
  auto& formals = decl->func_args;
  for (size_t i = 0; i < formals.size(); ++i) {
    auto* var = ctx.CreateLocalVariable(formals[i].name, vals[i].width);
    var->value = vals[i];
  }
}

static Logic4Vec EvalLetExpansion(ModuleItem* decl, const Expr* call,
                                  SimContext& ctx, Arena& arena) {

  if (expanding_lets.count(decl->name)) return MakeAllX(arena, 32);
  expanding_lets.insert(decl->name);

  auto vals = EvalLetActuals(decl, call, ctx, arena);

  auto saved_scopes = ctx.SwapScopeStack({});
  ctx.PushScope();
  BindLetArgs(decl, vals, ctx);
  auto result = EvalExpr(decl->init_expr, ctx, arena);
  ctx.PopScope();
  ctx.SwapScopeStack(std::move(saved_scopes));
  expanding_lets.erase(decl->name);
  return result;
}

static bool TryDispatchMethodOrLet(const Expr* expr, SimContext& ctx,
                                   Arena& arena, Logic4Vec& out) {
  if (TryBuiltinMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalSuperMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalClassMethodCall(expr, ctx, arena, out)) return true;
  if (TryEvalWeakRefStaticCall(expr, ctx, arena, out)) return true;
  if (TryEvalProcessStaticCall(expr, ctx, arena, out)) return true;
  if (TryEvalClassScopeCall(expr, ctx, arena, out)) return true;
  if (TryEvalParameterizedScopeCall(expr, ctx, arena, out)) return true;
  auto* let_decl = ctx.FindLetDecl(expr->callee);
  if (let_decl) {
    out = EvalLetExpansion(let_decl, expr, ctx, arena);
    return true;
  }
  return false;
}

Logic4Vec EvalFunctionCall(const Expr* expr, SimContext& ctx, Arena& arena) {
  Logic4Vec result;
  if (TryDispatchMethodOrLet(expr, ctx, arena, result)) return result;

  auto* func = ctx.FindFunction(expr->callee);
  if (!func) return EvalDpiCall(expr, ctx, arena);

  bool is_static = func->is_static && !func->is_automatic;
  bool is_void = (func->return_type.kind == DataTypeKind::kVoid);

  if (is_static) {
    ctx.PushStaticScope(func->name);
  } else {
    ctx.PushScope();
  }

  ctx.PushQueueRefFrame();
  ctx.PushAssocRefFrame();
  BindFunctionArgs(func, expr, ctx, arena);

  Variable dummy_ret;
  Variable* ret_var = &dummy_ret;
  if (!is_void) {
    auto* existing = is_static ? ctx.FindLocalVariable(func->name) : nullptr;
    uint32_t ret_width = EvalTypeWidth(func->return_type);
    if (ret_width == 0) ret_width = 32;
    ret_var = existing ? existing : ctx.CreateLocalVariable(func->name, ret_width);
  }

  ctx.EnterFunction();
  ExecFunctionBody(func, ret_var, ctx, arena);
  ctx.ExitFunction();
  WritebackOutputArgs(func, expr, ctx, arena);
  WritebackQueueRefs(ctx);
  WritebackAssocRefs(ctx);
  result = is_void ? MakeLogic4VecVal(arena, 1, 0) : ret_var->value;

  if (is_static) {
    ctx.PopStaticScope(func->name);
  } else {
    ctx.PopScope();
  }
  return result;
}

const ModuleItem* SetupTaskCall(const Expr* expr, SimContext& ctx,
                                Arena& arena) {
  if (!expr) return nullptr;

  if (expr->kind == ExprKind::kIdentifier) {
    auto* func = ctx.FindFunction(expr->text);
    if (!func) return nullptr;
    bool is_task = func->kind == ModuleItemKind::kTaskDecl;
    bool is_void_func = func->kind == ModuleItemKind::kFunctionDecl &&
                        func->return_type.kind == DataTypeKind::kVoid;
    if (!is_task && !is_void_func) return nullptr;

    bool is_static = func->is_static && !func->is_automatic;
    if (is_static) {
      ctx.PushStaticScope(func->name);
    } else {
      ctx.PushScope();
    }
    ctx.PushQueueRefFrame();
    ctx.PushAssocRefFrame();
    ctx.PushFuncName(func->name);
    if (is_void_func) ctx.EnterFunction();
    if (!func->func_args.empty()) BindFunctionArgs(func, expr, ctx, arena);
    return func;
  }
  if (expr->kind != ExprKind::kCall) return nullptr;
  auto* func = ctx.FindFunction(expr->callee);
  if (!func || func->kind != ModuleItemKind::kTaskDecl) return nullptr;

  bool is_static = func->is_static && !func->is_automatic;
  if (is_static) {
    ctx.PushStaticScope(func->name);
  } else {
    ctx.PushScope();
  }
  ctx.PushQueueRefFrame();
  ctx.PushAssocRefFrame();
  ctx.PushFuncName(func->name);
  BindFunctionArgs(func, expr, ctx, arena);
  return func;
}

void TeardownTaskCall(const ModuleItem* func, const Expr* expr,
                      SimContext& ctx, Arena& arena) {
  WritebackOutputArgs(func, expr, ctx, arena);
  WritebackQueueRefs(ctx);
  WritebackAssocRefs(ctx);
  bool is_void_func = func->kind == ModuleItemKind::kFunctionDecl &&
                      func->return_type.kind == DataTypeKind::kVoid;
  if (is_void_func) ctx.ExitFunction();
  ctx.PopFuncName();
  bool is_static = func->is_static && !func->is_automatic;
  if (is_static) {
    ctx.PopStaticScope(func->name);
  } else {
    ctx.PopScope();
  }
}

void ValidateRefLifetime(const ModuleItem* func, DiagEngine& diag) {
  if (!func) return;
  bool is_static = func->is_static && !func->is_automatic;
  if (!is_static) return;
  for (const auto& arg : func->func_args) {
    if (arg.direction == Direction::kRef) {
      diag.Error({}, "ref argument '" + std::string(arg.name) +
                         "' not allowed in static subroutine '" +
                         std::string(func->name) + "'");
    }
  }
}

static std::string_view GetLhsRootName(const Expr* e) {
  if (!e) return {};
  if (e->kind == ExprKind::kIdentifier) return e->text;
  if (e->kind == ExprKind::kSelect && e->base) return GetLhsRootName(e->base);
  if (e->kind == ExprKind::kMemberAccess && e->lhs)
    return GetLhsRootName(e->lhs);
  return {};
}

static void CheckConstRefWrites(
    const Stmt* stmt,
    const std::unordered_set<std::string_view>& const_ref_names,
    const ModuleItem* func, DiagEngine& diag) {
  if (!stmt) return;
  switch (stmt->kind) {
    case StmtKind::kBlockingAssign:
    case StmtKind::kNonblockingAssign:
    case StmtKind::kAssign:
    case StmtKind::kForce: {
      auto root = GetLhsRootName(stmt->lhs);
      if (!root.empty() && const_ref_names.count(root)) {
        diag.Error({}, "cannot write to const ref argument '" +
                           std::string(root) + "' in subroutine '" +
                           std::string(func->name) + "'");
      }
      break;
    }
    default:
      break;
  }
  for (auto* s : stmt->stmts) CheckConstRefWrites(s, const_ref_names, func, diag);
  CheckConstRefWrites(stmt->then_branch, const_ref_names, func, diag);
  CheckConstRefWrites(stmt->else_branch, const_ref_names, func, diag);
  CheckConstRefWrites(stmt->body, const_ref_names, func, diag);
  CheckConstRefWrites(stmt->for_body, const_ref_names, func, diag);
  for (auto* s : stmt->for_inits)
    CheckConstRefWrites(s, const_ref_names, func, diag);
  for (auto* s : stmt->for_steps)
    CheckConstRefWrites(s, const_ref_names, func, diag);
  for (const auto& ci : stmt->case_items)
    CheckConstRefWrites(ci.body, const_ref_names, func, diag);
  for (auto* s : stmt->fork_stmts)
    CheckConstRefWrites(s, const_ref_names, func, diag);
  CheckConstRefWrites(stmt->assert_pass_stmt, const_ref_names, func, diag);
  CheckConstRefWrites(stmt->assert_fail_stmt, const_ref_names, func, diag);
  for (const auto& ri : stmt->randcase_items)
    CheckConstRefWrites(ri.second, const_ref_names, func, diag);
}

void ValidateConstRefWriteProtection(const ModuleItem* func,
                                     DiagEngine& diag) {
  if (!func) return;
  std::unordered_set<std::string_view> const_ref_names;
  for (const auto& arg : func->func_args) {
    if (arg.direction == Direction::kRef && arg.is_const) {
      const_ref_names.insert(arg.name);
    }
  }
  if (const_ref_names.empty()) return;
  for (auto* stmt : func->func_body_stmts) {
    CheckConstRefWrites(stmt, const_ref_names, func, diag);
  }
}

}
