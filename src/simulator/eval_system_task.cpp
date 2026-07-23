#include <unistd.h>

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
#include "simulator/process.h"
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
// other singular type prints as it would unformatted (C7e) -- a real value in
// the shortest real form, anything else in the default decimal form with x/z
// status characters carried through by FormatArg and the sign shown for the
// signed integer kinds.
static std::string FormatSingularForP(const Logic4Vec& val, DataTypeKind kind) {
  if (kind == DataTypeKind::kString || val.is_string) {
    return "\"" + FormatValueAsString(val) + "\"";
  }
  if (val.is_real) return FormatArg(val, 'g');
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

static std::string FormatStructValueForP(const StructTypeInfo& st,
                                         const Logic4Vec& val, Arena& arena);

// §21.2.1.6 (C2/C7a): render one struct or union member as "name:value". A
// member that is itself a struct or union prints as a nested assignment
// pattern under the same rules; a singular member is formatted by the singular
// rules.
static std::string FormatMember(const StructFieldInfo& f, const Logic4Vec& val,
                                Arena& arena) {
  Logic4Vec slice = SliceField(val, f.bit_offset, f.width, f.type_kind, arena);
  if (f.nested != nullptr) {
    return std::string(f.name) + ":" +
           FormatStructValueForP(*f.nested, slice, arena);
  }
  return std::string(f.name) + ":" + FormatSingularForP(slice, f.type_kind);
}

// §21.2.1.6 (C2/C3/C7a): the assignment-pattern text of one struct or union
// value: every member as "name:value" in declaration order for a struct, only
// the first declared member for an (untagged) union. Nested aggregate members
// recurse through FormatMember.
static std::string FormatStructValueForP(const StructTypeInfo& st,
                                         const Logic4Vec& val, Arena& arena) {
  std::string out = "'{";
  size_t count =
      st.is_union ? std::min<size_t>(1, st.fields.size()) : st.fields.size();
  for (size_t i = 0; i < count; ++i) {
    if (i) out += ", ";
    out += FormatMember(st.fields[i], val, arena);
  }
  out += "}";
  return out;
}

// §21.2.1.6 (C7b): an enumerated value prints as the matching member name when
// the value is one named by the type; otherwise it prints in the base type's
// (decimal) form.
static std::string FormatEnumValueForP(const EnumTypeInfo& et,
                                       const Logic4Vec& val) {
  if (val.IsKnown()) {
    uint64_t v = val.ToUint64();
    for (const auto& m : et.members) {
      if (m.value == v) return std::string(m.name);
    }
  }
  return FormatArg(val, 'd');
}

// §21.2.1.6: render one element of an unpacked aggregate. The traversal
// descends until a singular value is reached: a struct-typed element becomes a
// nested assignment pattern, an enum-typed element its member name, and any
// other element the singular form.
static std::string FormatAggElemForP(const Logic4Vec& val, DataTypeKind kind,
                                     const StructTypeInfo* st,
                                     const EnumTypeInfo* et, Arena& arena) {
  if (st != nullptr) return FormatStructValueForP(*st, val, arena);
  if (et != nullptr) return FormatEnumValueForP(*et, val);
  return FormatSingularForP(val, kind);
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
  return FormatStructValueForP(*st, val, arena);
}

// §21.2.1.6 (C5): a fixed-size unpacked array prints as an assignment pattern
// of its elements in index order, each element rendered by the traversal rules
// (a struct element as a nested pattern, an enum element as its member name).
// Elements live as their own variables, named "arr[idx]" by the lowerer.
// Returns no value when the variable is not a non-empty unpacked array.
static std::optional<std::string> BuildFormatPArray(std::string_view name,
                                                    SimContext& ctx,
                                                    Arena& arena) {
  auto* ai = ctx.FindArrayInfo(name);
  if (ai == nullptr || ai->size == 0) return std::nullopt;
  const StructTypeInfo* st = ctx.GetVariableStructType(name);
  const EnumTypeInfo* et = ctx.GetVariableEnumType(name);
  std::string out = "'{";
  for (uint32_t i = 0; i < ai->size; ++i) {
    if (i) out += ", ";
    uint32_t idx = ai->lo + i;
    std::string elem_name = std::string(name) + "[" + std::to_string(idx) + "]";
    Variable* elem = ctx.FindVariable(elem_name);
    Logic4Vec ev =
        elem ? elem->value : MakeLogic4VecVal(arena, ai->elem_width, 0);
    out += FormatAggElemForP(ev, ai->elem_type_kind, st, et, arena);
  }
  out += "}";
  return out;
}

// §21.2.1.6 (C5): a queue or dynamic array (both stored as a QueueObject)
// prints its current elements as an assignment pattern in index order; an
// empty one prints the empty pattern. Returns no value when the name is not a
// queue or dynamic array.
static std::optional<std::string> BuildFormatPQueue(std::string_view name,
                                                    SimContext& ctx,
                                                    Arena& arena) {
  QueueObject* q = ctx.FindQueue(name);
  if (q == nullptr) return std::nullopt;
  const StructTypeInfo* st = ctx.GetVariableStructType(name);
  const EnumTypeInfo* et = ctx.GetVariableEnumType(name);
  std::string out = "'{";
  for (size_t i = 0; i < q->elements.size(); ++i) {
    if (i) out += ", ";
    out += FormatAggElemForP(q->elements[i], DataTypeKind::kImplicit, st, et,
                             arena);
  }
  out += "}";
  return out;
}

// §21.2.1.6 (C5): an associative array prints as an assignment pattern with
// index labels, one "key:value" item per populated element in key order (a
// string key is quoted). Returns no value when the name is not an associative
// array.
static std::optional<std::string> BuildFormatPAssoc(std::string_view name,
                                                    SimContext& ctx,
                                                    Arena& arena) {
  AssocArrayObject* aa = ctx.FindAssocArray(name);
  if (aa == nullptr) return std::nullopt;
  const StructTypeInfo* st = ctx.GetVariableStructType(name);
  const EnumTypeInfo* et = ctx.GetVariableEnumType(name);
  std::string out = "'{";
  bool first = true;
  auto add_item = [&](const std::string& key, const Logic4Vec& v) {
    if (!first) out += ", ";
    first = false;
    out += key + ":" +
           FormatAggElemForP(v, DataTypeKind::kImplicit, st, et, arena);
  };
  if (aa->is_string_key) {
    for (const auto& [k, v] : aa->str_data) add_item("\"" + k + "\"", v);
  } else {
    for (const auto& [k, v] : aa->int_data) add_item(std::to_string(k), v);
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

// §21.2.1.6 (C7d): a virtual interface prints in an implementation-dependent
// form -- here, the hierarchical name of the interface instance it is bound
// to -- except that a null (unbound) one prints the word "null". Returns no
// value when the variable is not a virtual interface.
static std::optional<std::string> BuildFormatPVirtualInterface(
    std::string_view name, SimContext& ctx) {
  Variable* v = ctx.FindVariable(name);
  if (v == nullptr || !ctx.IsVirtualInterfaceVar(v)) return std::nullopt;
  if (!ctx.VirtualInterfaceIsBound(v)) return "null";
  return std::string(ctx.VirtualInterfaceBinding(v));
}

// §21.2.1.6 (C7d): a chandle likewise prints in an implementation-dependent
// form, except that a null (zero) handle prints the word "null". Returns no
// value when the variable is not a chandle.
static std::optional<std::string> BuildFormatPChandle(std::string_view name,
                                                      const Logic4Vec& val,
                                                      SimContext& ctx) {
  if (!ctx.IsChandleVariable(name)) return std::nullopt;
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
  return FormatEnumValueForP(*et, val);
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
    // The aggregate forms are tried outermost-first: a queue/dynamic array,
    // an associative array, then a fixed-size unpacked array. An array whose
    // element type is a struct or enum also carries that type's info under the
    // same name, so the array checks must come before the struct/enum ones.
    if (auto r = BuildFormatPQueue(name, ctx, arena)) return *r;
    if (auto r = BuildFormatPAssoc(name, ctx, arena)) return *r;
    if (auto r = BuildFormatPArray(name, ctx, arena)) return *r;
    if (auto r = BuildFormatPStruct(name, val, ctx, arena)) return *r;
    if (auto r = BuildFormatPClassHandle(name, val, ctx)) return *r;
    if (auto r = BuildFormatPVirtualInterface(name, ctx)) return *r;
    if (auto r = BuildFormatPChandle(name, val, ctx)) return *r;
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
      std::vector<char> agg_flags;
      std::vector<std::string> byte_strings;
      while (i + 1 < kN && expr->args[i + 1] != nullptr &&
             expr->args[i + 1]->kind != ExprKind::kStringLiteral) {
        const Expr* val_arg = expr->args[++i];
        auto v = EvalExpr(val_arg, ctx, arena);
        arg_vals.push_back(v);
        p_fmts.push_back(BuildFormatP(val_arg, v, ctx));
        v_fmts.push_back(BuildFormatV(val_arg, ctx));
        char agg = ClassifyUnpackedAggregateArg(val_arg, ctx);
        agg_flags.push_back(agg);
        // §21.2.1.7: an unpacked array of byte governed by %s prints its
        // element characters from the left bound to the right bound. The
        // element variables live here, so the string is precomputed and
        // threaded to the formatter alongside the value.
        byte_strings.push_back(
            agg == 2
                ? FormatByteArrayLeftBoundFirst(
                      val_arg->text, *ctx.FindArrayInfo(val_arg->text), ctx)
                : std::string());
      }
      output += FormatDisplay(fmt, arg_vals,
                              {.p_fmts = &p_fmts,
                               .v_fmts = &v_fmts,
                               .ctx = &ctx,
                               .arg_unpacked_agg = &agg_flags,
                               .arg_byte_strings = &byte_strings});
      continue;
    }
    // §21.2.1.1: a bare argument that is a fixed-size unpacked array is handled
    // by its element type. An unpacked array of byte prints as a character
    // string; any other unpacked aggregate has no unformatted rendering and is
    // illegal. (Queues, dynamic, and associative arrays are left to their own
    // handling.)
    if (arg->kind == ExprKind::kIdentifier) {
      const ArrayInfo* ai = ctx.FindArrayInfo(arg->text);
      if (ai != nullptr && !ai->is_queue && !ai->is_dynamic) {
        if (ai->elem_type_kind == DataTypeKind::kByte) {
          output += FormatUnpackedByteArrayAsString(arg->text, *ai, ctx);
        } else {
          ctx.GetDiag().Error(
              {},
              "unformatted unpacked-array argument to a display or write task "
              "is illegal unless its elements are of type byte");
        }
        continue;
      }
    }
    // A bare expression renders under the task's default radix; a value
    // carrying string-typed data is always rendered as its character
    // sequence regardless of the task name. The rendering carries the
    // §21.2.1.2 automatic sizing, so a plain $display pads its default
    // decimal exactly as an explicit %d would.
    auto val = EvalExpr(arg, ctx, arena);
    char spec =
        val.is_string ? 's' : DefaultRadixForDisplayWriteTask(expr->callee);
    output += FormatArgAutoSized(val, spec);
  }
  std::cout << output;
  // The display family ($display, $displayb, $displayo, $displayh) terminates
  // its output with a newline; the write family does not.
  if (expr->callee.starts_with("$display")) std::cout << "\n";
}

// §20.10: the hierarchical name of the scope in which a severity system task is
// called -- the same walk %m performs (§21.2.1.5): the top instance name, then
// the running process's instance chain, then the active subroutine / named
// block / labeled statement scopes in lexical order.
static std::string SeverityScopeName(SimContext& ctx) {
  std::string name(ctx.FindInstanceType(""));
  if (Process* proc = ctx.CurrentProcess()) {
    std::string prefix = proc->inst_prefix;
    if (!prefix.empty() && prefix.back() == '.') prefix.pop_back();
    if (!prefix.empty()) {
      if (!name.empty()) name += '.';
      name += prefix;
    }
  }
  for (std::string_view scope : ctx.ActiveNamedScopes()) {
    if (!name.empty()) name += '.';
    name += std::string(scope);
  }
  return name;
}

void EmitSeverityHeader(SimContext& ctx, std::string_view prefix,
                        std::string_view msg, std::ostream& os, uint32_t line) {
  // §20.10: the tool-specific message reports the severity plus the required
  // call-site information -- the simulation time, the hierarchical scope of the
  // call, and its source line (the `__LINE__ equivalent, see §22.13). A line of
  // 0 marks a call site with no recorded source location.
  std::string scope = SeverityScopeName(ctx);
  os << "[" << ctx.CurrentTime().ticks << "] " << prefix;
  if (!scope.empty()) os << " " << scope;
  if (line != 0) os << " (line " << line << ")";
  if (!msg.empty()) os << ": " << msg;
  os << "\n";
  ctx.SetLastSeverity(prefix, msg, ctx.CurrentTime(), scope, line);
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
  // §20.10: report the source line of the call, matching the `__LINE__ the
  // preprocessor would produce here (§22.13).
  EmitSeverityHeader(ctx, prefix, msg, os, expr->range.start.line);
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

// §21.7.2.3: the $version section of the VCD header reproduces the $dumpfile
// task that created the file, and when the filename was specified by a
// variable or an expression the unevaluated literal -- not the resolved
// string -- is what shall appear there. This renders the argument back to its
// source spelling: literals and identifiers keep their token text, and the
// composite forms are rebuilt from their parts.
static std::string DumpfileArgSourceText(const Expr* arg) {
  if (arg == nullptr) return {};
  switch (arg->kind) {
    case ExprKind::kMemberAccess:
      return DumpfileArgSourceText(arg->lhs) +
             (arg->is_scope_resolution ? "::" : ".") +
             DumpfileArgSourceText(arg->rhs);
    case ExprKind::kSelect: {
      std::string text = DumpfileArgSourceText(arg->base) + "[" +
                         DumpfileArgSourceText(arg->index);
      if (arg->index_end != nullptr) {
        text += ":" + DumpfileArgSourceText(arg->index_end);
      }
      return text + "]";
    }
    case ExprKind::kConcatenation: {
      std::string text = "{";
      for (size_t i = 0; i < arg->elements.size(); ++i) {
        if (i > 0) text += ",";
        text += DumpfileArgSourceText(arg->elements[i]);
      }
      return text + "}";
    }
    case ExprKind::kCall: {
      // A function call naming the file keeps its call form -- the callee and
      // its (unevaluated) arguments -- not the string the call returns.
      std::string text = std::string(arg->callee) + "(";
      for (size_t i = 0; i < arg->args.size(); ++i) {
        if (i > 0) text += ",";
        text += DumpfileArgSourceText(arg->args[i]);
      }
      return text + ")";
    }
    default:
      // Literals (a string literal keeps its quotes) and identifiers carry
      // their own source text.
      return std::string(arg->text);
  }
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

// §21.7.3.1: the simulator performs the file-writing checks for the resolved
// $dumpports output name and reports problems rather than failing silently:
// the directory the name points into (the working directory for a bare name)
// must exist and be writable.
static void CheckDumpportsFileWritable(const std::string& name,
                                       SimContext& ctx) {
  std::string dir = ".";
  auto slash = name.rfind('/');
  if (slash == 0) {
    dir = "/";
  } else if (slash != std::string::npos) {
    dir = name.substr(0, slash);
  }
  if (access(dir.c_str(), W_OK) != 0) {
    ctx.GetDiag().Error({},
                        "$dumpports cannot write dump file at path: " + name);
  }
}

// §21.7.3.1: decide whether the trailing $dumpports argument denotes the
// filename. A string literal always does; an identifier does when it names a
// variable -- the filename may be a string-typed or integral variable holding
// a character string, whereas an identifier that names no variable is a
// module scope belonging to the scope_list.
static bool DumpportsLastArgIsFileName(const Expr* expr, SimContext& ctx) {
  if (expr->args.empty()) return false;
  const Expr* last = expr->args.back();
  if (last == nullptr) return false;
  if (last->kind == ExprKind::kStringLiteral) return true;
  return last->kind == ExprKind::kIdentifier &&
         ctx.FindVariable(last->text) != nullptr;
}

// Resolves the $dumpports output filename (§21.7.3.1). The filename is an
// expression given as a string literal, a string-typed variable, or an
// integral variable containing a character string; when no filename is
// supplied the output defaults to dumpports.vcd in the working directory.
static std::string ResolveDumpportsFileName(const Expr* expr, SimContext& ctx,
                                            Arena& arena, bool last_is_file) {
  if (last_is_file) {
    const Expr* last = expr->args.back();
    if (last->kind == ExprKind::kStringLiteral) {
      auto text = last->text;
      if (text.size() >= 2 && text.front() == '"') {
        return std::string(text.substr(1, text.size() - 2));
      }
      return std::string(text);
    }
    // A string or integral variable names the file through the character
    // string its evaluated value holds.
    return FormatValueAsString(EvalExpr(last, ctx, arena));
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

// §21.7.1.2: reduce a $dumpvars scope argument to the name under which the
// selected object is registered. A plain identifier keeps its name and a string
// literal loses its quotes. A hierarchical reference such as top.mod2.net1
// parses as a chain of member accesses whose text is spread across the chain,
// so rebuild it into the dotted downward path (e.g. c1.val) that matches the
// key an instance's variable is registered under -- without this a
// member-access argument would carry no text of its own and be dropped.
static std::string DumpvarsScopePath(const Expr* arg) {
  if (arg->kind == ExprKind::kMemberAccess) {
    std::vector<std::string_view> parts;
    const Expr* e = arg;
    while (e != nullptr && e->kind == ExprKind::kMemberAccess) {
      if (e->rhs != nullptr) parts.push_back(e->rhs->text);
      e = e->lhs;
    }
    if (e != nullptr) parts.push_back(e->text);
    std::string path;
    for (auto it = parts.rbegin(); it != parts.rend(); ++it) {
      if (!path.empty()) path.push_back('.');
      path.append(*it);
    }
    return path;
  }
  std::string_view text = arg->text;
  if (arg->kind == ExprKind::kStringLiteral && text.size() >= 2 &&
      text.front() == '"') {
    text = text.substr(1, text.size() - 2);
  }
  return std::string(text);
}

// §21.7.1.2: dump the variables named by a $dumpvars call. With no arguments
// every variable in the model is dumped. When arguments are present the first
// is the level count -- how many levels of the hierarchy below each named
// module instance to dump, with 0 meaning every level below -- and the
// remaining arguments name the scopes (whole module instances or individual
// variables) to dump. The level count never names a variable of its own and
// does not apply to scope arguments that name an individual variable.
static void ExecDumpvars(const Expr* expr, SimContext& ctx, Arena& arena,
                         VcdWriter* vcd) {
  if (!vcd) return;
  std::vector<std::string> scope_storage;
  for (size_t i = 1; i < expr->args.size(); ++i) {
    if (expr->args[i] == nullptr) continue;
    auto scope = DumpvarsScopePath(expr->args[i]);
    if (!scope.empty()) scope_storage.push_back(std::move(scope));
  }
  // §21.7.2.4: the checkpoint section follows the simulation_time command of
  // the time unit the task executed in, so the writer stamps that time first.
  uint64_t now = ctx.CurrentTime().ticks;
  if (scope_storage.empty()) {
    vcd->DumpAllValues(now);
    return;
  }
  uint64_t level = 0;
  if (!expr->args.empty() && expr->args[0] != nullptr) {
    level = EvalExpr(expr->args[0], ctx, arena).ToUint64();
  }
  std::vector<std::string_view> scopes(scope_storage.begin(),
                                       scope_storage.end());
  vcd->DumpScopeSelectedValues(scopes, level, now);
}

// §21.7.3.1: gather the unique module scopes named in a $dumpports scope_list.
// scope_end excludes a trailing filename argument. Only modules may be named:
// a string-literal entry is not a valid module_identifier and an entry naming
// a variable is rejected too. A hierarchical entry keeps its period-separated
// downward path. Duplicate scopes within this call and across earlier
// $dumpports calls are reported rather than dumped.
static std::vector<std::string> CollectDumpportsScopes(const Expr* expr,
                                                       size_t scope_end,
                                                       SimContext& ctx) {
  std::vector<std::string> scopes;
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
    // A plain or hierarchical entry becomes the dotted path a module
    // instance's variables are registered under (e.g. c1 or c1.g1).
    std::string scope = DumpvarsScopePath(expr->args[i]);
    if (scope.empty()) continue;
    // §21.7.3.1: only modules are allowed in the scope_list; an entry that
    // resolves to a variable is rejected.
    if (ctx.FindVariable(scope) != nullptr) {
      ctx.GetDiag().Error(
          {}, "$dumpports scope_list entry must be a module, not a variable");
      continue;
    }
    // §21.7.3.1: each scope named in a $dumpports scope_list shall be
    // unique; a repeated scope is reported rather than dumped twice.
    if (std::find(scopes.begin(), scopes.end(), scope) != scopes.end()) {
      ctx.GetDiag().Error({}, "$dumpports scope_list entries must be unique");
      continue;
    }
    // §21.7.3.1: scope names must also be unique across separate $dumpports
    // calls, not just within one call.
    if (!ctx.RegisterDumpportsScope(scope)) {
      ctx.GetDiag().Error({},
                          "$dumpports scope already named by an earlier call");
      continue;
    }
    scopes.push_back(std::move(scope));
  }
  return scopes;
}

// §21.7.3.1: name the (extended) VCD output and select the ports to dump. A
// trailing filename argument (string literal, or a string/integral variable
// holding the name) names the file, defaulting to dumpports.vcd when omitted.
// The leading arguments form the scope_list naming the modules whose ports
// are dumped; with no scope_list the scope is the calling module, so every
// port registered from the point of the call is treated as a primary I/O pin
// and dumped. The value change dumping itself starts at the end of the
// current simulation time unit, so the opening checkpoint is scheduled on the
// writer rather than emitted here. Dumping reuses the 4-state VCD machinery,
// which the extended VCD file inherits unless otherwise stated.
static void ExecDumpports(const Expr* expr, SimContext& ctx, Arena& arena,
                          VcdWriter* vcd) {
  // §21.7.3.1: $dumpports can be invoked multiple times, but every execution
  // shall be at the same simulation time.
  if (!ctx.RegisterDumpportsTime(ctx.CurrentTime().ticks)) {
    ctx.GetDiag().Error(
        {}, "all $dumpports tasks must execute at the same simulation time");
    return;
  }
  bool last_is_file = DumpportsLastArgIsFileName(expr, ctx);
  ctx.SetDumpFileName(ResolveDumpportsFileName(expr, ctx, arena, last_is_file));
  // §21.7.3.1: the simulator checks that the named file is writable and
  // reports an error when it is not.
  CheckDumpportsFileWritable(ctx.GetDumpFileName(), ctx);
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
  std::vector<std::string> scopes =
      CollectDumpportsScopes(expr, scope_end, ctx);
  vcd->SchedulePortDumpStart(std::move(scopes), ctx.CurrentTime().ticks);
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
static bool ExecBasicVcdControl(std::string_view name, VcdWriter* vcd,
                                SimContext& ctx) {
  // §21.7.2.4: each checkpoint section sits after the simulation_time command
  // of its execution time, so the timed writer entry points are used.
  uint64_t now = ctx.CurrentTime().ticks;
  if (name == "$dumpall") {
    // Emit a checkpoint of every selected variable's current value (§21.7.1.4).
    if (vcd) vcd->DumpAll(now);
  } else if (name == "$dumpoff") {
    // Suspend dumping with an all-x checkpoint (§21.7.1.3).
    if (vcd) vcd->DumpOff(now);
  } else if (name == "$dumpon") {
    // Resume dumping with a checkpoint of current values (§21.7.1.3).
    if (vcd) vcd->DumpOn(now);
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
    // §21.7.2.3: remember the filename argument exactly as written so the
    // $version section can reproduce the $dumpfile call unevaluated.
    ctx.SetDumpFileLiteral(expr->args.empty()
                               ? std::string{}
                               : DumpfileArgSourceText(expr->args[0]));
    ctx.SetDumpFileName(ResolveDumpFileName(expr, ctx, arena));
  } else if (name == "$dumpvars") {
    ExecDumpvars(expr, ctx, arena, vcd);
  } else if (name == "$dumplimit") {
    // §21.7.1.5: the single argument bounds the VCD file size in bytes.
    ExecDumpLimit(expr, ctx, arena, vcd);
  } else if (name == "$dumpports") {
    ExecDumpports(expr, ctx, arena, vcd);
  } else if (!ExecBasicVcdControl(name, vcd, ctx)) {
    ExecDumpportsControl(expr, ctx, arena, vcd, name);
  }
  return MakeLogic4VecVal(arena, 1, 0);
}

}  // namespace delta
