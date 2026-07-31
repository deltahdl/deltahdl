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
// §21.2.1.6: the %p rendering of a named object, or nullopt when the name
// denotes nothing with an aggregate or handle rendering of its own. The
// aggregate forms are tried outermost-first: a queue/dynamic array, an
// associative array, then a fixed-size unpacked array. An array whose element
// type is a struct or enum also carries that type's info under the same name,
// so the array checks come before the struct/enum ones.
static std::optional<std::string> BuildFormatPNamed(std::string_view name,
                                                    const Logic4Vec& val,
                                                    SimContext& ctx,
                                                    Arena& arena) {
  if (name.empty()) return std::nullopt;
  if (auto r = BuildFormatPTaggedUnion(name, val, ctx, arena)) return r;
  if (auto r = BuildFormatPQueue(name, ctx, arena)) return r;
  if (auto r = BuildFormatPAssoc(name, ctx, arena)) return r;
  if (auto r = BuildFormatPArray(name, ctx, arena)) return r;
  if (auto r = BuildFormatPStruct(name, val, ctx, arena)) return r;
  if (auto r = BuildFormatPClassHandle(name, val, ctx)) return r;
  if (auto r = BuildFormatPVirtualInterface(name, ctx)) return r;
  if (auto r = BuildFormatPChandle(name, val, ctx)) return r;
  return BuildFormatPEnum(name, val, ctx);
}

static std::string BuildFormatP(const Expr* arg, const Logic4Vec& val,
                                SimContext& ctx) {
  Arena& arena = ctx.GetArena();
  std::string_view name = (arg->kind == ExprKind::kIdentifier)
                              ? std::string_view(arg->text)
                              : std::string_view{};

  if (auto named = BuildFormatPNamed(name, val, ctx, arena)) return *named;

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

// §21.2: the per-argument renderings a format template consumes alongside the
// values -- the %p and %v forms of each argument, its unpacked-aggregate
// classification, and, for an unpacked array of byte, the character string %s
// prints.
struct DisplayArgRenderings {
  std::vector<Logic4Vec> vals;
  std::vector<std::string> p_fmts;
  std::vector<std::string> v_fmts;
  std::vector<char> agg_flags;
  std::vector<std::string> byte_strings;
};

// Evaluate the expression arguments that follow a format template, stopping at
// the next string literal (which starts a template of its own) and advancing
// `i` past those consumed.
static DisplayArgRenderings CollectDisplayArgs(const Expr* expr, size_t& i,
                                               SimContext& ctx, Arena& arena) {
  DisplayArgRenderings r;
  const size_t kN = expr->args.size();
  while (i + 1 < kN && expr->args[i + 1] != nullptr &&
         expr->args[i + 1]->kind != ExprKind::kStringLiteral) {
    const Expr* val_arg = expr->args[++i];
    auto v = EvalExpr(val_arg, ctx, arena);
    r.vals.push_back(v);
    r.p_fmts.push_back(BuildFormatP(val_arg, v, ctx));
    r.v_fmts.push_back(BuildFormatV(val_arg, ctx));
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
        {},
        "unformatted unpacked-array argument to a display or write task "
        "is illegal unless its elements are of type byte");
  }
  return true;
}

// Render one argument of a display or write task, consuming any expression
// arguments a format template takes with it.
static void AppendDisplayArg(const Expr* expr, size_t& i, SimContext& ctx,
                             Arena& arena, std::string& output) {
  const Expr* arg = expr->args[i];
  // An omitted argument -- a leading, trailing, or doubled comma in the call --
  // carries no expression and is rendered as a single space.
  if (arg == nullptr) {
    output += ' ';
    return;
  }
  if (arg->kind == ExprKind::kStringLiteral) {
    std::string fmt = ExtractFormatString(arg);
    DisplayArgRenderings r = CollectDisplayArgs(expr, i, ctx, arena);
    output += FormatDisplay(fmt, r.vals,
                            {.p_fmts = &r.p_fmts,
                             .v_fmts = &r.v_fmts,
                             .ctx = &ctx,
                             .arg_unpacked_agg = &r.agg_flags,
                             .arg_byte_strings = &r.byte_strings});
    return;
  }
  if (AppendUnpackedArrayArg(arg, ctx, output)) return;
  // A bare expression renders under the task's default radix; a value carrying
  // string-typed data is always rendered as its character sequence regardless
  // of the task name. The rendering carries the §21.2.1.2 automatic sizing, so
  // a plain $display pads its default decimal exactly as an explicit %d would.
  auto val = EvalExpr(arg, ctx, arena);
  char spec =
      val.is_string ? 's' : DefaultRadixForDisplayWriteTask(expr->callee);
  output += FormatArgAutoSized(val, spec);
}

void ExecDisplayWrite(const Expr* expr, SimContext& ctx, Arena& arena) {
  // The arguments are processed in the order they appear. A string literal acts
  // as a format template whose specifiers are filled by the expression
  // arguments that immediately follow it.
  std::string output;
  for (size_t i = 0; i < expr->args.size(); ++i)
    AppendDisplayArg(expr, i, ctx, arena, output);
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
  // §33.7: the text is produced after the calling process has run to
  // completion, so the instance this call was written in is recorded now and
  // reinstated for the span of the output. Without it the binding the %l/%L
  // specifier reports would be read off whatever process the context happens to
  // have installed when the deferred text is produced.
  std::string scope;
  if (Process* proc = ctx.CurrentProcess()) scope = proc->inst_prefix;
  event->callback = [expr, scope, &ctx, &arena]() {
    ctx.SetDeferredBindingScope(scope);
    ExecDisplayWrite(expr, ctx, arena);
    ctx.SetDeferredBindingScope(std::nullopt);
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

}  // namespace delta
