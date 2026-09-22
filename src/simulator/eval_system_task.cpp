
#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <cstring>
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
#include "simulator/eval_expr_internal.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/net.h"
#include "simulator/probabilistic_distribution.h"
#include "simulator/process.h"
#include "simulator/scope_hier_name.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
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

// §21.2.1.6 (C4, printed page 662): a tagged union prints its currently valid
// member as "tag:value". The active member's width and type come from the
// union's layout `st`, or the value's own width where none is registered.
static std::string FormatTaggedUnionForP(std::string_view tag,
                                         const StructTypeInfo* st,
                                         const Logic4Vec& val, Arena& arena) {
  DataTypeKind kind = DataTypeKind::kImplicit;
  uint32_t width = val.width;
  const StructFieldInfo* f = st ? FindStructField(st, tag) : nullptr;
  if (f != nullptr) {
    kind = f->type_kind;
    width = f->width;
  }
  Logic4Vec slice = SliceField(val, 0, width, kind, arena);
  return "'{" + std::string(tag) + ":" + FormatSingularForP(slice, kind) + "}";
}

// §21.2.1.6 (C4): the tagged form of the variable `name`. Returns no value
// when the variable is not a tagged union holding a tag (the caller falls
// through to the next aggregate form).
static std::optional<std::string> BuildFormatPTaggedUnion(std::string_view name,
                                                          const Logic4Vec& val,
                                                          SimContext& ctx,
                                                          Arena& arena) {
  auto tag = ctx.GetVariableTag(TagKeyOfName(name, ctx));
  if (tag.empty()) return std::nullopt;
  return FormatTaggedUnionForP(tag, StructLayoutOfName(name, ctx), val, arena);
}

// §21.2.1.6 (C2/C3/C7a): a struct prints every member as "name:value"; a
// plain (untagged) union prints only its first declared member. Returns no
// value when the variable is not a struct/union type.
static std::optional<std::string> BuildFormatPStruct(std::string_view name,
                                                     const Logic4Vec& val,
                                                     SimContext& ctx,
                                                     Arena& arena) {
  const StructTypeInfo* st = StructLayoutOfName(name, ctx);
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
  const StructTypeInfo* st = StructLayoutOfName(name, ctx);
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
  const StructTypeInfo* st = StructLayoutOfName(name, ctx);
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
  const StructTypeInfo* st = StructLayoutOfName(name, ctx);
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
//
// §23.9: the argument is a name resolved within the running instance, so each
// form above asks for its struct or union layout by the key that instance's
// storage was created under (StructLayoutOfName). Asked by the bare name, a
// struct of an instantiated module printed as one number, a tagged union's
// valid member printed at the union's width and as unsigned, and a queue of
// structs printed each element as a number.
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

// §21.2.1.6 (printed page 662) prints an aggregate wherever the argument names
// one, and §7.3.2 (printed 151) has a tagged union carry its tag as a member
// of a structure as it does as a variable: `s.u` after `s.u = tagged Valid 9`
// prints '{Valid:9}, and a structure member prints its named members. The
// member's layout and, for a tagged union, its current tag are walked to by
// ResolveMemberLayout, under the member's own key; asked by the variable's
// name alone, a member argument had no name and printed as one number.
// Returns no value for an argument that is no member of a variable's layout.
static std::optional<std::string> BuildFormatPMember(const Expr* arg,
                                                     const Logic4Vec& val,
                                                     SimContext& ctx,
                                                     Arena& arena) {
  if (arg->kind != ExprKind::kMemberAccess || arg->is_scope_resolution)
    return std::nullopt;
  std::string name;
  BuildLhsName(arg, name);
  size_t dot = MemberPathSplit(name, ctx);
  if (dot == std::string::npos) return std::nullopt;
  std::string_view base = std::string_view(name).substr(0, dot);
  const StructTypeInfo* info = StructLayoutOfName(base, ctx);
  if (info == nullptr) return std::nullopt;
  MemberLayout member = ResolveMemberLayout(
      base, info, std::string_view(name).substr(dot + 1), ctx);
  if (member.layout == nullptr) return std::nullopt;
  if (!member.tag.empty())
    return FormatTaggedUnionForP(member.tag, member.layout, val, arena);
  return FormatStructValueForP(*member.layout, val, arena);
}

static std::string BuildFormatP(const Expr* arg, const Logic4Vec& val,
                                SimContext& ctx) {
  Arena& arena = ctx.GetArena();
  std::string_view name = (arg->kind == ExprKind::kIdentifier)
                              ? std::string_view(arg->text)
                              : std::string_view{};

  if (auto named = BuildFormatPNamed(name, val, ctx, arena)) return *named;
  if (auto member = BuildFormatPMember(arg, val, ctx, arena)) return *member;

  // §21.2.1.6 (C10): %p on a singular expression formats it as one element of
  // an aggregate would be formatted.
  return FormatSingularForP(val, DataTypeKind::kImplicit);
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
// The clause asks a %v for "a corresponding scalar reference" and reports "the
// strength of a scalar net", so an argument is one of three things: a reference
// to a scalar of a net, whose strength there is to render; a reference to a net
// that is not a scalar, which the clause admits no rendering for and which is
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
// the declaration, since "the actual bit that is accessed by an address is, in
// part, determined by the declaration". An index carrying x or z names no bit
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

// §21.2.1.4's operand, classified. A net declared without a range is a scalar
// (§6.9) and names its only bit. A bit-select of a vector net is a scalar
// reference too: §11.5.1 has it address one bit of the vector, and one bit of a
// net is the scalar whose strength the clause reports. A select that still
// names more than one bit is not, being no more a single bit than the vector it
// selects from.
static PercentVArg ClassifyPercentVArg(const Expr* arg, SimContext& ctx,
                                       Arena& arena) {
  if (arg->kind == ExprKind::kIdentifier) {
    const Net* net = ctx.FindNet(arg->text);
    if (net == nullptr || net->resolved == nullptr) return {};
    if (!IsScalarNet(*net->resolved)) return {PercentVArgKind::kVectorNet};
    return {PercentVArgKind::kNetBit, net, 0};
  }
  if (arg->kind != ExprKind::kSelect || arg->base == nullptr ||
      arg->base->kind != ExprKind::kIdentifier)
    return {};
  const Net* net = ctx.FindNet(arg->base->text);
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

// §21.2.1.4: "For each %v specification that appears in a string literal, a
// corresponding scalar reference shall follow the string literal in the
// argument list". Whether this argument breaks that is settled here, where the
// net is in reach, and reported by the formatter, where it is known whether a
// %v is what consumed the argument: the renderings are built for every
// argument a template takes, so reporting here would report a vector net
// passed to %h. The two shapes that break it are told apart so that each is
// named by what it is: a net reference naming the whole net, or a select of it
// that still names more than one bit. Zero is every argument that does not
// break it.
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
// `default_radix` is the specifier a bare expression argument is rendered
// under: the task's own for the display and write families, decimal for a
// severity task, whose name says nothing of a radix ($info ends in the
// letter the octal family does).
static void AppendDisplayArg(const Expr* expr, size_t& i, SimContext& ctx,
                             Arena& arena, std::string& output,
                             char default_radix) {
  const Expr* arg = expr->args[i];
  // An omitted argument -- a leading, trailing, or doubled comma in the call --
  // carries no expression and is rendered as a single space.
  if (arg == nullptr) {
    output += ' ';
    return;
  }
  if (arg->kind == ExprKind::kStringLiteral) {
    std::string fmt = ExtractFormatString(arg);
    DisplayArgRenderings r = CollectDisplayArgs(expr, i, fmt, ctx, arena);
    output += FormatDisplay(fmt, r.vals,
                            {.p_fmts = &r.p_fmts,
                             .v_fmts = &r.v_fmts,
                             .arg_nonscalar_net = &r.nonscalar_nets,
                             .ctx = &ctx,
                             .arg_unpacked_agg = &r.agg_flags,
                             .arg_byte_strings = &r.byte_strings,
                             .loc = arg->range.start});
    return;
  }
  if (AppendUnpackedArrayArg(arg, ctx, output)) return;
  // A bare expression renders under the task's default radix; a value carrying
  // string-typed data is always rendered as its character sequence regardless
  // of the task name. The rendering carries the §21.2.1.2 automatic sizing, so
  // a plain $display pads its default decimal exactly as an explicit %d would.
  auto val = EvalExpr(arg, ctx, arena);
  char spec = val.is_string ? 's' : default_radix;
  output += FormatArgAutoSized(val, spec);
}

void ExecDisplayWrite(const Expr* expr, SimContext& ctx, Arena& arena) {
  // The arguments are processed in the order they appear. A string literal acts
  // as a format template whose specifiers are filled by the expression
  // arguments that immediately follow it.
  std::string output;
  char radix = DefaultRadixForDisplayWriteTask(expr->callee);
  for (size_t i = 0; i < expr->args.size(); ++i)
    AppendDisplayArg(expr, i, ctx, arena, output, radix);
  ctx.Out() << output;
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
  for (size_t i = start_idx; i < expr->args.size(); ++i) {
    AppendDisplayArg(expr, i, ctx, arena, msg, 'd');
  }
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
