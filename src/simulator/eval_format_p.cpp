// §21.2.1.6: the %p format specifier's assignment-pattern rendering of
// aggregates, enums, class handles and singular values.

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/eval_array.h"
#include "simulator/eval_array_element_queue.h"
#include "simulator/eval_expr_internal.h"
#include "simulator/eval_function_args_scoped.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/struct_string_member.h"
#include "simulator/variable.h"

namespace delta {

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

// §21.2.1.6 (C7b): an enumerated value prints as the matching member name when
// the value is one named by the type; otherwise it prints in the base type's
// (decimal) form.
static std::string FormatEnumValueForP(const EnumTypeInfo& et,
                                       const Logic4Vec& val) {
  // §21.2.1.6 with §6.19: a value is a member where every bit matches, x and
  // z included, as the enum methods match it, so `XX='x` prints XX; read as
  // a number, a value holding x or z matched no member.
  if (val.nwords > 0) {
    const Logic4Word& w = val.words[0];
    for (const auto& m : et.members) {
      if (m.value == w.aval && m.xz == w.bval) return std::string(m.name);
    }
  }
  return FormatArg(val, 'd');
}

static std::string FormatStructValueForP(const StructTypeInfo& st,
                                         const Logic4Vec& val, SimContext& ctx);

// §21.2.1.6 (C2/C7a): render one struct or union member as "name:value". A
// member that is itself a struct or union prints as a nested assignment
// pattern under the same rules, and one of an enum type as the name of its
// value (C7b) as the enum prints on its own; any other singular member is
// formatted by the singular rules.
static std::string FormatMember(const StructFieldInfo& f, const Logic4Vec& val,
                                SimContext& ctx) {
  Logic4Vec slice =
      SliceField(val, f.bit_offset, f.width, f.type_kind, ctx.GetArena());
  std::string label = std::string(f.name) + ":";
  if (f.nested != nullptr)
    return label + FormatStructValueForP(*f.nested, slice, ctx);
  if (!f.type_name.empty()) {
    if (const EnumTypeInfo* et = ctx.FindEnumType(f.type_name))
      return label + FormatEnumValueForP(*et, slice);
  }
  // §7.2 with §6.16: a string member's bits are a handle to its text.
  if (f.type_kind == DataTypeKind::kString)
    slice = StringMemberText(slice, ctx.GetArena());
  return label + FormatSingularForP(slice, f.type_kind);
}

// §21.2.1.6 (C2/C3/C7a): the assignment-pattern text of one struct or union
// value: every member as "name:value" in declaration order for a struct, only
// the first declared member for an (untagged) union. Nested aggregate members
// recurse through FormatMember.
static std::string FormatStructValueForP(const StructTypeInfo& st,
                                         const Logic4Vec& val,
                                         SimContext& ctx) {
  std::string out = "'{";
  size_t count =
      st.is_union ? std::min<size_t>(1, st.fields.size()) : st.fields.size();
  for (size_t i = 0; i < count; ++i) {
    if (i) out += ", ";
    out += FormatMember(st.fields[i], val, ctx);
  }
  out += "}";
  return out;
}

// §21.2.1.6: render one element of an unpacked aggregate. The traversal
// descends until a singular value is reached: a struct-typed element becomes a
// nested assignment pattern, an enum-typed element its member name, and any
// other element the singular form.
// The element layout and enum type an array's elements are rendered by.
struct AggElemTypes {
  const StructTypeInfo* st;
  const EnumTypeInfo* et;
};

static std::string FormatAggElemForP(const Logic4Vec& val, DataTypeKind kind,
                                     const StructTypeInfo* st,
                                     const EnumTypeInfo* et, SimContext& ctx) {
  if (st != nullptr) return FormatStructValueForP(*st, val, ctx);
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
                                                     SimContext& ctx) {
  const StructTypeInfo* st = StructLayoutOfName(name, ctx);
  if (st == nullptr) return std::nullopt;
  return FormatStructValueForP(*st, val, ctx);
}

// §7.6 (printed page 160): array elements correspond "by the left-to-right
// order of elements in each array", so int A[7:0] = B of int B[1:8] puts B[1]
// in A[7], and §10.9.1's array pattern matches its items "element for element"
// in that order. %p's pattern, which §21.2.1.6 requires be "a legal
// interpretation of the assignment pattern syntax", thus lists a dimension
// spanning addresses [lo, lo+size-1] from its left bound: its i-th item is the
// i-th address from the top when the dimension was declared descending.
static uint32_t LeftToRightAddress(uint32_t lo, uint32_t size, bool descending,
                                   uint32_t i) {
  return descending ? lo + size - 1 - i : lo + i;
}

// §21.2.1.6 (C5): dimension `d` of a multidimensional unpacked array, outermost
// first, as a pattern of the patterns of the dimensions below it; the elements
// of the last live as variables named "arr[i][j]" by the lowerer.
static std::string FormatArrayDimForP(const std::string& prefix,
                                      const ArrayInfo& ai, size_t d,
                                      const AggElemTypes& types,
                                      SimContext& ctx) {
  std::string out = "'{";
  for (uint32_t i = 0; i < ai.dim_sizes[d]; ++i) {
    if (i) out += ", ";
    bool descending = d < ai.dim_descending.size() && ai.dim_descending[d];
    uint32_t idx =
        LeftToRightAddress(ai.dim_los[d], ai.dim_sizes[d], descending, i);
    std::string elem = prefix + "[" + std::to_string(idx) + "]";
    if (d + 1 < ai.dim_sizes.size()) {
      out += FormatArrayDimForP(elem, ai, d + 1, types, ctx);
      continue;
    }
    Variable* var = ctx.FindVariable(elem);
    Logic4Vec ev =
        var ? var->value : MakeLogic4VecVal(ctx.GetArena(), ai.elem_width, 0);
    out += FormatAggElemForP(ev, ai.elem_type_kind, types.st, types.et, ctx);
  }
  return out + "}";
}

// §21.2.1.6 (C5): a fixed-size unpacked array prints as an assignment pattern
// of its elements from its left bound, each element rendered by the traversal
// rules (a struct element as a nested pattern, an enum element as its member
// name). Elements live as their own variables, named "arr[idx]" by the lowerer.
// Returns no value when the variable is not a non-empty unpacked array.
static std::optional<std::string> BuildFormatPArray(std::string_view name,
                                                    SimContext& ctx,
                                                    Arena& arena) {
  auto* ai = ctx.FindArrayInfo(name);
  if (ai == nullptr || ai->size == 0) return std::nullopt;
  const StructTypeInfo* st = StructLayoutOfName(name, ctx);
  const EnumTypeInfo* et = ctx.GetVariableEnumType(name);
  if (ai->dim_sizes.size() >= 2)
    return FormatArrayDimForP(std::string(name), *ai, 0, {st, et}, ctx);
  std::string out = "'{";
  for (uint32_t i = 0; i < ai->size; ++i) {
    if (i) out += ", ";
    uint32_t idx = LeftToRightAddress(ai->lo, ai->size, ai->is_descending, i);
    std::string elem_name = std::string(name) + "[" + std::to_string(idx) + "]";
    Variable* elem = ctx.FindVariable(elem_name);
    Logic4Vec ev =
        elem ? elem->value : MakeLogic4VecVal(arena, ai->elem_width, 0);
    out += FormatAggElemForP(ev, ai->elem_type_kind, st, et, ctx);
  }
  out += "}";
  return out;
}

// §21.2.1.6 (C5 with C7c): what %p prints each element of an unpacked array
// by -- its type, as far as %p tells elements apart, and its structure layout
// and enumeration.
struct ElementTypeForP {
  DataTypeKind kind = DataTypeKind::kImplicit;
  AggElemTypes types{nullptr, nullptr};
};

// The element type the array `name` declares. A fixed-size array records it;
// the elements of a queue, dynamic array or associative array carry no mark
// of their own, so a string array's elements read as numbers, the codes of
// their characters, unless the declaration's type reaches them from here: the
// lowerer marks such an array's own name a string variable when its elements
// are strings.
static ElementTypeForP ElementTypeOfName(std::string_view name,
                                         SimContext& ctx) {
  ElementTypeForP type;
  if (ctx.FindQueue(name) != nullptr || ctx.FindAssocArray(name) != nullptr) {
    if (ctx.IsStringVariable(name)) type.kind = DataTypeKind::kString;
  } else if (const ArrayInfo* ai = ctx.FindArrayInfo(name)) {
    type.kind = ai->elem_type_kind;
  }
  type.types = {StructLayoutOfName(name, ctx), ctx.GetVariableEnumType(name)};
  return type;
}

static std::string FormatQueueForP(const QueueObject* q,
                                   const ElementTypeForP& type,
                                   SimContext& ctx);

// §21.2.1.6 with §7.4 and §7.10: element `pos` of `q`. Where the elements are
// queues or fixed-size arrays (QueueObject::elements_are_queues) the value in
// `elements` only holds the element's place, and the element is its own
// queue, printed as a nested pattern; one never written holds its type's
// default (ElementQueueOrDefault).
static std::string FormatQueueElementForP(const QueueObject& q, size_t pos,
                                          const ElementTypeForP& type,
                                          SimContext& ctx) {
  if (!q.elements_are_queues)
    return FormatAggElemForP(q.elements[pos], type.kind, type.types.st,
                             type.types.et, ctx);
  return FormatQueueForP(ElementQueueOrDefault(q, pos, ctx.GetArena()), type,
                         ctx);
}

// §21.2.1.6 (C5): a queue or dynamic array (both stored as a QueueObject)
// prints its current elements as an assignment pattern in index order; an
// empty one prints the empty pattern, and so does a null one, the queue of an
// associative array's element never made.
static std::string FormatQueueForP(const QueueObject* q,
                                   const ElementTypeForP& type,
                                   SimContext& ctx) {
  std::string out = "'{";
  for (size_t i = 0; q != nullptr && i < q->elements.size(); ++i) {
    if (i) out += ", ";
    out += FormatQueueElementForP(*q, i, type, ctx);
  }
  return out + "}";
}

// §21.2.1.6 (C5): the queue or dynamic array `name` names, or no value when
// it names neither.
static std::optional<std::string> BuildFormatPQueue(std::string_view name,
                                                    SimContext& ctx) {
  QueueObject* q = ctx.FindQueue(name);
  if (q == nullptr) return std::nullopt;
  return FormatQueueForP(q, ElementTypeOfName(name, ctx), ctx);
}

// §21.2.1.6 (C5): an associative array prints as an assignment pattern with
// index labels, one "key:value" item per populated element in key order (a
// string key is quoted), an element that is a queue as a nested pattern.
// Returns no value when the name is not an associative array.
static std::optional<std::string> BuildFormatPAssoc(std::string_view name,
                                                    SimContext& ctx) {
  AssocArrayObject* aa = ctx.FindAssocArray(name);
  if (aa == nullptr) return std::nullopt;
  ElementTypeForP type = ElementTypeOfName(name, ctx);
  auto value_of = [&](const auto& queues, const auto& key, const Logic4Vec& v) {
    if (!aa->elements_are_queues)
      return FormatAggElemForP(v, type.kind, type.types.st, type.types.et, ctx);
    auto it = queues.find(key);
    return FormatQueueForP(it == queues.end() ? nullptr : it->second, type,
                           ctx);
  };
  std::string out = "'{";
  bool first = true;
  auto add_item = [&](const std::string& key, const std::string& value) {
    if (!first) out += ", ";
    first = false;
    out += key + ":" + value;
  };
  if (aa->is_string_key) {
    for (const auto& [k, v] : aa->str_data)
      add_item("\"" + k + "\"", value_of(aa->str_element_queues, k, v));
  } else {
    for (const auto& [k, v] : aa->int_data)
      add_item(std::to_string(k), value_of(aa->int_element_queues, k, v));
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
  if (auto r = BuildFormatPQueue(name, ctx)) return r;
  if (auto r = BuildFormatPAssoc(name, ctx)) return r;
  if (auto r = BuildFormatPArray(name, ctx, arena)) return r;
  if (auto r = BuildFormatPStruct(name, val, ctx)) return r;
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
  return FormatStructValueForP(*member.layout, val, ctx);
}

// §21.2.1.6 with §7.4 and §7.8: an element selected from an array whose
// elements are structs or enums -- `va[10]` of `pair_t va[int]`, `arr[1]` of a
// fixed-size array, `q[0]` of a queue -- is a struct or an enum, and prints as
// the whole array prints that element. Returns no value for any other
// argument, a select of a multidimensional array's higher dimension included.
static std::optional<std::string> BuildFormatPElement(const Expr* arg,
                                                      const Logic4Vec& val,
                                                      SimContext& ctx) {
  if (arg->kind != ExprKind::kSelect || arg->index_end != nullptr ||
      arg->base == nullptr || arg->base->kind != ExprKind::kIdentifier)
    return std::nullopt;
  std::string_view name = arg->base->text;
  DataTypeKind kind = DataTypeKind::kImplicit;
  if (const ArrayInfo* ai = ctx.FindArrayInfo(name)) {
    if (ai->dim_sizes.size() >= 2) return std::nullopt;
    kind = ai->elem_type_kind;
  } else if (ctx.FindAssocArray(name) == nullptr &&
             ctx.FindQueue(name) == nullptr) {
    return std::nullopt;
  }
  const StructTypeInfo* st = StructLayoutOfName(name, ctx);
  const EnumTypeInfo* et = ctx.GetVariableEnumType(name);
  if (st == nullptr && et == nullptr) return std::nullopt;
  return FormatAggElemForP(val, kind, st, et, ctx);
}

// §21.2.1.6 (C5): the pattern of `elems`, the elements of an unpacked array
// value that names no variable of its own, each printed by `type`.
static std::string FormatValuesForP(const std::vector<Logic4Vec>& elems,
                                    const ElementTypeForP& type,
                                    SimContext& ctx) {
  std::string out = "'{";
  for (size_t i = 0; i < elems.size(); ++i) {
    if (i) out += ", ";
    out += FormatAggElemForP(elems[i], type.kind, type.types.st, type.types.et,
                             ctx);
  }
  return out + "}";
}

// Whether the array `name` names holds arrays in its elements -- a
// multidimensional fixed-size array, or a queue or dynamic array whose
// elements are queues or fixed-size arrays -- whose values its element
// storage does not hold.
static bool ElementsAreArrays(std::string_view name, SimContext& ctx) {
  if (const QueueObject* q = ctx.FindQueue(name)) return q->elements_are_queues;
  const ArrayInfo* ai = ctx.FindArrayInfo(name);
  return ai != nullptr && ai->dim_sizes.size() >= 2;
}

// §21.2.1.6 with §7.10.1 and §7.4.5: a slice of a queue, `q[0:1]`, is a queue
// and a slice of a fixed-size array an unpacked array, so %p prints its run of
// elements, each as the whole array prints it. No value for any other
// argument.
static std::optional<std::string> BuildFormatPSlice(const Expr* arg,
                                                    SimContext& ctx,
                                                    Arena& arena) {
  if (arg->kind != ExprKind::kSelect || arg->index_end == nullptr ||
      arg->base == nullptr || arg->base->kind != ExprKind::kIdentifier)
    return std::nullopt;
  std::string_view name = arg->base->text;
  if ((ctx.FindQueue(name) == nullptr && ctx.FindArrayInfo(name) == nullptr) ||
      ElementsAreArrays(name, ctx))
    return std::nullopt;
  std::vector<Logic4Vec> elems;
  CollectQueueElements(arg, ctx, arena, elems);
  return FormatValuesForP(elems, ElementTypeOfName(name, ctx), ctx);
}

// §7.12.1: the locators returning indices rather than elements.
static bool ReturnsIndices(std::string_view method) {
  return method == "find_index" || method == "find_first_index" ||
         method == "find_last_index" || method == "unique_index";
}

// §21.2.1.6 with §7.12.1 and §7.4.4: the elements a locator selects of an
// array whose elements are arrays -- the subarrays of a multidimensional
// fixed-size array, or the element queues of a queue -- print as the whole
// array prints them, each a nested pattern. No value for a call selecting no
// such elements.
static std::optional<std::string> BuildFormatPLocatorRows(const Expr* arg,
                                                          SimContext& ctx,
                                                          Arena& arena) {
  LocatorRows rows;
  if (!TryCollectLocatorRows(arg, ctx, arena, rows)) return std::nullopt;
  ElementTypeForP type = ElementTypeOfName(rows.array_name, ctx);
  std::string out = "'{";
  for (size_t i = 0; i < rows.offsets.size(); ++i) {
    if (i) out += ", ";
    if (rows.queue != nullptr) {
      out += FormatQueueElementForP(*rows.queue, rows.offsets[i], type, ctx);
      continue;
    }
    std::string row = std::string(rows.array_name) + "[" +
                      std::to_string(rows.info->dim_los[0] + rows.offsets[i]) +
                      "]";
    out += FormatArrayDimForP(row, *rows.info, 1, type.types, ctx);
  }
  return out + "}";
}

// §21.2.1.6 with §7.12: a locator method returns a queue and so does map(), so
// %p prints the queue a call of one returns. The elements a locator finds are
// the array's, printed as the array prints them; the indices it finds are the
// array's index type, so a string key prints quoted; map()'s are the values
// its with clause gives, each printed as it is. No value for an argument that
// is no such call.
static std::optional<std::string> BuildFormatPLocator(const Expr* arg,
                                                      SimContext& ctx,
                                                      Arena& arena) {
  const Expr* access = arg->kind == ExprKind::kCall ? arg->lhs : arg;
  if (access == nullptr || access->kind != ExprKind::kMemberAccess ||
      access->is_scope_resolution || access->rhs == nullptr ||
      access->lhs == nullptr)
    return std::nullopt;
  if (auto rows = BuildFormatPLocatorRows(arg, ctx, arena)) return rows;
  std::string_view method = access->rhs->text;
  std::string_view recv = access->lhs->kind == ExprKind::kIdentifier
                              ? std::string_view(access->lhs->text)
                              : std::string_view{};
  ElementTypeForP type;
  if (ReturnsIndices(method)) {
    const AssocArrayObject* aa = ctx.FindAssocArray(recv);
    if (aa != nullptr && aa->is_string_key) type.kind = DataTypeKind::kString;
  } else if (method != "map" && !recv.empty()) {
    if (ElementsAreArrays(recv, ctx)) return std::nullopt;
    type = ElementTypeOfName(recv, ctx);
  }
  std::vector<Logic4Vec> elems;
  if (!TryCollectLocatorResult(arg, ctx, arena, elems)) return std::nullopt;
  return FormatValuesForP(elems, type, ctx);
}

// §21.2.1.6 with §26.3: `pk::pq`, a package's item named through its
// package, is the item the lowerer keeps under "pk.pq" (BuildLhsName), and
// prints as it does by the name an import gives it. Asked by no name, a
// package's queue or array printed as one number. No value for an argument
// that names no package item with a rendering of its own.
static std::optional<std::string> BuildFormatPPackageItem(const Expr* arg,
                                                          const Logic4Vec& val,
                                                          SimContext& ctx,
                                                          Arena& arena) {
  if (arg->kind != ExprKind::kMemberAccess || !arg->is_scope_resolution)
    return std::nullopt;
  std::string key;
  BuildLhsName(arg, key);
  return BuildFormatPNamed(key, val, ctx, arena);
}

std::string BuildFormatP(const Expr* arg, const Logic4Vec& val,
                         SimContext& ctx) {
  Arena& arena = ctx.GetArena();
  // §3.12.1: `$unit::uq` names the compilation unit's uq, kept under
  // "$unit.uq" past a module's own uq (DeclaredKindsKey); read by its text, it
  // printed the module's.
  std::string name = arg->kind == ExprKind::kIdentifier ? DeclaredKindsKey(arg)
                                                        : std::string();

  if (auto named = BuildFormatPNamed(name, val, ctx, arena)) return *named;
  if (auto scoped = BuildFormatPPackageItem(arg, val, ctx, arena))
    return *scoped;
  if (auto elem = BuildFormatPElement(arg, val, ctx)) return *elem;
  if (auto member = BuildFormatPMember(arg, val, ctx, arena)) return *member;
  if (auto slice = BuildFormatPSlice(arg, ctx, arena)) return *slice;
  if (auto found = BuildFormatPLocator(arg, ctx, arena)) return *found;

  // §21.2.1.6 (C10): %p on a singular expression formats it as one element of
  // an aggregate would be formatted.
  return FormatSingularForP(val, DataTypeKind::kImplicit);
}

}  // namespace delta
