#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_export.h"
#include "simulator/dpi_runtime.h"
#include "simulator/eval_expr_internal.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/instance_prefix_override.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/struct_string_member.h"
#include "simulator/svdpi.h"
#include "simulator/variable.h"

namespace delta {

namespace {

int ResolveDpiActualIndex(const DpiRtFunction* import, const Expr* expr,
                          size_t i, size_t positional_count) {
  if (i < positional_count) {
    return static_cast<int>(i);
  }
  for (size_t j = 0; j < expr->arg_names.size(); ++j) {
    if (expr->arg_names[j] == import->args[i].name) {
      return static_cast<int>(positional_count + j);
    }
  }
  return -1;
}

// §35.5.5 lists the types an imported function's result may have and §35.5.6
// the types its formals may have; this is the width the kind alone gives each.
// Built at a fixed width instead, a longint or a chandle result lost its upper
// half and a byte arrived padded with bits its type does not have. A void
// result falls to the default with everything else the clauses do not name:
// §35.5.5 gives such a call no value, so nothing reads what width it came out
// at. A packed formal is the one case the kind cannot answer for, which is what
// DpiValueWidth below takes the declaration's own width for.
uint32_t DpiKindWidth(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kBit:
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
      return 1;
    case DataTypeKind::kByte:
      return 8;
    case DataTypeKind::kShortint:
      return 16;
    case DataTypeKind::kLongint:
    case DataTypeKind::kChandle:
    case DataTypeKind::kTime:
    case DataTypeKind::kReal:
    case DataTypeKind::kShortreal:
    case DataTypeKind::kRealtime:
      return 64;
    default:
      return 32;
  }
}

// §35.5.6 admits a packed formal of any width, and the kind of `bit [127:0]` is
// just kBit, so the width the declaration wrote is what a formal crosses at
// wherever it is wider than the kind alone says. A formal whose type carries
// its own width records none and keeps the kind's.
uint32_t DpiValueWidth(DataTypeKind kind, uint32_t declared) {
  uint32_t kind_width = DpiKindWidth(kind);
  return declared > kind_width ? declared : kind_width;
}

bool IsRealKind(DataTypeKind kind) {
  return kind == DataTypeKind::kReal || kind == DataTypeKind::kShortreal ||
         kind == DataTypeKind::kRealtime;
}

// §35.2.2.1: "The implementation (representation and layout) of 4-state values
// ... is irrelevant for SystemVerilog semantics and can only impact the foreign
// side of the interface." A four-state scalar crosses in the sv_0/sv_1/sv_z/
// sv_x encoding svdpi.h names, which is what the aval/bval pair of bit 0 says:
// a clear bval selects 0 or 1, a set one selects z or x. Carried as one word
// per bit instead, a design's x came back 1 and its z came back 0.
SvLogic SvLogicOfWord(Logic4Word w) {
  bool one = (w.aval & 1U) != 0;
  if ((w.bval & 1U) == 0) {
    return static_cast<SvLogic>(one ? sv_1 : sv_0);
  }
  return static_cast<SvLogic>(one ? sv_x : sv_z);
}

Logic4Word WordOfSvLogic(SvLogic v) {
  switch (v) {
    case sv_0:
      return Logic4Word{0, 0};
    case sv_1:
      return Logic4Word{1, 0};
    case sv_z:
      return Logic4Word{0, 1};
    default:
      return Logic4Word{1, 1};
  }
}

// §35.2.2: a chandle is "capable of holding a pointer value", and a design
// holds that pointer as the bits of its variable. The pointer is rebuilt out of
// those bits rather than cast into being, so the handle the foreign side handed
// out is the handle it gets back when the design passes it in again.
SvChandle ChandleOfWord(Logic4Word w) {
  SvChandle handle = nullptr;
  auto bits = static_cast<uintptr_t>(w.aval);
  std::memcpy(static_cast<void*>(&handle), &bits, sizeof(handle));
  return handle;
}

// Annex H.10.1.2: `v` as the canonical array of aval/bval pairs, `width` bits
// of it. A Logic4Vec keeps 64 bits per word and the canonical array 32, so each
// word supplies two pairs; a word the vector does not have reads as zero, which
// is what a value narrower than its declared formal is zero-extended to.
std::vector<SvLogicVecVal> CanonicalWordsOfVec(const Logic4Vec& v,
                                               uint32_t width) {
  std::vector<SvLogicVecVal> words(DpiCanonicalWordCount(width),
                                   SvLogicVecVal{0, 0});
  for (size_t i = 0; i < words.size(); ++i) {
    size_t src = i / 2;
    if (src >= v.nwords) break;
    unsigned shift = (i % 2) == 0 ? 0U : 32U;
    words[i].aval = static_cast<uint32_t>(v.words[src].aval >> shift);
    words[i].bval = static_cast<uint32_t>(v.words[src].bval >> shift);
  }
  // The bits above the declared width belong to no bit of the value, so the
  // top pair is masked rather than carrying whatever the source word held
  // there.
  if (uint32_t rem = width % 32U; rem != 0 && !words.empty()) {
    uint32_t mask = (1U << rem) - 1U;
    words.back().aval &= mask;
    words.back().bval &= mask;
  }
  return words;
}

// The reverse: an arena-allocated Logic4Vec of `width` bits holding what the
// canonical array carries, unknown bits and all.
Logic4Vec VecOfCanonicalWords(Arena& arena,
                              const std::vector<SvLogicVecVal>& words,
                              uint32_t width) {
  Logic4Vec v = MakeLogic4Vec(arena, width);
  for (size_t i = 0; i < words.size(); ++i) {
    size_t dst = i / 2;
    if (dst >= v.nwords) break;
    unsigned shift = (i % 2) == 0 ? 0U : 32U;
    v.words[dst].aval |= static_cast<uint64_t>(words[i].aval) << shift;
    v.words[dst].bval |= static_cast<uint64_t>(words[i].bval) << shift;
  }
  return v;
}

// The value a design's expression presents to a formal (or a call's result to
// the expression it stands in), typed as the declaration types it. §35.6.1 has
// the crossing go through a temporary of the formal's type, so the type the
// declaration names is the one the value is built at; DpiRuntime then coerces
// between that and the foreign side.
DpiArgValue DpiArgValueOfType(DataTypeKind kind, uint32_t declared_width,
                              const Logic4Vec& v) {
  // §35.5.6's packed formal may be wider than the union member its kind lands
  // in, and every branch below reads that member. Such a formal crosses in the
  // canonical array instead, which is what keeps the bits above the member --
  // and the unknown bits among them -- from being dropped here.
  if (uint32_t width = DpiValueWidth(kind, declared_width);
      width > DpiInlineValueBits(kind)) {
    return DpiArgValue::FromLogicVecWords(CanonicalWordsOfVec(v, width), width,
                                          kind);
  }
  Logic4Word word = v.nwords == 0 ? Logic4Word{} : v.words[0];
  // §35.6.1 has the temporary "initialized with the value of the actual
  // argument with the appropriate coercion", and has "the assignments between a
  // temporary and the actual argument follow general SystemVerilog rules for
  // assignments and automatic coercion". §6.11.2 is what those rules say where
  // the type on the other side holds no unknown bit: the assignment converts
  // "any unknown or high-impedance bits in the value ... to zeros". Every
  // branch below but the four-state ones reads the aval alone and so has no
  // bval to put an x in, and read raw that aval says an x is a one. This is the
  // aval those branches read instead, which is the projection
  // ConvertRealForKnownLhs in statement_assign_core.cpp already applies to an
  // assignment reaching a real and Logic4Vec::ToUint64 to one reaching a
  // two-state integral.
  Logic4Word known{word.aval & ~word.bval, 0};
  DpiArgValue out;
  switch (kind) {
    case DataTypeKind::kReal:
    case DataTypeKind::kShortreal:
    case DataTypeKind::kRealtime:
      out = DpiArgValue::FromReal(v.is_real ? RealVecToDouble(v)
                                            : static_cast<double>(known.aval));
      out.type = kind;
      return out;
    case DataTypeKind::kChandle:
      return DpiArgValue::FromChandle(ChandleOfWord(known));
    case DataTypeKind::kBit:
      return DpiArgValue::FromBit(static_cast<SvBit>(known.aval & 1U));
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
      out = DpiArgValue::FromLogic(SvLogicOfWord(word));
      out.type = kind;
      return out;
    case DataTypeKind::kInteger:
      return DpiArgValue::FromLogicVec(SvLogicVecVal{
          static_cast<uint32_t>(word.aval), static_cast<uint32_t>(word.bval)});
    case DataTypeKind::kTime:
      // §H.7.3: time is a packed 4-state type, so it crosses as its two
      // aval/bval pairs (§H.7.7) and its unknown bits stay unknown.
      return DpiArgValue::FromLogicVecWords(CanonicalWordsOfVec(v, 64), 64,
                                            kind);
    case DataTypeKind::kString:
      // §35.5.6 admits a string formal, and §H.8.10 has its characters laid
      // out for C as a C string. A design's string is held a byte per
      // character, the first character highest, which is what is read back
      // into the characters here.
      return DpiArgValue::FromString(Logic4VecToString(v));
    default:
      // Every remaining integral type -- byte, shortint, int, and whatever a
      // declaration left at DpiArg's own default -- narrows and sign-extends
      // through §35.6.1's coercion rather than through a cast written here.
      return CoerceArgValue(
          DpiArgValue::FromLongint(static_cast<int64_t>(known.aval)), kind);
  }
}

// A value of the declared type carrying what crossed the boundary, unknown bits
// included. A real is carried as its own bit pattern in a 64-bit vector marked
// is_real, which is the shape MakeRealVec in src/simulator/evaluation.cpp
// builds and what the rest of the evaluator reads a real out of. An integral
// value is marked signed where the declared type is (`is_signed`): §11.8.1
// reads a function call's signedness off the type of its result, so a byte
// result of -100 is -100 wherever the call is used, and an output formal of a
// signed type sign-extends into a wider actual as an assignment of one does.
Logic4Vec DpiValueOfType(Arena& arena, DataTypeKind kind,
                         uint32_t declared_width, const DpiArgValue& value,
                         bool is_signed) {
  // A value that crossed in the canonical array carries the width it was built
  // at, and reading the union below would rebuild it out of a member nothing
  // wrote. §35.5.6's packed formals are what arrive this way, in both
  // directions: the write-back of an output formal is this call too.
  if (value.IsWideVec()) {
    Logic4Vec wide =
        VecOfCanonicalWords(arena, value.AsLogicVecWords(), value.VecWidth());
    wide.is_signed = is_signed;
    return wide;
  }
  uint32_t width = DpiValueWidth(kind, declared_width);
  if (IsRealKind(kind)) return MakeRealVec(arena, value.AsReal(), width);
  // §H.8.10: a string the foreign side supplies is copied into the design's
  // own storage, a byte per character, as a string literal is held.
  if (kind == DataTypeKind::kString) {
    return StringToLogic4Vec(arena, value.AsString());
  }

  Logic4Word word;
  switch (kind) {
    case DataTypeKind::kChandle:
      word.aval =
          static_cast<uint64_t>(reinterpret_cast<uintptr_t>(value.AsChandle()));
      break;
    case DataTypeKind::kBit:
      word.aval = value.AsBit() & 1U;
      break;
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
      word = WordOfSvLogic(value.AsLogic());
      break;
    case DataTypeKind::kInteger:
      word.aval = value.AsLogicVec().aval;
      word.bval = value.AsLogicVec().bval;
      break;
    case DataTypeKind::kLongint:
    case DataTypeKind::kTime:
      word.aval = static_cast<uint64_t>(value.AsLongint());
      break;
    default:
      word.aval = static_cast<uint64_t>(static_cast<int64_t>(value.AsInt()));
      break;
  }

  Logic4Vec v = MakeLogic4Vec(arena, width);
  uint64_t mask = width >= 64 ? ~0ULL : ((1ULL << width) - 1);
  v.words[0].aval = word.aval & mask;
  v.words[0].bval = word.bval & mask;
  v.is_signed = is_signed;
  return v;
}

// The elements of the fixed-size unpacked array an actual names, and its
// unpacked dimensions as declared, outermost first.
struct UnpackedActual {
  std::vector<Variable*> elements;
  std::vector<std::string> names;
  std::vector<DpiArrayRange> ranges;
};

// The declared dimensions of the array `info` describes, outermost first.
std::vector<DpiArrayRange> DeclaredRanges(const ArrayInfo& info) {
  std::vector<DpiArrayRange> ranges;
  const bool kSingle = info.dim_sizes.empty();
  const size_t kCount = kSingle ? 1 : info.dim_sizes.size();
  for (size_t d = 0; d < kCount; ++d) {
    const auto kLow = static_cast<int32_t>(kSingle ? info.lo : info.dim_los[d]);
    const auto kSize =
        static_cast<int32_t>(kSingle ? info.size : info.dim_sizes[d]);
    const bool kDescending =
        kSingle ? info.is_descending
                : d < info.dim_descending.size() && info.dim_descending[d];
    const int32_t kHigh = kLow + kSize - 1;
    ranges.push_back(kDescending ? DpiArrayRange{kHigh, kLow}
                                 : DpiArrayRange{kLow, kHigh});
  }
  return ranges;
}

// §H.7.3: the elements of the array `name` names, row-major. A sized formal
// lays each dimension out from its lower index (§H.7.6 c)) and an open one
// from its left bound (§H.12.4), which `from_left` selects. Empty where `name`
// names no fixed-size array.
UnpackedActual UnpackedActualOf(std::string_view name, bool from_left,
                                SimContext& ctx) {
  UnpackedActual actual;
  const ArrayInfo* info = ctx.FindArrayInfo(name);
  if (info == nullptr || info->is_dynamic || info->is_queue) return actual;
  actual.ranges = DeclaredRanges(*info);
  std::vector<std::string> names = {std::string(name)};
  for (const DpiArrayRange& range : actual.ranges) {
    const int32_t kFirst =
        from_left ? range.left : std::min(range.left, range.right);
    const int32_t kStep = from_left && range.left > range.right ? -1 : 1;
    const int32_t kCount = std::abs(range.left - range.right) + 1;
    std::vector<std::string> next;
    for (const std::string& prefix : names) {
      for (int32_t j = 0; j < kCount; ++j) {
        next.push_back(prefix + "[" + std::to_string(kFirst + (j * kStep)) +
                       "]");
      }
    }
    names = std::move(next);
  }
  for (const std::string& element : names) {
    actual.elements.push_back(ctx.FindVariable(element));
  }
  actual.names = std::move(names);
  return actual;
}

// §7.2 with §7.4.2: which slot of a member array's packed bits, counted from
// the least significant, holds the element at C index `k` -- the leftmost
// element stands in the most significant bits, and C index 0 is the lower
// index (§H.7.6 c)).
uint32_t MemberElementSlot(const StructFieldInfo& field, uint32_t k) {
  const int64_t kLower = std::min(field.elem_left, field.elem_right);
  const int64_t kFromLeft = std::abs(kLower + k - field.elem_left);
  return field.elem_count - 1 - static_cast<uint32_t>(kFromLeft);
}

// The bits one element of a member array takes.
uint32_t MemberElementWidth(const StructFieldInfo& field) {
  return field.elem_count == 0 ? field.width : field.width / field.elem_count;
}

// §H.7.8: the members of the unpacked struct or union `bits` holds under the
// layout `info`, each a value of `formal`'s member at the same position.
DpiArgValue AggregateValue(const DpiArg& formal, const StructTypeInfo& info,
                           const Logic4Vec& bits, Arena& arena) {
  DpiArgValue whole;
  whole.type = formal.type;
  for (size_t m = 0; m < formal.members.size() && m < info.fields.size(); ++m) {
    const DpiArg& member = formal.members[m];
    const StructFieldInfo& field = info.fields[m];
    Logic4Vec held =
        ExtractBitField(arena, bits, field.bit_offset, field.width);
    if (!member.members.empty() && field.nested != nullptr) {
      whole.elements.push_back(
          AggregateValue(member, *field.nested, held, arena));
      continue;
    }
    if (member.unpacked_dims.empty() || field.elem_count == 0) {
      whole.elements.push_back(
          DpiArgValueOfType(member.type, member.width,
                            MemberValueOf(held, field.type_kind, arena)));
      continue;
    }
    DpiArgValue array;
    array.type = member.type;
    const uint32_t kWidth = MemberElementWidth(field);
    for (uint32_t k = 0; k < field.elem_count; ++k) {
      array.elements.push_back(DpiArgValueOfType(
          member.type, member.width,
          ExtractBitField(arena, held, MemberElementSlot(field, k) * kWidth,
                          kWidth)));
    }
    whole.elements.push_back(std::move(array));
  }
  return whole;
}

// `value` of `formal`'s type, at `width` bits, as the bits a member holds.
Logic4Vec MemberBits(const DpiArg& formal, const DpiArgValue& value,
                     DataTypeKind held_kind, uint32_t width, Arena& arena) {
  Logic4Vec next = DpiValueOfType(arena, formal.type, formal.width, value,
                                  !formal.is_unsigned);
  return ResizeToWidth(MemberBitsOf(next, held_kind, arena), width, arena);
}

// §35.5.1.2 for an unpacked struct or union: the members C left in `value`
// are deposited into `bits`, which holds the actual under the layout `info`.
void DepositAggregate(Logic4Vec& bits, const DpiArg& formal,
                      const StructTypeInfo& info, const DpiArgValue& value,
                      Arena& arena) {
  for (size_t m = 0; m < formal.members.size() && m < info.fields.size() &&
                     m < value.elements.size();
       ++m) {
    const DpiArg& member = formal.members[m];
    const StructFieldInfo& field = info.fields[m];
    const DpiArgValue& part = value.elements[m];
    if (!member.members.empty() && field.nested != nullptr) {
      Logic4Vec held = OwnRhsWords(
          ExtractBitField(arena, bits, field.bit_offset, field.width), arena);
      DepositAggregate(held, member, *field.nested, part, arena);
      DepositBitField(bits, field.bit_offset, held, field.width);
    } else if (member.unpacked_dims.empty() || field.elem_count == 0) {
      DepositBitField(
          bits, field.bit_offset,
          MemberBits(member, part, field.type_kind, field.width, arena),
          field.width);
    } else {
      const uint32_t kWidth = MemberElementWidth(field);
      for (uint32_t k = 0; k < field.elem_count && k < part.elements.size();
           ++k) {
        DepositBitField(
            bits, field.bit_offset + (MemberElementSlot(field, k) * kWidth),
            MemberBits(member, part.elements[k], field.type_kind, kWidth,
                       arena),
            kWidth);
      }
    }
  }
}

// The actual of an unpacked struct or union formal, its members in order; an
// actual that is not a struct variable's name has none to give.
DpiArgValue DpiAggregateActual(const DpiArg& formal, const Expr* actual,
                               const ActualBindingCtx& b) {
  DpiArgValue whole;
  whole.type = formal.type;
  if (actual->kind != ExprKind::kIdentifier) return whole;
  const Variable* var = b.ctx.FindVariable(actual->text);
  const StructTypeInfo* info = StructLayoutOfName(actual->text, b.ctx);
  if (var == nullptr || info == nullptr) return whole;
  return AggregateValue(formal, *info, var->value, b.arena);
}

// The actual of an unpacked formal, sized or open: its elements each a value
// of the formal's element type in C order, and its declared dimensions. An
// actual that is not an array name has no elements to give.
DpiArgValue DpiArrayActual(const DpiArg& formal, const Expr* actual,
                           const ActualBindingCtx& b) {
  DpiArgValue array;
  array.type = formal.type;
  if (actual->kind != ExprKind::kIdentifier) return array;
  UnpackedActual found =
      UnpackedActualOf(actual->text, formal.is_open_array, b.ctx);
  array.ranges = std::move(found.ranges);
  for (size_t k = 0; k < found.elements.size(); ++k) {
    Variable* element = found.elements[k];
    // An element of an array of structures has the layout a member select of
    // it reads through (§7.4.2 with §7.2).
    const StructTypeInfo* info =
        formal.members.empty() ? nullptr
                               : StructLayoutOfName(found.names[k], b.ctx);
    if (element == nullptr) {
      array.elements.emplace_back();
    } else if (info != nullptr) {
      array.elements.push_back(
          AggregateValue(formal, *info, element->value, b.arena));
    } else {
      array.elements.push_back(
          DpiArgValueOfType(formal.type, formal.width, element->value));
    }
  }
  return array;
}

DpiArgValue EvalDpiActualForFormal(const DpiRtFunction* import, size_t i,
                                   const ActualBindingCtx& b) {
  DataTypeKind type = import->args[i].type;
  // The actual is evaluated whatever the formal's direction is, an output
  // included: §35.5.1.2 keeps the value from reaching the foreign function --
  // DpiRuntime::CallImportWithArgs seeds an output formal with the undetermined
  // value instead -- while §35.6.2 needs the value the actual held before the
  // call to say afterwards whether the call changed it.
  uint32_t width = import->args[i].width;
  int ai = ResolveDpiActualIndex(import, b.call, i, b.positional_count);
  if (ai >= 0 && b.call->args[static_cast<size_t>(ai)] != nullptr &&
      (!import->args[i].unpacked_dims.empty() ||
       import->args[i].is_open_array)) {
    return DpiArrayActual(import->args[i],
                          b.call->args[static_cast<size_t>(ai)], b);
  }
  if (ai >= 0 && b.call->args[static_cast<size_t>(ai)] != nullptr &&
      !import->args[i].members.empty()) {
    return DpiAggregateActual(import->args[i],
                              b.call->args[static_cast<size_t>(ai)], b);
  }
  if (ai >= 0 && b.call->args[static_cast<size_t>(ai)] != nullptr) {
    return DpiArgValueOfType(
        type, width,
        EvalExpr(b.call->args[static_cast<size_t>(ai)], b.ctx, b.arena));
  }
  if (import->args[i].default_value) {
    return DpiArgValueOfType(
        type, width, EvalExpr(import->args[i].default_value, b.ctx, b.arena));
  }
  // A formal the call bound nothing to and the declaration gave no default has
  // no value to present, so it presents the type's own undetermined value.
  return DpiRuntime::UndeterminedOutputValue(type, width);
}

std::vector<DpiArgValue> BindDpiActualsFromImport(const DpiRtFunction* import,
                                                  const ActualBindingCtx& b) {
  std::vector<DpiArgValue> args;
  args.reserve(import->args.size());
  for (size_t i = 0; i < import->args.size(); ++i) {
    args.push_back(EvalDpiActualForFormal(import, i, b));
  }
  return args;
}

std::vector<DpiArgValue> BindDpiActualsPositional(const ActualBindingCtx& b) {
  std::vector<DpiArgValue> args;
  args.reserve(b.call->args.size());
  for (auto* arg : b.call->args) {
    // With no formal to read a type off, the value crosses as the type DpiArg
    // itself declares when a declaration says nothing.
    args.push_back(DpiArgValueOfType(DataTypeKind::kInt, 0,
                                     EvalExpr(arg, b.ctx, b.arena)));
  }
  return args;
}

std::vector<DpiArgValue> BindDpiCallActuals(const DpiRtFunction* import,
                                            const ActualBindingCtx& b) {
  if (!import->args.empty()) return BindDpiActualsFromImport(import, b);
  return BindDpiActualsPositional(b);
}

// §35.6.2: "the value propagation (i.e., value change events) happens as if an
// actual argument was assigned a formal argument immediately after control
// returns", so what raises an event is that assignment leaving the actual
// holding something else. DpiRuntime answers a narrower question -- whether the
// foreign function moved the formal -- and the two agree only where the
// assignment loses nothing. Where it loses something they part: an `int` formal
// the callee leaves at 21, assigned to a `bit [3:0]` actual holding 5, leaves
// the 5 it found, which is no value change of the actual however far the formal
// moved.
//
// This is that assignment asked ahead of itself, by the conversions the store
// makes and no others: §6.12.1's real boundary and §10.7's width through
// ConvertRealOnAssign, and §6.11.2's unknowns through CoerceTo2State.
//
// It is asked only of a bare name, which is the one left-hand side
// PerformBlockingAssign carries down that path. A select, a concatenation, a
// streaming target or a member path is stored by a route of its own, over a
// window rather than the whole of what the name resolves to, and so is a
// left-hand side this cannot answer for: those report as changing and keep the
// propagation they have. So does a name resolving to no variable. A forced
// variable needs no case here -- §10.6.2 has the store leave it alone, and it
// leaves it without notifying either.
bool AssignmentWouldChangeActual(const Expr* lhs, const Logic4Vec& next,
                                 SimContext& ctx, Arena& arena) {
  Variable* var = lhs != nullptr && lhs->kind == ExprKind::kIdentifier
                      ? ResolveLhsVariable(lhs, ctx)
                      : nullptr;
  if (var == nullptr) return true;
  Logic4Vec stored = ConvertRealOnAssign(next, lhs, *var, ctx, arena);
  if (!var->is_4state) CoerceTo2State(stored);
  return !var->value.SameValueAs(stored);
}

// §35.6.2: the value changes of an imported function's output and inout
// arguments are handled once control has returned, by propagating each as if
// the actual were assigned the formal immediately after the return. `changes`
// names the actuals whose formal the call altered, in declaration order, so an
// actual whose formal the call left as it found it is assigned nothing and
// propagates nothing. Of the rest, the ones the assignment would leave holding
// what they already hold propagate nothing either, per
// AssignmentWouldChangeActual above.
// §13.5.2 has WritebackOutputArgs in eval_function_args.cpp do the equivalent
// for a native subroutine, reading the values out of the callee's local
// variables; a foreign callee has none, so the values are read out of the
// vector it was called with.
// §35.5.1.2 for an unpacked formal, sized or open: each element C left is
// copied back into the actual's element at the same position, at that
// element's width, a struct element member by member.
void WritebackDpiArray(const DpiArg& formal, const Expr* lhs,
                       const DpiArgValue& array, const ActualBindingCtx& b) {
  if (lhs->kind != ExprKind::kIdentifier) return;
  UnpackedActual found =
      UnpackedActualOf(lhs->text, formal.is_open_array, b.ctx);
  for (size_t k = 0; k < found.elements.size() && k < array.elements.size();
       ++k) {
    Variable* element = found.elements[k];
    if (element == nullptr) continue;
    const StructTypeInfo* info =
        formal.members.empty() ? nullptr
                               : StructLayoutOfName(found.names[k], b.ctx);
    Logic4Vec next = OwnRhsWords(element->value, b.arena);
    if (info != nullptr) {
      DepositAggregate(next, formal, *info, array.elements[k], b.arena);
    } else {
      next = OwnRhsWords(
          ResizeToWidth(DpiValueOfType(b.arena, formal.type, formal.width,
                                       array.elements[k], !formal.is_unsigned),
                        element->value.width, b.arena),
          b.arena);
    }
    element->value = next;
    element->NotifyWatchers();
  }
}

// §35.5.1.2 for an unpacked struct or union formal: the members C left are
// deposited into the struct variable the actual names.
void WritebackDpiAggregate(const DpiArg& formal, const Expr* lhs,
                           const DpiArgValue& value,
                           const ActualBindingCtx& b) {
  if (lhs->kind != ExprKind::kIdentifier) return;
  Variable* var = b.ctx.FindVariable(lhs->text);
  const StructTypeInfo* info = StructLayoutOfName(lhs->text, b.ctx);
  if (var == nullptr || info == nullptr) return;
  Logic4Vec next = OwnRhsWords(var->value, b.arena);
  DepositAggregate(next, formal, *info, value, b.arena);
  var->value = next;
  var->NotifyWatchers();
}

void WritebackDpiChangedArgs(const DpiRtFunction* import,
                             const ActualBindingCtx& b,
                             const std::vector<DpiArgValue>& actuals,
                             const std::vector<DpiArgValueChange>& changes) {
  for (const auto& change : changes) {
    size_t i = change.index;
    if (i >= import->args.size() || i >= actuals.size()) continue;
    int ai = ResolveDpiActualIndex(import, b.call, i, b.positional_count);
    if (ai < 0) continue;
    // The value arrives at the width the formal declares, unknown bits and
    // all, and the assignment narrows it to whatever the actual holds, as an
    // assignment to that actual would anywhere else.
    const Expr* lhs = b.call->args[static_cast<size_t>(ai)];
    if (!import->args[i].unpacked_dims.empty() ||
        import->args[i].is_open_array) {
      WritebackDpiArray(import->args[i], lhs, actuals[i], b);
      continue;
    }
    if (!import->args[i].members.empty()) {
      WritebackDpiAggregate(import->args[i], lhs, actuals[i], b);
      continue;
    }
    Logic4Vec next =
        DpiValueOfType(b.arena, import->args[i].type, import->args[i].width,
                       actuals[i], !import->args[i].is_unsigned);
    if (!AssignmentWouldChangeActual(lhs, next, b.ctx, b.arena)) continue;
    PerformBlockingAssign(lhs, next, b.ctx, b.arena);
  }
}

// §35.7: the temporary variable that carries formal `index` of the export
// whose function is keyed `key` across one call from C, its name starting with
// a `$` so that no name a design declares can stand for it. A dot would read
// as a hierarchical or member path, so the instance path's dots are `$` too.
std::string ExportTempName(std::string_view key, size_t index) {
  std::string name = "$dpi_export$" + std::string(key);
  std::replace(name.begin(), name.end(), '.', '$');
  return name + "$" + std::to_string(index);
}

// Makes the temporary `name` for `formal` the first time it is needed: a
// variable of the formal's width, or for an unpacked formal an array of such
// variables over the formal's dimensions.
void EnsureExportTemp(const std::string& name, const DpiArg& formal,
                      SimContext& ctx) {
  const uint32_t kWidth = DpiValueWidth(formal.type, formal.width);
  if (formal.unpacked_dims.empty()) {
    if (ctx.FindVariable(name) == nullptr) ctx.CreateVariable(name, kWidth);
    return;
  }
  if (ctx.FindArrayInfo(name) != nullptr) return;
  ArrayInfo info;
  info.lo = static_cast<uint32_t>(formal.unpacked_dims.front().low);
  info.size = static_cast<uint32_t>(formal.unpacked_dims.front().high -
                                    formal.unpacked_dims.front().low + 1);
  info.elem_width = kWidth;
  info.elem_type_kind = formal.type;
  if (formal.unpacked_dims.size() > 1) {
    for (const SvActualDimension& dim : formal.unpacked_dims) {
      info.dim_los.push_back(static_cast<uint32_t>(dim.low));
      info.dim_sizes.push_back(static_cast<uint32_t>(dim.high - dim.low + 1));
      info.dim_descending.push_back(false);
    }
  }
  ctx.RegisterArray(name, info);
  for (const std::string& element : UnpackedActualOf(name, false, ctx).names) {
    ctx.CreateVariable(element, kWidth);
  }
}

// An identifier naming `text`, which the arena keeps for the run.
Expr* IdentifierNaming(const std::string& text, Arena& arena) {
  auto* id = arena.Create<Expr>();
  id->kind = ExprKind::kIdentifier;
  id->text = *arena.Create<std::string>(text);
  return id;
}

// §35.7: makes each formal's temporary, names it as the formal's actual in
// `call`, and writes an input's or inout's value into it -- an array formal
// is an array the body can index, and a call with outputs writes them back.
void SendExportArguments(std::string_view key,
                         const std::vector<DpiArg>& formals,
                         const std::vector<DpiArgValue>& args, Expr* call,
                         const ActualBindingCtx& b) {
  for (size_t i = 0; i < formals.size() && i < args.size(); ++i) {
    const DpiArg& formal = formals[i];
    const std::string kTemp = ExportTempName(key, i);
    EnsureExportTemp(kTemp, formal, b.ctx);
    Expr* actual = IdentifierNaming(kTemp, b.arena);
    call->args.push_back(actual);
    if (formal.direction == Direction::kOutput) continue;
    if (!formal.unpacked_dims.empty()) {
      WritebackDpiArray(formal, actual, args[i], b);
      continue;
    }
    PerformBlockingAssign(actual,
                          DpiValueOfType(b.arena, formal.type, formal.width,
                                         args[i], !formal.is_unsigned),
                          b.ctx, b.arena);
  }
}

// §35.7: reads back what the call left in each output's and inout's
// temporary into `args`.
void ReceiveExportArguments(const std::vector<DpiArg>& formals,
                            std::vector<DpiArgValue>& args,
                            const ActualBindingCtx& b) {
  for (size_t i = 0; i < formals.size() && i < args.size(); ++i) {
    const DpiArg& formal = formals[i];
    if (formal.direction == Direction::kInput) continue;
    const Expr* actual = b.call->args[i];
    args[i] = formal.unpacked_dims.empty()
                  ? DpiArgValueOfType(formal.type, formal.width,
                                      EvalExpr(actual, b.ctx, b.arena))
                  : DpiArrayActual(formal, actual, b);
  }
}

}  // namespace

// §35.5.4: the name the call reaches its import declaration by -- the
// callee text of a bare call, or, for a package's declaration named through
// §26.3's package scope resolution operator, `p::p_mul(7, 8)`, which parses
// as a call with no callee text and the scoped name as its base, the member
// side of that name: the registry keys a declaration by its subroutine name.
static std::string_view DpiCalleeName(const Expr* expr) {
  if (!expr->callee.empty()) return expr->callee;
  const Expr* scoped = expr->lhs;
  if (scoped == nullptr || scoped->kind != ExprKind::kMemberAccess ||
      !scoped->is_scope_resolution || scoped->rhs == nullptr ||
      scoped->rhs->kind != ExprKind::kIdentifier) {
    return {};
  }
  return scoped->rhs->text;
}

Logic4Vec EvalDpiCall(const Expr* expr, SimContext& ctx, Arena& arena) {
  auto* dpi = ctx.GetDpiRuntime();
  std::string_view callee = DpiCalleeName(expr);
  const DpiRtFunction* import =
      dpi == nullptr ? nullptr : dpi->FindImport(callee);
  if (import == nullptr) return MakeLogic4VecVal(arena, 1, 0);
  // §35.4 makes an imported subroutine's declaration a reference to a global
  // symbol the foreign side defines, and §35.5.4 leaves the binding of that
  // symbol to the tool, which BindDpiImports makes before the run. A call
  // reaching a declaration it could not bind -- no loaded library defines the
  // symbol, or one does and the binding could not be made, whose reason is
  // then given -- is reported rather than answered: the zero it would
  // otherwise yield is a value the design reads as data and cannot tell from a
  // foreign function that returned zero.
  if (!import->impl && !import->arg_impl) {
    std::string message = "imported subroutine '" + std::string(callee) +
                          "' is bound to no foreign implementation";
    if (!import->unbound_reason.empty()) {
      message += ": " + import->unbound_reason;
    }
    ctx.GetDiag().Error(expr->range.start, std::move(message),
                        Subclause("35.5.4"));
    return MakeLogic4VecVal(arena, 1, 0);
  }
  // §35.6: calling an imported function uses the same usage and syntax as a
  // native function call. When the import's formals are known, resolve the
  // call-site actuals against them so that named-argument binding and omitted
  // arguments backed by defaults behave exactly as for native subroutine calls.
  ActualBindingCtx binding{expr, expr->args.size() - expr->arg_names.size(),
                           ctx, arena};
  std::vector<DpiArgValue> args = BindDpiCallActuals(import, binding);

  // §35.5.3: "A DPI call chain is a call chain ... that begins when
  // SystemVerilog code calls an imported subroutine." This call site is that
  // beginning, and the frame's context property is the one the import's own
  // declaration carries (§35.5.1.3). The frame's scope is the instance the
  // call is made in, by its fully qualified name (§H.9.3), which is the scope
  // an export that instance declares is reached in (§35.5.3).
  DpiScope scope;
  scope.name = DpiInstanceScopeName(ctx.ActiveInstancePrefix(), ctx);
  dpi->EnterDeclaredImportCall(callee, std::move(scope));

  DpiArgValue result;
  if (import->is_pure) {
    // §35.5.2: a pure function's call "can be ... replaced with the value
    // previously computed for the same values of the input arguments", and a
    // pure function has no output or inout formals for a copy-back to carry.
    result = dpi->CallImportReusingPureResult(callee, args);
  } else {
    // §35.5.1.2 and §35.6.1 copy the written formals back into the actuals;
    // §35.6.2 says which of those actuals the call actually changed.
    std::vector<DpiArgValueChange> changes;
    result = dpi->CallImportDetectingChanges(callee, args, changes);
    WritebackDpiChangedArgs(import, binding, args, changes);
  }

  // §35.9 item c): an imported function returning while a disable is in effect
  // shall have acknowledged it first, and a simulator checks that on the
  // return. Leaving the frame is that return.
  dpi->LeaveImportCall();

  // §35.6.1: the result crosses back through a temporary of the declared result
  // type, so a body that computed it in another type is coerced to the type
  // §35.5.5 says the call site receives.
  // §35.5.5 restricts a function result to the small values it lists, every
  // one of which the kind's own width states, so no declared width travels
  // with it the way §35.5.6's packed formals carry one.
  return DpiValueOfType(arena, import->return_type, 0,
                        CoerceArgValue(result, import->return_type),
                        !import->return_is_unsigned);
}

DpiArgValue CallDpiExportedFunction(std::string_view key,
                                    const DpiRtExport& exp,
                                    std::vector<DpiArgValue>& args,
                                    SimContext& ctx) {
  Arena& arena = ctx.GetArena();
  auto* call = arena.Create<Expr>();
  call->kind = ExprKind::kCall;
  call->callee = *arena.Create<std::string>(key);
  ActualBindingCtx binding{call, exp.args.size(), ctx, arena};
  SendExportArguments(key, exp.args, args, call, binding);
  // The key and the temporaries are names from the root of the design, so the
  // call is evaluated as from there whatever instance C was entered from.
  InstancePrefixOverride root(ctx.InstancePrefixOverride(), "");
  Logic4Vec value = EvalExpr(call, ctx, arena);
  ReceiveExportArguments(exp.args, args, binding);
  return DpiArgValueOfType(exp.return_type, 0, value);
}

}  // namespace delta
