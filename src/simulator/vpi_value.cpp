#include <algorithm>
#include <cctype>
#include <cmath>
#include <cstdarg>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <deque>
#include <functional>
#include <optional>
#include <utility>
#include <vector>

#include "common/packed_range.h"
#include "common/types.h"
#include "simulator/class_object.h"
#include "simulator/deferred_caller.h"
#include "simulator/evaluation.h"
#include "simulator/net.h"
#include "simulator/process.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/vpi_user.h"
// §37.10 detail 3: the package/interface/program instance kinds are defined in
// the SystemVerilog VPI header alongside the §37.10 vpiInstance relation.
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"
#include "simulator/vpi_collection_elements.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_expr_scope.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_value_pools.h"
#include "simulator/vpi_value_strings.h"

namespace delta {

static int ScalarFromBits(uint64_t aval, uint64_t bval) {
  if (!bval) return aval ? kVpi1 : kVpi0;
  return aval ? kVpiX : kVpiZ;  // x=(1,1), z=(0,1)
}

static void GetValueVector(const Logic4Vec& v, s_vpi_value* value,
                           std::vector<std::vector<s_vpi_vecval>>& pool) {
  int width = static_cast<int>(v.width);
  // §38.15: the vector value occupies an array of s_vpi_vecval whose size is
  // ((vector_size - 1) / 32 + 1), one element per 32 bits of the vector; a
  // value of no bits is handed back as one element of 0.
  const int kGroups = (width + 31) / 32;
  std::vector<s_vpi_vecval> vec(static_cast<size_t>(std::max(kGroups, 1)));
  for (int i = 0; i < kGroups; ++i) {
    // Internal four-state words are 64 bits wide, so two vecval elements map
    // onto each word: the LSB of the vector lands in element 0, bit 33 in the
    // LSB of element 1, and so on.
    const Logic4Word& word = v.words[i / 2];
    int shift = (i % 2) * 32;
    auto a32 = static_cast<uint32_t>((word.aval >> shift) & 0xFFFFFFFFu);
    auto b32 = static_cast<uint32_t>((word.bval >> shift) & 0xFFFFFFFFu);
    // §38.15 / Figure 38-8: the returned encoding is ab 00=0, 10=1, 11=X,
    // 01=Z. The internal word now uses this same canonical encoding (X=a1/b1,
    // Z=a0/b1), so the boundary value is a direct copy with no conversion.
    vec[static_cast<size_t>(i)].aval = a32;
    vec[static_cast<size_t>(i)].bval = b32;
  }
  pool.push_back(std::move(vec));
  value->value.vector = pool.back().data();
}

static void GetValueStrength(
    const Logic4Vec& v, s_vpi_value* value,
    std::vector<std::vector<s_vpi_strengthval>>& pool) {
  int width = static_cast<int>(v.width);
  // §38.15: the strength arm holds one descriptor per bit of the vector, a
  // value of no bits one of 0. A reg or variable is always reported at strong
  // strength, so both the 0 and 1 drive components carry the strong-drive
  // code.
  std::vector<s_vpi_strengthval> arr(
      static_cast<size_t>(std::max(width, 1)),
      s_vpi_strengthval{kVpi0, vpiStrongDrive, vpiStrongDrive});
  for (int i = 0; i < width; ++i) {
    const Logic4Word& word = v.words[i / 64];
    const int kBit = i % 64;
    arr[static_cast<size_t>(i)].logic =
        ScalarFromBits((word.aval >> kBit) & 1, (word.bval >> kBit) & 1);
  }
  pool.push_back(std::move(arr));
  value->value.strength = pool.back().data();
}

static void GetValueIntVal(const Logic4Vec& v, s_vpi_value* value) {
  // §38.15, Table 38-3: any x or z bit of the object maps to a 0 in the
  // returned integer, so drop every unknown bit before handing it back.
  uint64_t aval = v.words[0].aval;
  uint64_t bval = v.words[0].bval;
  value->value.integer = static_cast<int>(aval & ~bval);
}

// §38.15, Table 38-3 (vpiTimeVal row): the value in an s_vpi_time the routine
// owns, value.time pointing at it, its high and low words the value's upper
// and lower 32 bits.
static void GetValueTime(const Logic4Vec& v, s_vpi_value* value,
                         std::deque<s_vpi_time>& pool) {
  const uint64_t kValue = v.ToUint64();
  s_vpi_time& time = pool.emplace_back();
  time.type = vpiSimTime;
  time.high = static_cast<PLI_UINT32>(kValue >> 32);
  time.low = static_cast<PLI_UINT32>(kValue & 0xFFFFFFFFu);
  time.real = 0.0;
  value->value.time = &time;
}

// §38.15: unpack the IEEE-754 pattern that a real object stores in its
// four-state word (§6.13 lays that pattern into the value bits). §6.12 makes
// a shortreal single precision, and RealVecToDouble reads which precision the
// object carries off its width.
static double ObjectRealValue(const Logic4Vec& v) { return RealVecToDouble(v); }

static void GetValueObjType(const Logic4Vec& v, s_vpi_value* value,
                            std::vector<std::vector<s_vpi_vecval>>& pool) {
  // §38.15: fill in the value and rewrite the format field to the closest
  // format for the object's type. A real object reports vpiRealVal, a
  // single-bit object is a scalar, and anything wider is a vector.
  if (v.is_real) {
    value->format = kVpiRealVal;
    value->value.real = ObjectRealValue(v);
  } else if (v.width == 1) {
    value->format = kVpiScalarVal;
    value->value.scalar =
        ScalarFromBits(v.words[0].aval & 1, v.words[0].bval & 1);
  } else {
    value->format = kVpiVectorVal;
    GetValueVector(v, value, pool);
  }
}

static void RecordVpiError(s_vpi_error_info& error, const char* message) {
  error.state = kVpiPLI;
  error.level = kVpiError;
  error.message = VpiText(message);
}

// Applies the §37.31/§37.26/§37.36 read-side restrictions. Returns true (with
// last_error recorded) when the read must be refused and the value buffer left
// untouched.
static bool GetValueIsRefused(VpiHandle obj, s_vpi_value* value,
                              s_vpi_error_info& error) {
  // §37.31 detail 2: vpi_get_value() is not allowed for variable and event
  // handles obtained from a class defn handle. Such a handle denotes a class
  // member rather than a free-standing object, so the read is refused, an error
  // is recorded, and the caller's value buffer is left untouched.
  if (obj->parent && obj->parent->type == vpiClassDefn &&
      VpiIsClassMemberValueType(obj->type)) {
    RecordVpiError(
        error,
        "vpi_get_value(): a variable or event handle obtained from a "
        "class definition handle has no accessible value");
    return true;
  }
  // §37.26 detail 1: the value of an entire unpacked structure or unpacked
  // union is not accessible through vpi_get_value(). Such an aggregate holds no
  // single scalar or vector value to hand back, so the read is refused, an
  // error is recorded, and the caller's value buffer is left untouched. A
  // packed struct/union is excluded by the helper and reads normally.
  if (VpiIsEntireUnpackedStructOrUnion(obj->type, obj->packed)) {
    RecordVpiError(error,
                   "vpi_get_value(): the value of an entire unpacked structure "
                   "or union cannot be accessed");
    return true;
  }
  // §37.36 detail 1: only a string value (the decompiled symbol row) and a
  // vector value (the row's ASCII symbol codes) shall be obtained for a table
  // entry object through vpi_get_value(). Any other requested format is
  // refused, an error is recorded, and the caller's value buffer is left
  // untouched.
  if (obj->type == vpiTableEntry && value->format != kVpiStringVal &&
      value->format != kVpiVectorVal) {
    RecordVpiError(
        error,
        "vpi_get_value(): a table entry value is available only as a "
        "string or a vector");
    return true;
  }
  return false;
}

static void DispatchIntegerFormat(const Logic4Vec& v, s_vpi_value* value,
                                  VpiValuePools& pools) {
  // §38.15, Table 38-3: fill the value buffer according to the requested
  // format. Each arm is the format-specific conversion; most delegate to a
  // dedicated helper, while the scalar and real arms are short inline reads.
  switch (value->format) {
    case kVpiIntVal:
      GetValueIntVal(v, value);
      break;
    case kVpiRealVal:
      value->value.real = static_cast<double>(v.ToUint64());
      break;
    case kVpiScalarVal:
      value->value.scalar =
          ScalarFromBits(v.words[0].aval & 1, v.words[0].bval & 1);
      break;
    case kVpiBinStrVal:
      GetValueBinStr(v, value, pools.strings);
      break;
    case kVpiDecStrVal:
      GetValueDecStr(v, value, pools.strings);
      break;
    case kVpiHexStrVal:
      GetValueHexStr(v, value, pools.strings);
      break;
    case kVpiOctStrVal:
      GetValueOctStr(v, value, pools.strings);
      break;
    case kVpiStringVal:
      GetValueStringVal(v, value, pools.strings);
      break;
    case kVpiTimeVal:
      GetValueTime(v, value, pools.times);
      break;
    case kVpiVectorVal:
      GetValueVector(v, value, pools.vectors);
      break;
    case kVpiStrengthVal:
      GetValueStrength(v, value, pools.strengths);
      break;
    case kVpiObjTypeVal:
      GetValueObjType(v, value, pools.vectors);
      break;
    default:
      break;
  }
}

// §37.16, §37.17: the one bit at `offset` of `whole`, as a value of its own.
// Every bit and select stands inside its vector, so the bit is one `whole`
// holds.
static Logic4Word BitOfValue(const Logic4Vec& whole, int offset) {
  const auto kWord = static_cast<uint32_t>(offset) / 64;
  const uint32_t kShift = static_cast<uint32_t>(offset) % 64;
  return Logic4Word{(whole.words[kWord].aval >> kShift) & 1,
                    (whole.words[kWord].bval >> kShift) & 1};
}

// §37.16 detail 31, §37.17 detail 26: the `width` bits at `offset` of `whole`,
// copied into `words`, as a value of their own.
static Logic4Vec SliceOfValue(const Logic4Vec& whole, int64_t offset, int width,
                              std::vector<Logic4Word>& words) {
  words.assign((static_cast<std::size_t>(width) + 63) / 64, Logic4Word{0, 0});
  for (int k = 0; k < width; ++k) {
    const Logic4Word kBit = BitOfValue(whole, static_cast<int>(offset + k));
    words[k / 64].aval |= kBit.aval << (k % 64);
    words[k / 64].bval |= kBit.bval << (k % 64);
  }
  Logic4Vec view;
  view.width = static_cast<uint32_t>(width);
  view.nwords = static_cast<uint32_t>(words.size());
  view.words = words.data();
  return view;
}

static void DispatchValueByFormat(const Logic4Vec& v, s_vpi_value* value,
                                  VpiValuePools& pools);

static void DispatchGetValueByFormat(VpiHandle obj, s_vpi_value* value,
                                     VpiValuePools& pools) {
  // A net bit or var bit reads its own bit of its parent's storage, and a
  // select leaving packed dimensions unindexed the bits it spans.
  if (obj->bit_offset >= 0) {
    std::vector<Logic4Word> words;
    const Logic4Vec kSlice = SliceOfValue(obj->var->value, obj->bit_offset,
                                          std::max(obj->size, 1), words);
    DispatchIntegerFormat(kSlice, value, pools);
    return;
  }
  DispatchValueByFormat(obj->var->value, value, pools);
}

// §38.15: `v` in the format `value` asks for, a real value read as a real in
// the formats that take one and as its rounded integer in the others.
static void DispatchValueByFormat(const Logic4Vec& v, s_vpi_value* value,
                                  VpiValuePools& pools) {
  if (v.is_real) {
    // §38.15: a real object is read as its floating-point value only in the
    // vpiRealVal and vpiStringVal formats. vpiObjTypeVal reduces to vpiRealVal
    // for a real object. Every other format first converts the real to an
    // integer using the rounding defined in §6.12.1 (round to nearest, ties
    // away from zero) and then formats that integer.
    if (value->format == kVpiObjTypeVal) {
      GetValueObjType(v, value, pools.vectors);
      return;
    }
    double d = ObjectRealValue(v);
    if (value->format == kVpiRealVal) {
      value->value.real = d;
      return;
    }
    if (value->format == kVpiStringVal) {
      // §38.15: return a decimal-notation string of the floating-point number
      // with at most 16 digits of precision.
      char buf[64];
      std::snprintf(buf, sizeof(buf), "%.16g", d);
      pools.strings.emplace_back(buf);
      value->value.str = VpiText(pools.strings.back().c_str());
      return;
    }
    // §6.12.1 rounding: nearest integer, ties away from zero.
    auto rounded = static_cast<uint64_t>(std::llround(d));
    Logic4Word iw{rounded, 0};
    Logic4Vec int_view;
    int_view.width = 64;
    int_view.nwords = 1;
    int_view.words = &iw;
    DispatchIntegerFormat(int_view, value, pools);
    return;
  }
  DispatchIntegerFormat(v, value, pools);
}

// §37.16 detail 31, §37.17 detail 26: a select out of a vector whose index is
// not a constant, which holds no bits of its parent's storage of its own and
// stands for those its index names when its value is read or written.
// PackedSelectObject records the dimension every such select indexes, each
// vector with bits recording its packed dimensions (MakeVectorBits); one whose
// index expression the model could not build is no varying select. The
// dimension a varying select indexes, null for any other object.
static const PackedRange* VaryingSelectDim(const VpiObject& obj) {
  return obj.select_dim.has_value() && obj.index_expr != nullptr
             ? &*obj.select_dim
             : nullptr;
}

// §37.3.5 with §38.15: the value of `obj`, which holds no storage but stands
// for an expression, an operation or a call (ExpressionObject records its
// scope): the expression evaluated where the source wrote it, by a stand-in
// process of the instance and generate blocks it stands in, as a process
// running there would read its names.
static Logic4Vec EvaluateExpressionObject(const VpiObject& obj,
                                          SimContext& sim) {
  const VpiExprScope& scope = *obj.expr_scope;
  Process stand_in;
  stand_in.stand_in = true;
  stand_in.inst_prefix = scope.inst_prefix;
  stand_in.gen_prefixes = scope.gen_prefixes;
  const CallerStandIn kStandIn(&stand_in, sim);
  return EvalExpr(scope.expr, sim, sim.GetArena());
}

// The index a varying select's index expression now holds: the value of the
// variable or net it names, or of the expression it is, an index holding no
// storage being one; none where it holds an x or z bit (§11.5.1).
static std::optional<int64_t> VaryingIndex(const VpiObject& obj,
                                           SimContext* sim) {
  VpiObject& index = *obj.index_expr;
  Logic4Vec held;
  if (index.var != nullptr) {
    VpiRefreshElementCopy(index);
    held = index.var->value;
  } else {
    held = EvaluateExpressionObject(index, *sim);
  }
  if (!held.IsKnown()) return std::nullopt;
  return SelectBoundValue(held);
}

// §37.16 detail 31, §37.17 detail 26: the offset in its parent's storage of
// the bits a varying select now stands for; none where its index names no
// element of the dimension it indexes.
static std::optional<int64_t> VaryingOffset(const VpiObject& obj,
                                            const PackedRange& dim,
                                            SimContext* sim) {
  const std::optional<int64_t> kIndex = VaryingIndex(obj, sim);
  if (!kIndex || !dim.Contains(*kIndex)) return std::nullopt;
  return obj.select_base_offset +
         (dim.OffsetOf(*kIndex) * std::max(obj.size, 1));
}

// §38.15 for a varying select: the value of the bits its index selects, or,
// when it selects none, x of a 4-state vector and 0 of a 2-state one in each
// of its bits (§11.5.1). Its storage is its vector's (SliceObject).
static void GetVaryingSelectValue(VpiHandle obj, const PackedRange& dim,
                                  s_vpi_value* value, VpiValuePools& pools,
                                  SimContext* sim) {
  const Variable& whole = *obj->var;
  const int kWidth = std::max(obj->size, 1);
  std::vector<Logic4Word> words;
  if (const std::optional<int64_t> kOffset = VaryingOffset(*obj, dim, sim)) {
    DispatchIntegerFormat(SliceOfValue(whole.value, *kOffset, kWidth, words),
                          value, pools);
    return;
  }
  const uint64_t kFill = whole.is_4state ? ~uint64_t{0} : 0;
  words.assign((static_cast<std::size_t>(kWidth) + 63) / 64,
               Logic4Word{kFill, kFill});
  if (kWidth % 64 != 0) {
    const uint64_t kMask = (uint64_t{1} << (kWidth % 64)) - 1;
    words.back().aval &= kMask;
    words.back().bval &= kMask;
  }
  Logic4Vec fill;
  fill.width = static_cast<uint32_t>(kWidth);
  fill.nwords = static_cast<uint32_t>(words.size());
  fill.words = words.data();
  DispatchIntegerFormat(fill, value, pools);
}

// §37.12: binds the object of a variable a named block declares to the storage
// the run made for it when the block ran, after the model was built, once that
// storage exists.
static void BindRunStorage(VpiObject& obj, SimContext* sim) {
  // An object carries a run key only where a run built it, so the run is
  // there to look it up in.
  if (obj.var == nullptr && !obj.run_key.empty()) {
    obj.var = sim->FindVariable(obj.run_key);
  }
}

void VpiContext::GetValue(VpiHandle obj, s_vpi_value* value) {
  if (!obj || !value) return;
  // §37.3.6: an object a decryption envelope sealed gives up no value; the
  // caller's buffer is left as it was.
  if (VpiReadSealed(*obj)) {
    last_error_.state = kVpiPLI;
    last_error_.level = kVpiError;
    last_error_.message =
        VpiText("vpi_get_value() on a protected object is an error");
    return;
  }
  // §37.3.5: applying vpi_get_value() to an expression with side effects shall
  // fully evaluate the expression together with its side effects. Reading the
  // value performs that evaluation, so record that the side effect occurred
  // before the value is handed back below - the count is the observable
  // evidence that evaluation, and thus the embedded state change, took place.
  if (VpiExpressionHasSideEffects(obj)) {
    ++obj->side_effect_count;
  }
  if (GetValueIsRefused(obj, value, last_error_)) return;
  VpiRefreshElementCopy(*obj);
  BindRunStorage(*obj, sim_ctx_);
  if (!obj->var) {
    // §37.3.5 with §38.15: an operation or a call holds no storage; its value
    // is its expression's, evaluated now. Any other object without storage
    // gives none, and the caller's buffer is left as it was.
    if (obj->expr_scope != nullptr) {
      DispatchValueByFormat(EvaluateExpressionObject(*obj, *sim_ctx_), value,
                            value_pools_);
    }
    return;
  }
  if (const PackedRange* dim = VaryingSelectDim(*obj)) {
    GetVaryingSelectValue(obj, *dim, value, value_pools_, sim_ctx_);
    return;
  }
  DispatchGetValueByFormat(obj, value, value_pools_);
}

// Applies the §37.31/§37.26/§37.35/§37.3.5 target-kind restrictions that hold
// regardless of the requested delay mode. Returns true (with error recorded)
// when the put must be refused and the target left unchanged.
static bool PutValueTargetIsRejected(VpiHandle obj, s_vpi_error_info& error) {
  // §37.31 detail 2: vpi_put_value() is not allowed for variable and event
  // handles obtained from a class defn handle, the write side of the same
  // restriction vpi_get_value() observes. The put is rejected, an error is
  // recorded, and the member is left unchanged.
  if (obj->parent && obj->parent->type == vpiClassDefn &&
      VpiIsClassMemberValueType(obj->type)) {
    RecordVpiError(
        error,
        "vpi_put_value(): a variable or event handle obtained from a "
        "class definition handle has no accessible value");
    return true;
  }

  // §37.26 detail 1: an entire unpacked structure or union cannot be written
  // through vpi_put_value() any more than it can be read - it has no single
  // value to take the write. The put is rejected, an error is recorded, and the
  // aggregate is left unchanged. A packed struct/union is excluded by the
  // helper and is written through the normal path below.
  if (VpiIsEntireUnpackedStructOrUnion(obj->type, obj->packed)) {
    RecordVpiError(error,
                   "vpi_put_value(): the value of an entire unpacked structure "
                   "or union cannot be accessed");
    return true;
  }

  // §36.5: a user-defined system function yields a value and a user-defined
  // system task yields none, so a write through the call handle
  // §37.42 gives the application -- which is how a system function's result is
  // delivered -- has nowhere to land on a task call. §38.34 lists the objects
  // this routine applies to and names system function calls among
  // them, with no system task call beside it. The put is rejected, an error is
  // recorded, and the run reads no value out of the task.
  if (obj->type == vpiSysTaskCall) {
    RecordVpiError(error,
                   "vpi_put_value(): a user-defined system task call has no "
                   "return value to write");
    return true;
  }

  // §37.35 detail 2: among primitives, vpi_put_value() may be applied only to a
  // sequential UDP. Putting a value to any other primitive kind - a gate,
  // switch, combinational UDP, or a generic primitive - is not allowed, so the
  // put is rejected before any value is written. (The complementary delay-mode
  // restriction on a sequential UDP itself is checked further below.)
  if (VpiObjectIsPrimitive(obj->type) && obj->type != vpiSeqPrim) {
    RecordVpiError(
        error,
        "vpi_put_value(): only a sequential UDP primitive may be written");
    return true;
  }

  // §37.3.5: it is an error to apply vpi_put_value() to an object when any of
  // its index expressions has side effects (for instance my_array[i++] or
  // my_array[--i]). The write is rejected before any value is stored - an error
  // is recorded, the target is left unchanged, and the side-effecting index is
  // not evaluated.
  for (const VpiObject* index : obj->index_expressions) {
    if (VpiExpressionHasSideEffects(index)) {
      RecordVpiError(
          error,
          "vpi_put_value(): an index expression with side effects is "
          "not allowed");
      return true;
    }
  }
  return false;
}

// Applies the §38.34 format-legality checks for the (now known) target
// variable. Returns true (with error recorded) when the requested format is not
// legal for the object and the put must be refused.
static bool PutValueFormatIsRejected(VpiHandle obj, const s_vpi_value* value,
                                     s_vpi_error_info& error) {
  // §38.34: it is illegal to give the value the vpiStringVal format when the
  // target is a real object. Record the error and leave the object unchanged.
  if (value->format == kVpiStringVal && obj->var->value.is_real) {
    RecordVpiError(error,
                   "vpi_put_value(): vpiStringVal is not a legal format for a "
                   "real object");
    return true;
  }

  // §38.34: it is illegal to give the value the vpiStrengthVal format when the
  // target is a vector object (more than one bit wide).
  if (value->format == kVpiStrengthVal && obj->var->value.width > 1) {
    RecordVpiError(
        error,
        "vpi_put_value(): vpiStrengthVal is not a legal format for a "
        "vector object");
    return true;
  }
  return false;
}

// §38.34 with Table 38-3: the value `value` gives, decoded from whichever
// format it is in, written to every bit of the target variable, or, for a net
// bit or var bit, to its bit of the parent's storage, and for a select leaving
// packed dimensions unindexed (§37.16 detail 31, §37.17 detail 26) to the
// `size` bits it spans, from the least significant up. A format that gives no
// bits writes nothing.
static void PutValueWriteBits(VpiHandle obj, const s_vpi_value* value) {
  const uint32_t kWidth = VpiPutWidth(*obj);
  std::vector<Logic4Word> bits;
  if (VpiPutValueBits(*value, kWidth, bits)) {
    VpiWriteDecodedBits(*obj, bits, kWidth);
  }
}

// §38.34: resolves whether the target carries a writable variable before any
// value is stored. Returns true when PutValue must stop here (no var and no
// net, the net-only write attempt, or the named-event trigger all finish in
// this phase, and the caller returns nullptr); returns false to continue to the
// value-store path.
static bool PutValueResolveWritableTarget(VpiHandle obj, Scheduler* scheduler) {
  if (!obj->var && !obj->net) return true;

  if (!obj->var) {
    if (scheduler) scheduler->NoteWriteAttempt();
    return true;
  }

  // §38.34: putting to a vpiNamedEvent toggles (triggers) the named event. Such
  // an object needs no value, so value_p may be NULL and is not consulted.
  if (obj->var->is_event) {
    if (scheduler) obj->var->triggered_ticks = scheduler->CurrentTime().ticks;
    return true;
  }
  return false;
}

// §38.34: notes the write attempt, stores the supplied value into the target,
// and, for vpiForceFlag, latches it as the held forced value. This is the
// committed-write phase reached once every legality check has passed.
static void PutValueApplyWriteAndForce(VpiHandle obj, const s_vpi_value* value,
                                       int mode, Scheduler* scheduler) {
  if (scheduler) scheduler->NoteWriteAttempt();

  PutValueWriteBits(obj, value);
  // §4.3: the write is an update event of the object, which resumes what
  // waits on it (§9.4.2), as vpi_put_value_array's writes do.
  obj->var->NotifyWatchers();

  // §38.34: vpiForceFlag performs a procedural force (§10.6.2): the supplied
  // value takes effect now and is held as the forced value.
  if (mode == vpiForceFlag) {
    obj->var->is_forced = true;
    obj->var->forced_value = obj->var->value;
  }
}

// §38.34: vpiNoDelay, vpiForceFlag, and vpiReleaseFlag all act immediately and
// ignore time_p; every other mode takes its delay from time_p, where a delay is
// present when a nonzero time is supplied.
static bool PutValueHasDelay(int mode, const s_vpi_time* time) {
  bool immediate =
      (mode == vpiNoDelay || mode == vpiForceFlag || mode == vpiReleaseFlag);
  return !immediate && time &&
         (time->low != 0 || time->high != 0 || time->real != 0.0);
}

// Applies the §38.34/§37.43 delay-mode restrictions (sequential UDP must be
// written with vpiNoDelay; no delayed put on an automatic variable). Returns
// true (with error recorded) when the put must be refused.
static bool PutValueDelayModeIsRejected(VpiHandle obj, int mode, bool has_delay,
                                        s_vpi_error_info& error) {
  // §38.34: a sequential UDP is always set with no delay, no matter what delay
  // the primitive instance carries, so a value may be put to it only with the
  // vpiNoDelay flag. Supplying one of the scheduled delay modes instead is an
  // error, and the put is rejected.
  if (obj->type == vpiSeqPrim &&
      (mode == vpiInertialDelay || mode == vpiTransportDelay ||
       mode == vpiPureTransportDelay)) {
    RecordVpiError(error,
                   "vpi_put_value(): a sequential UDP must be written with the "
                   "vpiNoDelay flag");
    return true;
  }

  // §37.43 detail 3: it is illegal to put a value with a delay on an automatic
  // variable. A delay would schedule the update for a future time, but the
  // automatic object's storage may no longer exist by then. Reject the put
  // rather than applying it.
  if (obj->automatic && has_delay) {
    RecordVpiError(error,
                   "vpi_put_value(): a value with a delay may not be put on an "
                   "automatic variable");
    return true;
  }
  return false;
}

// §37.3.6: nor is a value written to an object a decryption envelope sealed;
// the error is recorded and nothing is scheduled.
static bool PutValueIsSealed(const VpiObject& obj, s_vpi_error_info& error) {
  if (!VpiWriteSealed(obj)) return false;
  RecordVpiError(error, "vpi_put_value() on a protected object is an error");
  return true;
}

// The object a value put to `obj` is written to: `obj` itself, or for a
// varying select (§37.16, §37.17) a slice, made through `alloc`, of the bits
// its index names; null when it names none and nothing is written (§11.5.1).
static VpiHandle PutValueTargetOf(VpiHandle obj,
                                  const std::function<VpiObject*()>& alloc,
                                  SimContext* sim) {
  const PackedRange* dim = VaryingSelectDim(*obj);
  if (dim == nullptr) return obj;
  // A varying select stands for the bits its index names when the value is
  // put, made a slice of them here, one bit wide for a select of one bit.
  const std::optional<int64_t> kOffset = VaryingOffset(*obj, *dim, sim);
  if (!kOffset) return nullptr;
  VpiObject* slice = alloc();
  slice->type = obj->type;
  slice->parent = obj->parent;
  slice->var = obj->parent->var;
  slice->net = obj->parent->net;
  slice->size = obj->size;
  slice->bit_offset = static_cast<int>(*kOffset);
  return slice;
}

// §38.34: a vpiCancelEvent put, which leaves a scheduled event no longer
// scheduled and hands back no handle.
// §9.4.3 with §37.33: a put into a class property is a write of it, which
// resumes what waits on the owning object's properties, or, for a static
// property, on the class's.
static void NotifyPropertyWrite(const VpiObject& obj, SimContext& ctx) {
  const ClassObject& owner = *obj.property_of;
  // A class object is an instance of its class, which it always names.
  const ClassTypeInfo* declarer = owner.type->StaticPropertyDeclarer(obj.name);
  if (declarer != nullptr) {
    declarer->NotifyStaticWatchers();
    return;
  }
  ctx.NotifyClassHandleWatchers(owner.handle);
}

static VpiHandle CancelScheduledEvent(VpiHandle obj) {
  if (obj->type != vpiSchedEvent) return nullptr;
  if (obj->scheduled && obj->put_superseded) *obj->put_superseded = true;
  obj->scheduled = false;
  return nullptr;
}

// §38.36.2 with §4.4.2.9: whether a put with `flags` is refused for being
// made while a cbReadOnlySynch routine runs, as `at_read_only_synch` says one
// is: no value is written, and no event scheduled, then; a cancel writes none.
static bool PutValueRefusedInReadOnlySynch(bool at_read_only_synch, int flags,
                                           s_vpi_error_info& error) {
  if (!at_read_only_synch || (flags & ~vpiReturnEvent) == vpiCancelEvent) {
    return false;
  }
  RecordVpiError(error,
                 "vpi_put_value(): no value may be written from a "
                 "cbReadOnlySynch callback");
  return true;
}

// §38.34: release the force on `obj` as the procedural release of §10.6.2
// does in the run `sim`, or, outside a run, clear its forced state.
static void PutValueRelease(VpiObject& obj, SimContext* sim) {
  if (sim != nullptr) {
    ReleaseForcedTarget(obj.var, obj.net, *sim, sim->GetArena());
  } else {
    obj.var->is_forced = false;
  }
}

// The run a put writes in: its scheduler and context, null outside one, its
// simulation time unit, and how a handle for a scheduled event is made.
struct PutValueRun {
  Scheduler* scheduler;
  SimContext* sim;
  int sim_time_unit;
  std::function<VpiObject*()> alloc;
};

// §38.34: write `value` to the resolved target `obj` under `flags`, at the
// delay `time` gives, in `run`: a put with a delay in a run is an event in its
// queue, and any other is written now, the waiters on the object or the class
// property it is woken; the scheduled event's handle where vpiReturnEvent
// asked for it, else null.
static VpiHandle PutValueWrite(VpiObject* obj, s_vpi_value* value,
                               const s_vpi_time* time, int flags,
                               const PutValueRun& run) {
  const bool kReturnEvent = (flags & vpiReturnEvent) != 0;
  const int kMode = flags & ~vpiReturnEvent;
  const bool kHasDelay = PutValueHasDelay(kMode, time);
  if (kHasDelay && run.scheduler != nullptr) {
    VpiObject* event = run.alloc();
    event->event_time = run.scheduler->CurrentTime().ticks +
                        VpiPutDelayTicks(*obj, *time, run.sim_time_unit);
    VpiSchedulePut(*obj, *value, kMode, *run.scheduler, *event);
    return kReturnEvent ? event : nullptr;
  }

  PutValueApplyWriteAndForce(obj, value, kMode, run.scheduler);
  if (!kHasDelay) VpiStoreElementCopy(*obj);
  // A class property's object is made by a run, which is there to wake.
  if (obj->property_of != nullptr) {
    NotifyPropertyWrite(*obj, *run.sim);
  }

  // §38.34: a handle to the scheduled event is returned only when
  // vpiReturnEvent was requested and a delay actually scheduled an event; in
  // every other case (no bit mask, no delay, or nothing scheduled) the return
  // value is NULL.
  if (!kReturnEvent || !kHasDelay) return nullptr;
  VpiObject* ev = run.alloc();
  ev->type = vpiSchedEvent;
  ev->scheduled = true;
  return ev;
}

VpiHandle VpiContext::PutValue(VpiHandle obj, s_vpi_value* value,
                               s_vpi_time* time, int flags) {
  if (!obj) return nullptr;
  if (PutValueIsSealed(*obj, last_error_) ||
      PutValueTargetIsRejected(obj, last_error_) ||
      PutValueRefusedInReadOnlySynch(at_read_only_synch_time_, flags,
                                     last_error_)) {
    return nullptr;
  }

  // §38.34: vpiReturnEvent is an independent bit mask layered on top of the
  // delay-mode selector that lives in the low bits of the flags word.
  int mode = flags & ~vpiReturnEvent;

  // §38.34: vpiCancelEvent removes a previously scheduled event. The object
  // must be a vpiSchedEvent handle, and value_p and time_p are not needed. It
  // is not an error to cancel an event that has already occurred, so a handle
  // that is no longer scheduled is simply left alone. Cancelling removes the
  // event from the queue and frees the handle to it.
  if (mode == vpiCancelEvent) {
    CancelScheduledEvent(obj);
    if (obj->type == vpiSchedEvent) ReleaseHandle(obj);
    return nullptr;
  }

  obj = PutValueTargetOf(obj, [this] { return AllocObject(); }, sim_ctx_);
  if (obj == nullptr) return nullptr;

  bool has_delay = PutValueHasDelay(mode, time);

  if (PutValueDelayModeIsRejected(obj, mode, has_delay, last_error_)) {
    return nullptr;
  }

  BindRunStorage(*obj, sim_ctx_);
  if (PutValueResolveWritableTarget(obj, scheduler_)) return nullptr;

  if (!value || PutValueFormatIsRejected(obj, value, last_error_)) {
    return nullptr;
  }

  // §38.34: vpiReleaseFlag releases a forced value, the same operation as the
  // procedural release of §10.6.2, and writes the object's post-release value
  // back through value_p so the caller can observe what the object settled to.
  if (mode == vpiReleaseFlag) {
    PutValueRelease(*obj, sim_ctx_);
    GetValue(obj, value);
    return nullptr;
  }

  return PutValueWrite(
      obj, value, time, flags,
      {scheduler_, sim_ctx_, sim_time_unit_, [this] { return AllocObject(); }});
}

// §38.35: the value formats vpi_put_value_array() accepts. The int/vector/time/
// real forms are the vpi_get_value() formats reused from §38.15 (Table 38-3);
// the raw aval/bval forms and the short/long/short-real C-scalar forms are the
// additions §38.35 defines. Any other format is unsupported.
}  // namespace delta
