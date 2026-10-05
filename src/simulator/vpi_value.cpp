#include <algorithm>
#include <cctype>
#include <cmath>
#include <cstdarg>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <functional>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "common/packed_range.h"
#include "common/types.h"
#include "simulator/evaluation.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/vpi_user.h"
// §37.10 detail 3: the package/interface/program instance kinds are defined in
// the SystemVerilog VPI header alongside the §37.10 vpiInstance relation.
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"
#include "simulator/vpi_collection_elements.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"

namespace delta {

static void GetValueBinStr(const Logic4Vec& v, s_vpi_value* value,
                           std::vector<std::string>& pool) {
  uint64_t aval = v.words[0].aval;
  uint64_t bval = v.words[0].bval;
  int width = static_cast<int>(v.width);
  std::string result;
  result.reserve(width);
  for (int i = width - 1; i >= 0; --i) {
    bool a_bit = (aval >> i) & 1;
    bool b_bit = (bval >> i) & 1;
    if (!b_bit) {
      result += (a_bit ? '1' : '0');
    } else {
      result += (a_bit ? 'x' : 'z');  // x=(1,1), z=(0,1)
    }
  }
  pool.push_back(std::move(result));
  value->value.str = VpiText(pool.back().c_str());
}

static char HexDigitFromBits(uint8_t nibble) {
  if (nibble < 10) return static_cast<char>('0' + nibble);
  return static_cast<char>('a' + nibble - 10);
}

// §38.15, Table 38-3 (octal/hex rows): choose the character for a digit group
// that contains at least one unknown bit. `mask` selects the group's valid bits
// (the top group may be narrower than a full digit). A group with any x bit
// prints lowercase 'x' only when every valid bit is x, otherwise uppercase 'X';
// otherwise the unknown bits are all z, printing lowercase 'z' when every valid
// bit is z, otherwise uppercase 'Z'. Canonical bit encoding: x=(a1,b1),
// z=(a0,b1).
static char UnknownGroupChar(uint8_t a_bits, uint8_t b_bits, uint8_t mask) {
  uint8_t unknown = b_bits & mask;
  uint8_t x_bits = a_bits & b_bits & mask;  // unknown bits that are x
  if (x_bits != 0) {
    bool all_x = unknown == mask && (a_bits & mask) == mask;
    return all_x ? 'x' : 'X';
  }
  bool all_z = unknown == mask && (a_bits & mask) == 0;
  return all_z ? 'z' : 'Z';
}

static void GetValueHexStr(const Logic4Vec& v, s_vpi_value* value,
                           std::vector<std::string>& pool) {
  uint64_t aval = v.words[0].aval;
  uint64_t bval = v.words[0].bval;
  int width = static_cast<int>(v.width);
  int hex_digits = (width + 3) / 4;
  std::string result;
  result.reserve(hex_digits);
  for (int i = hex_digits - 1; i >= 0; --i) {
    uint8_t a_nibble = (aval >> (i * 4)) & 0xF;
    uint8_t b_nibble = (bval >> (i * 4)) & 0xF;
    if (b_nibble != 0) {
      int valid = std::min(4, width - i * 4);
      result += UnknownGroupChar(a_nibble, b_nibble,
                                 static_cast<uint8_t>((1u << valid) - 1));
    } else {
      result += HexDigitFromBits(a_nibble);
    }
  }
  pool.push_back(std::move(result));
  value->value.str = VpiText(pool.back().c_str());
}

static void GetValueOctStr(const Logic4Vec& v, s_vpi_value* value,
                           std::vector<std::string>& pool) {
  uint64_t aval = v.words[0].aval;
  uint64_t bval = v.words[0].bval;
  int width = static_cast<int>(v.width);
  int oct_digits = (width + 2) / 3;
  std::string result;
  result.reserve(oct_digits);
  for (int i = oct_digits - 1; i >= 0; --i) {
    uint8_t a_bits = (aval >> (i * 3)) & 0x7;
    uint8_t b_bits = (bval >> (i * 3)) & 0x7;
    if (b_bits != 0) {
      int valid = std::min(3, width - i * 3);
      result += UnknownGroupChar(a_bits, b_bits,
                                 static_cast<uint8_t>((1u << valid) - 1));
    } else {
      result += static_cast<char>('0' + a_bits);
    }
  }
  pool.push_back(std::move(result));
  value->value.str = VpiText(pool.back().c_str());
}

static int ScalarFromBits(uint64_t aval, uint64_t bval) {
  if (!bval) return aval ? kVpi1 : kVpi0;
  return aval ? kVpiX : kVpiZ;  // x=(1,1), z=(0,1)
}

static void GetValueVector(const Logic4Vec& v, s_vpi_value* value,
                           std::vector<std::vector<s_vpi_vecval>>& pool) {
  int width = static_cast<int>(v.width);
  // §38.15: the vector value occupies an array of s_vpi_vecval whose size is
  // ((vector_size - 1) / 32 + 1), one element per 32 bits of the vector.
  int array_size = width > 0 ? ((width - 1) / 32 + 1) : 1;
  std::vector<s_vpi_vecval> vec(static_cast<size_t>(array_size));
  for (int i = 0; i < array_size; ++i) {
    // Internal four-state words are 64 bits wide, so two vecval elements map
    // onto each word: the LSB of the vector lands in element 0, bit 33 in the
    // LSB of element 1, and so on.
    int word_idx = i / 2;
    int shift = (i % 2) * 32;
    uint64_t aval =
        word_idx < static_cast<int>(v.nwords) ? v.words[word_idx].aval : 0;
    uint64_t bval =
        word_idx < static_cast<int>(v.nwords) ? v.words[word_idx].bval : 0;
    auto a32 = static_cast<uint32_t>((aval >> shift) & 0xFFFFFFFFu);
    auto b32 = static_cast<uint32_t>((bval >> shift) & 0xFFFFFFFFu);
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
  if (width < 1) width = 1;
  // §38.15: the strength arm holds one descriptor per bit of the vector.
  std::vector<s_vpi_strengthval> arr(static_cast<size_t>(width));
  for (int i = 0; i < width; ++i) {
    int word_idx = i / 64;
    int bit = i % 64;
    uint64_t aval =
        word_idx < static_cast<int>(v.nwords) ? v.words[word_idx].aval : 0;
    uint64_t bval =
        word_idx < static_cast<int>(v.nwords) ? v.words[word_idx].bval : 0;
    arr[static_cast<size_t>(i)].logic =
        ScalarFromBits((aval >> bit) & 1, (bval >> bit) & 1);
    // §38.15: a reg or variable is always reported at strong strength, so both
    // the 0 and 1 drive components carry the strong-drive code.
    arr[static_cast<size_t>(i)].s0 = vpiStrongDrive;
    arr[static_cast<size_t>(i)].s1 = vpiStrongDrive;
  }
  pool.push_back(std::move(arr));
  value->value.strength = pool.back().data();
}

static void GetValueStringVal(const Logic4Vec& v, s_vpi_value* value,
                              std::vector<std::string>& pool) {
  uint64_t val = v.ToUint64();
  std::string s;
  for (int i = 56; i >= 0; i -= 8) {
    auto ch = static_cast<char>((val >> i) & 0xFF);
    if (ch != 0) s += ch;
  }
  pool.push_back(std::move(s));
  value->value.str = VpiText(pool.back().c_str());
}

static void GetValueIntVal(const Logic4Vec& v, s_vpi_value* value) {
  // §38.15, Table 38-3: any x or z bit of the object maps to a 0 in the
  // returned integer, so drop every unknown bit before handing it back.
  uint64_t aval = v.words[0].aval;
  uint64_t bval = v.words[0].bval;
  value->value.integer = static_cast<int>(aval & ~bval);
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

static void DispatchIntegerFormat(
    const Logic4Vec& v, s_vpi_value* value, std::vector<std::string>& str_pool,
    std::vector<std::vector<s_vpi_vecval>>& vec_pool,
    std::vector<std::vector<s_vpi_strengthval>>& strength_pool) {
  // §38.15, Table 38-3: fill the value buffer according to the requested
  // format. Each arm is the format-specific conversion; most delegate to a
  // dedicated helper, while the scalar/real/time arms are short inline reads.
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
      GetValueBinStr(v, value, str_pool);
      break;
    case kVpiHexStrVal:
      GetValueHexStr(v, value, str_pool);
      break;
    case kVpiOctStrVal:
      GetValueOctStr(v, value, str_pool);
      break;
    case kVpiStringVal:
      GetValueStringVal(v, value, str_pool);
      break;
    case kVpiTimeVal:
      value->value.integer = static_cast<int>(v.ToUint64());
      break;
    case kVpiVectorVal:
      GetValueVector(v, value, vec_pool);
      break;
    case kVpiStrengthVal:
      GetValueStrength(v, value, strength_pool);
      break;
    case kVpiObjTypeVal:
      GetValueObjType(v, value, vec_pool);
      break;
    default:
      break;
  }
}

// §37.16, §37.17: the one bit at `offset` of `whole`, as a value of its own.
static Logic4Word BitOfValue(const Logic4Vec& whole, int offset) {
  const auto kWord = static_cast<uint32_t>(offset) / 64;
  const uint32_t kShift = static_cast<uint32_t>(offset) % 64;
  if (kWord >= whole.nwords) return Logic4Word{0, 1};
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

static void DispatchGetValueByFormat(
    VpiHandle obj, s_vpi_value* value, std::vector<std::string>& str_pool,
    std::vector<std::vector<s_vpi_vecval>>& vec_pool,
    std::vector<std::vector<s_vpi_strengthval>>& strength_pool) {
  // A net bit or var bit reads its own bit of its parent's storage, and a
  // select leaving packed dimensions unindexed the bits it spans.
  if (obj->bit_offset >= 0) {
    std::vector<Logic4Word> words;
    const Logic4Vec kSlice = SliceOfValue(obj->var->value, obj->bit_offset,
                                          std::max(obj->size, 1), words);
    DispatchIntegerFormat(kSlice, value, str_pool, vec_pool, strength_pool);
    return;
  }
  const Logic4Vec& v = obj->var->value;
  if (v.is_real) {
    // §38.15: a real object is read as its floating-point value only in the
    // vpiRealVal and vpiStringVal formats. vpiObjTypeVal reduces to vpiRealVal
    // for a real object. Every other format first converts the real to an
    // integer using the rounding defined in §6.12.1 (round to nearest, ties
    // away from zero) and then formats that integer.
    if (value->format == kVpiObjTypeVal) {
      GetValueObjType(v, value, vec_pool);
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
      str_pool.emplace_back(buf);
      value->value.str = VpiText(str_pool.back().c_str());
      return;
    }
    // §6.12.1 rounding: nearest integer, ties away from zero.
    auto rounded = static_cast<uint64_t>(std::llround(d));
    Logic4Word iw{rounded, 0};
    Logic4Vec int_view;
    int_view.width = 64;
    int_view.nwords = 1;
    int_view.words = &iw;
    DispatchIntegerFormat(int_view, value, str_pool, vec_pool, strength_pool);
    return;
  }
  DispatchIntegerFormat(v, value, str_pool, vec_pool, strength_pool);
}

// §37.16, §37.17: a net bit or var bit selected by an index that is not a
// constant, which has no bit of its parent's storage of its own.
static bool IsVaryingBit(const VpiObject& obj) {
  return (obj.type == vpiNetBit || obj.type == vpiRegBit ||
          obj.select_dim.has_value()) &&
         obj.bit_offset < 0 && obj.parent != nullptr &&
         obj.index_expr != nullptr;
}

// The index a varying select's index expression now holds; none where it
// holds an x or z bit (§11.5.1).
static std::optional<int64_t> VaryingIndex(VpiHandle obj) {
  VpiHandle index = obj->index_expr;
  if (index->var == nullptr) return std::nullopt;
  VpiRefreshElementCopy(*index);
  const Logic4Vec& held = index->var->value;
  if (held.width == 0 || held.is_real || !held.IsKnown()) return std::nullopt;
  return SelectBoundValue(held);
}

// §37.16 detail 31, §37.17 detail 26: the offset in its parent's storage of
// the bits a varying select that records the dimension it indexes now
// stands for; none where its index names no element of the dimension.
static std::optional<int64_t> VaryingOffset(VpiHandle obj) {
  const std::optional<PackedRange>& dim = obj->select_dim;
  const std::optional<int64_t> kIndex = VaryingIndex(obj);
  if (!dim || !kIndex || !dim->Contains(*kIndex)) return std::nullopt;
  return obj->select_base_offset +
         (dim->OffsetOf(*kIndex) * std::max(obj->size, 1));
}

// The bit of its vector a varying bit stands for when a value is read or
// written: the vector's bit at the index its index expression then holds. An
// index with an x or z bit, or one naming no bit of the vector, selects none
// (§11.5.1).
static VpiHandle VaryingBitTarget(VpiHandle obj) {
  if (obj->select_dim && obj->size > 1) return nullptr;
  const std::optional<int64_t> kIndex = VaryingIndex(obj);
  const std::optional<int64_t> kOffset =
      obj->select_dim ? VaryingOffset(obj) : std::nullopt;
  if (!kIndex || (obj->select_dim && !kOffset)) return nullptr;
  for (VpiHandle bit : obj->parent->children) {
    const bool kSelected =
        kOffset ? bit->bit_offset == *kOffset : bit->index == *kIndex;
    if (bit != obj && bit->type == obj->type && bit->bit_offset >= 0 &&
        kSelected) {
      return bit;
    }
  }
  return nullptr;
}

// §38.15 for a varying select: the value of the bits its index selects, or,
// when it selects none, x of a 4-state vector and 0 of a 2-state one in each
// of its bits (§11.5.1).
static void GetVaryingBitValue(
    VpiHandle obj, s_vpi_value* value, std::vector<std::string>& str_pool,
    std::vector<std::vector<s_vpi_vecval>>& vec_pool,
    std::vector<std::vector<s_vpi_strengthval>>& strength_pool) {
  const Variable* whole = obj->parent->var;
  const int kWidth = std::max(obj->size, 1);
  std::vector<Logic4Word> words;
  if (obj->select_dim) {
    const std::optional<int64_t> kOffset = VaryingOffset(obj);
    if (kOffset && whole != nullptr) {
      DispatchIntegerFormat(SliceOfValue(whole->value, *kOffset, kWidth, words),
                            value, str_pool, vec_pool, strength_pool);
      return;
    }
  } else if (VpiHandle target = VaryingBitTarget(obj);
             target != nullptr && target->var != nullptr) {
    DispatchGetValueByFormat(target, value, str_pool, vec_pool, strength_pool);
    return;
  }
  const bool kTwoState = whole != nullptr && !whole->is_4state;
  const uint64_t kFill = kTwoState ? 0 : ~uint64_t{0};
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
  DispatchIntegerFormat(fill, value, str_pool, vec_pool, strength_pool);
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
  if (IsVaryingBit(*obj)) {
    GetVaryingBitValue(obj, value, str_pool_, vec_pool_, strength_pool_);
    return;
  }
  VpiRefreshElementCopy(*obj);
  if (!obj->var) return;
  DispatchGetValueByFormat(obj, value, str_pool_, vec_pool_, strength_pool_);
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

  // §36.5: a user-defined system function "returns a value" and a user-defined
  // system task "does not return any value", so a write through the call handle
  // §37.42 gives the application -- which is how a system function's result is
  // delivered -- has nowhere to land on a task call. §38.34 lists the objects
  // this routine "can be applied to" and names system function calls among
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

// §37.16, §37.17: a value put to a net bit or var bit is put to its bit of
// the parent's storage, and one put to a select leaving packed dimensions
// unindexed (§37.16 detail 31, §37.17 detail 26) to the `size` bits it spans,
// from the least significant up. They are taken from the bit pattern a
// whole object's write stores of a scalar, integer or real value: the scalar
// in the low bit and 0 above it, and the integer or real as 64 bits.
static void PutValueWriteSlice(VpiHandle obj, const s_vpi_value* value) {
  uint64_t aval = 0;
  uint64_t bval = 0;
  if (value->format == kVpiIntVal) {
    aval = static_cast<uint64_t>(value->value.integer);
  } else if (value->format == kVpiRealVal) {
    aval = static_cast<uint64_t>(value->value.real);
  } else if (value->format == kVpiScalarVal) {
    int s = value->value.scalar;
    aval = (s == kVpi1 || s == kVpiX) ? 1 : 0;
    bval = (s == kVpiX || s == kVpiZ) ? 1 : 0;
  } else {
    return;
  }
  Logic4Vec& whole = obj->var->value;
  for (int k = 0; k < std::max(obj->size, 1); ++k) {
    const auto kBit = static_cast<uint32_t>(obj->bit_offset + k);
    if (kBit / 64 >= whole.nwords) return;
    const uint64_t kMask = uint64_t{1} << (kBit % 64);
    const bool kA = k < 64 && ((aval >> k) & 1) != 0;
    const bool kB = k < 64 && ((bval >> k) & 1) != 0;
    Logic4Word& word = whole.words[kBit / 64];
    word.aval = (word.aval & ~kMask) | (kA ? kMask : 0);
    word.bval = (word.bval & ~kMask) | (kB ? kMask : 0);
  }
}

// §38.34: stores the supplied scalar/integer/real value into the target
// variable's first four-state word, or a bit or slice's bits of its parent.
// Formats with no direct word encoding here (e.g. string/vector) are left for
// the caller's other paths and are ignored.
static void PutValueWriteWord(VpiHandle obj, const s_vpi_value* value) {
  if (obj->bit_offset >= 0) {
    PutValueWriteSlice(obj, value);
    return;
  }
  if (value->format == kVpiIntVal) {
    auto new_val = static_cast<uint64_t>(value->value.integer);
    obj->var->value.words[0].aval = new_val;
    obj->var->value.words[0].bval = 0;
  } else if (value->format == kVpiRealVal) {
    auto new_val = static_cast<uint64_t>(value->value.real);
    obj->var->value.words[0].aval = new_val;
    obj->var->value.words[0].bval = 0;
  } else if (value->format == kVpiScalarVal) {
    int s = value->value.scalar;
    // Canonical encoding: x=(aval=1,bval=1), z=(aval=0,bval=1).
    obj->var->value.words[0].aval = (s == kVpi1 || s == kVpiX) ? 1 : 0;
    obj->var->value.words[0].bval = (s == kVpiX || s == kVpiZ) ? 1 : 0;
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

  PutValueWriteWord(obj, value);

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
// varying bit (§37.16, §37.17) the bit its index selects, and for a varying
// select leaving packed dimensions unindexed a slice, made through `alloc`, of
// the bits its index names; null when it names none and nothing is written
// (§11.5.1).
static VpiHandle PutValueTargetOf(VpiHandle obj,
                                  const std::function<VpiObject*()>& alloc) {
  if (!IsVaryingBit(*obj)) return obj;
  if (!obj->select_dim || obj->size <= 1) return VaryingBitTarget(obj);
  // A varying select leaving packed dimensions unindexed stands for the bits
  // its index names when the value is put, made a slice of them here.
  const std::optional<int64_t> kOffset = VaryingOffset(obj);
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

VpiHandle VpiContext::PutValue(VpiHandle obj, s_vpi_value* value,
                               s_vpi_time* time, int flags) {
  if (!obj) return nullptr;
  if (PutValueIsSealed(*obj, last_error_)) return nullptr;

  if (PutValueTargetIsRejected(obj, last_error_)) return nullptr;

  // §38.34: vpiReturnEvent is an independent bit mask layered on top of the
  // delay-mode selector that lives in the low bits of the flags word.
  bool return_event = (flags & vpiReturnEvent) != 0;
  int mode = flags & ~vpiReturnEvent;

  // §38.34: vpiCancelEvent removes a previously scheduled event. The object
  // must be a vpiSchedEvent handle, and value_p and time_p are not needed. It
  // is not an error to cancel an event that has already occurred, so a handle
  // that is no longer scheduled is simply left alone. Cancelling removes the
  // event from the queue; the handle itself remains for the caller to free.
  if (mode == vpiCancelEvent) {
    if (obj->type == vpiSchedEvent) obj->scheduled = false;
    return nullptr;
  }

  obj = PutValueTargetOf(obj, [this] { return AllocObject(); });
  if (obj == nullptr) return nullptr;

  bool has_delay = PutValueHasDelay(mode, time);

  if (PutValueDelayModeIsRejected(obj, mode, has_delay, last_error_)) {
    return nullptr;
  }

  if (PutValueResolveWritableTarget(obj, scheduler_)) return nullptr;

  if (!value) return nullptr;

  if (PutValueFormatIsRejected(obj, value, last_error_)) return nullptr;

  // §38.34: vpiReleaseFlag releases a forced value, the same operation as the
  // procedural release of §10.6.2, and writes the object's post-release value
  // back through value_p so the caller can observe what the object settled to.
  if (mode == vpiReleaseFlag) {
    obj->var->is_forced = false;
    GetValue(obj, value);
    return nullptr;
  }

  PutValueApplyWriteAndForce(obj, value, mode, scheduler_);
  if (!has_delay) VpiStoreElementCopy(*obj);

  // §38.34: a handle to the scheduled event is returned only when
  // vpiReturnEvent was requested and a delay actually scheduled an event; in
  // every other case (no bit mask, no delay, or nothing scheduled) the return
  // value is NULL.
  if (return_event && has_delay) {
    auto* ev = AllocObject();
    ev->type = vpiSchedEvent;
    ev->scheduled = true;
    return ev;
  }
  return nullptr;
}

// §38.35: the value formats vpi_put_value_array() accepts. The int/vector/time/
// real forms are the vpi_get_value() formats reused from §38.15 (Table 38-3);
// the raw aval/bval forms and the short/long/short-real C-scalar forms are the
// additions §38.35 defines. Any other format is unsupported.
}  // namespace delta
