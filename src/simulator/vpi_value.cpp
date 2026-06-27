#include <algorithm>
#include <cctype>
#include <cmath>
#include <cstdarg>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <string>
#include <string_view>
#include <vector>

#include "common/types.h"
#include "simulator/dpi.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"
// §37.10 detail 3: the package/interface/program instance kinds are defined in
// the SystemVerilog VPI header alongside the §37.10 vpiInstance relation.
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"
#include "simulator/vpi_internal.h"

namespace delta {

static void GetValueBinStr(VpiHandle obj, VpiValue* value,
                           std::vector<std::string>& pool) {
  uint64_t aval = obj->var->value.words[0].aval;
  uint64_t bval = obj->var->value.words[0].bval;
  int width = static_cast<int>(obj->var->value.width);
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
  value->value.str = pool.back().c_str();
}

static char HexDigitFromBits(uint8_t nibble) {
  if (nibble < 10) return static_cast<char>('0' + nibble);
  return static_cast<char>('a' + nibble - 10);
}

static void GetValueHexStr(VpiHandle obj, VpiValue* value,
                           std::vector<std::string>& pool) {
  uint64_t aval = obj->var->value.words[0].aval;
  uint64_t bval = obj->var->value.words[0].bval;
  int width = static_cast<int>(obj->var->value.width);
  int hex_digits = (width + 3) / 4;
  std::string result;
  result.reserve(hex_digits);
  for (int i = hex_digits - 1; i >= 0; --i) {
    uint8_t a_nibble = (aval >> (i * 4)) & 0xF;
    uint8_t b_nibble = (bval >> (i * 4)) & 0xF;
    if (b_nibble != 0) {
      result += (b_nibble == 0xF && a_nibble == 0xF) ? 'x' : 'z';
    } else {
      result += HexDigitFromBits(a_nibble);
    }
  }
  pool.push_back(std::move(result));
  value->value.str = pool.back().c_str();
}

static void GetValueOctStr(VpiHandle obj, VpiValue* value,
                           std::vector<std::string>& pool) {
  uint64_t aval = obj->var->value.words[0].aval;
  uint64_t bval = obj->var->value.words[0].bval;
  int width = static_cast<int>(obj->var->value.width);
  int oct_digits = (width + 2) / 3;
  std::string result;
  result.reserve(oct_digits);
  for (int i = oct_digits - 1; i >= 0; --i) {
    uint8_t a_bits = (aval >> (i * 3)) & 0x7;
    uint8_t b_bits = (bval >> (i * 3)) & 0x7;
    if (b_bits != 0) {
      // §38.15, Table 38-3 (octal row): a digit covering any unknown bit is
      // reported as x only when the whole group is x, otherwise as z. Under the
      // canonical encoding (Figure 38-8) x=(1,1), so an all-x group is a=0x7.
      result += (b_bits == 0x7 && a_bits == 0x7) ? 'x' : 'z';
    } else {
      result += static_cast<char>('0' + a_bits);
    }
  }
  pool.push_back(std::move(result));
  value->value.str = pool.back().c_str();
}

static int ScalarFromBits(uint64_t aval, uint64_t bval) {
  if (!bval) return aval ? kVpi1 : kVpi0;
  return aval ? kVpiX : kVpiZ;  // x=(1,1), z=(0,1)
}

static void GetValueVector(VpiHandle obj, VpiValue* value,
                           std::vector<std::vector<VpiVectorVal>>& pool) {
  const auto& v = obj->var->value;
  int width = static_cast<int>(v.width);
  // §38.15: the vector value occupies an array of s_vpi_vecval whose size is
  // ((vector_size - 1) / 32 + 1), one element per 32 bits of the vector.
  int array_size = width > 0 ? ((width - 1) / 32 + 1) : 1;
  std::vector<VpiVectorVal> vec(static_cast<size_t>(array_size));
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

static void GetValueStrength(VpiHandle obj, VpiValue* value,
                             std::vector<std::vector<VpiStrengthVal>>& pool) {
  const auto& v = obj->var->value;
  int width = static_cast<int>(v.width);
  if (width < 1) width = 1;
  // §38.15: the strength arm holds one descriptor per bit of the vector.
  std::vector<VpiStrengthVal> arr(static_cast<size_t>(width));
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

static void GetValueStringVal(VpiHandle obj, VpiValue* value,
                              std::vector<std::string>& pool) {
  uint64_t val = obj->var->value.ToUint64();
  std::string s;
  for (int i = 56; i >= 0; i -= 8) {
    auto ch = static_cast<char>((val >> i) & 0xFF);
    if (ch != 0) s += ch;
  }
  pool.push_back(std::move(s));
  value->value.str = pool.back().c_str();
}

static void GetValueIntVal(VpiHandle obj, VpiValue* value) {
  // §38.15, Table 38-3: any x or z bit of the object maps to a 0 in the
  // returned integer, so drop every unknown bit before handing it back.
  uint64_t aval = obj->var->value.words[0].aval;
  uint64_t bval = obj->var->value.words[0].bval;
  value->value.integer = static_cast<int>(aval & ~bval);
}

static void GetValueObjType(VpiHandle obj, VpiValue* value,
                            std::vector<std::vector<VpiVectorVal>>& pool) {
  // §38.15: fill in the value and rewrite the format field to the closest
  // format for the object's type. A real object reports vpiRealVal, a
  // single-bit object is a scalar, and anything wider is a vector.
  const auto& v = obj->var->value;
  if (v.is_real) {
    value->format = kVpiRealVal;
    value->value.real = static_cast<double>(v.ToUint64());
  } else if (v.width == 1) {
    value->format = kVpiScalarVal;
    value->value.scalar =
        ScalarFromBits(v.words[0].aval & 1, v.words[0].bval & 1);
  } else {
    value->format = kVpiVectorVal;
    GetValueVector(obj, value, pool);
  }
}

// ===========================================================================
// §37.3.4 Delays and values.
// ===========================================================================

bool VpiObjectCarriesSourceDelay(int type) {
  // §37.3.4: the object kinds that can carry a delay written within the
  // SystemVerilog source - nets, primitives, module paths, timing checks, and
  // continuous assignments. "Primitive" covers the gate, switch, and udp forms
  // as well as the primitive supertype. Other delays (module input port delays,
  // inter-module path delays) do not appear in the source and so are excluded.
  switch (type) {
    case vpiNet:
    case vpiPrimitive:
    case vpiGate:
    case vpiSwitch:
    case vpiUdp:
    case vpiModPath:
    case vpiTchk:
    case vpiContAssign:
      return true;
    default:
      return false;
  }
}

VpiHandle VpiSourceDelayExpr(VpiHandle obj) {
  // §37.3.4: the vpiDelay relation reaches the source-specified delay
  // expression of a delay-carrying object. It is a designated expression, not a
  // child found by type (a single delay is a plain constant-valued expression),
  // so it is held on the object directly. Null when the handle is null, is not
  // a delay-carrying kind, or carries no source delay.
  if (!obj) return nullptr;
  if (!VpiObjectCarriesSourceDelay(obj->type)) return nullptr;
  return obj->delay_expr;
}

bool VpiSourceDelayExprIsListOp(VpiHandle expr) {
  // §37.3.4: when more than one delay is specified the vpiDelay expression
  // shall be an operation whose vpiOpType is vpiListOp; a single delay is a
  // plain constant-valued expression instead. This holds iff the expression is
  // that operation form.
  return expr && expr->type == vpiOperation && expr->op_type == vpiListOp;
}

bool VpiExpressionHasSideEffects(const VpiObject* obj) {
  // §37.3.5: the mark records the classification described in the subclause; an
  // absent object cannot have side effects.
  return obj && obj->has_side_effects;
}

static void RecordVpiError(VpiErrorInfo& error, const char* message) {
  error.state = kVpiError;
  error.level = kVpiError;
  error.message = message;
}

// Applies the §37.31/§37.26/§37.36 read-side restrictions. Returns true (with
// last_error recorded) when the read must be refused and the value buffer left
// untouched.
static bool GetValueIsRefused(VpiHandle obj, VpiValue* value,
                              VpiErrorInfo& error) {
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

static void DispatchGetValueByFormat(
    VpiHandle obj, VpiValue* value, std::vector<std::string>& str_pool,
    std::vector<std::vector<VpiVectorVal>>& vec_pool,
    std::vector<std::vector<VpiStrengthVal>>& strength_pool) {
  // §38.15, Table 38-3: fill the value buffer according to the requested
  // format. Each arm is the format-specific conversion; most delegate to a
  // dedicated helper, while the scalar/real/time arms are short inline reads.
  switch (value->format) {
    case kVpiIntVal:
      GetValueIntVal(obj, value);
      break;
    case kVpiRealVal:
      value->value.real = static_cast<double>(obj->var->value.ToUint64());
      break;
    case kVpiScalarVal:
      value->value.scalar = ScalarFromBits(obj->var->value.words[0].aval & 1,
                                           obj->var->value.words[0].bval & 1);
      break;
    case kVpiBinStrVal:
      GetValueBinStr(obj, value, str_pool);
      break;
    case kVpiHexStrVal:
      GetValueHexStr(obj, value, str_pool);
      break;
    case kVpiOctStrVal:
      GetValueOctStr(obj, value, str_pool);
      break;
    case kVpiStringVal:
      GetValueStringVal(obj, value, str_pool);
      break;
    case kVpiTimeVal:
      value->value.integer = static_cast<int>(obj->var->value.ToUint64());
      break;
    case kVpiVectorVal:
      GetValueVector(obj, value, vec_pool);
      break;
    case kVpiStrengthVal:
      GetValueStrength(obj, value, strength_pool);
      break;
    case kVpiObjTypeVal:
      GetValueObjType(obj, value, vec_pool);
      break;
    default:
      break;
  }
}

void VpiContext::GetValue(VpiHandle obj, VpiValue* value) {
  if (!obj || !value) return;
  // §37.3.5: applying vpi_get_value() to an expression with side effects shall
  // fully evaluate the expression together with its side effects. Reading the
  // value performs that evaluation, so record that the side effect occurred
  // before the value is handed back below - the count is the observable
  // evidence that evaluation, and thus the embedded state change, took place.
  if (VpiExpressionHasSideEffects(obj)) {
    ++obj->side_effect_count;
  }
  if (GetValueIsRefused(obj, value, last_error_)) return;
  if (!obj->var) return;
  DispatchGetValueByFormat(obj, value, str_pool_, vec_pool_, strength_pool_);
}

// Applies the §37.31/§37.26/§37.35/§37.3.5 target-kind restrictions that hold
// regardless of the requested delay mode. Returns true (with error recorded)
// when the put must be refused and the target left unchanged.
static bool PutValueTargetIsRejected(VpiHandle obj, VpiErrorInfo& error) {
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
static bool PutValueFormatIsRejected(VpiHandle obj, const VpiValue* value,
                                     VpiErrorInfo& error) {
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

// §38.34: stores the supplied scalar/integer/real value into the target
// variable's first four-state word. Formats with no direct word encoding here
// (e.g. string/vector) are left for the caller's other paths and are ignored.
static void PutValueWriteWord(VpiHandle obj, const VpiValue* value) {
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
static void PutValueApplyWriteAndForce(VpiHandle obj, const VpiValue* value,
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
static bool PutValueHasDelay(int mode, const VpiTime* time) {
  bool immediate =
      (mode == vpiNoDelay || mode == vpiForceFlag || mode == vpiReleaseFlag);
  return !immediate && time &&
         (time->low != 0 || time->high != 0 || time->real != 0.0);
}

// Applies the §38.34/§37.43 delay-mode restrictions (sequential UDP must be
// written with vpiNoDelay; no delayed put on an automatic variable). Returns
// true (with error recorded) when the put must be refused.
static bool PutValueDelayModeIsRejected(VpiHandle obj, int mode, bool has_delay,
                                        VpiErrorInfo& error) {
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

VpiHandle VpiContext::PutValue(VpiHandle obj, VpiValue* value, VpiTime* time,
                               int flags) {
  if (!obj) return nullptr;

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
