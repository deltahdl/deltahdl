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

namespace delta {

static bool VpiArrayPutFormatSupported(int format) {
  switch (format) {
    case kVpiIntVal:
    case kVpiVectorVal:
    case kVpiTimeVal:
    case kVpiRealVal:
    case kVpiShortIntVal:
    case kVpiLongIntVal:
    case kVpiShortRealVal:
    case kVpiRawTwoStateVal:
    case kVpiRawFourStateVal:
      return true;
    default:
      return false;
  }
}

// §38.35: read up to eight little-endian bytes of one raw aval (or bval) group
// into a 64-bit word. ngroups is (elemBits + 7)/8; the LSB of byte 0 is bit 0
// of the element, the significance order the standard fixes for the avalbits
// and bvalbits arrays.
static uint64_t VpiReadRawGroup(const char* base, int ngroups) {
  uint64_t v = 0;
  for (int b = 0; b < ngroups && b < 8; ++b) {
    v |= static_cast<uint64_t>(static_cast<unsigned char>(base[b])) << (8 * b);
  }
  return v;
}

// §38.16: store the low ngroups bytes of a 64-bit word into one raw aval (or
// bval) group, least-significant byte first - the inverse of VpiReadRawGroup
// and the same byte significance order the standard fixes for
// vpi_put_value_array (§38.35). Any group bytes beyond the eight a word can
// supply are left zero.
static void VpiWriteRawGroup(char* base, int ngroups, uint64_t v) {
  for (int b = 0; b < ngroups; ++b) {
    base[b] = (b < 8) ? static_cast<char>((v >> (8 * b)) & 0xFF) : 0;
  }
}

// §38.16/§38.35: turn a starting coordinate into the flat ordinal of the first
// element, with the rightmost dimension varying fastest - a mixed-radix value
// over each dimension's declared index order (dims[d] lists the declared
// indices of unpacked dimension d, index_p[d] the requested coordinate). A
// coordinate value that names no declared index is not a legal element
// reference: returns false (out of range) and leaves *out_ordinal unset.
static bool ComputeStartOrdinal(const std::vector<std::vector<int>>& dims,
                                const int* index_p, long long* out_ordinal) {
  long long start_ordinal = 0;
  for (size_t d = 0; d < dims.size(); ++d) {
    const auto& order = dims[d];
    long long pos = -1;
    for (size_t p = 0; p < order.size(); ++p) {
      if (order[p] == index_p[d]) {
        pos = static_cast<long long>(p);
        break;
      }
    }
    if (pos < 0) {
      return false;
    }
    start_ordinal = start_ordinal * static_cast<long long>(order.size()) + pos;
  }
  *out_ordinal = start_ordinal;
  return true;
}

void VpiContext::PutValueArray(VpiHandle obj, VpiArrayValue* arrayvalue_p,
                               int* index_p, unsigned int num) {
  if (!obj || !arrayvalue_p) return;

  // §38.35: the routine modifies only static unpacked variable or net arrays -
  // arrays whose vpiArrayType is vpiStaticArray, which also have a static
  // lifetime and contain no dynamic array or dynamic element. A handle that is
  // not such an array has no element section to fill, so the call is rejected
  // and the error recorded (§38.2).
  bool is_unpacked_array =
      VpiIsArrayVarType(obj->type) || obj->type == vpiNetArray;
  if (!is_unpacked_array || obj->array_type != vpiStaticArray) {
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message =
        "vpi_put_value_array() requires a static unpacked array object";
    return;
  }

  // §38.35: vpiNoDelay is the only scheduling mode allowed here - the delay and
  // event modes of vpi_put_value() (§38.34) are not available. Only vpiOneValue
  // and vpiPropagateOff may accompany it (vpiNoDelay is the default, value 0 in
  // the flags word); any other flag bit is an error.
  const unsigned int kAllowed = kVpiOneValue | kVpiPropagateOff;
  if (arrayvalue_p->flags & ~kAllowed) {
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message =
        "vpi_put_value_array() allows only the vpiOneValue and vpiPropagateOff "
        "flags";
    return;
  }

  // §38.35: every format outside the supported set is unsupported and is an
  // error if specified.
  if (!VpiArrayPutFormatSupported(static_cast<int>(arrayvalue_p->format))) {
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message =
        "vpi_put_value_array() was given an unsupported value format";
    return;
  }

  // §38.35: index_p carries the starting element's coordinate, one entry per
  // unpacked dimension of obj, ordered left to right as the indices appear in
  // an HDL reference. With no coordinate there is no element to start from.
  const auto& dims = obj->array_dim_indices;
  if (index_p == nullptr || dims.empty()) {
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message =
        "vpi_put_value_array() requires a starting index for each unpacked "
        "dimension";
    return;
  }

  // §38.35: turn the starting coordinate into the flat ordinal of the first
  // element. A coordinate value that names no declared index is not a legal
  // element reference.
  long long start_ordinal = 0;
  if (!ComputeStartOrdinal(dims, index_p, &start_ordinal)) {
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message =
        "vpi_put_value_array() starting index is out of range";
    return;
  }

  // §38.35: elements are filled consecutively in fastest-varying-index order,
  // which is exactly consecutive flat ordinals from the starting element. With
  // vpiOneValue the single supplied element value is applied to the whole
  // section, so the source position stays pinned at 0.
  bool one_value = (arrayvalue_p->flags & kVpiOneValue) != 0;
  for (unsigned int k = 0; k < num; ++k) {
    long long ordinal = start_ordinal + static_cast<long long>(k);
    VpiObject* element = nullptr;
    for (auto* child : obj->children) {
      if (child->index == ordinal) {
        element = child;
        break;
      }
    }
    if (!element || !element->var) continue;

    unsigned int src = one_value ? 0u : k;
    Logic4Vec& ev = element->var->value;
    uint32_t width = ev.width;
    uint64_t mask = (width >= 64) ? ~uint64_t{0} : ((uint64_t{1} << width) - 1);
    bool elem_4state = element->var->is_4state;
    uint64_t aval = 0;
    uint64_t bval = 0;

    switch (static_cast<int>(arrayvalue_p->format)) {
      case kVpiIntVal:
        aval = static_cast<uint64_t>(
            static_cast<uint32_t>(arrayvalue_p->value.integers[src]));
        break;
      case kVpiShortIntVal:
        aval = static_cast<uint64_t>(
            static_cast<uint16_t>(arrayvalue_p->value.shortints[src]));
        break;
      case kVpiLongIntVal:
        aval = static_cast<uint64_t>(arrayvalue_p->value.longints[src]);
        break;
      case kVpiRealVal:
        aval = static_cast<uint64_t>(arrayvalue_p->value.reals[src]);
        break;
      case kVpiShortRealVal:
        aval = static_cast<uint64_t>(arrayvalue_p->value.shortreals[src]);
        break;
      case kVpiTimeVal: {
        const VpiTime& t = arrayvalue_p->value.times[src];
        aval = (static_cast<uint64_t>(t.high) << 32) | t.low;
        break;
      }
      case kVpiVectorVal: {
        const VpiVectorVal& vv = arrayvalue_p->value.vectors[src];
        aval = vv.aval;
        bval = elem_4state ? vv.bval : 0;
        break;
      }
      case kVpiRawFourStateVal: {
        int ngroups = (static_cast<int>(width) + 7) / 8;
        const char* abase = arrayvalue_p->value.rawvals +
                            static_cast<size_t>(src) * ngroups * 2;
        aval = VpiReadRawGroup(abase, ngroups);
        // §38.35: when this 4-state format is used for a 2-state array, the
        // bvalbits group is ignored.
        bval = elem_4state ? VpiReadRawGroup(abase + ngroups, ngroups) : 0;
        break;
      }
      case kVpiRawTwoStateVal: {
        int ngroups = (static_cast<int>(width) + 7) / 8;
        const char* abase =
            arrayvalue_p->value.rawvals + static_cast<size_t>(src) * ngroups;
        aval = VpiReadRawGroup(abase, ngroups);
        // §38.35: this 2-state format carries no bvalbits; for a 4-state array
        // its bval bits are taken to be 0.
        bval = 0;
        break;
      }
      default:
        break;
    }

    if (ev.nwords > 0) {
      ev.words[0].aval = aval & mask;
      ev.words[0].bval = bval & mask;
    }
  }

  // §38.35: for a vpiArrayNet target the written values override the resolved
  // values of the named net elements and stay in effect until one of that
  // element's drivers next changes, when normal net resolution resumes. The
  // override is the write applied above; the re-resolution is a property of the
  // net solver, outside this routine. vpiPropagateOff, when set, suppresses
  // fanout notification of the change.
}

void VpiContext::GetValueArray(VpiHandle obj, VpiArrayValue* arrayvalue_p,
                               int* index_p, unsigned int num) {
  if (!obj || !arrayvalue_p) return;

  // §38.16: on any failure the value arm is set to NULL, which is how the
  // routine signals a VPI error to the application (the value pointer
  // overwritten to NULL). Setting the rawvals arm clears the whole union, since
  // every arm aliases the same storage.
  auto fail = [&](const char* msg) {
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message = msg;
    arrayvalue_p->value.rawvals = nullptr;
  };

  // §38.16: the routine retrieves values only from static unpacked variable or
  // net arrays - arrays whose vpiArrayType is vpiStaticArray, with static
  // lifetimes and no dynamic array or dynamic element. Anything else has no
  // element section to read.
  bool is_unpacked_array =
      VpiIsArrayVarType(obj->type) || obj->type == vpiNetArray;
  if (!is_unpacked_array || obj->array_type != vpiStaticArray) {
    fail("vpi_get_value_array() requires a static unpacked array object");
    return;
  }

  // §38.16: every format outside the supported set is unsupported and is an
  // error if requested. The supported set is the vpi_get_value() formats reused
  // from §38.15 plus the raw/short/long/short-real additions.
  if (!VpiArrayPutFormatSupported(static_cast<int>(arrayvalue_p->format))) {
    fail("vpi_get_value_array() was given an unsupported value format");
    return;
  }

  // §38.16: index_p carries the starting element's coordinate, one entry per
  // unpacked dimension of obj, ordered left to right as the indices appear in
  // an HDL reference. Without a coordinate there is no element to start from.
  const auto& dims = obj->array_dim_indices;
  if (index_p == nullptr || dims.empty()) {
    fail(
        "vpi_get_value_array() requires a starting index for each unpacked "
        "dimension");
    return;
  }

  // §38.16: turn the starting coordinate into the flat ordinal of the first
  // element. A coordinate naming no declared index is not a legal element
  // reference.
  long long start_ordinal = 0;
  if (!ComputeStartOrdinal(dims, index_p, &start_ordinal)) {
    fail("vpi_get_value_array() starting index is out of range");
    return;
  }

  // §38.16: locate the section's element children up front, in fastest-varying
  // order (consecutive flat ordinals from the start). The element width fixes
  // the raw-group and vector word counts and the size of any VPI-owned buffer.
  std::vector<VpiObject*> section(num, nullptr);
  for (auto* child : obj->children) {
    long long rel = static_cast<long long>(child->index) - start_ordinal;
    if (rel >= 0 && rel < static_cast<long long>(num)) {
      section[static_cast<size_t>(rel)] = child;
    }
  }
  uint32_t width = 0;
  for (auto* el : section) {
    if (el && el->var) {
      width = el->var->value.width;
      break;
    }
  }
  int ngroups = (static_cast<int>(width) + 7) / 8;
  int words_per_elem = (static_cast<int>(width) + 31) / 32;
  int fmt = static_cast<int>(arrayvalue_p->format);

  // §38.16: by default the values are returned in VPI-allocated storage
  // (treated as read-only by the caller); with vpiUserAllocFlag the caller has
  // already pointed the value arm at a buffer of sufficient size. In the
  // default case size the buffer per the format: the raw formats follow their
  // byte-group instructions, the others are num entries of the arm's element
  // type.
  bool user_alloc = (arrayvalue_p->flags & kVpiUserAllocFlag) != 0;
  if (!user_alloc) {
    size_t bytes = 0;
    switch (fmt) {
      case kVpiRawFourStateVal:
        bytes = static_cast<size_t>(ngroups) * 2 * num;
        break;
      case kVpiRawTwoStateVal:
        bytes = static_cast<size_t>(ngroups) * num;
        break;
      case kVpiShortIntVal:
        bytes = sizeof(int16_t) * num;
        break;
      case kVpiLongIntVal:
        bytes = sizeof(int64_t) * num;
        break;
      case kVpiShortRealVal:
        bytes = sizeof(float) * num;
        break;
      case kVpiRealVal:
        bytes = sizeof(double) * num;
        break;
      case kVpiTimeVal:
        bytes = sizeof(VpiTime) * num;
        break;
      case kVpiVectorVal:
        bytes =
            sizeof(VpiVectorVal) * static_cast<size_t>(words_per_elem) * num;
        break;
      case kVpiIntVal:
      default:
        bytes = sizeof(int32_t) * num;
        break;
    }
    value_array_storage_.assign(bytes, 0);
    arrayvalue_p->value.rawvals =
        reinterpret_cast<char*>(value_array_storage_.data());
  }

  // §38.16: fill the section consecutively in fastest-varying-index order,
  // encoding each element's current value into the arm the format selects. The
  // raw and vector formats lay the element bits out per their byte/word group
  // descriptions; the scalar arms widen the element value into one C scalar.
  for (unsigned int k = 0; k < num; ++k) {
    VpiObject* element = section[k];
    uint64_t aval = 0;
    uint64_t bval = 0;
    bool elem_4state = false;
    if (element && element->var) {
      const Logic4Vec& ev = element->var->value;
      if (ev.nwords > 0) {
        aval = ev.words[0].aval;
        bval = ev.words[0].bval;
      }
      elem_4state = element->var->is_4state;
    }

    switch (fmt) {
      case kVpiIntVal:
        arrayvalue_p->value.integers[k] = static_cast<int32_t>(aval);
        break;
      case kVpiShortIntVal:
        arrayvalue_p->value.shortints[k] = static_cast<int16_t>(aval);
        break;
      case kVpiLongIntVal:
        arrayvalue_p->value.longints[k] = static_cast<int64_t>(aval);
        break;
      case kVpiRealVal:
        arrayvalue_p->value.reals[k] = static_cast<double>(aval);
        break;
      case kVpiShortRealVal:
        arrayvalue_p->value.shortreals[k] = static_cast<float>(aval);
        break;
      case kVpiTimeVal:
        arrayvalue_p->value.times[k].high = static_cast<uint32_t>(aval >> 32);
        arrayvalue_p->value.times[k].low =
            static_cast<uint32_t>(aval & 0xFFFFFFFFu);
        break;
      case kVpiVectorVal:
        arrayvalue_p->value.vectors[k].aval = static_cast<uint32_t>(aval);
        // §38.16: bvalbits carry the unknown/high-impedance state for a 4-state
        // element; a 2-state element reports a known (bval 0) value.
        arrayvalue_p->value.vectors[k].bval =
            elem_4state ? static_cast<uint32_t>(bval) : 0;
        break;
      case kVpiRawFourStateVal: {
        // §38.16: each element occupies ngroups*2 bytes - an aval group
        // followed by a bval group - loaded least-significant byte first.
        char* abase =
            arrayvalue_p->value.rawvals + static_cast<size_t>(k) * ngroups * 2;
        VpiWriteRawGroup(abase, ngroups, aval);
        VpiWriteRawGroup(abase + ngroups, ngroups, elem_4state ? bval : 0);
        break;
      }
      case kVpiRawTwoStateVal: {
        // §38.16: the 2-state raw format omits the bval group, so each element
        // occupies just ngroups bytes.
        char* abase =
            arrayvalue_p->value.rawvals + static_cast<size_t>(k) * ngroups;
        VpiWriteRawGroup(abase, ngroups, aval);
        break;
      }
      default:
        break;
    }
  }
}

}  // namespace delta
