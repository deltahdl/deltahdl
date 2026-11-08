#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <vector>

#include "common/types.h"
#include "simulator/evaluation.h"
#include "simulator/net.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"
#include "simulator/vpi_value_numbers.h"

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

namespace {

uint64_t PieceOf(const Logic4Word* words, bool bval, uint32_t piece,
                 uint32_t bits) {
  const uint32_t kBit = piece * bits;
  const Logic4Word& word = words[kBit / 64];
  return ((bval ? word.bval : word.aval) >> (kBit % 64)) &
         ((uint64_t{1} << bits) - 1);
}

void SetPiece(Logic4Word* words, bool bval, uint32_t piece, uint32_t bits,
              uint64_t v) {
  const uint32_t kBit = piece * bits;
  Logic4Word& word = words[kBit / 64];
  (bval ? word.bval : word.aval) |= (v & ((uint64_t{1} << bits) - 1))
                                    << (kBit % 64);
}

struct ElementWords {
  const Logic4Word* words = nullptr;
  bool is_4state = false;
  const Variable* var = nullptr;
  bool is_real = false;
};

bool IsRealElement(const VpiObject& element) {
  return element.type == vpiRealVar || element.type == vpiShortRealVar;
}

bool RecordArrayError(s_vpi_error_info* err, const char* msg) {
  err->state = kVpiError;
  err->level = kVpiError;
  err->message = VpiText(msg);
  return false;
}

bool HoldsDynamicElements(const VpiObject& obj);

bool ValidatePutValueArrayRequest(VpiHandle obj, s_vpi_arrayvalue* arrayvalue_p,
                                  int* index_p, long long* out_start_ordinal,
                                  s_vpi_error_info* err) {
  if (VpiWriteSealed(*obj)) {
    return RecordArrayError(
        err, "vpi_put_value_array() on a protected object is an error");
  }
  bool is_unpacked_array =
      VpiIsArrayVarType(obj->type) || obj->type == vpiNetArray;
  if (!is_unpacked_array || obj->array_type != vpiStaticArray) {
    return RecordArrayError(
        err, "vpi_put_value_array() requires a static unpacked array object");
  }
  if (HoldsDynamicElements(*obj)) {
    return RecordArrayError(
        err,
        "vpi_put_value_array() does not take an array of dynamic elements such "
        "as strings");
  }

  const unsigned int kAllowed = kVpiOneValue | kVpiPropagateOff;
  if (arrayvalue_p->flags & ~kAllowed) {
    return RecordArrayError(
        err,
        "vpi_put_value_array() allows only the vpiOneValue and vpiPropagateOff "
        "flags");
  }

  if (!VpiArrayPutFormatSupported(static_cast<int>(arrayvalue_p->format))) {
    return RecordArrayError(
        err, "vpi_put_value_array() was given an unsupported value format");
  }

  const auto& dims = obj->array_dim_indices;
  if (index_p == nullptr || dims.empty()) {
    return RecordArrayError(
        err,
        "vpi_put_value_array() requires a starting index for each unpacked "
        "dimension");
  }

  if (!ComputeStartOrdinal(dims, index_p, out_start_ordinal)) {
    return RecordArrayError(
        err, "vpi_put_value_array() starting index is out of range");
  }
  return true;
}

uint64_t RealElementBits(double value, uint32_t width) {
  if (width == 32) {
    const auto kSingle = static_cast<float>(value);
    uint32_t bits = 0;
    std::memcpy(&bits, &kSingle, sizeof(bits));
    return bits;
  }
  uint64_t bits = 0;
  std::memcpy(&bits, &value, sizeof(bits));
  return bits;
}

uint64_t DecodePutScalarAval(const s_vpi_arrayvalue* arrayvalue_p,
                             unsigned int src, int fmt, Logic4Vec& ev,
                             bool real_element) {
  double real = 0.0;
  switch (fmt) {
    case kVpiShortIntVal:
      return static_cast<uint64_t>(
          static_cast<int64_t>(arrayvalue_p->value.shortints[src]));
    case kVpiLongIntVal:
      return static_cast<uint64_t>(arrayvalue_p->value.longints[src]);
    case kVpiRealVal:
      real = arrayvalue_p->value.reals[src];
      break;
    case kVpiShortRealVal:
      real = arrayvalue_p->value.shortreals[src];
      break;
    default:
      return static_cast<uint64_t>(
          static_cast<int64_t>(arrayvalue_p->value.integers[src]));
  }
  if (real_element) {
    ev.is_real = true;
    return RealElementBits(real, ev.width);
  }
  return static_cast<uint64_t>(static_cast<int64_t>(real));
}

uint64_t DecodePutTimeAval(const s_vpi_arrayvalue* arrayvalue_p,
                           unsigned int src) {
  const s_vpi_time& t = arrayvalue_p->value.times[src];
  return (static_cast<uint64_t>(t.high) << 32) | t.low;
}

void DecodePutVectorValue(const s_vpi_arrayvalue* arrayvalue_p,
                          unsigned int src, Logic4Vec& ev, bool is_4state) {
  const uint32_t kWords = (ev.width + 31) / 32;
  const s_vpi_vecval* vecs =
      arrayvalue_p->value.vectors + static_cast<size_t>(src) * kWords;
  for (uint32_t w = 0; w < kWords; ++w) {
    SetPiece(ev.words, false, w, 32, vecs[w].aval);
    if (is_4state) SetPiece(ev.words, true, w, 32, vecs[w].bval);
  }
}

void DecodePutRaw(const s_vpi_arrayvalue* arrayvalue_p, unsigned int src,
                  Logic4Vec& ev, bool is_4state) {
  const bool kFourStateFormat =
      static_cast<int>(arrayvalue_p->format) == kVpiRawFourStateVal;
  const uint32_t kGroups = (ev.width + 7) / 8;
  const char* abase =
      arrayvalue_p->value.rawvals +
      static_cast<size_t>(src) * kGroups * (kFourStateFormat ? 2 : 1);
  for (uint32_t b = 0; b < kGroups; ++b) {
    SetPiece(ev.words, false, b, 8, static_cast<unsigned char>(abase[b]));
    if (kFourStateFormat && is_4state) {
      SetPiece(ev.words, true, b, 8,
               static_cast<unsigned char>(abase[kGroups + b]));
    }
  }
}

void DecodePutSourceValue(const s_vpi_arrayvalue* arrayvalue_p,
                          unsigned int src, Logic4Vec& ev, bool is_4state,
                          bool real_element) {
  int fmt = static_cast<int>(arrayvalue_p->format);
  switch (fmt) {
    case kVpiTimeVal:
      ev.words[0].aval = DecodePutTimeAval(arrayvalue_p, src);
      break;
    case kVpiVectorVal:
      DecodePutVectorValue(arrayvalue_p, src, ev, is_4state);
      break;
    case kVpiRawFourStateVal:
    case kVpiRawTwoStateVal:
      DecodePutRaw(arrayvalue_p, src, ev, is_4state);
      break;
    default:
      ev.words[0].aval =
          DecodePutScalarAval(arrayvalue_p, src, fmt, ev, real_element);
      break;
  }
}

bool IsArrayElement(const VpiObject& child) {
  return child.type != vpiRange && child.type != vpiConstant &&
         !VpiIsTypespecType(child.type);
}

void AppendElementsInOrder(const VpiObject& obj, std::vector<VpiObject*>& out) {
  for (VpiObject* child : obj.children) {
    if (!IsArrayElement(*child)) continue;
    if (child->array_member && VpiIsArrayVarType(child->type)) {
      AppendElementsInOrder(*child, out);
    } else {
      out.push_back(child);
    }
  }
}

std::vector<VpiObject*> ElementsInOrder(const VpiObject& obj) {
  std::vector<VpiObject*> elements;
  AppendElementsInOrder(obj, elements);
  return elements;
}

bool HoldsDynamicElements(const VpiObject& obj) {
  for (const VpiObject* element : ElementsInOrder(obj)) {
    if (element->var != nullptr && element->var->is_string) return true;
  }
  return false;
}

VpiObject* ElementAtOrdinal(const std::vector<VpiObject*>& elements,
                            long long ordinal) {
  if (ordinal >= static_cast<long long>(elements.size())) return nullptr;
  return elements[static_cast<std::size_t>(ordinal)];
}

Variable* PutValueArrayElement(VpiObject* element,
                               const s_vpi_arrayvalue* arrayvalue_p,
                               unsigned int src) {
  if (!element || !element->var) return nullptr;

  Logic4Vec& ev = element->var->value;
  for (uint32_t i = 0; i < ev.nwords; ++i) ev.words[i] = Logic4Word{};
  DecodePutSourceValue(arrayvalue_p, src, ev, element->var->is_4state,
                       IsRealElement(*element));
  const uint32_t kTopBits = ev.width % 64;
  if (kTopBits != 0) {
    const uint64_t kMask = (uint64_t{1} << kTopBits) - 1;
    ev.words[ev.nwords - 1].aval &= kMask;
    ev.words[ev.nwords - 1].bval &= kMask;
  }
  return element->var;
}

bool VpiArrayFormatSuitsElementType(int fmt, int elem_type) {
  switch (fmt) {
    case kVpiShortIntVal:
      return elem_type == vpiShortIntVar || elem_type == vpiByteVar;
    case kVpiLongIntVal:
      return elem_type == vpiLongIntVar || elem_type == vpiShortIntVar ||
             elem_type == vpiByteVar;
    case kVpiShortRealVal:
      return elem_type == vpiShortRealVar;
    default:
      return true;
  }
}

bool ValidateGetValueArrayRequest(VpiHandle obj, s_vpi_arrayvalue* arrayvalue_p,
                                  int* index_p, long long* out_start_ordinal,
                                  const char** out_err_msg) {
  if (VpiReadSealed(*obj)) {
    *out_err_msg = "vpi_get_value_array() on a protected object is an error";
    return false;
  }
  bool is_unpacked_array =
      VpiIsArrayVarType(obj->type) || obj->type == vpiNetArray;
  if (!is_unpacked_array || obj->array_type != vpiStaticArray) {
    *out_err_msg =
        "vpi_get_value_array() requires a static unpacked array object";
    return false;
  }
  if (HoldsDynamicElements(*obj)) {
    *out_err_msg =
        "vpi_get_value_array() does not take an array of dynamic elements such "
        "as strings";
    return false;
  }

  if (!VpiArrayPutFormatSupported(static_cast<int>(arrayvalue_p->format))) {
    *out_err_msg =
        "vpi_get_value_array() was given an unsupported value format";
    return false;
  }

  for (const VpiObject* element : ElementsInOrder(*obj)) {
    if (!VpiArrayFormatSuitsElementType(static_cast<int>(arrayvalue_p->format),
                                        element->type)) {
      *out_err_msg =
          "vpi_get_value_array() was given a format the array's element data "
          "type does not support";
      return false;
    }
  }

  const auto& dims = obj->array_dim_indices;
  if (index_p == nullptr || dims.empty()) {
    *out_err_msg =
        "vpi_get_value_array() requires a starting index for each unpacked "
        "dimension";
    return false;
  }

  if (!ComputeStartOrdinal(dims, index_p, out_start_ordinal)) {
    *out_err_msg = "vpi_get_value_array() starting index is out of range";
    return false;
  }
  return true;
}

void CollectGetValueArraySection(VpiHandle obj, long long start_ordinal,
                                 unsigned int num,
                                 std::vector<VpiObject*>* section) {
  const std::vector<VpiObject*> kElements = ElementsInOrder(*obj);
  for (unsigned int rel = 0; rel < num; ++rel) {
    (*section)[rel] = ElementAtOrdinal(kElements, start_ordinal + rel);
  }
}

size_t ComputeGetValueArrayBytes(int fmt, int ngroups, int words_per_elem,
                                 unsigned int num) {
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
      bytes = sizeof(s_vpi_time) * num;
      break;
    case kVpiVectorVal:
      bytes = sizeof(s_vpi_vecval) * static_cast<size_t>(words_per_elem) * num;
      break;
    default:
      bytes = sizeof(int32_t) * num;
      break;
  }
  return bytes;
}

void EncodeGetScalarValue(s_vpi_arrayvalue* arrayvalue_p, unsigned int k,
                          int fmt, const ElementWords& value) {
  int64_t integer = 0;
  double real = 0.0;
  if (value.var != nullptr) {
    Logic4Vec element = value.var->value;
    element.is_signed = element.is_signed || value.var->is_signed;
    integer = VpiKnownIntegerValue(element);
    if (value.is_real) {
      real = RealVecToDouble(element);
    } else {
      real = element.is_signed ? static_cast<double>(integer)
                               : static_cast<double>(element.ToUint64());
    }
  }
  switch (fmt) {
    case kVpiShortIntVal:
      arrayvalue_p->value.shortints[k] = static_cast<int16_t>(integer);
      break;
    case kVpiLongIntVal:
      arrayvalue_p->value.longints[k] = integer;
      break;
    case kVpiRealVal:
      arrayvalue_p->value.reals[k] = real;
      break;
    case kVpiShortRealVal:
      arrayvalue_p->value.shortreals[k] = static_cast<float>(real);
      break;
    default:
      arrayvalue_p->value.integers[k] = static_cast<int32_t>(integer);
      break;
  }
}

void EncodeGetTimeValue(s_vpi_arrayvalue* arrayvalue_p, unsigned int k,
                        uint64_t aval) {
  arrayvalue_p->value.times[k].high = static_cast<uint32_t>(aval >> 32);
  arrayvalue_p->value.times[k].low = static_cast<uint32_t>(aval & 0xFFFFFFFFu);
}

void EncodeGetVectorValue(s_vpi_arrayvalue* arrayvalue_p, unsigned int k,
                          uint32_t width, const ElementWords& value) {
  const uint32_t kWords = (width + 31) / 32;
  s_vpi_vecval* vecs =
      arrayvalue_p->value.vectors + static_cast<size_t>(k) * kWords;
  for (uint32_t w = 0; w < kWords; ++w) {
    vecs[w].aval = static_cast<uint32_t>(PieceOf(value.words, false, w, 32));
    vecs[w].bval =
        value.is_4state
            ? static_cast<uint32_t>(PieceOf(value.words, true, w, 32))
            : 0;
  }
}

void EncodeGetRaw(s_vpi_arrayvalue* arrayvalue_p, unsigned int k,
                  uint32_t width, const ElementWords& value) {
  const bool kFourStateFormat =
      static_cast<int>(arrayvalue_p->format) == kVpiRawFourStateVal;
  const uint32_t kGroups = (width + 7) / 8;
  char* abase = arrayvalue_p->value.rawvals +
                static_cast<size_t>(k) * kGroups * (kFourStateFormat ? 2 : 1);
  for (uint32_t b = 0; b < kGroups; ++b) {
    abase[b] = static_cast<char>(PieceOf(value.words, false, b, 8));
    if (kFourStateFormat) {
      abase[kGroups + b] =
          value.is_4state ? static_cast<char>(PieceOf(value.words, true, b, 8))
                          : static_cast<char>(0);
    }
  }
}

void EncodeGetElementValue(s_vpi_arrayvalue* arrayvalue_p, unsigned int k,
                           uint32_t width, const ElementWords& value) {
  int fmt = static_cast<int>(arrayvalue_p->format);
  switch (fmt) {
    case kVpiTimeVal:
      EncodeGetTimeValue(arrayvalue_p, k, value.words[0].aval);
      break;
    case kVpiVectorVal:
      EncodeGetVectorValue(arrayvalue_p, k, width, value);
      break;
    case kVpiRawFourStateVal:
    case kVpiRawTwoStateVal:
      EncodeGetRaw(arrayvalue_p, k, width, value);
      break;
    default:
      EncodeGetScalarValue(arrayvalue_p, k, fmt, value);
      break;
  }
}

}  // namespace

void VpiContext::PutValueArray(VpiHandle obj, s_vpi_arrayvalue* arrayvalue_p,
                               int* index_p, unsigned int num) {
  if (!obj || !arrayvalue_p) return;
  if (at_read_only_synch_time_) {
    last_error_.state = kVpiPLI;
    last_error_.level = kVpiError;
    last_error_.message = VpiText(
        "vpi_put_value_array(): no value may be written from a "
        "cbReadOnlySynch callback");
    return;
  }

  long long start_ordinal = 0;
  if (!ValidatePutValueArrayRequest(obj, arrayvalue_p, index_p, &start_ordinal,
                                    &last_error_)) {
    return;
  }

  bool one_value = (arrayvalue_p->flags & kVpiOneValue) != 0;
  const std::vector<VpiObject*> kElements = ElementsInOrder(*obj);
  std::vector<Variable*> written;
  for (unsigned int k = 0; k < num; ++k) {
    long long ordinal = start_ordinal + static_cast<long long>(k);
    unsigned int src = one_value ? 0u : k;
    Variable* var = PutValueArrayElement(ElementAtOrdinal(kElements, ordinal),
                                         arrayvalue_p, src);
    if (var) written.push_back(var);
  }

  if ((arrayvalue_p->flags & kVpiPropagateOff) == 0) {
    for (Variable* var : written) var->NotifyWatchers();
  }
}

void VpiContext::GetValueArray(VpiHandle obj, s_vpi_arrayvalue* arrayvalue_p,
                               int* index_p, unsigned int num) {
  if (!obj || !arrayvalue_p) return;

  auto fail = [&](const char* msg) {
    last_error_.state = kVpiPLI;
    last_error_.level = kVpiError;
    last_error_.message = VpiText(msg);
    arrayvalue_p->value.rawvals = nullptr;
  };

  long long start_ordinal = 0;
  const char* err_msg = nullptr;
  if (!ValidateGetValueArrayRequest(obj, arrayvalue_p, index_p, &start_ordinal,
                                    &err_msg)) {
    fail(err_msg);
    return;
  }

  std::vector<VpiObject*> section(num, nullptr);
  CollectGetValueArraySection(obj, start_ordinal, num, &section);
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

  bool user_alloc = (arrayvalue_p->flags & kVpiUserAllocFlag) != 0;
  if (!user_alloc) {
    size_t bytes = ComputeGetValueArrayBytes(fmt, ngroups, words_per_elem, num);
    value_array_storage_.assign(bytes, 0);
    arrayvalue_p->value.rawvals =
        reinterpret_cast<char*>(value_array_storage_.data());
  }

  const std::vector<Logic4Word> kZeros((width + 63) / 64 + 1);
  for (unsigned int k = 0; k < num; ++k) {
    const VpiObject* element = section[k];
    ElementWords value{kZeros.data(), false};
    if (element != nullptr && element->var != nullptr) {
      value = {element->var->value.words, element->var->is_4state, element->var,
               IsRealElement(*element)};
    }
    EncodeGetElementValue(arrayvalue_p, k, width, value);
  }
}

}  // namespace delta
