#include "simulator/dpi_c_type.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <string>
#include <string_view>
#include <vector>

#include "parser/ast.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/svdpi_open_array.h"

namespace delta {

namespace {

// The C type a small SystemVerilog type maps to, the one an input of it is
// passed by value as and a pointer to which an output or inout of it is
// passed by reference as: Table H.1's row, a scalar bit or logic under the
// svBit and svLogic names svdpi.h gives its unsigned char.
std::string SmallCType(DataTypeKind kind, bool is_unsigned) {
  switch (kind) {
    case DataTypeKind::kBit:
      return "svBit";
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
      return "svLogic";
    default:
      return DpiCTypeOfBasicType(kind, is_unsigned);
  }
}

// A formal of bit, logic or reg whose declaration gave it a width is a packed
// array; one without is the scalar.
bool IsPackedArray(const DpiArg& formal) {
  switch (formal.type) {
    case DataTypeKind::kBit:
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
      return formal.width > 1;
    case DataTypeKind::kInteger:
    case DataTypeKind::kTime:
      return true;
    default:
      return false;
  }
}

// §H.7.3: the width of a packed formal, which integer and time carry in
// their type and a bit, logic or reg array in its declaration.
uint32_t PackedWidth(const DpiArg& formal) {
  switch (formal.type) {
    case DataTypeKind::kInteger:
      return 32;
    case DataTypeKind::kTime:
      return 64;
    default:
      return formal.width;
  }
}

// Table H.1: sizeof the C type a small type maps to.
std::size_t SmallCTypeBytes(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kByte:
    case DataTypeKind::kBit:
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
      return 1;
    case DataTypeKind::kShortint:
      return sizeof(short int);
    case DataTypeKind::kInt:
      return sizeof(int);
    case DataTypeKind::kLongint:
      return sizeof(long long);
    case DataTypeKind::kReal:
    case DataTypeKind::kRealtime:
      return sizeof(double);
    case DataTypeKind::kShortreal:
      return sizeof(float);
    case DataTypeKind::kChandle:
    case DataTypeKind::kString:
      return sizeof(void*);
    default:
      return 0;
  }
}

// The count of a dimension's range, however it runs.
uint32_t SizeOfDimension(const SvActualDimension& dim) {
  return static_cast<uint32_t>(std::abs(dim.high - dim.low)) + 1U;
}

// §H.7.1: the range of the one-dimensional packed array equivalent to the
// actual's packed dimensions, one element per combination of their indices,
// normalized to [size-1:0].
SvActualDimension LinearizedNormalizedRange(
    const std::vector<SvActualDimension>& actual_packed) {
  int32_t size = actual_packed.empty() ? 0 : 1;
  for (const SvActualDimension& dim : actual_packed) {
    size *= static_cast<int32_t>(SizeOfDimension(dim));
  }
  return SvActualDimension{size > 0 ? size - 1 : 0, 0};
}

}  // namespace

bool DpiTypeIsSmall(DataTypeKind kind) {
  // §H.8.7: byte, shortint, int, longint, real, shortreal; scalar bit and
  // logic; chandle and string.
  return !SmallCType(kind, false).empty();
}

std::string_view DpiCTypeOfHandleArgument() {
  return "const svOpenArrayHandle";
}

bool DpiUserMayModifyHandleContents() { return false; }

std::string DpiCTypeOfFormal(const DpiArg& formal, bool open_array) {
  // §H.8.6: an open array is passed by handle whatever the direction, and the
  // handle always carries the const qualifier.
  if (open_array) return std::string(DpiCTypeOfHandleArgument());
  const bool kInput = formal.direction == Direction::kInput;
  if (IsPackedArray(formal)) {
    // §H.8.4 and §H.8.8: a packed array is passed by reference to its
    // canonical representation, const for an input.
    const std::string kChunk = DpiCanonicalElementType(formal.type);
    if (kChunk.empty()) return "";
    return (kInput ? "const " : "") + kChunk + "*";
  }
  if ((formal.type == DataTypeKind::kStruct ||
       formal.type == DataTypeKind::kUnion) &&
      !formal.type_name.empty()) {
    // §H.7.5 and §H.8.4: a struct or union is passed by reference to the
    // C-compatible object of the type it was declared with, const for an
    // input -- §H.10.2's `pair i2` being `const pair* i2`.
    return (kInput ? "const " : "") + std::string(formal.type_name) + "*";
  }
  const std::string kSmall = SmallCType(formal.type, formal.is_unsigned);
  if (kSmall.empty()) return "";
  // §H.8.7: an input of a small type is passed by value with the const
  // qualifier, which a string's table type const char* already carries
  // (§H.8.10); §H.8.8: an inout or output is passed by reference.
  if (!kInput) return kSmall + "*";
  return kSmall.starts_with("const ") ? kSmall : "const " + kSmall;
}

std::size_t DpiCElementBytes(const DpiArg& formal) {
  if (IsPackedArray(formal)) {
    // §H.7.7: the canonical representation, one chunk per 32 bits, a
    // 2-state chunk being one word and a 4-state one an aval/bval pair.
    const std::size_t kChunk = formal.type == DataTypeKind::kBit
                                   ? sizeof(SvBitVecVal)
                                   : sizeof(SvLogicVecVal);
    return DpiCanonicalWordCount(PackedWidth(formal)) * kChunk;
  }
  return SmallCTypeBytes(formal.type);
}

std::string DpiCDeclarationOfUnpackedFormal(
    const DpiArg& formal, const std::vector<SvActualDimension>& unpacked_dims) {
  const bool kPacked = IsPackedArray(formal);
  const std::string kElement =
      kPacked ? DpiCanonicalElementType(formal.type)
              : SmallCType(formal.type, formal.is_unsigned);
  if (kElement.empty()) return "";
  // §H.8.10.1: a string element's const char* already carries the const an
  // input has, and an array of strings is const char** in every direction.
  const bool kQualify =
      formal.direction == Direction::kInput && !kElement.starts_with("const ");
  std::string decl = kQualify ? "const " : "";
  decl += kElement + " " + std::string(formal.name);
  for (const SvActualDimension& dim : unpacked_dims) {
    decl += "[" + std::to_string(SizeOfDimension(dim)) + "]";
  }
  if (kPacked) {
    decl +=
        "[" + std::to_string(DpiCanonicalWordCount(PackedWidth(formal))) + "]";
  }
  return decl;
}

std::vector<uint32_t> DpiCIndicesOfUnpackedElement(
    const std::vector<SvActualDimension>& unpacked_dims,
    const std::vector<int32_t>& sv_indices) {
  std::vector<uint32_t> c_indices;
  for (std::size_t k = 0; k < unpacked_dims.size() && k < sv_indices.size();
       ++k) {
    const int32_t kLow = std::min(unpacked_dims[k].low, unpacked_dims[k].high);
    c_indices.push_back(static_cast<uint32_t>(sv_indices[k] - kLow));
  }
  return c_indices;
}

std::size_t DpiCOffsetOfUnpackedElement(
    const DpiArg& formal, const std::vector<SvActualDimension>& unpacked_dims,
    const std::vector<int32_t>& sv_indices) {
  const std::vector<uint32_t> kIndices =
      DpiCIndicesOfUnpackedElement(unpacked_dims, sv_indices);
  // Row-major: each dimension's index is scaled by the count of elements
  // under one step of it, the product of the sizes of the dimensions after.
  std::size_t linear = 0;
  for (std::size_t k = 0; k < kIndices.size(); ++k) {
    linear = linear * SizeOfDimension(unpacked_dims[k]) + kIndices[k];
  }
  return linear * DpiCElementBytes(formal);
}

bool DpiPartSelectAppliesTo(const DpiArg& formal) {
  // §H.11.5: a slice of a packed array of bit or logic, which is what has a
  // canonical representation to slice.
  return IsPackedArray(formal);
}

bool DpiPartSelectIsDetermined(uint32_t width, int i, int w) {
  if (w < 1 || w > kDpiPartSelectMaxWidth || i < 0) return false;
  // [(i+w-1):i] within [width-1:0]: the bit past the top of the select is
  // no further than the bit past the top of the array.
  return static_cast<uint64_t>(i) + static_cast<uint64_t>(w) <= width;
}

int DpiNormalizedBitIndex(SvActualDimension packed, int32_t sv_index) {
  // §H.7.6 b): [L:R] is normalized to [abs(L-R):0], the LSB at R index 0.
  return std::abs(sv_index - packed.high);
}

uint64_t DpiOpenArrayElementCount(const SvOpenArrayDesc& desc) {
  // §H.12: the actual's size, over the unpacked dimensions the handle
  // records after the packed part at dimension 0; a dimension is counted
  // however its range runs.
  if (desc.ranges == nullptr) return 0;
  uint64_t count = 1;
  for (int d = 1; d < desc.n_dims; ++d) {
    const SvOpenArrayDimRange& r = desc.ranges[d];
    count *= static_cast<uint64_t>(
        std::abs(static_cast<int64_t>(r.left) - r.right) + 1);
  }
  return count;
}

uint64_t DpiOpenArrayCapacityBytes(const SvOpenArrayDesc& desc) {
  return DpiOpenArrayElementCount(desc) * desc.elem_size;
}

bool DpiOpenArrayWriteIsDefined(const SvOpenArrayDesc& desc, uint64_t bytes) {
  return bytes <= DpiOpenArrayCapacityBytes(desc);
}

std::string DpiCanonicalElementType(DataTypeKind kind) {
  // §H.7.3 and §H.7.7: 2-state for bit, 4-state for logic and reg and for
  // integer and time.
  switch (kind) {
    case DataTypeKind::kBit:
      return "svBitVecVal";
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
    case DataTypeKind::kInteger:
    case DataTypeKind::kTime:
      return "svLogicVecVal";
    default:
      return "";
  }
}

DpiCanonicalBitPosition DpiCanonicalPositionOfBit(uint32_t bit) {
  // §H.7.7: element 0 holds bits 0 to 31, element 1 the 32 more significant
  // bits, and so on.
  return DpiCanonicalBitPosition{bit / kDpiCanonicalElementBits,
                                 bit % kDpiCanonicalElementBits};
}

uint32_t DpiCanonicalUnusedBits(uint32_t width) {
  // §H.7.7: the last element holds width mod 32 bits when the width is not
  // a multiple of 32, and the rest of it is unused.
  const uint32_t kUsed = width % kDpiCanonicalElementBits;
  return kUsed == 0 ? 0 : kDpiCanonicalElementBits - kUsed;
}

uint32_t DpiCanonicalLastElementWithUnusedBits(uint32_t last, uint32_t width,
                                               bool is_signed) {
  const uint32_t kUnused = DpiCanonicalUnusedBits(width);
  if (kUnused == 0) return last;
  const uint32_t kUsed = kDpiCanonicalElementBits - kUnused;
  const uint32_t kUsedMask = (1U << kUsed) - 1U;
  // §H.7.7: masking for an unsigned array, sign extension for a signed one
  // from the array's most significant bit, bit kUsed-1 of the element.
  const bool kNegative = is_signed && ((last >> (kUsed - 1)) & 1U) != 0;
  return kNegative ? (last | ~kUsedMask) : (last & kUsedMask);
}

std::string DpiCTypeOfBasicType(DataTypeKind kind, bool is_unsigned) {
  switch (kind) {
    case DataTypeKind::kByte:
      return is_unsigned ? "unsigned char" : "char";
    case DataTypeKind::kShortint:
      return is_unsigned ? "unsigned short" : "short int";
    case DataTypeKind::kInt:
      return is_unsigned ? "unsigned int" : "int";
    case DataTypeKind::kLongint:
      return is_unsigned ? "unsigned long long" : "long long";
    case DataTypeKind::kReal:
    case DataTypeKind::kRealtime:
      return "double";
    case DataTypeKind::kShortreal:
      return "float";
    case DataTypeKind::kChandle:
      return "void*";
    case DataTypeKind::kString:
      return "const char*";
    case DataTypeKind::kBit:
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
      return "unsigned char";
    default:
      return "";
  }
}

DpiActualCoercion DpiCoercionOfPackedActual(uint32_t actual_width,
                                            uint32_t formal_width) {
  if (actual_width > formal_width) return DpiActualCoercion::kTruncate;
  if (actual_width < formal_width) return DpiActualCoercion::kExtend;
  return DpiActualCoercion::kNone;
}

bool DpiCTypeMatchesFormal(const DpiArg& formal, bool open_array,
                           std::string_view c_type) {
  // The spelling DpiCTypeOfFormal gives puts the * against the type, so the
  // prototype's spaces around a * are dropped before the comparison.
  std::string spelled;
  for (std::size_t i = 0; i < c_type.size(); ++i) {
    if (c_type[i] == ' ' && (i + 1 == c_type.size() || c_type[i + 1] == '*' ||
                             (!spelled.empty() && spelled.back() == '*'))) {
      continue;
    }
    spelled += c_type[i];
  }
  return spelled == DpiCTypeOfFormal(formal, open_array);
}

std::vector<SvActualDimension> DpiFormalRangesAtCall(
    const DpiFormalDimension& packed,
    const std::vector<DpiFormalDimension>& unpacked,
    const std::vector<SvActualDimension>& actual_packed,
    const std::vector<SvActualDimension>& actual_unpacked) {
  std::vector<SvActualDimension> ranges;
  ranges.push_back(packed.sized ? packed.range
                                : LinearizedNormalizedRange(actual_packed));
  for (std::size_t k = 0; k < unpacked.size(); ++k) {
    if (unpacked[k].sized) {
      ranges.push_back(unpacked[k].range);
    } else if (k < actual_unpacked.size()) {
      ranges.push_back(actual_unpacked[k]);
    }
  }
  return ranges;
}

bool DpiForeignCodeMayModifyFormal(Direction direction) {
  return direction != Direction::kInput;
}

bool DpiFormalIsDeterminedOnEntry(Direction direction) {
  return direction != Direction::kOutput;
}

bool DpiSimulatorDetectsChangesOf(Direction direction) {
  return direction == Direction::kOutput || direction == Direction::kInout;
}

DpiImportAccess DpiAccessOfImport(bool is_context) {
  return is_context ? DpiImportAccess::kAnyDataObject
                    : DpiImportAccess::kActualArgumentsOnly;
}

bool DpiImportMaySafelyCallOtherApis(bool is_context) { return is_context; }

bool DpiImportCallIsOptimizationBarrier(bool is_context) { return is_context; }

bool DpiSideMayFree(DpiMemorySide allocated_by, DpiMemorySide freed_by) {
  return allocated_by == freed_by;
}

DpiMemorySide DpiSideOwningBlockBehindChandle() { return DpiMemorySide::kC; }

DpiMemorySide DpiSideOfImportedCall() { return DpiMemorySide::kC; }

DpiCLayerType DpiCLayerTypeOfFormal(const DpiArg& formal, bool open_array) {
  if (open_array) return DpiCLayerType::kOpenArrayHandle;
  if (IsPackedArray(formal)) return DpiCLayerType::kCanonicalElement;
  if (DpiTypeIsSmall(formal.type)) return DpiCLayerType::kBasic;
  return DpiCLayerType::kNone;
}

std::string_view DpiSubclauseDefiningCLayerType(DpiCLayerType type) {
  switch (type) {
    case DpiCLayerType::kBasic:
      return "H.7.4";
    case DpiCLayerType::kCanonicalElement:
      return "H.7.7";
    case DpiCLayerType::kOpenArrayHandle:
      return "H.12";
    case DpiCLayerType::kNone:
      return "";
  }
  return "";
}

DpiRepresentation DpiRepresentationOfFormal(const DpiArg& formal) {
  if (IsPackedArray(formal)) return DpiRepresentation::kCanonical;
  if (DpiTypeIsSmall(formal.type)) return DpiRepresentation::kBasic;
  if (formal.type == DataTypeKind::kStruct ||
      formal.type == DataTypeKind::kUnion) {
    return DpiRepresentation::kCCompatible;
  }
  return DpiRepresentation::kNone;
}

DpiRepresentation DpiRepresentationOfOpenArrayElement(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kBit:
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
    case DataTypeKind::kInteger:
    case DataTypeKind::kTime:
      return DpiRepresentation::kCanonical;
    default:
      return DpiRepresentation::kCCompatible;
  }
}

bool DpiEnumIsSmall(DataTypeKind base, uint32_t base_width) {
  DpiArg as_formal;
  as_formal.type = base;
  as_formal.width = base_width;
  return DpiRepresentationOfFormal(as_formal) == DpiRepresentation::kBasic;
}

bool DpiAggregateIsAnArgument(const DpiAggregateElement& aggregate) {
  if (aggregate.kind == DataTypeKind::kStruct ||
      aggregate.kind == DataTypeKind::kUnion) {
    return std::all_of(aggregate.members.begin(), aggregate.members.end(),
                       DpiAggregateIsAnArgument);
  }
  DpiArg as_formal;
  as_formal.type = aggregate.kind;
  as_formal.width = aggregate.width;
  return IsPackedArray(as_formal) || DpiTypeIsSmall(aggregate.kind);
}

bool DpiAggregateLayoutIsCCompatible(const DpiAggregateElement& aggregate) {
  if (aggregate.kind == DataTypeKind::kStruct ||
      aggregate.kind == DataTypeKind::kUnion) {
    return std::all_of(aggregate.members.begin(), aggregate.members.end(),
                       DpiAggregateLayoutIsCCompatible);
  }
  DpiArg as_formal;
  as_formal.type = aggregate.kind;
  as_formal.width = aggregate.width;
  return !IsPackedArray(as_formal);
}

DpiPassingMode DpiPassingModeOfFormal(const DpiArg& formal, bool open_array) {
  if (open_array) return DpiPassingMode::kByHandle;
  if (formal.direction == Direction::kInput && !IsPackedArray(formal) &&
      DpiTypeIsSmall(formal.type)) {
    return DpiPassingMode::kByValue;
  }
  return DpiPassingMode::kByReference;
}

DpiPassingMode DpiPassingModeOfResult() { return DpiPassingMode::kByValue; }

bool DpiFormalIsDirectlyAccessibleInC(DpiPassingMode mode) {
  return mode != DpiPassingMode::kByHandle;
}

DpiReferent DpiReferentOfFormal(const DpiArg& formal) {
  return IsPackedArray(formal) ? DpiReferent::kCanonicalDataObject
                               : DpiReferent::kActualDataObject;
}

bool DpiReferenceOutlivesTheCall() { return false; }

DpiMemorySide DpiSideOwningACopyKeptAcrossCalls() { return DpiMemorySide::kC; }

bool DpiFormalIsPassedByValue(const DpiArg& formal, bool open_array) {
  return DpiPassingModeOfFormal(formal, open_array) == DpiPassingMode::kByValue;
}

std::string DpiCTypeOfResult(DataTypeKind kind) {
  if (kind == DataTypeKind::kVoid) return "void";
  return SmallCType(kind, false);
}

const std::vector<DataTypeKind>& DpiSmallTypes() {
  static const std::vector<DataTypeKind> kSmall = {
      DataTypeKind::kByte,    DataTypeKind::kShortint, DataTypeKind::kInt,
      DataTypeKind::kLongint, DataTypeKind::kReal,     DataTypeKind::kShortreal,
      DataTypeKind::kBit,     DataTypeKind::kLogic,    DataTypeKind::kChandle,
      DataTypeKind::kString};
  return kSmall;
}

bool DpiModeIsAFormOfReference(DpiPassingMode mode) {
  return mode != DpiPassingMode::kByValue;
}

bool DpiTypeMayBeAResult(DataTypeKind kind) {
  return kind == DataTypeKind::kVoid || DpiTypeIsSmall(kind);
}

std::string DpiCFunctionHeader(std::string_view c_name, DataTypeKind result,
                               const std::vector<DpiArg>& formals) {
  std::string header =
      DpiCTypeOfResult(result) + " " + std::string(c_name) + "(";
  for (std::size_t i = 0; i < formals.size(); ++i) {
    if (i > 0) header += ", ";
    header += DpiCTypeOfFormal(formals[i], false) + " " +
              std::string(formals[i].name);
  }
  return header + ")";
}

std::string DpiCHeaderOfExportedSubroutine(std::string_view c_name,
                                           DataTypeKind result,
                                           const std::vector<DpiArg>& formals,
                                           bool is_task) {
  return DpiCFunctionHeader(c_name, is_task ? DataTypeKind::kInt : result,
                            formals);
}

std::string_view DpiCTypeOfExportedTaskResult() { return "int"; }

bool DpiExportFormalMayBeAnOpenArray() { return false; }

bool DpiExportFormalMayHaveType(DataTypeKind kind) {
  DpiArg as_formal;
  as_formal.type = kind;
  as_formal.width =
      kind == DataTypeKind::kBit || kind == DataTypeKind::kLogic ? 1 : 0;
  return !DpiCTypeOfFormal(as_formal, false).empty();
}

DpiMemorySide DpiSideAllocatingActualOfExportCall() {
  return DpiMemorySide::kC;
}

bool DpiCallerAllocatesExportActual(const DpiArg& formal) {
  return DpiPassingModeOfFormal(formal, false) == DpiPassingMode::kByReference;
}

std::string DpiCAllocationOfExportActual(const DpiArg& formal) {
  DpiArg as_allocated = formal;
  as_allocated.direction = Direction::kOutput;
  return DpiCDeclarationOfUnpackedFormal(as_allocated, {});
}

bool DpiOutputOrInoutIsPassedByReference(const DpiArg& formal,
                                         bool open_array) {
  return formal.direction != Direction::kInput &&
         DpiPassingModeOfFormal(formal, open_array) ==
             DpiPassingMode::kByReference;
}

const std::vector<DataTypeKind>& DpiResultTypes() {
  static const std::vector<DataTypeKind> kResults = {
      DataTypeKind::kByte,    DataTypeKind::kShortint, DataTypeKind::kInt,
      DataTypeKind::kLongint, DataTypeKind::kReal,     DataTypeKind::kShortreal,
      DataTypeKind::kChandle, DataTypeKind::kString,   DataTypeKind::kBit,
      DataTypeKind::kLogic};
  return kResults;
}

DpiMemorySide DpiSideProvidingStringPointer(DpiStringPointerProvider provider) {
  switch (provider) {
    case DpiStringPointerProvider::kImportInput:
    case DpiStringPointerProvider::kImportInoutOnArrival:
    case DpiStringPointerProvider::kExportOutput:
    case DpiStringPointerProvider::kExportInoutChanged:
      return DpiMemorySide::kSystemVerilog;
    case DpiStringPointerProvider::kImportOutput:
    case DpiStringPointerProvider::kImportInoutChanged:
    case DpiStringPointerProvider::kExportInput:
    case DpiStringPointerProvider::kExportInoutOnArrival:
      return DpiMemorySide::kC;
  }
  return DpiMemorySide::kC;
}

DpiMemorySide DpiSideCopyingString(DpiStringPointerProvider provider) {
  return DpiSideProvidingStringPointer(provider) == DpiMemorySide::kC
             ? DpiMemorySide::kSystemVerilog
             : DpiMemorySide::kC;
}

bool DpiStringCharactersMayBeModifiedByReceiver() { return false; }

std::string_view DpiCTypeOfStringMember() { return "const char*"; }

bool DpiStringMemberStipulationsAreStandalone() { return true; }

std::string_view DpiCTypeOfStringArray(Direction /*direction*/) {
  return "const char**";
}

bool DpiProgrammerChoosesFormalSizing() { return true; }

DpiPassingMode DpiPassingModeOfSizing(DpiFormalArraySizing sizing) {
  return sizing == DpiFormalArraySizing::kOpen ? DpiPassingMode::kByHandle
                                               : DpiPassingMode::kByReference;
}

bool DpiSizingHasOverhead(DpiFormalArraySizing sizing) {
  return sizing == DpiFormalArraySizing::kOpen;
}

DpiArrayAccessibility DpiAccessibilityOfSizing(DpiFormalArraySizing sizing) {
  return sizing == DpiFormalArraySizing::kOpen
             ? DpiArrayAccessibility::kMostlyIndirectlyThroughTheHandle
             : DpiArrayAccessibility::kDirectlyAsNormalizedArray;
}

std::vector<SvActualDimension> DpiCRangesAtCall(
    const DpiFormalDimension& packed,
    const std::vector<DpiFormalDimension>& unpacked,
    const std::vector<SvActualDimension>& actual_packed,
    const std::vector<SvActualDimension>& actual_unpacked) {
  std::vector<SvActualDimension> ranges =
      DpiFormalRangesAtCall(packed, unpacked, actual_packed, actual_unpacked);
  if (ranges.empty()) return ranges;
  // §H.12.1: the packed part is normalized on the C side either way, [n:0].
  ranges[0] = DpiNormalizedRange(ranges[0]);
  for (std::size_t k = 1; k < ranges.size() && k - 1 < unpacked.size(); ++k) {
    // §H.12.1: a sized unpacked dimension is normalized to C style, [0:k];
    // an unsized one keeps the actual's original range.
    if (unpacked[k - 1].sized) {
      const auto kSize = static_cast<int32_t>(SizeOfDimension(ranges[k]));
      ranges[k] = SvActualDimension{0, kSize - 1};
    }
  }
  return ranges;
}

DpiElementAccessMethod DpiElementAccessMethodOf(DataTypeKind kind,
                                                uint32_t width) {
  DpiArg element;
  element.type = kind;
  element.width = width;
  if (IsPackedArray(element)) {
    return DpiElementAccessMethod::kCopyingToOrFromCanonical;
  }
  if (kind == DataTypeKind::kBit || kind == DataTypeKind::kLogic ||
      kind == DataTypeKind::kReg) {
    return DpiElementAccessMethod::kDirectly;
  }
  return DpiElementAccessMethod::kGenericPointerWithCasting;
}

bool DpiScalarOrPackedElementIsAccessibleByPointer(
    bool implementation_supports_it_for_the_array) {
  return implementation_supports_it_for_the_array;
}

bool DpiIndexingFunctionIsSpecializedFor(uint32_t index_count) {
  return index_count >= 1 && index_count <= 3;
}

bool DpiWholeArrayIsAccessible(bool actual_layout_is_c) {
  return actual_layout_is_c;
}

bool DpiElementAddressIsAlwaysSupported() { return true; }

std::string_view DpiAddressFunctionPointerType() { return "void*"; }

bool DpiElementPointerIsMeaningful(
    bool element_represented_as_individual_value) {
  return element_represented_as_individual_value;
}

DpiElementFunctionGroup DpiElementFunctionGroupOf(DataTypeKind kind,
                                                  uint32_t width) {
  switch (DpiElementAccessMethodOf(kind, width)) {
    case DpiElementAccessMethod::kDirectly:
      return DpiElementFunctionGroup::kScalar;
    case DpiElementAccessMethod::kCopyingToOrFromCanonical:
      return DpiElementFunctionGroup::kCanonical;
    case DpiElementAccessMethod::kGenericPointerWithCasting:
      return DpiElementFunctionGroup::kAddress;
  }
  return DpiElementFunctionGroup::kAddress;
}

std::string_view DpiScalarElementFunction(bool four_state, bool put) {
  if (four_state) return put ? "svPutLogicArrElem" : "svGetLogicArrElem";
  return put ? "svPutBitArrElem" : "svGetBitArrElem";
}

DpiMemorySide DpiSideProvidingCanonicalBuffer() { return DpiMemorySide::kC; }

bool DpiAccessCopiesThroughCanonicalBuffer(DpiOpenArrayAccess access) {
  return access == DpiOpenArrayAccess::kCopyElementToCanonicalBuffer ||
         access == DpiOpenArrayAccess::kCopyElementFromCanonicalBuffer;
}

std::string_view DpiAccessFunction(DpiOpenArrayAccess access, bool four_state) {
  switch (access) {
    case DpiOpenArrayAccess::kCopyElementToCanonicalBuffer:
      return four_state ? "svGetLogicArrElemVecVal" : "svGetBitArrElemVecVal";
    case DpiOpenArrayAccess::kCopyElementFromCanonicalBuffer:
      return four_state ? "svPutLogicArrElemVecVal" : "svPutBitArrElemVecVal";
    case DpiOpenArrayAccess::kAddressOfArray:
      return "svGetArrayPtr";
    case DpiOpenArrayAccess::kAddressOfElement:
      return "svGetArrElemPtr";
  }
  return "";
}

DpiArg DpiPackedAggregateAsPackedArrayFormal(const DpiArg& aggregate,
                                             bool four_state, uint32_t width) {
  DpiArg formal = aggregate;
  formal.type = four_state ? DataTypeKind::kLogic : DataTypeKind::kBit;
  formal.width = width;
  formal.type_name = {};
  return formal;
}

SvActualDimension DpiLinearizedPackedRange(
    const std::vector<SvActualDimension>& packed_dims) {
  return LinearizedNormalizedRange(packed_dims);
}

uint32_t DpiPackedDimensionCountInC() { return 1; }

bool DpiUnpackedDimensionCountIsLimited() { return false; }

bool DpiCCompatibleFormalCanHoldTwoStateVector(uint32_t width) {
  return width <= kDpiInlineValueBits;
}

DpiTwoStateTechnique DpiTechniqueRequiredForTwoStateVector(uint32_t width) {
  return DpiCCompatibleFormalCanHoldTwoStateVector(width)
             ? DpiTwoStateTechnique::kCCompatibleFormal
             : DpiTwoStateTechnique::kCanonical;
}

bool DpiTechniqueIsMoreEfficient(DpiTwoStateTechnique technique,
                                 DpiTwoStateTechnique other) {
  return technique == DpiTwoStateTechnique::kCCompatibleFormal &&
         other == DpiTwoStateTechnique::kCanonical;
}

DpiArrayRanges DpiRangesUsedForAccessing(bool formal_is_open_array) {
  return formal_is_open_array ? DpiArrayRanges::kOfTheActual
                              : DpiArrayRanges::kNormalized;
}

SvActualDimension DpiNormalizedRange(SvActualDimension declared) {
  return SvActualDimension{static_cast<int32_t>(SizeOfDimension(declared)) - 1,
                           0};
}

std::vector<SvActualDimension> DpiRangesForAccessing(
    const std::vector<SvActualDimension>& declared, bool formal_is_open_array) {
  if (formal_is_open_array) return declared;
  std::vector<SvActualDimension> normalized;
  normalized.reserve(declared.size());
  for (const SvActualDimension& dim : declared) {
    normalized.push_back(DpiNormalizedRange(dim));
  }
  return normalized;
}

std::string DpiCDeclarationOfAggregateMember(
    std::string_view name, DataTypeKind kind,
    const std::vector<SvActualDimension>& packed_dims,
    const std::vector<SvActualDimension>& unpacked_dims) {
  DpiArg member;
  member.name = name;
  member.type = kind;
  // §H.7.1: the packed dimensions linearize to one normalized range, whose
  // count is the member's width.
  member.width = SizeOfDimension(LinearizedNormalizedRange(packed_dims));
  if (packed_dims.empty()) member.width = 0;
  // A member is qualified by no direction; an inout formal carries none.
  member.direction = Direction::kInout;
  return DpiCDeclarationOfUnpackedFormal(member, unpacked_dims);
}

std::string_view DpiCLayerIncludeFile() { return "svdpi.h"; }

uint32_t DpiCLayerIncludeFileCount() { return 1; }

bool DpiCLayerIncludeFileIsImplementationIndependent() { return true; }

bool DpiIncludeFileDefines(DpiIncludeFileContent /*content*/) {
  // §H.10: the canonical representation, all basic types and all interface
  // functions alike.
  return true;
}

std::string_view DpiAnnexShowingIncludeFile() { return "Annex I"; }

}  // namespace delta
