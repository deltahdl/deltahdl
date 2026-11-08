#pragma once

#include <array>
#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/svdpi_open_array.h"

namespace delta {

std::string DpiCTypeOfFormal(const DpiArg& formal, bool open_array);

bool DpiOutputOrInoutIsPassedByReference(const DpiArg& formal, bool open_array);

bool DpiTypeIsSmall(DataTypeKind kind);

const std::vector<DataTypeKind>& DpiSmallTypes();

enum class DpiPassingMode : uint8_t { kByValue, kByReference, kByHandle };

DpiPassingMode DpiPassingModeOfFormal(const DpiArg& formal, bool open_array);

DpiPassingMode DpiPassingModeOfResult();

bool DpiModeIsAFormOfReference(DpiPassingMode mode);

bool DpiTypeMayBeAResult(DataTypeKind kind);

const std::vector<DataTypeKind>& DpiResultTypes();

bool DpiFormalIsPassedByValue(const DpiArg& formal, bool open_array);

std::string DpiCTypeOfResult(DataTypeKind kind);

bool DpiFormalIsDirectlyAccessibleInC(DpiPassingMode mode);

std::string_view DpiCTypeOfHandleArgument();

bool DpiUserMayModifyHandleContents();

enum class DpiCLayerType : uint8_t {
  kBasic,
  kCanonicalElement,
  kOpenArrayHandle,
  kNone
};

DpiCLayerType DpiCLayerTypeOfFormal(const DpiArg& formal, bool open_array);

std::string_view DpiSubclauseDefiningCLayerType(DpiCLayerType type);

std::string DpiCTypeOfBasicType(DataTypeKind kind, bool is_unsigned);

std::string DpiCDeclarationOfUnpackedFormal(
    const DpiArg& formal, const std::vector<SvActualDimension>& unpacked_dims);

std::size_t DpiCElementBytes(const DpiArg& formal);

std::vector<uint32_t> DpiCIndicesOfUnpackedElement(
    const std::vector<SvActualDimension>& unpacked_dims,
    const std::vector<int32_t>& sv_indices);

std::size_t DpiCOffsetOfUnpackedElement(
    const DpiArg& formal, const std::vector<SvActualDimension>& unpacked_dims,
    const std::vector<int32_t>& sv_indices);

bool DpiPartSelectAppliesTo(const DpiArg& formal);

constexpr int kDpiPartSelectMaxWidth = 32;

bool DpiPartSelectIsDetermined(uint32_t width, int i, int w);

int DpiNormalizedBitIndex(SvActualDimension packed, int32_t sv_index);

uint64_t DpiOpenArrayElementCount(const SvOpenArrayDesc& desc);

uint64_t DpiOpenArrayCapacityBytes(const SvOpenArrayDesc& desc);

bool DpiOpenArrayWriteIsDefined(const SvOpenArrayDesc& desc, uint64_t bytes);

constexpr uint32_t kDpiCanonicalElementBits = 32;

std::string DpiCanonicalElementType(DataTypeKind kind);

struct DpiCanonicalBitPosition {
  uint32_t element = 0;
  uint32_t bit = 0;
};
DpiCanonicalBitPosition DpiCanonicalPositionOfBit(uint32_t bit);

uint32_t DpiCanonicalUnusedBits(uint32_t width);

uint32_t DpiCanonicalLastElementWithUnusedBits(uint32_t last, uint32_t width,
                                               bool is_signed);

enum class DpiActualCoercion : uint8_t { kNone, kTruncate, kExtend };
DpiActualCoercion DpiCoercionOfPackedActual(uint32_t actual_width,
                                            uint32_t formal_width);

bool DpiCTypeMatchesFormal(const DpiArg& formal, bool open_array,
                           std::string_view c_type);

struct DpiFormalDimension {
  bool sized = true;
  SvActualDimension range;
};

std::vector<SvActualDimension> DpiFormalRangesAtCall(
    const DpiFormalDimension& packed,
    const std::vector<DpiFormalDimension>& unpacked,
    const std::vector<SvActualDimension>& actual_packed,
    const std::vector<SvActualDimension>& actual_unpacked);

bool DpiForeignCodeMayModifyFormal(Direction direction);

bool DpiFormalIsDeterminedOnEntry(Direction direction);

bool DpiSimulatorDetectsChangesOf(Direction direction);

enum class DpiImportAccess : uint8_t { kActualArgumentsOnly, kAnyDataObject };
DpiImportAccess DpiAccessOfImport(bool is_context);

bool DpiImportMaySafelyCallOtherApis(bool is_context);

bool DpiImportCallIsOptimizationBarrier(bool is_context);

enum class DpiMemorySide : uint8_t { kC, kSystemVerilog };

bool DpiSideMayFree(DpiMemorySide allocated_by, DpiMemorySide freed_by);

DpiMemorySide DpiSideOwningBlockBehindChandle();

DpiMemorySide DpiSideOfImportedCall();

enum class DpiRepresentation : uint8_t {
  kCCompatible,
  kBasic,
  kCanonical,
  kNone
};

DpiRepresentation DpiRepresentationOfFormal(const DpiArg& formal);

DpiRepresentation DpiRepresentationOfOpenArrayElement(DataTypeKind kind);

bool DpiEnumIsSmall(DataTypeKind base, uint32_t base_width);

struct DpiAggregateElement {
  DataTypeKind kind = DataTypeKind::kInt;
  uint32_t width = 0;
  std::vector<DpiAggregateElement> members;
};

bool DpiAggregateIsAnArgument(const DpiAggregateElement& aggregate);

bool DpiAggregateLayoutIsCCompatible(const DpiAggregateElement& aggregate);

enum class DpiReferent : uint8_t { kActualDataObject, kCanonicalDataObject };
DpiReferent DpiReferentOfFormal(const DpiArg& formal);

bool DpiReferenceOutlivesTheCall();

DpiMemorySide DpiSideOwningACopyKeptAcrossCalls();

std::string DpiCFunctionHeader(std::string_view c_name, DataTypeKind result,
                               const std::vector<DpiArg>& formals);

std::string DpiCHeaderOfExportedSubroutine(std::string_view c_name,
                                           DataTypeKind result,
                                           const std::vector<DpiArg>& formals,
                                           bool is_task);

std::string_view DpiCTypeOfExportedTaskResult();

bool DpiExportFormalMayBeAnOpenArray();

bool DpiExportFormalMayHaveType(DataTypeKind kind);

DpiMemorySide DpiSideAllocatingActualOfExportCall();

bool DpiCallerAllocatesExportActual(const DpiArg& formal);

std::string DpiCAllocationOfExportActual(const DpiArg& formal);

enum class DpiStringPointerProvider : uint8_t {
  kImportInput,
  kImportOutput,
  kImportInoutOnArrival,
  kImportInoutChanged,
  kExportInput,
  kExportOutput,
  kExportInoutOnArrival,
  kExportInoutChanged,
};

DpiMemorySide DpiSideProvidingStringPointer(DpiStringPointerProvider provider);

DpiMemorySide DpiSideCopyingString(DpiStringPointerProvider provider);

bool DpiStringCharactersMayBeModifiedByReceiver();

std::string_view DpiCTypeOfStringMember();

bool DpiStringMemberStipulationsAreStandalone();

std::string_view DpiCTypeOfStringArray(Direction direction);

enum class DpiArrayRanges : uint8_t { kNormalized, kOfTheActual };

DpiArrayRanges DpiRangesUsedForAccessing(bool formal_is_open_array);

SvActualDimension DpiNormalizedRange(SvActualDimension declared);

std::vector<SvActualDimension> DpiRangesForAccessing(
    const std::vector<SvActualDimension>& declared, bool formal_is_open_array);

SvActualDimension DpiLinearizedPackedRange(
    const std::vector<SvActualDimension>& packed_dims);

uint32_t DpiPackedDimensionCountInC();

bool DpiUnpackedDimensionCountIsLimited();

enum class DpiFormalArraySizing : uint8_t { kSized, kOpen };

bool DpiProgrammerChoosesFormalSizing();
DpiPassingMode DpiPassingModeOfSizing(DpiFormalArraySizing sizing);
bool DpiSizingHasOverhead(DpiFormalArraySizing sizing);

enum class DpiArrayAccessibility : uint8_t {
  kDirectlyAsNormalizedArray,
  kMostlyIndirectlyThroughTheHandle,
};

DpiArrayAccessibility DpiAccessibilityOfSizing(DpiFormalArraySizing sizing);

std::vector<SvActualDimension> DpiCRangesAtCall(
    const DpiFormalDimension& packed,
    const std::vector<DpiFormalDimension>& unpacked,
    const std::vector<SvActualDimension>& actual_packed,
    const std::vector<SvActualDimension>& actual_unpacked);

enum class DpiOpenArrayAccess : uint8_t {
  kCopyElementToCanonicalBuffer,
  kCopyElementFromCanonicalBuffer,
  kAddressOfArray,
  kAddressOfElement,
};

DpiMemorySide DpiSideProvidingCanonicalBuffer();

bool DpiAccessCopiesThroughCanonicalBuffer(DpiOpenArrayAccess access);

std::string_view DpiAccessFunction(DpiOpenArrayAccess access, bool four_state);

enum class DpiElementAccessMethod : uint8_t {
  kCopyingToOrFromCanonical,
  kDirectly,
  kGenericPointerWithCasting,
};

DpiElementAccessMethod DpiElementAccessMethodOf(DataTypeKind kind,
                                                uint32_t width);
bool DpiScalarOrPackedElementIsAccessibleByPointer(
    bool implementation_supports_it_for_the_array);
bool DpiIndexingFunctionIsSpecializedFor(uint32_t index_count);

bool DpiWholeArrayIsAccessible(bool actual_layout_is_c);
bool DpiElementAddressIsAlwaysSupported();
std::string_view DpiAddressFunctionPointerType();
bool DpiElementPointerIsMeaningful(
    bool element_represented_as_individual_value);

enum class DpiElementFunctionGroup : uint8_t { kScalar, kCanonical, kAddress };

DpiElementFunctionGroup DpiElementFunctionGroupOf(DataTypeKind kind,
                                                  uint32_t width);
std::string_view DpiScalarElementFunction(bool four_state, bool put);

bool DpiCanonicalRepresentationIsNeededForElement(DataTypeKind kind,
                                                  uint32_t width);

enum class DpiPointerAccessStep : uint8_t {
  kComputeTheElementsAddress,
  kAccessTheElementThroughIt,
};

std::array<DpiPointerAccessStep, 2> DpiPointerAccessSteps();

DpiArg DpiPackedAggregateAsPackedArrayFormal(const DpiArg& aggregate,
                                             bool four_state, uint32_t width);

enum class DpiTwoStateTechnique : uint8_t { kCCompatibleFormal, kCanonical };

bool DpiCCompatibleFormalCanHoldTwoStateVector(uint32_t width);

DpiTwoStateTechnique DpiTechniqueRequiredForTwoStateVector(uint32_t width);

bool DpiTechniqueIsMoreEfficient(DpiTwoStateTechnique technique,
                                 DpiTwoStateTechnique other);

std::string DpiCDeclarationOfAggregateMember(
    std::string_view name, DataTypeKind kind,
    const std::vector<SvActualDimension>& packed_dims,
    const std::vector<SvActualDimension>& unpacked_dims);

std::string_view DpiCLayerIncludeFile();
uint32_t DpiCLayerIncludeFileCount();
bool DpiCLayerIncludeFileIsImplementationIndependent();

enum class DpiIncludeFileContent : uint8_t {
  kCanonicalRepresentation,
  kBasicTypes,
  kInterfaceFunctions,
};

bool DpiIncludeFileDefines(DpiIncludeFileContent content);

std::string_view DpiAnnexShowingIncludeFile();

}  // namespace delta
