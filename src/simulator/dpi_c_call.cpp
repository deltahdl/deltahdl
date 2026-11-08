#include "simulator/dpi_c_call.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <optional>
#include <string>
#include <unordered_set>
#include <utility>
#include <vector>

#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"
#include "simulator/dpi_runtime.h"
#include "simulator/svdpi_open_array.h"

namespace delta {

namespace {

enum class DpiCObject : uint8_t {
  kChar,
  kShort,
  kInt,
  kLongLong,
  kFloat,
  kDouble,
  kPointer,
  kString,
  kScalar,
  kBitVector,
  kLogicVector,
  kArray,
  kAggregate,
  kOpenArray,
};

DpiCObject ObjectOfSmallKind(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kByte:
      return DpiCObject::kChar;
    case DataTypeKind::kShortint:
      return DpiCObject::kShort;
    case DataTypeKind::kLongint:
      return DpiCObject::kLongLong;
    case DataTypeKind::kShortreal:
      return DpiCObject::kFloat;
    case DataTypeKind::kReal:
    case DataTypeKind::kRealtime:
      return DpiCObject::kDouble;
    case DataTypeKind::kChandle:
      return DpiCObject::kPointer;
    case DataTypeKind::kString:
      return DpiCObject::kString;
    case DataTypeKind::kBit:
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
      return DpiCObject::kScalar;
    default:
      return DpiCObject::kInt;
  }
}

std::optional<DpiCObject> ObjectOfFormal(const DpiArg& formal);

std::optional<DpiCObject> ObjectOfElement(const DpiArg& formal) {
  if (!formal.members.empty()) {
    for (const DpiArg& member : formal.members) {
      if (!ObjectOfFormal(member).has_value()) return std::nullopt;
    }
    return DpiCObject::kAggregate;
  }
  switch (DpiCLayerTypeOfFormal(formal, false)) {
    case DpiCLayerType::kCanonicalElement:
      return formal.type == DataTypeKind::kBit ? DpiCObject::kBitVector
                                               : DpiCObject::kLogicVector;
    case DpiCLayerType::kBasic:
      return ObjectOfSmallKind(formal.type);
    default:
      return std::nullopt;
  }
}

DpiArg ElementOf(const DpiArg& formal);

std::optional<DpiCObject> ObjectOfFormal(const DpiArg& formal) {
  if (!formal.has_unpacked_dimensions) return ObjectOfElement(formal);
  if (formal.is_open_array) {
    if (!ObjectOfElement(ElementOf(formal)).has_value()) return std::nullopt;
    return DpiCObject::kOpenArray;
  }
  if (formal.unpacked_dims.empty() || !ObjectOfElement(formal).has_value()) {
    return std::nullopt;
  }
  return DpiCObject::kArray;
}

DpiArg ElementOf(const DpiArg& formal) {
  DpiArg element = formal;
  element.has_unpacked_dimensions = false;
  element.unpacked_dims.clear();
  element.is_open_array = false;
  if (formal.is_open_array && formal.members.empty()) {
    element.is_packed_array = formal.is_packed_array ||
                              formal.type == DataTypeKind::kBit ||
                              formal.type == DataTypeKind::kLogic ||
                              formal.type == DataTypeKind::kReg;
    if (element.is_packed_array && element.width == 0) element.width = 1;
  }
  return element;
}

std::size_t ElementCount(const DpiArg& formal) {
  std::size_t count = 1;
  for (const SvActualDimension& dim : formal.unpacked_dims) {
    count *= static_cast<std::size_t>(dim.high - dim.low + 1);
  }
  return count;
}

struct DpiCAggregateLayout {
  std::vector<std::size_t> offsets;
  std::size_t size = 0;
  std::size_t alignment = 1;
};

DpiCAggregateLayout LayoutOf(const DpiArg& formal);

std::size_t ElementBytes(const DpiArg& formal) {
  if (!formal.members.empty()) return LayoutOf(formal).size;
  return DpiCElementBytes(formal);
}

std::size_t AlignmentOf(const DpiArg& formal) {
  if (!formal.members.empty()) return LayoutOf(formal).alignment;
  if (DpiCLayerTypeOfFormal(formal, false) ==
      DpiCLayerType::kCanonicalElement) {
    return sizeof(SvBitVecVal);
  }
  return std::max<std::size_t>(DpiCElementBytes(formal), 1);
}

std::size_t RoundUp(std::size_t value, std::size_t alignment) {
  return (value + alignment - 1) / alignment * alignment;
}

DpiCAggregateLayout LayoutOf(const DpiArg& formal) {
  DpiCAggregateLayout layout;
  const bool kUnion = formal.type == DataTypeKind::kUnion;
  std::size_t end = 0;
  for (const DpiArg& member : formal.members) {
    const std::size_t kAlignment = AlignmentOf(member);
    const std::size_t kBytes = ElementBytes(member) * ElementCount(member);
    const std::size_t kOffset = kUnion ? 0 : RoundUp(end, kAlignment);
    layout.offsets.push_back(kOffset);
    end = std::max(end, kOffset + kBytes);
    layout.alignment = std::max(layout.alignment, kAlignment);
  }
  layout.size = RoundUp(end, layout.alignment);
  return layout;
}

uint32_t PackedWidthOf(const DpiArg& formal) {
  switch (formal.type) {
    case DataTypeKind::kInteger:
      return 32;
    case DataTypeKind::kTime:
      return 64;
    default:
      return formal.width;
  }
}

std::optional<SvOpenArrayDimRange> PackedRangeOf(const DpiArg& formal) {
  switch (formal.type) {
    case DataTypeKind::kBit:
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
      return SvOpenArrayDimRange{
          static_cast<int>(std::max<uint32_t>(formal.width, 1)) - 1, 0};
    case DataTypeKind::kByte:
      return SvOpenArrayDimRange{7, 0};
    case DataTypeKind::kShortint:
      return SvOpenArrayDimRange{15, 0};
    case DataTypeKind::kInt:
    case DataTypeKind::kInteger:
      return SvOpenArrayDimRange{31, 0};
    case DataTypeKind::kLongint:
    case DataTypeKind::kTime:
      return SvOpenArrayDimRange{63, 0};
    default:
      return std::nullopt;
  }
}

uint32_t UsedBitsMask(uint32_t width) {
  return ~0U >> ((32U - (width % 32U)) % 32U);
}

struct DpiCStorage {
  DpiCObject object = DpiCObject::kInt;
  uint32_t width = 0;
  union Scalar {
    long long ll;
    char c;
    short s;
    int i;
    float f;
    double d;
    void* p;
    const char* str;
    unsigned char u8;
  } scalar{};
  std::vector<uint32_t> bits;
  std::vector<SvLogicVecVal> logic;
  std::string text;
  std::vector<unsigned char> bytes;
  std::vector<DpiCStorage> parts;
  std::vector<std::size_t> offsets;
  std::vector<std::size_t> sizes;
  std::vector<DataTypeKind> kinds;
  std::vector<SvOpenArrayDimRange> ranges;
  SvOpenArrayDesc desc{};
  std::size_t element_stride = 0;

  void* Address() {
    switch (object) {
      case DpiCObject::kBitVector:
        return bits.data();
      case DpiCObject::kLogicVector:
        return logic.data();
      case DpiCObject::kArray:
      case DpiCObject::kAggregate:
        return bytes.data();
      default:
        return &scalar;
    }
  }
};

void Prepare(DpiCStorage& storage, const DpiArg& formal) {
  storage.object = ObjectOfFormal(formal).value_or(DpiCObject::kInt);
  storage.width = PackedWidthOf(formal);
  if (storage.object == DpiCObject::kArray) {
    const DpiArg kElement = ElementOf(formal);
    DpiCStorage element;
    Prepare(element, kElement);
    const std::size_t kBytes = ElementBytes(kElement);
    const std::size_t kCount = ElementCount(formal);
    storage.parts.assign(kCount, element);
    for (std::size_t k = 0; k < kCount; ++k) {
      storage.offsets.push_back(k * kBytes);
    }
    storage.sizes.assign(kCount, kBytes);
    storage.kinds.assign(kCount, formal.type);
    storage.bytes.assign(kCount * kBytes, 0);
  } else if (storage.object == DpiCObject::kOpenArray) {
    const DpiArg kElement = ElementOf(formal);
    storage.parts.emplace_back();
    Prepare(storage.parts.back(), kElement);
    storage.sizes.push_back(ElementBytes(kElement));
    storage.kinds.push_back(formal.type);
    const std::optional<SvOpenArrayDimRange> kPacked = PackedRangeOf(formal);
    storage.ranges.push_back(kPacked.value_or(SvOpenArrayDimRange{0, 0}));
    storage.desc.has_packed_part = kPacked.has_value() ? 1 : 0;
    storage.element_stride =
        kElement.is_packed_array && !formal.is_packed_array && formal.width <= 1
            ? 0
            : ElementBytes(kElement);
  } else if (storage.object == DpiCObject::kAggregate) {
    const DpiCAggregateLayout kLayout = LayoutOf(formal);
    for (const DpiArg& member : formal.members) {
      storage.parts.emplace_back();
      Prepare(storage.parts.back(), member);
      storage.sizes.push_back(ElementBytes(member) * ElementCount(member));
      storage.kinds.push_back(member.type);
    }
    storage.offsets = kLayout.offsets;
    storage.bytes.assign(kLayout.size, 0);
  }
}

std::vector<SvLogicVecVal> CanonicalWordsOf(const DpiArgValue& value,
                                            DataTypeKind kind, uint32_t width) {
  std::vector<SvLogicVecVal> words(DpiCanonicalWordCount(width),
                                   SvLogicVecVal{0, 0});
  if (value.IsWideVec()) {
    const std::vector<SvLogicVecVal>& from = value.AsLogicVecWords();
    std::copy_n(from.begin(), std::min(from.size(), words.size()),
                words.begin());
  } else if (kind == DataTypeKind::kInteger) {
    words[0] = value.AsLogicVec();
  } else if (value.type == DataTypeKind::kBit) {
    words[0].aval = value.AsBit() & 1U;
  } else if (value.type == DataTypeKind::kLogic ||
             value.type == DataTypeKind::kReg) {
    const auto kCode = static_cast<uint32_t>(value.AsLogic());
    words[0] = {kCode & 1U, (kCode >> 1U) & 1U};
  } else {
    const auto kBits = static_cast<uint64_t>(value.AsLongint());
    words[0].aval = static_cast<uint32_t>(kBits);
    if (words.size() > 1) words[1].aval = static_cast<uint32_t>(kBits >> 32U);
  }
  return words;
}

std::vector<uint32_t> AvalsOf(const std::vector<SvLogicVecVal>& words) {
  std::vector<uint32_t> avals;
  avals.reserve(words.size());
  for (const SvLogicVecVal& word : words) avals.push_back(word.aval);
  return avals;
}

std::vector<SvLogicVecVal> PairsOf(const std::vector<uint32_t>& bits) {
  std::vector<SvLogicVecVal> words;
  words.reserve(bits.size());
  for (uint32_t word : bits) words.push_back({word, 0});
  return words;
}

void StoreValue(DpiCStorage& storage, DataTypeKind kind,
                const DpiArgValue& value);

void StoreParts(DpiCStorage& storage, const DpiArgValue& value) {
  for (std::size_t k = 0; k < storage.parts.size(); ++k) {
    DpiCStorage& part = storage.parts[k];
    StoreValue(part, storage.kinds[k],
               k < value.elements.size() ? value.elements[k] : DpiArgValue{});
    std::memcpy(storage.bytes.data() + storage.offsets[k], part.Address(),
                storage.sizes[k]);
  }
}

void StoreOpen(DpiCStorage& storage, const DpiArgValue& value) {
  const DpiCStorage kElement = storage.parts.front();
  const std::size_t kBytes = storage.sizes.front();
  const DataTypeKind kKind = storage.kinds.front();
  std::size_t count = value.ranges.empty() ? 0 : 1;
  storage.ranges.resize(1);
  for (const DpiArrayRange& range : value.ranges) {
    count *= static_cast<std::size_t>(std::abs(range.left - range.right) + 1);
    storage.ranges.push_back({range.left, range.right});
  }
  storage.parts.assign(count, kElement);
  storage.offsets.clear();
  for (std::size_t k = 0; k < count; ++k) {
    storage.offsets.push_back(k * kBytes);
  }
  storage.sizes.assign(count, kBytes);
  storage.kinds.assign(count, kKind);
  storage.bytes.assign(count * kBytes, 0);
  StoreParts(storage, value);
  storage.desc.data = storage.bytes.data();
  storage.desc.n_dims = static_cast<int>(storage.ranges.size());
  storage.desc.ranges = storage.ranges.data();
  storage.desc.elem_size = storage.element_stride;
  storage.scalar.p = &storage.desc;
}

void StoreValue(DpiCStorage& storage, DataTypeKind kind,
                const DpiArgValue& value) {
  switch (storage.object) {
    case DpiCObject::kChar:
      storage.scalar.c = static_cast<char>(value.AsInt());
      break;
    case DpiCObject::kShort:
      storage.scalar.s = static_cast<short>(value.AsInt());
      break;
    case DpiCObject::kInt:
      storage.scalar.i = value.AsInt();
      break;
    case DpiCObject::kLongLong:
      storage.scalar.ll = value.AsLongint();
      break;
    case DpiCObject::kFloat:
      storage.scalar.f = static_cast<float>(value.AsReal());
      break;
    case DpiCObject::kDouble:
      storage.scalar.d = value.AsReal();
      break;
    case DpiCObject::kPointer:
      storage.scalar.p = value.AsChandle();
      break;
    case DpiCObject::kString:
      storage.text = value.AsString();
      storage.scalar.str = storage.text.c_str();
      break;
    case DpiCObject::kScalar:
      storage.scalar.u8 =
          kind == DataTypeKind::kBit ? value.AsBit() : value.AsLogic();
      break;
    case DpiCObject::kBitVector:
      storage.bits = AvalsOf(CanonicalWordsOf(value, kind, storage.width));
      break;
    case DpiCObject::kArray:
    case DpiCObject::kAggregate:
      StoreParts(storage, value);
      break;
    case DpiCObject::kOpenArray:
      StoreOpen(storage, value);
      break;
    default:
      storage.logic = CanonicalWordsOf(value, kind, storage.width);
      break;
  }
}

DpiArgValue PackedValueOf(std::vector<SvLogicVecVal> words, DataTypeKind kind,
                          uint32_t width) {
  words.back().aval &= UsedBitsMask(width);
  words.back().bval &= UsedBitsMask(width);
  if (kind == DataTypeKind::kInteger)
    return DpiArgValue::FromLogicVec(words[0]);
  return DpiArgValue::FromLogicVecWords(std::move(words), width, kind);
}

DpiArgValue LoadValue(const DpiCStorage& storage, DataTypeKind kind);

DpiArgValue LoadParts(const DpiCStorage& storage, DataTypeKind kind) {
  DpiArgValue whole;
  whole.type = kind;
  for (std::size_t k = 0; k < storage.parts.size(); ++k) {
    DpiCStorage part = storage.parts[k];
    std::memcpy(part.Address(), storage.bytes.data() + storage.offsets[k],
                storage.sizes[k]);
    whole.elements.push_back(LoadValue(part, storage.kinds[k]));
  }
  return whole;
}

DpiArgValue LoadValue(const DpiCStorage& storage, DataTypeKind kind) {
  DpiArgValue value;
  switch (storage.object) {
    case DpiCObject::kChar:
      value = DpiArgValue::FromInt(storage.scalar.c);
      break;
    case DpiCObject::kShort:
      value = DpiArgValue::FromInt(storage.scalar.s);
      break;
    case DpiCObject::kInt:
      value = DpiArgValue::FromInt(storage.scalar.i);
      break;
    case DpiCObject::kLongLong:
      value = DpiArgValue::FromLongint(storage.scalar.ll);
      break;
    case DpiCObject::kFloat:
      value = DpiArgValue::FromReal(storage.scalar.f);
      break;
    case DpiCObject::kDouble:
      value = DpiArgValue::FromReal(storage.scalar.d);
      break;
    case DpiCObject::kPointer:
      value = DpiArgValue::FromChandle(storage.scalar.p);
      break;
    case DpiCObject::kString:
      value = DpiArgValue::FromString(
          storage.scalar.str == nullptr ? "" : storage.scalar.str);
      break;
    case DpiCObject::kScalar:
      value =
          kind == DataTypeKind::kBit
              ? DpiArgValue::FromBit(static_cast<SvBit>(storage.scalar.u8 & 1U))
              : DpiArgValue::FromLogic(storage.scalar.u8);
      break;
    case DpiCObject::kBitVector:
      return PackedValueOf(PairsOf(storage.bits), kind, storage.width);
    case DpiCObject::kArray:
    case DpiCObject::kAggregate:
      return LoadParts(storage, kind);
    case DpiCObject::kOpenArray: {
      DpiArgValue open = LoadParts(storage, kind);
      for (std::size_t d = 1; d < storage.ranges.size(); ++d) {
        open.ranges.push_back(
            {storage.ranges[d].left, storage.ranges[d].right});
      }
      return open;
    }
    default:
      return PackedValueOf(storage.logic, kind, storage.width);
  }
  value.type = kind;
  return value;
}

struct DpiCParameter {
  std::string type;
  std::string argument;
};

DpiCParameter ParameterOf(const DpiArg& formal, std::size_t index) {
  const std::string kObject = "args[" + std::to_string(index) + "]";
  if (formal.is_open_array) return {"void*", "*(void**)" + kObject};
  if (!DpiFormalIsPassedByValue(formal, false)) return {"void*", kObject};
  const std::string kType = DpiCTypeOfFormal(formal, false);
  return {kType, "*(" + kType + "*)" + kObject};
}

std::string TrampolineOf(const DpiRtFunction& import, std::size_t index) {
  std::string types;
  std::string arguments;
  for (std::size_t i = 0; i < import.args.size(); ++i) {
    const DpiCParameter kParameter = ParameterOf(import.args[i], i);
    const std::string kSeparator = i == 0 ? "" : ", ";
    types += kSeparator + kParameter.type;
    arguments += kSeparator + kParameter.argument;
  }
  if (types.empty()) types = "void";
  const std::string kResult =
      import.is_task ? "int" : DpiCTypeOfResult(import.return_type);
  const std::string kCall =
      "((" + kResult + " (*)(" + types + "))symbol)(" + arguments + ")";
  const std::string kStatement =
      kResult == "void" ? kCall : "*(" + kResult + "*)result = " + kCall;
  return "void " + DpiCTrampolineName(index) +
         "(void (*symbol)(void), void** args, void* result) {\n"
         "  (void)args;\n"
         "  (void)result;\n"
         "  " +
         kStatement + ";\n}\n";
}

std::size_t ScalarBytes(DpiCObject object) {
  switch (object) {
    case DpiCObject::kChar:
    case DpiCObject::kScalar:
      return 1;
    case DpiCObject::kShort:
      return sizeof(short);
    case DpiCObject::kLongLong:
      return sizeof(long long);
    case DpiCObject::kFloat:
      return sizeof(float);
    case DpiCObject::kDouble:
      return sizeof(double);
    case DpiCObject::kPointer:
    case DpiCObject::kString:
    case DpiCObject::kOpenArray:
      return sizeof(void*);
    default:
      return sizeof(int);
  }
}

std::size_t ObjectBytes(const DpiCStorage& storage) {
  switch (storage.object) {
    case DpiCObject::kBitVector:
      return storage.bits.size() * sizeof(uint32_t);
    case DpiCObject::kLogicVector:
      return storage.logic.size() * sizeof(SvLogicVecVal);
    case DpiCObject::kArray:
    case DpiCObject::kAggregate:
      return storage.bytes.size();
    default:
      return ScalarBytes(storage.object);
  }
}

std::string ForwarderOf(const DpiRtExport& exp, std::size_t index) {
  std::string parameters;
  std::string addresses;
  for (std::size_t i = 0; i < exp.args.size(); ++i) {
    const DpiArg& formal = exp.args[i];
    const std::string kName = "a" + std::to_string(i);
    if (i != 0) {
      parameters += ", ";
      addresses += ", ";
    }
    if (DpiFormalIsPassedByValue(formal, false)) {
      parameters.append(DpiCTypeOfFormal(formal, false)).append(" ");
      addresses += "(void*)&";
    } else {
      parameters +=
          formal.direction == Direction::kInput ? "const void* " : "void* ";
      addresses += "(void*)";
    }
    parameters += kName;
    addresses += kName;
  }
  if (parameters.empty()) {
    parameters = "void";
    addresses = "0";
  }
  const std::string kResult =
      exp.is_task ? "int" : DpiCTypeOfResult(exp.return_type);
  const std::string kIndex = std::to_string(index);
  std::string body = "  void* args[] = {" + addresses + "};\n";
  if (kResult == "void") {
    body += "  deltahdl_dpi_export_entry(" + kIndex + ", args, 0);\n";
  } else {
    body += "  " + kResult + " result;\n  deltahdl_dpi_export_entry(" + kIndex +
            ", args, &result);\n  return result;\n";
  }
  return kResult + " " + std::string(DpiGlobalName(exp)) + "(" + parameters +
         ") {\n" + body + "}\n";
}

const char* KeptForC(const std::string& text) {
  static std::unordered_set<std::string> kept;
  return kept.insert(text).first->c_str();
}

void KeepStringsForC(DpiCStorage& storage) {
  if (storage.object == DpiCObject::kString) {
    storage.scalar.str = KeptForC(storage.text);
  }
  for (std::size_t k = 0; k < storage.parts.size(); ++k) {
    KeepStringsForC(storage.parts[k]);
    std::memcpy(storage.bytes.data() + storage.offsets[k],
                storage.parts[k].Address(), storage.sizes[k]);
  }
}

}  // namespace

std::string DpiCTrampolineName(std::size_t index) {
  return "deltahdl_dpi_trampoline_" + std::to_string(index);
}

std::string DpiImportNotCallableInC(const DpiRtFunction& import) {
  for (const DpiArg& formal : import.args) {
    if (!ObjectOfFormal(formal).has_value()) {
      return "deltahdl does not yet lay out in C the type of its formal '" +
             std::string(formal.name) + "'";
    }
  }
  if (!import.is_task && !DpiTypeMayBeAResult(import.return_type)) {
    return "its result type is not one §H.8.9 lets a C function return";
  }
  return "";
}

std::string DpiCTrampolineSource(
    const std::vector<const DpiRtFunction*>& imports) {
  std::string source =
      "typedef unsigned char svBit;\n"
      "typedef unsigned char svLogic;\n";
  for (std::size_t i = 0; i < imports.size(); ++i) {
    source += TrampolineOf(*imports[i], i);
  }
  return source;
}

DpiArgValue CallDpiCFunction(const DpiCFunction& function,
                             std::vector<DpiArgValue>& args) {
  const std::size_t kCount = function.formals.size();
  std::vector<DpiCStorage> objects(kCount);
  std::vector<void*> addresses(kCount);
  for (std::size_t i = 0; i < kCount; ++i) {
    const DpiArg& formal = function.formals[i];
    Prepare(objects[i], formal);
    StoreValue(objects[i], formal.type, args[i]);
    addresses[i] = objects[i].Address();
  }
  const DataTypeKind kResultKind = function.result == DataTypeKind::kVoid
                                       ? DataTypeKind::kInt
                                       : function.result;
  DpiCStorage result;
  result.object = ObjectOfSmallKind(kResultKind);
  function.trampoline(function.symbol, addresses.data(), result.Address());
  for (std::size_t i = 0; i < kCount; ++i) {
    const Direction kDirection = function.formals[i].direction;
    if (kDirection == Direction::kOutput || kDirection == Direction::kInout) {
      args[i] = LoadValue(objects[i], function.formals[i].type);
    }
  }
  return LoadValue(result, kResultKind);
}

std::string DpiExportNotCallableFromC(const DpiRtExport& exp) {
  for (const DpiArg& formal : exp.args) {
    if (formal.is_open_array || !ObjectOfFormal(formal).has_value()) {
      return "deltahdl does not yet pass to an exported subroutine the type "
             "of its formal '" +
             std::string(formal.name) + "'";
    }
  }
  if (!exp.is_task && !DpiTypeMayBeAResult(exp.return_type)) {
    return "its result type is not one §H.8.9 lets a C function return";
  }
  return "";
}

std::string DpiCExportEntrySetterName() {
  return "deltahdl_dpi_set_export_entry";
}

std::string DpiCForwarderSource(
    const std::vector<const DpiRtExport*>& exports) {
  if (exports.empty()) return "";
  std::string source =
      "static void (*deltahdl_dpi_export_entry)(int, void**, void*);\n"
      "void " +
      DpiCExportEntrySetterName() +
      "(void (*entry)(int, void**, void*)) {\n"
      "  deltahdl_dpi_export_entry = entry;\n}\n";
  for (std::size_t i = 0; i < exports.size(); ++i) {
    source += ForwarderOf(*exports[i], i);
  }
  return source;
}

DpiArgValue DpiValueOfCObject(const DpiArg& formal, const void* object) {
  DpiCStorage storage;
  Prepare(storage, formal);
  StoreValue(storage, formal.type, DpiArgValue{});
  std::memcpy(storage.Address(), object, ObjectBytes(storage));
  return LoadValue(storage, formal.type);
}

void DpiStoreInCObject(const DpiArg& formal, const DpiArgValue& value,
                       void* object) {
  DpiCStorage storage;
  Prepare(storage, formal);
  StoreValue(storage, formal.type, value);
  KeepStringsForC(storage);
  std::memcpy(object, storage.Address(), ObjectBytes(storage));
}

void DpiStoreResultInCObject(DataTypeKind kind, const DpiArgValue& value,
                             void* result) {
  if (kind == DataTypeKind::kVoid || result == nullptr) return;
  DpiCStorage storage;
  storage.object = ObjectOfSmallKind(kind);
  StoreValue(storage, kind, value);
  KeepStringsForC(storage);
  std::memcpy(result, storage.Address(), ScalarBytes(storage.object));
}
}  // namespace delta
