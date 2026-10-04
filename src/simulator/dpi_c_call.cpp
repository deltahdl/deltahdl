#include "simulator/dpi_c_call.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"
#include "simulator/dpi_runtime.h"
#include "simulator/svdpi_open_array.h"

namespace delta {

namespace {

// The C object a formal or a result is held in on this side of a call: one of
// Table H.1's types (§H.7.4), a string's const char*, a scalar bit or logic's
// svBit or svLogic, or the canonical array of a packed value (§H.7.7), words
// of svBitVecVal for a 2-state one and pairs of svLogicVecVal for a 4-state
// one.
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
  // §H.7.3: a sized unpacked array, its elements laid out one after another
  // as C lays out an array of the element's own C object.
  kArray,
  // §H.7.8: an unpacked struct or union, its members laid out as the C
  // compiler lays them out.
  kAggregate,
  // §H.8.6: an open array, passed by the handle of a descriptor (§H.12)
  // over its elements laid out as svdpi.cpp reads them.
  kOpenArray,
};

// Table H.1: the object a small type is held in. An int, and the int an
// imported task returns (§35.9) where the declaration gives no result, take
// the int.
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

// The object one element of `formal` is held in -- the formal itself where it
// has no unpacked dimension -- or none where it is of a type whose C layout is
// not built here: one this side cannot see through to its C type, or an
// unpacked struct or union whose members it does not know.
std::optional<DpiCObject> ObjectOfElement(const DpiArg& formal) {
  if (!formal.members.empty()) {
    // §H.7.8: an unpacked struct or union has the C compiler's layout of its
    // members, so it is built where each member is.
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

// The object a formal is held in, or none where its C layout is not built
// here (ObjectOfElement).
DpiArg ElementOf(const DpiArg& formal);

std::optional<DpiCObject> ObjectOfFormal(const DpiArg& formal) {
  if (!formal.has_unpacked_dimensions) return ObjectOfElement(formal);
  if (formal.is_open_array) {
    if (!ObjectOfElement(ElementOf(formal)).has_value()) return std::nullopt;
    return DpiCObject::kOpenArray;
  }
  // §H.7.3: a stand-alone array passed to a sized formal has the C layout of
  // an array of its elements, so it is built where every dimension is sized
  // and the element is an object built here. An open array (§35.5.6.1), and
  // an array of structs or unions, are not built yet.
  if (formal.unpacked_dims.empty() || !formal.members.empty() ||
      !ObjectOfElement(formal).has_value()) {
    return std::nullopt;
  }
  return DpiCObject::kArray;
}

// One element of the unpacked formal `formal`. svdpi.cpp reads a scalar bit
// or logic element of an open array as one canonical chunk (§H.12.5), so such
// an element is held as the one-bit packed array.
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

// The count of elements the sized unpacked dimensions of `formal` hold, 1 for
// a formal with none.
std::size_t ElementCount(const DpiArg& formal) {
  std::size_t count = 1;
  for (const SvActualDimension& dim : formal.unpacked_dims) {
    count *= static_cast<std::size_t>(dim.high - dim.low + 1);
  }
  return count;
}

// §H.7.8: where the C compiler places each member of an unpacked struct or
// union, how big the whole is, and the alignment it takes.
struct DpiCAggregateLayout {
  std::vector<std::size_t> offsets;
  std::size_t size = 0;
  std::size_t alignment = 1;
};

DpiCAggregateLayout LayoutOf(const DpiArg& formal);

// The bytes one element of `formal` takes in C: its own C type's size, the
// canonical array of a packed one (DpiCElementBytes), or an aggregate's size.
std::size_t ElementBytes(const DpiArg& formal) {
  if (!formal.members.empty()) return LayoutOf(formal).size;
  return DpiCElementBytes(formal);
}

// The alignment of one element of `formal`: a basic C type's own size, an
// svBitVecVal or svLogicVecVal chunk's 4 for a packed one, and the largest
// of its members' for an aggregate.
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

// §H.7.3: the width of a packed formal, which integer and time carry in
// their type and a bit, logic or reg array in its declaration.
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

// §H.12.2: dimension 0 of an open array's descriptor, the packed part of its
// element normalized to [n-1:0] (§H.7.5) -- a scalar's [0:0], and none for
// an element with no packed part.
SvOpenArrayDimRange PackedRangeOf(const DpiArg& formal) {
  switch (formal.type) {
    case DataTypeKind::kBit:
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
      return {static_cast<int>(std::max<uint32_t>(formal.width, 1)) - 1, 0};
    case DataTypeKind::kByte:
      return {7, 0};
    case DataTypeKind::kShortint:
      return {15, 0};
    case DataTypeKind::kInt:
    case DataTypeKind::kInteger:
      return {31, 0};
    case DataTypeKind::kLongint:
    case DataTypeKind::kTime:
      return {63, 0};
    default:
      return {0, 0};
  }
}

// §H.7.7: the bits of the last chunk of a canonical array beyond the width are
// undetermined, so a value read out of one keeps only the bits within it.
uint32_t UsedBitsMask(uint32_t width) {
  return ~0U >> ((32U - (width % 32U)) % 32U);
}

// The C objects of one formal or result for the length of a call. The union's
// first member is the widest, so zeroing the union zeroes all of it.
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
  // An array's or an aggregate's bytes as C lays them out, and the object of
  // each of its parts -- an array's elements, an aggregate's members -- with
  // the part's offset, size and type. The objects keep a string part's
  // characters alive for the call.
  std::vector<unsigned char> bytes;
  std::vector<DpiCStorage> parts;
  std::vector<std::size_t> offsets;
  std::vector<std::size_t> sizes;
  std::vector<DataTypeKind> kinds;
  // An open array's descriptor and the dimensions it points at, dimension 0
  // the packed part (§H.12.2), with the stride svGetArrElemPtr steps by: 0
  // where an element is not held as an individual value of its type is.
  std::vector<SvOpenArrayDimRange> ranges;
  SvOpenArrayDesc desc{};
  std::size_t element_stride = 0;

  // The address a trampoline reads a formal passed by value out of, hands a
  // formal passed by reference, or stores the result at.
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
        // An open array's handle is held in the scalar, and crosses by value.
        return &scalar;
    }
  }
};

// Readies `storage` to hold `formal`: the object it is held in and, for an
// array or an aggregate, the object of each part at the offset C gives it
// (§H.7.6 c), §H.7.8).
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
    storage.ranges.push_back(PackedRangeOf(formal));
    // §H.12.4: a scalar bit or logic element is held as a canonical chunk,
    // not as the svBit or svLogic an individual value is.
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

// §H.10.1.2: `value`, of the packed type `kind`, as the canonical array of
// `width` bits. A bit, logic or reg array arrives already in that form; an
// integer arrives as its one aval/bval pair and a time as the 64 bits of a
// longint.
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
    // A one-bit packed array arrives as the scalar of its kind (§H.7.3).
    words[0].aval = value.AsBit() & 1U;
  } else if (value.type == DataTypeKind::kLogic ||
             value.type == DataTypeKind::kReg) {
    // §H.10.1.2: sv_0, sv_1, sv_z and sv_x are aval/bval 00, 10, 01 and 11.
    const auto kCode = static_cast<uint32_t>(value.AsLogic());
    words[0] = {kCode & 1U, (kCode >> 1U) & 1U};
  } else {
    const auto kBits = static_cast<uint64_t>(value.AsLongint());
    words[0].aval = static_cast<uint32_t>(kBits);
    if (words.size() > 1) words[1].aval = static_cast<uint32_t>(kBits >> 32U);
  }
  return words;
}

// §H.7.7: the svBitVecVal words of a 2-state canonical array, the avals of
// the pairs `words` hold.
std::vector<uint32_t> AvalsOf(const std::vector<SvLogicVecVal>& words) {
  std::vector<uint32_t> avals;
  avals.reserve(words.size());
  for (const SvLogicVecVal& word : words) avals.push_back(word.aval);
  return avals;
}

// The 2-state canonical array `bits` as pairs of aval and bval, every bval 0.
std::vector<SvLogicVecVal> PairsOf(const std::vector<uint32_t>& bits) {
  std::vector<SvLogicVecVal> words;
  words.reserve(bits.size());
  for (uint32_t word : bits) words.push_back({word, 0});
  return words;
}

void StoreValue(DpiCStorage& storage, DataTypeKind kind,
                const DpiArgValue& value);

// Lays the parts of `value` -- an array's elements, an aggregate's members --
// out in the parts `storage` holds, each at its offset; a part `value` does
// not carry, an output's, is laid out as the zero of its type.
void StoreParts(DpiCStorage& storage, const DpiArgValue& value) {
  for (std::size_t k = 0; k < storage.parts.size(); ++k) {
    DpiCStorage& part = storage.parts[k];
    StoreValue(part, storage.kinds[k],
               k < value.elements.size() ? value.elements[k] : DpiArgValue{});
    std::memcpy(storage.bytes.data() + storage.offsets[k], part.Address(),
                storage.sizes[k]);
  }
}

// §35.6.1.1 with §H.12: sizes the open array `storage` holds to the ranges
// of the actual `value` carries, lays its elements out, each dimension from
// its left bound, and points the descriptor the handle names at them.
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

// Lays `value` out in the C objects `storage` holds for a formal of `kind`.
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
      // §H.8.10: the characters are laid out as a C string, and the pointer is
      // what crosses.
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
      // DpiCObject::kLogicVector, the one object left.
      storage.logic = CanonicalWordsOf(value, kind, storage.width);
      break;
  }
}

// The canonical array `words`, `width` bits of it, as a value of the packed
// type `kind`: an integer is its one aval/bval pair, and a time and a bit,
// logic or reg array the array itself, a time's unknown bits with it (§H.7.3).
DpiArgValue PackedValueOf(std::vector<SvLogicVecVal> words, DataTypeKind kind,
                          uint32_t width) {
  words.back().aval &= UsedBitsMask(width);
  words.back().bval &= UsedBitsMask(width);
  if (kind == DataTypeKind::kInteger)
    return DpiArgValue::FromLogicVec(words[0]);
  return DpiArgValue::FromLogicVecWords(std::move(words), width, kind);
}

DpiArgValue LoadValue(const DpiCStorage& storage, DataTypeKind kind);

// What the array or aggregate `storage` holds, part by part.
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

// What the C objects of `storage` hold, as a value of `kind`.
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
      // §H.8.10: SystemVerilog copies the characters the pointer the C side
      // left names; a C side that left none has given no characters.
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
      // The actual's shape goes back with what C left in it.
      DpiArgValue open = LoadParts(storage, kind);
      for (std::size_t d = 1; d < storage.ranges.size(); ++d) {
        open.ranges.push_back(
            {storage.ranges[d].left, storage.ranges[d].right});
      }
      return open;
    }
    default:
      // DpiCObject::kLogicVector, the one object left.
      return PackedValueOf(storage.logic, kind, storage.width);
  }
  value.type = kind;
  return value;
}

// The C type a formal takes in the trampoline's call and the expression that
// passes it: the formal's own C type read out of its object for one passed by
// value, and the object's address, as a void*, for one passed by reference --
// a pointer being passed alike whatever it points at.
struct DpiCParameter {
  std::string type;
  std::string argument;
};

DpiCParameter ParameterOf(const DpiArg& formal, std::size_t index) {
  const std::string kObject = "args[" + std::to_string(index) + "]";
  // §H.8.6: an open array crosses as its handle, by value in every direction.
  if (formal.is_open_array) return {"void*", "*(void**)" + kObject};
  if (!DpiFormalIsPassedByValue(formal, false)) return {"void*", kObject};
  const std::string kType = DpiCTypeOfFormal(formal, false);
  return {kType, "*(" + kType + "*)" + kObject};
}

// The trampoline of one import: casts the symbol to the prototype §H.8 gives
// the import and calls it, storing a result where there is one. An imported
// task returns the int §35.9 gives it.
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

// The bytes the C object `object` takes where it holds a value outright.
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

// The bytes the C objects of `storage` take, laid out as C reads them.
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

// The forwarder of one export: under the export's linkage name, each formal
// passed by value as its own C type and every other as a pointer, which is
// one in the calling convention whatever it points at, handing the address of
// each to the entry point.
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
  // §35.8: an exported task returns the int that says whether a disable is
  // active.
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
  // §35.9: an imported task returns the int that says whether it was
  // disabled, whatever its declaration names as a result.
  if (!import.is_task && !DpiTypeMayBeAResult(import.return_type)) {
    return "its result type is not one §H.8.9 lets a C function return";
  }
  return "";
}

std::string DpiCTrampolineSource(
    const std::vector<const DpiRtFunction*>& imports) {
  // svdpi.h's names for the C types of a scalar bit and logic (§H.10.1.1);
  // every other type a trampoline names is a C type of its own.
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
    // Only an import DpiImportNotCallableInC accepted is bound, so every formal
    // here has an object; the int is never taken.
    Prepare(objects[i], formal);
    StoreValue(objects[i], formal.type, args[i]);
    addresses[i] = objects[i].Address();
  }
  // §35.5.5: a function with no result, and a task, return no value the call
  // site reads; the int an imported task returns is held and not read.
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
    if (formal.is_open_array || !formal.members.empty() ||
        !ObjectOfFormal(formal).has_value()) {
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
  // Laying a value out first sizes the objects C's are read into.
  StoreValue(storage, formal.type, DpiArgValue{});
  std::memcpy(storage.Address(), object, ObjectBytes(storage));
  return LoadValue(storage, formal.type);
}

void DpiStoreInCObject(const DpiArg& formal, const DpiArgValue& value,
                       void* object) {
  DpiCStorage storage;
  Prepare(storage, formal);
  StoreValue(storage, formal.type, value);
  std::memcpy(object, storage.Address(), ObjectBytes(storage));
}

void DpiStoreResultInCObject(DataTypeKind kind, const DpiArgValue& value,
                             void* result) {
  if (kind == DataTypeKind::kVoid || result == nullptr) return;
  DpiCStorage storage;
  storage.object = ObjectOfSmallKind(kind);
  StoreValue(storage, kind, value);
  std::memcpy(result, storage.Address(), ScalarBytes(storage.object));
}
}  // namespace delta
