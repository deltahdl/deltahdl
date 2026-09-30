#include "simulator/dpi_c_call.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"
#include "simulator/dpi_runtime.h"

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

// The object a formal is held in, or none where the formal is of a type whose
// C layout is not built here: §H.7.3 lays an unpacked array and an unpacked
// struct out as C does and an open array behind a handle, and none of those,
// nor a type this side cannot see through to its C type, is a small value or
// a packed array.
std::optional<DpiCObject> ObjectOfFormal(const DpiArg& formal) {
  if (formal.has_unpacked_dimensions) return std::nullopt;
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

  // The address a trampoline reads a formal passed by value out of, hands a
  // formal passed by reference, or stores the result at.
  void* Address() {
    switch (object) {
      case DpiCObject::kBitVector:
        return bits.data();
      case DpiCObject::kLogicVector:
        return logic.data();
      default:
        return &scalar;
    }
  }
};

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
  } else {
    const auto kBits = static_cast<uint64_t>(value.AsLongint());
    words[0].aval = static_cast<uint32_t>(kBits);
    words[1].aval = static_cast<uint32_t>(kBits >> 32U);
  }
  return words;
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
    case DpiCObject::kBitVector: {
      const std::vector<SvLogicVecVal> kWords =
          CanonicalWordsOf(value, kind, storage.width);
      storage.bits.resize(kWords.size());
      for (std::size_t i = 0; i < kWords.size(); ++i) {
        storage.bits[i] = kWords[i].aval;
      }
      break;
    }
    case DpiCObject::kLogicVector:
      storage.logic = CanonicalWordsOf(value, kind, storage.width);
      break;
  }
}

// The canonical array `words`, `width` bits of it, as a value of the packed
// type `kind`: an integer is its one aval/bval pair, a time the longint its
// two words' avals make, and a bit, logic or reg array the array itself.
DpiArgValue PackedValueOf(std::vector<SvLogicVecVal> words, DataTypeKind kind,
                          uint32_t width) {
  words.back().aval &= UsedBitsMask(width);
  words.back().bval &= UsedBitsMask(width);
  if (kind == DataTypeKind::kInteger)
    return DpiArgValue::FromLogicVec(words[0]);
  if (kind == DataTypeKind::kTime) {
    DpiArgValue time = DpiArgValue::FromLongint(static_cast<int64_t>(
        (static_cast<uint64_t>(words[1].aval) << 32U) | words[0].aval));
    time.type = kind;
    return time;
  }
  return DpiArgValue::FromLogicVecWords(std::move(words), width, kind);
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
    case DpiCObject::kBitVector: {
      std::vector<SvLogicVecVal> words;
      words.reserve(storage.bits.size());
      for (uint32_t word : storage.bits) words.push_back({word, 0});
      return PackedValueOf(std::move(words), kind, storage.width);
    }
    case DpiCObject::kLogicVector:
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
  if (!DpiTypeMayBeAResult(import.return_type)) {
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
    objects[i].object = ObjectOfFormal(formal).value_or(DpiCObject::kInt);
    objects[i].width = PackedWidthOf(formal);
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

}  // namespace delta
