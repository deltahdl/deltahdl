#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <cstring>
#include <string>
#include <vector>

#include "helpers_dpi_c_binding.h"
#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"
#include "simulator/dpi_runtime.h"

using namespace delta;

namespace {

// §H.8.10 (item 1): when a string value is passed from SystemVerilog to C, the
// simulator lays the characters out per C-string conventions, including a
// trailing null terminator. The foreign function inspects the value as a C
// string and confirms that strlen finds the full length, the byte one past the
// end is a null, and every character matches the SystemVerilog source.
TEST(DpiStringArguments, ImportInputStringDeliveredAsNullTerminatedCString) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_inspect";
  func.sv_name = "sv_inspect";
  func.return_type = DataTypeKind::kInt;
  func.args = {DpiArg{"s", DataTypeKind::kString, Direction::kInput}};
  func.arg_impl = [](std::vector<DpiArgValue>& args) -> DpiArgValue {
    const std::string& sv = args[0].AsString();
    const char* c = sv.c_str();
    // C-string view of the delivered value: length terminates at the null.
    EXPECT_EQ(std::strlen(c), sv.size());
    EXPECT_EQ(c[sv.size()], '\0');
    EXPECT_EQ(std::memcmp(c, "world", 5), 0);
    return DpiArgValue::FromInt(static_cast<int32_t>(std::strlen(c)));
  };
  rt.RegisterImport(func);

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromString("world")};
  auto result = rt.CallImportWithArgs("sv_inspect", actuals);
  EXPECT_EQ(result.AsInt(), 5);
}

// §H.8.10 (item 1, edge case): an empty SystemVerilog string still reaches C as
// a valid null-terminated C string of length zero — the first byte is the
// terminator.
TEST(DpiStringArguments, ImportEmptyStringDeliveredAsNullTerminatedCString) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_empty";
  func.sv_name = "sv_empty";
  func.return_type = DataTypeKind::kInt;
  func.args = {DpiArg{"s", DataTypeKind::kString, Direction::kInput}};
  func.arg_impl = [](std::vector<DpiArgValue>& args) -> DpiArgValue {
    const char* c = args[0].AsString().c_str();
    EXPECT_EQ(c[0], '\0');
    EXPECT_EQ(std::strlen(c), 0u);
    return DpiArgValue::FromInt(static_cast<int32_t>(std::strlen(c)));
  };
  rt.RegisterImport(func);

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromString("")};
  auto result = rt.CallImportWithArgs("sv_empty", actuals);
  EXPECT_EQ(result.AsInt(), 0);
}

// §H.8.10 (item 4, imported input): for an input mode string, changes the
// foreign code makes to the pointer value it received are not propagated back
// to SystemVerilog. The runtime passes inputs by value, so overwriting the
// local copy leaves the caller's actual unchanged.
TEST(DpiStringArguments, ImportInputStringPointerWriteNotPropagated) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_clobber";
  func.sv_name = "sv_clobber";
  func.return_type = DataTypeKind::kVoid;
  func.args = {DpiArg{"s", DataTypeKind::kString, Direction::kInput}};
  func.arg_impl = [](std::vector<DpiArgValue>& args) -> DpiArgValue {
    args[0] = DpiArgValue::FromString("rewritten");
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(func);

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromString("original")};
  rt.CallImportWithArgs("sv_clobber", actuals);
  EXPECT_EQ(actuals[0].AsString(), "original");
}

// §H.8.10 (item 4, imported output): an output mode string does not arrive with
// a meaningful value; the foreign code writes a valid string that SystemVerilog
// then observes. The runtime seeds the output with an undetermined (empty)
// value rather than the actual, and copies the foreign-written string back.
TEST(DpiStringArguments, ImportOutputStringWrittenBackToActual) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_produce";
  func.sv_name = "sv_produce";
  func.return_type = DataTypeKind::kVoid;
  func.args = {DpiArg{"s", DataTypeKind::kString, Direction::kOutput}};
  func.arg_impl = [](std::vector<DpiArgValue>& args) -> DpiArgValue {
    // The output arrives with no meaningful value, not the caller's actual.
    EXPECT_TRUE(args[0].AsString().empty());
    args[0] = DpiArgValue::FromString("produced");
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(func);

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromString("seed-ignored")};
  rt.CallImportWithArgs("sv_produce", actuals);
  EXPECT_EQ(actuals[0].AsString(), "produced");
}

// §H.8.10 (item 4, imported output, edge case): an output mode string carries
// no meaningful value on arrival, so the caller's actual is not handed in. When
// the foreign code writes nothing, the actual is left holding the undetermined
// (empty) seed rather than its prior value — the original contents are
// discarded regardless of any foreign write.
TEST(DpiStringArguments,
     ImportOutputStringDiscardsActualWhenForeignWritesNothing) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_noop_out";
  func.sv_name = "sv_noop_out";
  func.return_type = DataTypeKind::kVoid;
  func.args = {DpiArg{"s", DataTypeKind::kString, Direction::kOutput}};
  func.arg_impl = [](std::vector<DpiArgValue>& args) -> DpiArgValue {
    // The output arrives empty, not carrying the caller's prior value, and the
    // foreign code deliberately leaves it untouched.
    EXPECT_TRUE(args[0].AsString().empty());
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(func);

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromString("stale")};
  rt.CallImportWithArgs("sv_noop_out", actuals);
  EXPECT_TRUE(actuals[0].AsString().empty());
}

// §H.8.10 (item 4, imported inout): an inout mode string arrives with a valid
// value the foreign code may read; when the foreign code supplies new contents,
// SystemVerilog copies them into its own space. The runtime copies the actual
// in and the foreign-written value back.
TEST(DpiStringArguments, ImportInoutStringContentsCopiedBack) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_revise";
  func.sv_name = "sv_revise";
  func.return_type = DataTypeKind::kVoid;
  func.args = {DpiArg{"s", DataTypeKind::kString, Direction::kInout}};
  func.arg_impl = [](std::vector<DpiArgValue>& args) -> DpiArgValue {
    // The inout value arrives readable, then is replaced by new contents.
    EXPECT_EQ(args[0].AsString(), "before");
    args[0] = DpiArgValue::FromString("after");
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(func);

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromString("before")};
  rt.CallImportWithArgs("sv_revise", actuals);
  EXPECT_EQ(actuals[0].AsString(), "after");
}

// §H.8.10 (item 1 + item 4, imported inout, edge case): an inout mode string is
// also handed to C in the SystemVerilog-to-C direction, so it arrives as a
// null-terminated C string. When the foreign code reads it but supplies no new
// value, the copy-back leaves the actual carrying its original contents intact.
TEST(DpiStringArguments,
     ImportInoutStringRoundTripsUnchangedWhenForeignLeavesItAlone) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_peek_inout";
  func.sv_name = "sv_peek_inout";
  func.return_type = DataTypeKind::kVoid;
  func.args = {DpiArg{"s", DataTypeKind::kString, Direction::kInout}};
  func.arg_impl = [](std::vector<DpiArgValue>& args) -> DpiArgValue {
    const std::string& sv = args[0].AsString();
    const char* c = sv.c_str();
    // The inbound inout value reads back as a null-terminated C string.
    EXPECT_EQ(std::strlen(c), sv.size());
    EXPECT_EQ(c[sv.size()], '\0');
    EXPECT_EQ(std::memcmp(c, "keep-me", 7), 0);
    // No new value is supplied; the actual must survive the call unchanged.
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(func);

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromString("keep-me")};
  rt.CallImportWithArgs("sv_peek_inout", actuals);
  EXPECT_EQ(actuals[0].AsString(), "keep-me");
}

// §H.8.10 as a statement about the C layer, in src/simulator/dpi_c_type.h:
// the direction of a string argument applies to the pointer and not to the
// characters, the side that provided a pointer owns the storage it refers
// to and the other side shall not free it, a receiver never modifies the
// characters, and a string to be kept beyond the call is copied.

DpiArg StringFormal(Direction direction) {
  DpiArg formal;
  formal.name = "s";
  formal.type = DataTypeKind::kString;
  formal.direction = direction;
  return formal;
}

// §H.8.10: the direction mode applies to the const char* pointer, so an
// input is a const char* and an output or inout a const char**, the
// characters const under every mode.
TEST(DpiStringArgumentRules, TheDirectionAppliesToThePointer) {
  EXPECT_EQ(DpiCTypeOfFormal(StringFormal(Direction::kInput), false),
            "const char*");
  EXPECT_EQ(DpiCTypeOfFormal(StringFormal(Direction::kOutput), false),
            "const char**");
  EXPECT_EQ(DpiCTypeOfFormal(StringFormal(Direction::kInout), false),
            "const char**");
  EXPECT_FALSE(DpiStringCharactersMayBeModifiedByReceiver());
}

// §H.8.10: the storage a string pointer refers to is the provider's -- for
// an import, SystemVerilog provides an input's and an inout's on arrival
// and C provides an output's and an inout's it changed; for an export, C
// provides an input's and an inout's on arrival and SystemVerilog provides
// an output's and an inout's it changed -- and the other side shall not
// free it.
TEST(DpiStringArgumentRules, TheSideThatProvidedThePointerOwnsTheStorage) {
  EXPECT_EQ(
      DpiSideProvidingStringPointer(DpiStringPointerProvider::kImportInput),
      DpiMemorySide::kSystemVerilog);
  EXPECT_EQ(
      DpiSideProvidingStringPointer(DpiStringPointerProvider::kImportOutput),
      DpiMemorySide::kC);
  EXPECT_EQ(DpiSideProvidingStringPointer(
                DpiStringPointerProvider::kImportInoutOnArrival),
            DpiMemorySide::kSystemVerilog);
  EXPECT_EQ(DpiSideProvidingStringPointer(
                DpiStringPointerProvider::kImportInoutChanged),
            DpiMemorySide::kC);
  EXPECT_EQ(
      DpiSideProvidingStringPointer(DpiStringPointerProvider::kExportInput),
      DpiMemorySide::kC);
  EXPECT_EQ(
      DpiSideProvidingStringPointer(DpiStringPointerProvider::kExportOutput),
      DpiMemorySide::kSystemVerilog);
  EXPECT_EQ(DpiSideProvidingStringPointer(
                DpiStringPointerProvider::kExportInoutOnArrival),
            DpiMemorySide::kC);
  EXPECT_EQ(DpiSideProvidingStringPointer(
                DpiStringPointerProvider::kExportInoutChanged),
            DpiMemorySide::kSystemVerilog);
  // Only the provider frees what it provided.
  EXPECT_FALSE(DpiSideMayFree(
      DpiSideProvidingStringPointer(DpiStringPointerProvider::kImportInput),
      DpiMemorySide::kC));
  EXPECT_FALSE(DpiSideMayFree(
      DpiSideProvidingStringPointer(DpiStringPointerProvider::kImportOutput),
      DpiMemorySide::kSystemVerilog));
  EXPECT_FALSE(DpiSideMayFree(
      DpiSideProvidingStringPointer(DpiStringPointerProvider::kExportOutput),
      DpiMemorySide::kC));
}

// §H.8.10: no assumption holds about the lifetime of a string's storage
// beyond the call, so a string to be kept is copied into memory the
// keeping side owns -- C for an export's output or changed inout, and
// SystemVerilog, which copies the contents of an import's changed inout
// into its own memory.
TEST(DpiStringArgumentRules, AStringToBeKeptIsCopiedByTheKeepingSide) {
  EXPECT_FALSE(DpiReferenceOutlivesTheCall());
  EXPECT_EQ(DpiSideCopyingString(DpiStringPointerProvider::kExportOutput),
            DpiMemorySide::kC);
  EXPECT_EQ(DpiSideCopyingString(DpiStringPointerProvider::kExportInoutChanged),
            DpiMemorySide::kC);
  EXPECT_EQ(DpiSideCopyingString(DpiStringPointerProvider::kImportInoutChanged),
            DpiMemorySide::kSystemVerilog);
  EXPECT_EQ(DpiSideCopyingString(DpiStringPointerProvider::kImportOutput),
            DpiMemorySide::kSystemVerilog);
}

// The C functions the imports below are bound to, each taking or giving a
// string as §H.8.10 has it cross.
int LengthOfInput(const char* s) { return static_cast<int>(std::strlen(s)); }
void PointOutputAtText(const char** o) { *o = "from C"; }
void PointOutputAtNothing(const char** o) { *o = nullptr; }
char shouted[16] = {};
void ShoutInout(const char** s) {
  std::size_t i = 0;
  for (; (*s)[i] != '\0' && i + 1 < sizeof(shouted); ++i) {
    shouted[i] = static_cast<char>((*s)[i] - 'a' + 'A');
  }
  shouted[i] = '\0';
  *s = shouted;
}
const char* ReturnText() { return "returned"; }

// §H.8.10: an input string reaches C as a const char* to its characters laid
// out as a C string; an output string's pointer is written by C and the
// characters it names are copied back, none where it names nothing; an inout
// arrives pointing at the string's characters and its new pointer's are
// copied back; and a string result is the pointer C returns, its characters
// copied likewise.
TEST(DpiStringArguments, EachDirectionAndTheResultCrossAsCStrings) {
  DpiCBinding b;
  b.dpi.RegisterImport(
      CImport("length_of_input", DataTypeKind::kInt,
              {CFormal("s", DataTypeKind::kString, Direction::kInput)}));
  b.dpi.RegisterImport(
      CImport("point_output_at_text", DataTypeKind::kVoid,
              {CFormal("o", DataTypeKind::kString, Direction::kOutput)}));
  b.dpi.RegisterImport(
      CImport("point_output_at_nothing", DataTypeKind::kVoid,
              {CFormal("o", DataTypeKind::kString, Direction::kOutput)}));
  b.dpi.RegisterImport(
      CImport("shout_inout", DataTypeKind::kVoid,
              {CFormal("s", DataTypeKind::kString, Direction::kInout)}));
  b.dpi.RegisterImport(CImport("return_text", DataTypeKind::kString, {}));
  b.Bind({{"length_of_input", reinterpret_cast<void*>(&LengthOfInput)},
          {"point_output_at_text", reinterpret_cast<void*>(&PointOutputAtText)},
          {"point_output_at_nothing",
           reinterpret_cast<void*>(&PointOutputAtNothing)},
          {"shout_inout", reinterpret_cast<void*>(&ShoutInout)},
          {"return_text", reinterpret_cast<void*>(&ReturnText)}},
         "annex_h_08_10_strings");
  ASSERT_TRUE(b.diag.Diagnostics().empty());
  std::vector<DpiArgValue> input = {DpiArgValue::FromString("hello")};
  EXPECT_EQ(b.Call("length_of_input", input).AsInt(), 5);
  std::vector<DpiArgValue> output = {DpiArgValue::FromString("seed")};
  b.Call("point_output_at_text", output);
  EXPECT_EQ(output[0].AsString(), "from C");
  std::vector<DpiArgValue> nothing = {DpiArgValue::FromString("seed")};
  b.Call("point_output_at_nothing", nothing);
  EXPECT_EQ(nothing[0].AsString(), "");
  std::vector<DpiArgValue> inout = {DpiArgValue::FromString("hello")};
  b.Call("shout_inout", inout);
  EXPECT_EQ(inout[0].AsString(), "HELLO");
  std::vector<DpiArgValue> none;
  EXPECT_EQ(b.Call("return_text", none).AsString(), "returned");
}

}  // namespace
