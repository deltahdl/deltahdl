#include <gtest/gtest.h>

#include <cstdint>
#include <cstring>
#include <string>
#include <vector>

#include "simulator/dpi_runtime.h"

using namespace delta;

namespace {

// §H.8.10: a SystemVerilog string passed to imported foreign code is accessed
// by that code through a pointer the simulator provides (the input direction
// mode). The DPI runtime carries the string as a DpiArgValue and the foreign
// function reads it back, observing the value crossing the boundary intact.
TEST(DpiStringArguments, ImportWithStringArg) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_strlen";
  func.sv_name = "sv_strlen";
  func.return_type = DataTypeKind::kInt;
  func.impl = [](const std::vector<DpiArgValue>& args) -> DpiArgValue {
    return DpiArgValue::FromInt(
        static_cast<int32_t>(args[0].AsString().size()));
  };
  rt.RegisterImport(func);

  auto result = rt.CallImport("sv_strlen", {DpiArgValue::FromString("hello")});
  EXPECT_EQ(result.AsInt(), 5);
}

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

}
