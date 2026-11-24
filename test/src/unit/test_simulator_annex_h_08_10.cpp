#include <dlfcn.h>
#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <cstring>
#include <string>
#include <string_view>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_dpi_c_binding.h"
#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"
#include "simulator/dpi_runtime.h"

using namespace delta;

namespace {

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

TEST(DpiStringArguments, ImportOutputStringWrittenBackToActual) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_produce";
  func.sv_name = "sv_produce";
  func.return_type = DataTypeKind::kVoid;
  func.args = {DpiArg{"s", DataTypeKind::kString, Direction::kOutput}};
  func.arg_impl = [](std::vector<DpiArgValue>& args) -> DpiArgValue {
    EXPECT_TRUE(args[0].AsString().empty());
    args[0] = DpiArgValue::FromString("produced");
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(func);

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromString("seed-ignored")};
  rt.CallImportWithArgs("sv_produce", actuals);
  EXPECT_EQ(actuals[0].AsString(), "produced");
}

TEST(DpiStringArguments, ImportInoutStringContentsCopiedBack) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_revise";
  func.sv_name = "sv_revise";
  func.return_type = DataTypeKind::kVoid;
  func.args = {DpiArg{"s", DataTypeKind::kString, Direction::kInout}};
  func.arg_impl = [](std::vector<DpiArgValue>& args) -> DpiArgValue {
    EXPECT_EQ(args[0].AsString(), "before");
    args[0] = DpiArgValue::FromString("after");
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(func);

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromString("before")};
  rt.CallImportWithArgs("sv_revise", actuals);
  EXPECT_EQ(actuals[0].AsString(), "after");
}

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
    EXPECT_EQ(std::strlen(c), sv.size());
    EXPECT_EQ(c[sv.size()], '\0');
    EXPECT_EQ(std::memcmp(c, "keep-me", 7), 0);
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(func);

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromString("keep-me")};
  rt.CallImportWithArgs("sv_peek_inout", actuals);
  EXPECT_EQ(actuals[0].AsString(), "keep-me");
}

DpiArg StringFormal(Direction direction) {
  DpiArg formal;
  formal.name = "s";
  formal.type = DataTypeKind::kString;
  formal.direction = direction;
  return formal;
}

TEST(DpiStringArgumentRules, TheDirectionAppliesToThePointer) {
  EXPECT_EQ(DpiCTypeOfFormal(StringFormal(Direction::kInput), false),
            "const char*");
  EXPECT_EQ(DpiCTypeOfFormal(StringFormal(Direction::kOutput), false),
            "const char**");
  EXPECT_EQ(DpiCTypeOfFormal(StringFormal(Direction::kInout), false),
            "const char**");
  EXPECT_FALSE(DpiStringCharactersMayBeModifiedByReceiver());
}

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

int LengthOfInput(const char* s) { return static_cast<int>(std::strlen(s)); }
void PointOutputAtText(const char** o) { *o = "from C"; }
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

TEST(DpiStringArguments, EachDirectionAndTheResultCrossAsCStrings) {
  DpiCBinding b;
  b.dpi.RegisterImport(
      CImport("length_of_input", DataTypeKind::kInt,
              {CFormal("s", DataTypeKind::kString, Direction::kInput)}));
  b.dpi.RegisterImport(
      CImport("point_output_at_text", DataTypeKind::kVoid,
              {CFormal("o", DataTypeKind::kString, Direction::kOutput)}));
  b.dpi.RegisterImport(
      CImport("shout_inout", DataTypeKind::kVoid,
              {CFormal("s", DataTypeKind::kString, Direction::kInout)}));
  b.dpi.RegisterImport(CImport("return_text", DataTypeKind::kString, {}));
  b.Bind({{"length_of_input", reinterpret_cast<void*>(&LengthOfInput)},
          {"point_output_at_text", reinterpret_cast<void*>(&PointOutputAtText)},
          {"shout_inout", reinterpret_cast<void*>(&ShoutInout)},
          {"return_text", reinterpret_cast<void*>(&ReturnText)}},
         "annex_h_08_10_strings");
  ASSERT_TRUE(b.diag.Diagnostics().empty());
  std::vector<DpiArgValue> input = {DpiArgValue::FromString("hello")};
  EXPECT_EQ(b.Call("length_of_input", input).AsInt(), 5);
  std::vector<DpiArgValue> output = {DpiArgValue::FromString("seed")};
  b.Call("point_output_at_text", output);
  EXPECT_EQ(output[0].AsString(), "from C");
  std::vector<DpiArgValue> inout = {DpiArgValue::FromString("hello")};
  b.Call("shout_inout", inout);
  EXPECT_EQ(inout[0].AsString(), "HELLO");
  std::vector<DpiArgValue> none;
  EXPECT_EQ(b.Call("return_text", none).AsString(), "returned");
}

template <typename Function>
Function ExportNamed(const char* name) {
  return reinterpret_cast<Function>(dlsym(RTLD_DEFAULT, name));
}

void Relay(const char** greeting, const char** named) {
  static std::string kept_greeting;
  static std::string kept_named;
  auto greet = ExportNamed<const char* (*)(const char*)>("greet");
  auto name_it = ExportNamed<void (*)(const char**)>("name_it");
  if (greet == nullptr || name_it == nullptr) {
    *greeting = "";
    *named = "";
    return;
  }
  const char* from_greet = greet("you");
  const char* from_name_it = nullptr;
  name_it(&from_name_it);
  const std::vector<std::string> kChurn(64, std::string(48, 'x'));
  kept_greeting = from_greet;
  kept_named = from_name_it == nullptr ? "" : from_name_it;
  *greeting = kept_greeting.c_str();
  *named = kept_named.c_str();
}

uint64_t VariableValue(SimFixture& f, std::string_view name) {
  auto* var = f.ctx.FindVariable(name);
  return var == nullptr ? ~uint64_t{0} : var->value.ToUint64();
}

TEST(DpiStringArguments, AnExportsStringResultAndOutputStayValidInC) {
  SimFixture f;
  RunWithImportsBound(
      "module top;\n"
      "  export \"DPI-C\" function greet;\n"
      "  export \"DPI-C\" function name_it;\n"
      "  import \"DPI-C\" context function void relay(output string g,\n"
      "      output string n);\n"
      "  function string greet(input string who);\n"
      "    return {\"hi \", who};\n"
      "  endfunction\n"
      "  function void name_it(output string s);\n"
      "    s = \"a string longer than any small-string buffer\";\n"
      "  endfunction\n"
      "  string g, n;\n"
      "  int ok_g, ok_n;\n"
      "  initial begin\n"
      "    relay(g, n);\n"
      "    ok_g = g == \"hi you\";\n"
      "    ok_n = n == \"a string longer than any small-string buffer\";\n"
      "  end\n"
      "endmodule\n",
      f, {{"relay", reinterpret_cast<void*>(&Relay)}},
      "annex_h_08_10_export_strings");
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_EQ(VariableValue(f, "ok_g"), 1U);
  EXPECT_EQ(VariableValue(f, "ok_n"), 1U);
}

void SeeTerminator(const char* s) {
  SeeInC({s != nullptr && *s == '\0' ? 1 : 0});
}

TEST(DpiStringArguments, AnEmptyInputStringReachesCAsAPointerToItsTerminator) {
  SimFixture f;
  RunModuleWithC(
      "  import \"DPI-C\" function void see(input string s);\n"
      "  string empty;\n"
      "  initial begin see(\"\"); see(empty); see(\"a\"); end\n",
      f, {{"see", CAddress(&SeeTerminator)}}, "annex_h_08_10_empty");
  EXPECT_EQ(SeenInC(), (std::vector<long long>{1, 1, 0}));
}

void LeaveInout(const char** s) {
  SeeInC({*s != nullptr && std::strcmp(*s, "kept as it was") == 0 ? 1 : 0});
}

TEST(DpiStringArguments, AnInoutCLeavesUnchangedKeepsItsValue) {
  DpiCBinding b;
  b.dpi.RegisterImport(
      CImport("leave_inout", DataTypeKind::kVoid,
              {CFormal("s", DataTypeKind::kString, Direction::kInout)}));
  b.Bind({{"leave_inout", CAddress(&LeaveInout)}}, "annex_h_08_10_left");
  ASSERT_TRUE(b.diag.Diagnostics().empty());
  SeenInC().clear();
  std::vector<DpiArgValue> inout = {DpiArgValue::FromString("kept as it was")};
  b.Call("leave_inout", inout);
  EXPECT_EQ(SeenInC(), (std::vector<long long>{1}));
  EXPECT_EQ(inout[0].AsString(), "kept as it was");
}

void PassAnInputToKeep() {
  auto rewrite = NamedExport<void (*)(const char*)>("rewrite_input");
  if (rewrite == nullptr) return;
  char text[] = "hello";
  rewrite(text);
  SeeInC({std::memcmp(text, "hello", sizeof(text)) == 0 ? 1 : 0});
}

TEST(DpiStringArguments, AnExportLeavesTheCharactersOfCsInputUnmodified) {
  SimFixture f;
  RunModuleWithC(
      "  export \"DPI-C\" function rewrite_input;\n"
      "  import \"DPI-C\" context function void pass_input();\n"
      "  string changed;\n"
      "  bit ok;\n"
      "  function void rewrite_input(input string s);\n"
      "    s.putc(0, \"J\"); s = {s, \"!\"}; changed = s;\n"
      "  endfunction\n"
      "  initial begin pass_input(); ok = changed == \"Jello!\"; end\n",
      f, {{"pass_input", CAddress(&PassAnInputToKeep)}},
      "annex_h_08_10_input_kept");
  EXPECT_EQ(SeenInC(), (std::vector<long long>{1}));
  EXPECT_EQ(DesignValue(f, "ok"), 1U);
}

void PassInouts() {
  auto change = NamedExport<void (*)(const char**)>("change_inout");
  auto keep = NamedExport<void (*)(const char**)>("keep_inout");
  if (change == nullptr || keep == nullptr) return;
  char text[] = "hello";
  const char* changed = text;
  const char* kept = text;
  change(&changed);
  SeeInC(
      {changed != text ? 1 : 0,
       changed != nullptr && std::strcmp(changed, "hello there") == 0 ? 1 : 0,
       std::memcmp(text, "hello", sizeof(text)) == 0 ? 1 : 0});
  keep(&kept);
  SeeInC({kept == text ? 1 : 0});
}

void RunInoutExports(SimFixture& f) {
  RunModuleWithC(
      "  export \"DPI-C\" function change_inout;\n"
      "  export \"DPI-C\" function keep_inout;\n"
      "  import \"DPI-C\" context function void pass_inouts();\n"
      "  function void change_inout(inout string s);\n"
      "    s = {s, \" there\"};\n"
      "  endfunction\n"
      "  function void keep_inout(inout string s); endfunction\n"
      "  initial pass_inouts();\n",
      f, {{"pass_inouts", CAddress(&PassInouts)}},
      "annex_h_08_10_export_inouts");
  ASSERT_EQ(SeenInC().size(), 4U);
}

TEST(DpiStringArguments, AnInoutAnExportChangesReachesCAsANewAddress) {
  SimFixture f;
  RunInoutExports(f);
  EXPECT_EQ(std::vector<long long>(SeenInC().begin(), SeenInC().begin() + 3),
            (std::vector<long long>{1, 1, 1}));
}

TEST(DpiStringArguments, DISABLED_AnInoutAnExportLeavesKeepsCsOwnPointer) {
  SimFixture f;
  RunInoutExports(f);
  EXPECT_EQ(SeenInC().back(), 1);
}

}  // namespace
