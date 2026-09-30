#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_dpi_c_binding.h"
#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_runtime.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(DpiRuntime, ArgValueLongint) {
  auto v = DpiArgValue::FromLongint(0x1'0000'0000LL);
  EXPECT_EQ(v.type, DataTypeKind::kLongint);
  EXPECT_EQ(v.AsLongint(), 0x1'0000'0000LL);
}

TEST(DpiRuntime, ArgValueChandle) {
  int dummy = 0;
  auto v = DpiArgValue::FromChandle(&dummy);
  EXPECT_EQ(v.type, DataTypeKind::kChandle);
  EXPECT_EQ(v.AsChandle(), &dummy);
}

TEST(DpiRuntime, ArgValueLogic) {
  auto v = DpiArgValue::FromLogic(0);
  EXPECT_EQ(v.type, DataTypeKind::kLogic);
  EXPECT_EQ(v.AsLogic(), 0);
}

TEST(DpiRuntime, ImportWithRealArgs) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_mul_real";
  func.sv_name = "sv_mul_real";
  func.return_type = DataTypeKind::kReal;
  func.impl = [](const std::vector<DpiArgValue>& args) -> DpiArgValue {
    return DpiArgValue::FromReal(args[0].AsReal() * args[1].AsReal());
  };
  rt.RegisterImport(func);

  auto result = rt.CallImport(
      "sv_mul_real", {DpiArgValue::FromReal(2.5), DpiArgValue::FromReal(4.0)});
  EXPECT_DOUBLE_EQ(result.AsReal(), 10.0);
}

TEST(DpiRuntime, ImportWithChandleArg) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_identity";
  func.sv_name = "sv_identity";
  func.return_type = DataTypeKind::kChandle;
  func.impl = [](const std::vector<DpiArgValue>& args) -> DpiArgValue {
    return DpiArgValue::FromChandle(args[0].AsChandle());
  };
  rt.RegisterImport(func);

  int dummy = 42;
  auto result =
      rt.CallImport("sv_identity", {DpiArgValue::FromChandle(&dummy)});
  EXPECT_EQ(result.AsChandle(), &dummy);
}

// The C functions the imports below are bound to.
int CountCharacters(const char* s) {
  int n = 0;
  while (s[n] != '\0') ++n;
  return n;
}
void GiveText(const char** o) { *o = "from C"; }
const char* ReturnedText() { return "returned"; }

// §35.5.6 admits a string formal and result, and §H.8.10 has a string cross
// as its characters: the design's string reaches the C function as the text it
// holds, and the text C gives back through an output or as the result is what
// the design's string then holds.
TEST(DpiStringFormals, ADesignsStringsCrossAsTheirCharacters) {
  SimFixture f;
  RunWithImportsBound(
      "module t;\n"
      "  import \"DPI-C\" function int count_characters(input string s);\n"
      "  import \"DPI-C\" function void give_text(output string o);\n"
      "  import \"DPI-C\" function string returned_text();\n"
      "  string s = \"hello\";\n"
      "  string o;\n"
      "  string back;\n"
      "  int n;\n"
      "  initial begin\n"
      "    n = count_characters(s);\n"
      "    give_text(o);\n"
      "    back = returned_text();\n"
      "  end\n"
      "endmodule\n",
      f,
      {{"count_characters", reinterpret_cast<void*>(&CountCharacters)},
       {"give_text", reinterpret_cast<void*>(&GiveText)},
       {"returned_text", reinterpret_cast<void*>(&ReturnedText)}},
      "subclause_35_05_06_strings");
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  auto* n = f.ctx.FindVariable("n");
  auto* o = f.ctx.FindVariable("o");
  auto* back = f.ctx.FindVariable("back");
  ASSERT_NE(n, nullptr);
  ASSERT_NE(o, nullptr);
  ASSERT_NE(back, nullptr);
  EXPECT_EQ(n->value.ToUint64(), 5U);
  EXPECT_EQ(Logic4VecToString(o->value), "from C");
  EXPECT_EQ(Logic4VecToString(back->value), "returned");
}

}  // namespace
