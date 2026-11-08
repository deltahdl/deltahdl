#include <gtest/gtest.h>

#include <utility>
#include <vector>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_dpi_c_binding.h"
#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_runtime.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/svdpi.h"

using namespace delta;

namespace {

struct ImportResultOfType {
  DpiRuntime dpi;
  SimFixture f;
  Logic4Vec result;

  ImportResultOfType(DataTypeKind kind, const DpiArgValue& value) {
    DpiRtFunction func;
    func.c_name = "c_result";
    func.sv_name = "sv_result";
    func.return_type = kind;
    func.impl = [value](const std::vector<DpiArgValue>&) -> DpiArgValue {
      return value;
    };
    dpi.RegisterImport(std::move(func));
    f.ctx.SetDpiRuntime(&dpi);
    result = EvalFunctionCall(ParseExprFrom("sv_result()", f), f.ctx, f.arena);
  }
};

TEST(DpiFunctionResultInADesign, AScalarLogicResultCarriesAnUnknownBit) {
  ImportResultOfType run(DataTypeKind::kLogic, DpiArgValue::FromLogic(sv_x));

  EXPECT_EQ(run.result.words[0].bval, 1U);
  EXPECT_EQ(run.result.words[0].aval, 1U);
}

TEST(DpiFunctionResultInADesign, ALongintResultCarriesItsUpperWord) {
  ImportResultOfType run(DataTypeKind::kLongint,
                         DpiArgValue::FromLongint(0x123456789ABCDEF0LL));

  EXPECT_EQ(run.result.width, 64U);
  EXPECT_EQ(run.result.words[0].aval, 0x123456789ABCDEF0ULL);
}

TEST(DpiFunctionResultInADesign, AnIntResultIsThirtyTwoBitsWide) {
  ImportResultOfType run(DataTypeKind::kInt,
                         DpiArgValue::FromLongint(0x100000007LL));

  EXPECT_EQ(run.result.width, 32U);
  EXPECT_EQ(run.result.words[0].aval, 7U);
}

TEST(DpiFunctionResultInADesign, ANarrowResultStillOccupiesOneWord) {
  ImportResultOfType run(DataTypeKind::kByte, DpiArgValue::FromInt(0x5A));

  EXPECT_EQ(run.result.width, 8U);
  EXPECT_EQ(run.result.nwords, 1U);
  EXPECT_EQ(run.result.words[0].aval, 0x5AU);
}

char NegativeByte() { return -100; }
void WriteNegativeByte(char* b) { *b = -100; }
unsigned int AllOnes() { return 0xFFFFFFFFU; }

TEST(DpiFunctionResult, AResultAndAnOutputAreSignedAsTheirTypesAre) {
  SimFixture f;
  RunWithImportsBound(
      "module t;\n"
      "  import \"DPI-C\" function byte negative_byte();\n"
      "  import \"DPI-C\" function void write_negative_byte(output byte b);\n"
      "  import \"DPI-C\" function int unsigned all_ones();\n"
      "  int r;\n"
      "  int o;\n"
      "  longint u;\n"
      "  initial begin\n"
      "    r = negative_byte();\n"
      "    write_negative_byte(o);\n"
      "    u = all_ones();\n"
      "  end\n"
      "endmodule\n",
      f,
      {{"negative_byte", reinterpret_cast<void*>(&NegativeByte)},
       {"write_negative_byte", reinterpret_cast<void*>(&WriteNegativeByte)},
       {"all_ones", reinterpret_cast<void*>(&AllOnes)}},
      "subclause_35_05_05_signedness");
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  auto* r = f.ctx.FindVariable("r");
  auto* o = f.ctx.FindVariable("o");
  auto* u = f.ctx.FindVariable("u");
  ASSERT_NE(r, nullptr);
  ASSERT_NE(o, nullptr);
  ASSERT_NE(u, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 0xFFFFFF9CU);
  EXPECT_EQ(o->value.ToUint64(), 0xFFFFFF9CU);
  EXPECT_EQ(u->value.ToUint64(), 0xFFFFFFFFU);
}

}  // namespace
