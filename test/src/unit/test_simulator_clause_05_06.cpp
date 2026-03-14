#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

TEST(IdentifierSim, IdentifierWithDollarSign) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] n$657;\n"
      "  initial n$657 = 8'd42;\n"
      "endmodule\n",
      "n$657");
  EXPECT_EQ(result, 42u);
}

TEST(IdentifierSim, IdentifierStartingWithUnderscore) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] _bus3;\n"
      "  initial _bus3 = 8'd55;\n"
      "endmodule\n",
      "_bus3");
  EXPECT_EQ(result, 55u);
}

TEST(IdentifierSim, IdentifiersCaseSensitive) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] data, Data, DATA;\n"
      "  initial begin\n"
      "    data = 8'd10;\n"
      "    Data = 8'd20;\n"
      "    DATA = 8'd30;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* v1 = f.ctx.FindVariable("data");
  auto* v2 = f.ctx.FindVariable("Data");
  auto* v3 = f.ctx.FindVariable("DATA");
  ASSERT_NE(v1, nullptr);
  ASSERT_NE(v2, nullptr);
  ASSERT_NE(v3, nullptr);
  EXPECT_EQ(v1->value.ToUint64(), 10u);
  EXPECT_EQ(v2->value.ToUint64(), 20u);
  EXPECT_EQ(v3->value.ToUint64(), 30u);
}

TEST(IdentifierSim, LongIdentifier1024Chars) {
  std::string long_id(1024, 'a');
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] " +
          long_id +
          ";\n"
          "  initial " +
          long_id +
          " = 8'd77;\n"
          "endmodule\n",
      long_id.c_str());
  EXPECT_EQ(result, 77u);
}

TEST(IdentifierSim, IdentifierWithDigits) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] abc123;\n"
      "  initial abc123 = 8'd88;\n"
      "endmodule\n",
      "abc123");
  EXPECT_EQ(result, 88u);
}

TEST(IdentifierSim, IdentifierReferencesObject) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] source, sink;\n"
      "  initial begin\n"
      "    source = 8'd66;\n"
      "    sink = source;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("sink");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 66u);
}

TEST(IdentifierSim, IdentifierMixedCharClasses) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] _start, mid$dle, end_99, result;\n"
      "  initial begin\n"
      "    _start = 8'd1;\n"
      "    mid$dle = 8'd2;\n"
      "    end_99 = 8'd3;\n"
      "    result = _start + mid$dle + end_99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 6u);
}
