#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_lower_run.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(VariableInitSim, VarInitBeforeInitialBlock) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "module t;\n"
      "  int x = 42;\n"
      "  int y;\n"
      "  initial y = x;\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(y, nullptr);

  EXPECT_EQ(y->value.ToUint64(), 42u);
}

TEST(VariableInitSim, VarInitIsNotContinuous) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a = 8'd10;\n"
      "  logic [7:0] b;\n"
      "  initial begin\n"
      "    b = a;\n"
      "    a = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a = f.ctx.FindVariable("a");
  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(a, nullptr);
  ASSERT_NE(b, nullptr);

  EXPECT_EQ(a->value.ToUint64(), 99u);

  EXPECT_EQ(b->value.ToUint64(), 10u);
}

TEST(VariableInitSim, VarInitHoldsUntilAssignment) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  int x = 100;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);

  EXPECT_EQ(x->value.ToUint64(), 100u);
}

TEST(VariableInitSim, VarInitWithExpression) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] v = 8'hF0 & 8'h3C;\n"
      "endmodule\n",
      f, "v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 0x30u);
}

TEST(VariableInitSim, MultipleVarInitSameDecl) {
  SimFixture f;
  auto* design = ElaborateLowerRun(f,
                                   "module t;\n"
                                   "  int a = 1, b = 2, c = 3;\n"
                                   "endmodule\n");
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("c")->value.ToUint64(), 3u);
}

TEST(VariableInitSim, VarInitBeforeAlwaysBlock) {
  SimFixture f;
  auto* result = RunAndFindVar(
      "module t;\n"
      "  logic clk = 0;\n"
      "  logic [7:0] count = 8'd5;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    #1 clk = 1;\n"
      "  end\n"
      "  always_ff @(posedge clk) begin\n"
      "    result <= count;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(result, nullptr);

  EXPECT_EQ(result->value.ToUint64(), 5u);
}

TEST(VariableInitSim, VarInitOverwrittenByProceduralAssign) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  int x = 100;\n"
      "  initial x = 200;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 200u);
}

TEST(VariableInitSim, BlockLevelVarInit) {
  SimFixture f;
  auto* result = RunAndFindVar(
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    static int local_var = 77;\n"
      "    result = local_var;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(result, nullptr);
  EXPECT_EQ(result->value.ToUint64(), 77u);
}

TEST(VariableInitSim, StaticClassMemberInitBeforeInitialBlock) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  static int val = 55;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial result = C::val;\n"
                      "endmodule\n",
                      "result"),
            55u);
}

TEST(VariableInitSim, FourStateInitializerPreservesXZ) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] v = 4'b10xz;\n"
      "endmodule\n",
      f, "v");
  ASSERT_NE(v, nullptr);
  EXPECT_FALSE(v->value.IsKnown());
}

TEST(VariableInitSim, SignedNegativeInitializer) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  int x = -5;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 0xFFFFFFFBull);
}

TEST(VariableInitSim, InitValuePersistsAcrossTime) {
  SimFixture f;
  auto* snap = RunAndFindVar(
      "module t;\n"
      "  int x = 7;\n"
      "  int snapshot;\n"
      "  initial #5 snapshot = x;\n"
      "endmodule\n",
      f, "snapshot");
  ASSERT_NE(snap, nullptr);
  EXPECT_EQ(snap->value.ToUint64(), 7u);
}

TEST(VariableInitSim, VarInitFromOtherInitializedVariables) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] consta = 8'hFC;\n"
      "  logic [7:0] constb = 8'h3F;\n"
      "  logic [7:0] v = consta & constb;\n"
      "endmodule\n",
      f, "v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 0x3Cu);
}

TEST(VariableInitSim, VarInitFromParameterOperand) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  parameter [7:0] P = 8'h3C;\n"
                      "  logic [7:0] v = P;\n"
                      "endmodule\n",
                      "v"),
            0x3Cu);
}

TEST(VariableInitSim, VarInitFromLocalparamInExpression) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  localparam [7:0] L = 8'd20;\n"
                      "  logic [7:0] v = L + 8'd3;\n"
                      "endmodule\n",
                      "v"),
            23u);
}

TEST(VariableInitSim, VarInitBeforeAlwaysCombBlock) {
  SimFixture f;
  auto* o = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a = 8'd9;\n"
      "  logic [7:0] o;\n"
      "  always_comb o = a + 1;\n"
      "endmodule\n",
      f, "o");
  ASSERT_NE(o, nullptr);
  EXPECT_EQ(o->value.ToUint64(), 10u);
}

TEST(VariableInitSim, BlockFixedArrayInitFromPattern) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int r;\n"
                      "  initial begin\n"
                      "    static int a[3] = '{7, 8, 9};\n"
                      "    r = a[0] * 100 + a[1] * 10 + a[2];\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            789u);
}

TEST(VariableInitSim, BlockFixedArrayInitFromDefaultPattern) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int r;\n"
                      "  initial begin\n"
                      "    static int a[2] = '{default: 5};\n"
                      "    r = a[0] + a[1];\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            10u);
}

TEST(VariableInitSim, BlockQueueInitFromConcatenation) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int r;\n"
                      "  initial begin\n"
                      "    static int q[$] = {1, 2};\n"
                      "    q.push_back(3);\n"
                      "    r = q.size() * 10 + q[1];\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            32u);
}

TEST(VariableInitSim, BlockDynamicArrayInitFromPattern) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int r;\n"
                      "  initial begin\n"
                      "    static int d[] = '{4, 5, 6};\n"
                      "    r = d.size() * 10 + d[2];\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            36u);
}

TEST(VariableInitSim, BlockAssocArrayInitFromPattern) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int r;\n"
                      "  initial begin\n"
                      "    static int m[string] = '{\"x\": 1, \"y\": 2};\n"
                      "    r = m.num() * 10 + m[\"y\"];\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            22u);
}

TEST(VariableInitSim, BlockStringQueueInitAndAssign) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int r;\n"
                      "  initial begin\n"
                      "    static string p[$] = '{\"a\", \"b\"};\n"
                      "    string s[$];\n"
                      "    s = {\"c\", \"d\", \"e\"};\n"
                      "    r = p.size() * 10 + s.size();\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            23u);
}

TEST(VariableInitSim, FunctionLocalArrayInits) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int r;\n"
                      "  function automatic int f();\n"
                      "    int a[3] = '{7, 8, 9};\n"
                      "    int q[$] = {1, 2};\n"
                      "    int d[] = '{4, 5, 6};\n"
                      "    return a[2] * 100 + q.size() * 10 + d.size();\n"
                      "  endfunction\n"
                      "  initial r = f();\n"
                      "endmodule\n",
                      "r"),
            923u);
}

TEST(VariableInitSim, BlockArrayInitEvaluatedOnce) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int cnt = 0;\n"
                      "  function int bump(); cnt++; return 7; endfunction\n"
                      "  initial begin\n"
                      "    static int q[$] = {bump()};\n"
                      "  end\n"
                      "endmodule\n",
                      "cnt"),
            1u);
}

TEST(VariableInitSim, StaticBlockQueueInitRunsOnce) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int r;\n"
                      "  initial begin\n"
                      "    for (int i = 0; i < 3; i++) begin\n"
                      "      static int q[$] = {1};\n"
                      "      automatic int a[$] = {1};\n"
                      "      q.push_back(i);\n"
                      "      a.push_back(i);\n"
                      "      r = q.size() * 10 + a.size();\n"
                      "    end\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            42u);
}

TEST(VariableInitSim, StaticFunctionQueueInitRunsOnce) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int r;\n"
                      "  function int f();\n"
                      "    static int q[$] = {1, 2};\n"
                      "    q.push_back(3);\n"
                      "    return q.size();\n"
                      "  endfunction\n"
                      "  initial begin\n"
                      "    r = f();\n"
                      "    r = r * 10 + f();\n"
                      "  end\n"
                      "endmodule\n",
                      "r"),
            34u);
}

TEST(VariableInitSim, AStaticLocalIsInitializedBeforeTheProceduresStart) {
  const char* src =
      "module t;\n"
      "  int g = 1;\n"
      "  int rf, ra, rt, rb;\n"
      "  function int f(); static int s = g; return s; endfunction\n"
      "  function automatic int fa(); static int s = g + 10; return s;\n"
      "  endfunction\n"
      "  task tk(output int o); begin static int s = g + 20; o = s; end\n"
      "  endtask\n"
      "  initial begin\n"
      "    g = 2;\n"
      "    rf = f(); ra = fa(); tk(rt);\n"
      "    begin static int s = g + 30; rb = s; end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "rf"), 1u);
  EXPECT_EQ(RunAndGet(src, "ra"), 11u);
  EXPECT_EQ(RunAndGet(src, "rt"), 21u);
  EXPECT_EQ(RunAndGet(src, "rb"), 31u);
}

TEST(VariableInitSim, AStaticLocalInitializerReadsItsOwnScope) {
  const char* src =
      "module c;\n"
      "  int g = 5;\n"
      "  int r;\n"
      "  function int f(); static int s = g; return s; endfunction\n"
      "  initial begin g = 6; r = f(); end\n"
      "endmodule\n"
      "module t;\n"
      "  int g = 1;\n"
      "  int rp, rg;\n"
      "  c u();\n"
      "  for (genvar i = 3; i < 4; i++) begin : gb\n"
      "    int h = 7;\n"
      "    function int gf(); static int s = g + i; return s; endfunction\n"
      "    initial begin\n"
      "      h = 8; g = 2;\n"
      "      begin static int s = h * 10 + i; rp = s; end\n"
      "    end\n"
      "  end\n"
      "  initial #1 rg = gb[3].gf();\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "u.r"), 5u);
  EXPECT_EQ(RunAndGet(src, "rp"), 73u);
  EXPECT_EQ(RunAndGet(src, "rg"), 4u);
}

TEST(VariableInitSim, AStaticLocalsInitializerRunsInNoProcess) {
  const char* src =
      "module t;\n"
      "  int none, own;\n"
      "  initial begin\n"
      "    static process p = process::self();\n"
      "    automatic process q = process::self();\n"
      "    none = p == null; own = q != null;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "none"), 1u);
  EXPECT_EQ(RunAndGet(src, "own"), 1u);
}

TEST(VariableInitSim, AStaticWeakReferenceIsMadeBeforeTheProceduresStart) {
  const char* src =
      "class C; endclass\n"
      "module t;\n"
      "  C o;\n"
      "  int still_null;\n"
      "  initial begin\n"
      "    o = new;\n"
      "    begin\n"
      "      static weak_reference #(C) w = new(o);\n"
      "      still_null = w.get() == null;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "still_null"), 1u);
}

TEST(VariableInitSim, PackageAndUnitStaticLocalsAreSetBeforeTheProcedures) {
  const char* src =
      "int g = 3;\n"
      "function int uf(); static int s = g; return s; endfunction\n"
      "package p;\n"
      "  int g = 1;\n"
      "  function int f(); static int s = g; return s; endfunction\n"
      "endpackage\n"
      "module t;\n"
      "  int r, u;\n"
      "  initial begin p::g = 2; $unit::g = 4; r = p::f(); u = uf(); end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
  EXPECT_EQ(RunAndGet(src, "u"), 3u);
}

TEST(VariableInitSim, UnitAndPackageClassMethodStaticLocalsAreSetEarly) {
  const char* src =
      "int g = 1;\n"
      "class C;\n"
      "  static function int f(); static int s = $unit::g; return s;\n"
      "  endfunction\n"
      "endclass\n"
      "package p;\n"
      "  int h = 3;\n"
      "  class D;\n"
      "    task t(output int o); static int s = h; o = s; endtask\n"
      "  endclass\n"
      "endpackage\n"
      "module t;\n"
      "  int r, u;\n"
      "  p::D d;\n"
      "  initial begin\n"
      "    d = new; $unit::g = 2; p::h = 4; r = C::f(); d.t(u);\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
  EXPECT_EQ(RunAndGet(src, "u"), 3u);
}

TEST(VariableInitSim, ModuleClassMethodStaticLocalsAreSetEarly) {
  const char* src =
      "module m;\n"
      "  int g = 5;\n"
      "  class E;\n"
      "    function int f(); static int s = g; return s; endfunction\n"
      "  endclass\n"
      "  int r;\n"
      "  initial begin E h; h = new; g = 6; r = h.f(); end\n"
      "endmodule\n"
      "module t;\n"
      "  int g = 1;\n"
      "  class C;\n"
      "    function int f(); static int s = g; return s; endfunction\n"
      "  endclass\n"
      "  m u();\n"
      "  int r, v;\n"
      "  initial begin C h; h = new; g = 2; r = h.f(); #1 v = u.r; end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
  EXPECT_EQ(RunAndGet(src, "v"), 5u);
}

TEST(VariableInitSim, SpecializationMethodStaticLocalsAreSetEarly) {
  const char* src =
      "int g = 1;\n"
      "class P #(int N = 0);\n"
      "  static function int f(); static int s = $unit::g + N; return s;\n"
      "  endfunction\n"
      "endclass\n"
      "typedef P#(10) p10;\n"
      "typedef P#(20) p20;\n"
      "module t;\n"
      "  int r, u;\n"
      "  initial begin $unit::g = 2; r = p10::f(); u = p20::f(); end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "r"), 11u);
  EXPECT_EQ(RunAndGet(src, "u"), 21u);
}

}  // namespace
