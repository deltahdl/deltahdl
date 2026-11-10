#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(DynamicArraySimulation, DeclWithInitHasElements) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[] = '{10, 20, 30};\n"
      "  int result;\n"
      "  initial result = d[1];\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 20u);
}

TEST(DynamicArraySimulation, DefaultUninitializedSizeZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[];\n"
      "  int result;\n"
      "  initial result = d.size();\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(DynamicArraySimulation, DeclWithInitCorrectSize) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[] = '{5, 6, 7, 8};\n"
      "  int result;\n"
      "  initial result = d.size();\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 4u);
}

TEST(DynamicArraySimulation, PackedVectorElementHoldsValue) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] d[] = '{8'hA1, 8'hB2, 8'hC3};\n"
      "  int result;\n"
      "  initial result = d[2];\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xC3u);
}

TEST(DynamicArraySimulation, BlockDeclaredDynamicArraySizedByNewHoldsElements) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    int d[];\n"
                      "    d = new[3];\n"
                      "    d[1] = 5;\n"
                      "    y = d[1] + d.size();\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            8u);
}

TEST(DynamicArraySimulation, ElementWriteTakesTheElementWidth) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    byte d[];\n"
                      "    d = new[2];\n"
                      "    d[0] = 1;\n"
                      "    d[1] = 300;\n"
                      "    y = $bits(d[0]) * 1000 + d[1];\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            8044u);
}

TEST(DynamicArraySimulation, FunctionBodyDynamicArraySizedByNewHoldsElements) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  function int f();\n"
                      "    int d[];\n"
                      "    d = new[3];\n"
                      "    d[1] = 5;\n"
                      "    return d[1] + d.size();\n"
                      "  endfunction\n"
                      "  int y;\n"
                      "  initial y = f();\n"
                      "endmodule\n",
                      "y"),
            8u);
}

TEST(DynamicArraySimulation,
     BlockDeclaredDynamicArraySizedByItsNewInitializer) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    static int d[] = new[3];\n"
                      "    y = d.size();\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            3u);
}

TEST(DynamicArraySimulation, FunctionBodyDynamicArraySizedByItsNewInitializer) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  function int f();\n"
                      "    static int d[] = new[3];\n"
                      "    int e[];\n"
                      "    d[1] = 5;\n"
                      "    e = new[4](d);\n"
                      "    return e.size() * 100 + e[1] + e[3];\n"
                      "  endfunction\n"
                      "  int y;\n"
                      "  initial y = f();\n"
                      "endmodule\n",
                      "y"),
            405u);
}

TEST(DynamicArraySim, MemberOfAStructElement) {
  const char* src =
      "module t;\n"
      "  typedef struct { int f1; bit f2; } T;\n"
      "  T md[];\n"
      "  int mod, loc, fn;\n"
      "  function automatic int g(input T a[]);\n"
      "    return a[1].f1;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    T ld[];\n"
      "    T e;\n"
      "    md = new[2];\n"
      "    ld = new[2];\n"
      "    e.f1 = 9;\n"
      "    e.f2 = 1;\n"
      "    md[1] = e;\n"
      "    ld[1] = e;\n"
      "    mod = md[1].f1;\n"
      "    loc = ld[1].f1;\n"
      "    fn = g(md);\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "mod"), 9u);
  EXPECT_EQ(RunAndGet(src, "loc"), 9u);
  EXPECT_EQ(RunAndGet(src, "fn"), 9u);
}

TEST(DynamicArraySim, PropertyOfClassHandlesSizedByNew) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  class Item;\n"
      "    int id;\n"
      "    function new(int i); id = i; endfunction\n"
      "  endclass\n"
      "  class Holder;\n"
      "    Item items[];\n"
      "    function void fill(int n); items = new[n];\n"
      "      foreach (items[i]) items[i] = new(10 + i); endfunction\n"
      "    function int total(); int s = 0; foreach (items[i]) s += "
      "items[i].id;\n"
      "      return s; endfunction\n"
      "  endclass\n"
      "  Holder h, g;\n"
      "  initial begin\n"
      "    h = new; h.fill(3); g = new;\n"
      "    g.items = new[2]; g.items[1] = new(5);\n"
      "    $display(\"%0d %0d %0d %0d\", h.items[2].id, h.total(),\n"
      "             g.items.size(), g.items[1].id);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "12 33 2 5\n");
}

TEST(DynamicArraySimulation, AnElementReadsWithTheElementTypesSignedness) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  bit [31:0] ud[];\n"
      "  int d[];\n"
      "  bit [31:0] u;\n"
      "  initial begin\n"
      "    u = 32'hDEADBEEF;\n"
      "    ud = new[1]; d = new[1];\n"
      "    ud[0] = -5; d[0] = u;\n"
      "    $display(\"%0d %0d\", ud[0] < 0, d[0] < 0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0 1\n");
}

TEST(DynamicArraySimulation, AnElementOfAPackageDynamicArrayReadsSigned) {
  SimFixture f;
  auto out = RunCapture(
      "package p;\n"
      "  int d[];\n"
      "endpackage\n"
      "module t;\n"
      "  bit [31:0] u;\n"
      "  initial begin\n"
      "    u = 32'hDEADBEEF;\n"
      "    p::d = new[1];\n"
      "    p::d[0] = u;\n"
      "    $display(\"%0d\", p::d[0] < 0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1\n");
}

TEST(DynamicArraySimulation, AnElementOfADynamicArrayFormalReadsSigned) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int d[];\n"
      "  bit [31:0] u;\n"
      "  function int negative(int a[]);\n"
      "    return a[0] < 0;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    u = 32'hDEADBEEF;\n"
      "    d = new[1];\n"
      "    d[0] = u;\n"
      "    $display(\"%0d\", negative(d));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1\n");
}

TEST(DynamicArraySim, ClauseExamplesAndElementsOfEveryKindOfType) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module t;\n"
          "  typedef struct {int a; logic [1:0] b;} s_t;\n"
          "  class K; int v = 3; endclass\n"
          "  bit [3:0] nibble []; integer mem [2][]; s_t sd []; K kd [];\n"
          "  int dq [][$];\n"
          "  initial begin\n"
          "    nibble = new[2]; nibble[1] = 4'ha; mem[1] = new[3]; "
          "mem[1][2] = 6;\n"
          "    sd = new[1]; sd[0] = '{4, 2'b1x}; kd = new[2]; kd[1] = new;\n"
          "    dq = new[2]; dq[1].push_back(7);\n"
          "    $display(\"%h %0d %0d %0d %0d %0d %b %0d %0d %0d\", nibble[1], "
          "$bits(nibble[0]), mem[0].size(), mem[1][2], $isunknown(mem[1][0]), "
          "sd[0].a, sd[0].b, kd[1].v, kd[0] == null, dq[1][0]);\n"
          "  end\n"
          "endmodule\n",
          f),
      "a 4 0 6 1 4 1x 3 1 7\n");
}

TEST(DynamicArraySim, DISABLED_EventElementIsTriggeredAndWaitedOn) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  event ev [];\n"
                 "  initial begin\n"
                 "    ev = new[1];\n"
                 "    fork\n"
                 "      begin @(ev[0]); $display(\"ev %0t\", $time); end\n"
                 "      begin #1 ->ev[0]; end\n"
                 "    join\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "ev 1\n");
}

TEST(DynamicArraySim, DISABLED_ElementThatIsAnAssociativeArrayKeepsItsEntries) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  int da [][int];\n"
                       "  initial begin\n"
                       "    da = new[2]; da[1][9] = 5;\n"
                       "    $display(\"%0d %0d\", da[1][9], da[1].num());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "5 1\n");
}

}  // namespace
