#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(TaskSim, GenerateBlockFunctionFormalReadsTheBlocksTypedefOverTheModules) {
  EXPECT_EQ(RunAndGet("module top;\n"
                      "  typedef struct { int a; } pair_t;\n"
                      "  if (1) begin : g\n"
                      "    typedef struct { int a, b; } pair_t;\n"
                      "    function int f(union tagged { void N; pair_t A; }"
                      " a);\n"
                      "      return a.A.a * 10 + a.A.b;\n"
                      "    endfunction\n"
                      "  end\n"
                      "  int y;\n"
                      "  initial y = g.f(tagged A '{3, 4});\n"
                      "endmodule\n",
                      "y"),
            34u);
}

TEST(TaskSim, ModuleFunctionBesideAShadowingBlockReadsTheModulesOwnTypedef) {
  EXPECT_EQ(RunAndGet("module top;\n"
                      "  typedef struct { int a; } pair_t;\n"
                      "  function int f(union tagged { void N; pair_t A; }"
                      " a);\n"
                      "    return a.A.a;\n"
                      "  endfunction\n"
                      "  if (1) begin : g\n"
                      "    typedef struct { int a, b; } pair_t;\n"
                      "    function int f(union tagged { void N; pair_t A; }"
                      " a);\n"
                      "      return a.A.a * 10 + a.A.b;\n"
                      "    endfunction\n"
                      "  end\n"
                      "  int y;\n"
                      "  initial y = f(tagged A '{7}) * 100"
                      " + g.f(tagged A '{3, 4});\n"
                      "endmodule\n",
                      "y"),
            734u);
}

TEST(TaskSim,
     NestedGenerateBlockFunctionFormalReadsItsOwnTypedefOverTheOuters) {
  EXPECT_EQ(RunAndGet("module top;\n"
                      "  typedef struct { int a; } pair_t;\n"
                      "  if (1) begin : g\n"
                      "    typedef struct { int a, b; } pair_t;\n"
                      "    function int f(union tagged { void N; pair_t A; }"
                      " a);\n"
                      "      return a.A.a * 10 + a.A.b;\n"
                      "    endfunction\n"
                      "    if (1) begin : h\n"
                      "      typedef struct { int a, b, c; } pair_t;\n"
                      "      function int f(union tagged { void N; pair_t A; }"
                      " a);\n"
                      "        return a.A.a * 100 + a.A.b * 10 + a.A.c;\n"
                      "      endfunction\n"
                      "    end\n"
                      "  end\n"
                      "  int y;\n"
                      "  initial y = g.h.f(tagged A '{1, 2, 3}) * 1000"
                      " + g.f(tagged A '{5, 6});\n"
                      "endmodule\n",
                      "y"),
            123056u);
}

TEST(TaskSim, GenerateBlockForwardTypedefStandsOverTheModulesTypedef) {
  EXPECT_EQ(RunAndGet("module top;\n"
                      "  typedef struct { int a; } pair_t;\n"
                      "  if (1) begin : g\n"
                      "    typedef struct pair_t;\n"
                      "    function int f(union tagged { void N; pair_t A; }"
                      " a);\n"
                      "      return a.A.a * 10 + a.A.b;\n"
                      "    endfunction\n"
                      "    typedef struct { int a, b; } pair_t;\n"
                      "  end\n"
                      "  int y;\n"
                      "  initial y = g.f(tagged A '{3, 4});\n"
                      "endmodule\n",
                      "y"),
            34u);
}

TEST(TaskSim, GenerateBlockForwardTypedefBelowItsDefinitionKeepsTheDefinition) {
  EXPECT_EQ(RunAndGet("module top;\n"
                      "  typedef struct { int a; } pair_t;\n"
                      "  if (1) begin : g\n"
                      "    typedef struct { int a, b; } pair_t;\n"
                      "    typedef struct pair_t;\n"
                      "    function int f(union tagged { void N; pair_t A; }"
                      " a);\n"
                      "      return a.A.b * 10 + a.A.a;\n"
                      "    endfunction\n"
                      "  end\n"
                      "  int y;\n"
                      "  initial y = g.f(tagged A '{3, 4});\n"
                      "endmodule\n",
                      "y"),
            43u);
}

TEST(TaskSim, GenerateBlockFunctionBelowANestedBlockReadsItsOwnTypedef) {
  EXPECT_EQ(RunAndGet("module top;\n"
                      "  if (1) begin : g\n"
                      "    typedef struct { int a, b, c; } pair_t;\n"
                      "    if (1) begin : h\n"
                      "      typedef struct { int a, b; } pair_t;\n"
                      "      function int f2(union tagged { void N; pair_t A; }"
                      " a);\n"
                      "        return a.A.a * 10 + a.A.b;\n"
                      "      endfunction\n"
                      "    end\n"
                      "    function int f(union tagged { void N; pair_t A; }"
                      " a);\n"
                      "      return a.A.a * 100 + a.A.b * 10 + a.A.c;\n"
                      "    endfunction\n"
                      "  end\n"
                      "  int y;\n"
                      "  initial y = g.h.f2(tagged A '{1, 2}) * 1000"
                      " + g.f(tagged A '{1, 2, 3});\n"
                      "endmodule\n",
                      "y"),
            12123u);
}

struct ElementTaskShape {
  std::string_view members;
  std::string_view decl;
  std::string_view setup;
  std::string_view elem;
  std::string_view reader;
};

static std::string ElementTaskDesign(const ElementTaskShape& shape) {
  std::string r(shape.reader);
  return "class C;\n"
         "  int v = 1;\n"
         "  task run(); #10; v = 5; endtask\n"
         "  function int get(); return v; endfunction\n" +
         std::string(shape.members) +
         "endclass\n"
         "module t;\n"
         "  int at5, at15, done_at, y;\n" +
         std::string(shape.decl) + "  initial begin\n" +
         std::string(shape.setup) +
         "    fork\n"
         "      begin " +
         std::string(shape.elem) + ".run(); done_at = $time; end\n" +
         "      begin #5 at5 = " + r + ".get(); #10 at15 = " + r +
         ".get(); end\n"
         "    join\n"
         "    y = at5 * 10000 + at15 * 100 + done_at;\n"
         "  end\n"
         "endmodule\n";
}

TEST(TaskSim, ClassTaskEnabledThroughAnArrayElementConsumesItsDelay) {
  EXPECT_EQ(
      RunAndGet(ElementTaskDesign({"", "  C arr[2];\n", "    arr[0] = new;\n",
                                   "arr[0]", "arr[0]"}),
                "y"),
      10510u);
}

TEST(TaskSim, ClassTaskEnabledThroughAQueueElementConsumesItsDelay) {
  EXPECT_EQ(
      RunAndGet(ElementTaskDesign({"",
                                   "  C q[$];\n"
                                   "  C c = new;\n",
                                   "    q.push_back(c);\n", "q[0]", "q[0]"}),
                "y"),
      10510u);
}

TEST(TaskSim, ClassTaskEnabledThroughAnAssocElementConsumesItsDelay) {
  EXPECT_EQ(RunAndGet(ElementTaskDesign({"", "  C aa[string];\n",
                                         "    aa[\"k\"] = new;\n", "aa[\"k\"]",
                                         "aa[\"k\"]"}),
                      "y"),
            10510u);
}

TEST(TaskSim, ClassTaskEnabledThroughACallResultConsumesItsDelay) {
  EXPECT_EQ(RunAndGet(ElementTaskDesign(
                          {"  function C self(); return this; endfunction\n",
                           "  C c = new;\n", "", "c.self()", "c"}),
                      "y"),
            10510u);
}

TEST(TaskSim, ClassTaskEnabledThroughAnElementsPropertyConsumesItsDelay) {
  EXPECT_EQ(RunAndGet(ElementTaskDesign({"",
                                         "  class H; C kid = new; endclass\n"
                                         "  H arr[2];\n"
                                         "  C k;\n",
                                         "    arr[0] = new;\n"
                                         "    k = arr[0].kid;\n",
                                         "arr[0].kid", "k"}),
                      "y"),
            10510u);
}

TEST(TaskSim, ClassTaskEnabledThroughAFunctionResultRunsOnItsObject) {
  EXPECT_EQ(RunAndGet(ElementTaskDesign(
                          {"  C kid;\n"
                           "  function C get_kid(); return kid; endfunction\n",
                           "  C c = new;\n"
                           "  C k;\n",
                           "    c.kid = new;\n"
                           "    k = c.kid;\n",
                           "c.get_kid()", "k"}),
                      "y"),
            10510u);
}

TEST(TaskSim, BodyDeclarationTypesADirectionOnlyFormal) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int r;\n"
                      "  task mytask2;\n"
                      "    output x;\n"
                      "    input y;\n"
                      "    int x;\n"
                      "    int y;\n"
                      "    x = y * 3;\n"
                      "  endtask\n"
                      "  initial mytask2(r, 7);\n"
                      "endmodule\n",
                      "r"),
            21u);
}

}  // namespace
