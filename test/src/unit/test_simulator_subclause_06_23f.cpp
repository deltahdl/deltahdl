#include <gtest/gtest.h>

#include <array>
#include <cstddef>
#include <cstdint>
#include <format>
#include <string>
#include <string_view>
#include <vector>

#include "fixture_vpi_run.h"
#include "helpers_final_output.h"
#include "helpers_instance_type_procedures.h"
#include "helpers_scheduler.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_user.h"

using namespace delta;

namespace {

std::string Comparisons(std::string_view operand, std::string_view type) {
  return std::format(
      "{{type({0}) == type({1}), type({0}) != type({1}), "
      "type({0}) === type({1}), type({0}) !== type({1})}}",
      operand, type);
}

std::string ComparingModule(std::string_view header, std::string_view decl,
                            std::string_view type) {
  const std::string kCompare = Comparisons("x", type);
  return std::format(
      "module {0};\n"
      "  {1}\n"
      "  bit [3:0] c, vi = {2};\n"
      "  bit [15:0] r;\n"
      "  function bit [3:0] fn(); return {2}; endfunction\n"
      "  assign c = {2};\n"
      "  initial #1 r = {{{2}, fn(), c, vi}};\n"
      "endmodule\n",
      header, decl, kCompare);
}

constexpr uint64_t kAllMatch = 0xAAAA;
constexpr uint64_t kNoneMatch = 0x5555;

TEST(TypeRefCompareInstanceSim, EachInstanceComparesItsOwnTypeParameter) {
  const std::string kModule =
      ComparingModule("m #(type T = int)", "T x;", "int");
  for (const std::string_view kTop :
       {"module t; m #(byte) b(); m #(int) a(); endmodule\n",
        "module t; m #(int) a(); m #(byte) b(); endmodule\n"}) {
    const std::string kSrc = kModule + std::string(kTop);
    SCOPED_TRACE(kTop);
    EXPECT_EQ(RunAndGet(kSrc, "a.r"), kAllMatch);
    EXPECT_EQ(RunAndGet(kSrc, "b.r"), kNoneMatch);
  }
}

TEST(TypeRefCompareInstanceSim, EachInstanceComparesItsOwnWidth) {
  const std::string kModule =
      ComparingModule("w #(int W = 8)", "logic [W-1:0] x;", "logic [7:0]");
  for (const std::string_view kTop :
       {"module t; w #(4) d(); w #(8) c(); endmodule\n",
        "module t; w #(8) c(); w #(4) d(); endmodule\n"}) {
    const std::string kSrc = kModule + std::string(kTop);
    SCOPED_TRACE(kTop);
    EXPECT_EQ(RunAndGet(kSrc, "c.r"), kAllMatch);
    EXPECT_EQ(RunAndGet(kSrc, "d.r"), kNoneMatch);
  }
}

TEST(TypeRefCompareInstanceSim, InterfaceProgramAndTaskCompareTheirOwnTypes) {
  const std::string kCompare = Comparisons("x", "int");
  const std::string kSrc = std::format(
      "interface ifc #(type T = int);\n"
      "  T x;\n"
      "  bit [3:0] r;\n"
      "  initial #1 r = {0};\n"
      "endinterface\n"
      "program pg #(type T = int);\n"
      "  T x;\n"
      "  bit [3:0] r;\n"
      "  initial #1 r = {0};\n"
      "endprogram\n"
      "module m #(type T = int);\n"
      "  T x;\n"
      "  bit [3:0] r;\n"
      "  task automatic tk(); r = {0}; endtask\n"
      "  initial #1 tk();\n"
      "endmodule\n"
      "module t;\n"
      "  ifc #(byte) i1(); ifc #(int) i2();\n"
      "  pg #(byte) p1(); pg #(int) p2();\n"
      "  m #(byte) m1(); m #(int) m2();\n"
      "endmodule\n",
      kCompare);
  for (const char* inst : {"i", "p", "m"}) {
    SCOPED_TRACE(inst);
    EXPECT_EQ(RunAndGet(kSrc, std::format("{}1.r", inst).c_str()), 0b0101u);
    EXPECT_EQ(RunAndGet(kSrc, std::format("{}2.r", inst).c_str()), 0b1010u);
  }
}

TEST(TypeRefCompareInstanceSim, ParameterWidthIsFoldedInConstantComparisons) {
  const std::string kSrc =
      "module w #(int W = 8);\n"
      "  localparam int K = W / 2;\n"
      "  localparam bit P = type(logic [W-1:0]) == type(logic [7:0]);\n"
      "  localparam bit Q = type(logic [K-1:0]) == type(logic [3:0]);\n"
      "  bit [2:0] r;\n"
      "  if (type(logic [W-1:0]) != type(logic [7:0])) begin : g\n"
      "    initial r[2] = 1;\n"
      "  end\n"
      "  initial r[1:0] = {P, Q};\n"
      "endmodule\n"
      "module t; w #(8) c(); w #(4) d(); endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "c.r"), 0b011u);
  EXPECT_EQ(RunAndGet(kSrc, "d.r"), 0b100u);
}

TEST(TypeRefCompareInstanceSim, EachLoopIterationComparesItsOwnWidth) {
  const std::string kCompare = Comparisons("v", "logic [0:0]");
  const std::string kSrc = std::format(
      "module t;\n"
      "  bit [31:0] r;\n"
      "  for (genvar i = 0; i < 2; i++) begin : g\n"
      "    logic [i:0] v;\n"
      "    bit [3:0] c, vi = {0};\n"
      "    function bit [3:0] fn(); return {0}; endfunction\n"
      "    assign c = {0};\n"
      "    initial #1 r[i*16 +: 16] = {{{0}, fn(), c, vi}};\n"
      "  end\n"
      "endmodule\n",
      kCompare);
  EXPECT_EQ(RunAndGet(kSrc, "r"), (kNoneMatch << 16) | kAllMatch);
}

TEST(TypeRefOverrideSim, TypeReferenceOverridesATypeParameter) {
  EXPECT_EQ(RunAndGet("module add_float #(type T = int) (input var T a);\n"
                      "  localparam int W = $bits(T);\n"
                      "  localparam bit IsReal = type(T) == type(real);\n"
                      "endmodule\n"
                      "module sub #(type T = int);\n"
                      "  localparam int W = $bits(T);\n"
                      "endmodule\n"
                      "interface ifc #(type T = int);\n"
                      "  localparam int W = $bits(T);\n"
                      "endinterface\n"
                      "module top;\n"
                      "  real R1;\n"
                      "  bit [12:0] A_bus;\n"
                      "  logic [4:0] n;\n"
                      "  int r;\n"
                      "  add_float #(type(R1)) u(R1);\n"
                      "  sub #(.T(type(A_bus))) s();\n"
                      "  ifc #(type(n + 3'b0)) i();\n"
                      "  initial r = u.W * 100000 + u.IsReal * 10000 + s.W * "
                      "100 + i.W;\n"
                      "endmodule\n",
                      "r"),
            6411305u);
}

constexpr std::array<InstanceTypeSpelling, 2> kTypeParameterReferences{{
    {"type T = int", "T", "type(y)", "var "},
    {"type T = int", "T", "type(y + y)", "var "},
}};

constexpr std::array<InstanceTypeSpelling, 2> kWidthParameterReferences{{
    {"int W = 32", "logic [W-1:0]", "type(y)", "var "},
    {"int W = 32", "logic [W-1:0]", "type(y + y)", "var "},
}};

TEST(ProceduralTypeRefInstanceSim, EachInstanceDeclaresWithItsTypeParameter) {
  for (const InstanceTypeSpelling& spelling : kTypeParameterReferences) {
    SCOPED_TRACE(spelling.declared);
    ExpectEachInstanceTakesItsType(spelling, {"byte", "int", "shortint"},
                                   ByteIntShortintExpected());
  }
}

TEST(ProceduralTypeRefInstanceSim, EachInstanceDeclaresWithItsWidth) {
  for (const InstanceTypeSpelling& spelling : kWidthParameterReferences) {
    SCOPED_TRACE(spelling.declared);
    ExpectEachInstanceTakesItsType(
        spelling, {"8", "32", "16"},
        InstanceTypeExpected({{"t.a", "44", "255", "8"},
                              {"t.b", "300", "511", "32"},
                              {"t.c", "300", "511", "16"}}));
  }
}

TEST(ProceduralTypeRefInstanceSim, EachLoopInstanceDeclaresWithItsType) {
  for (const InstanceTypeSpelling& spelling : kTypeParameterReferences) {
    SCOPED_TRACE(spelling.declared);
    ExpectEachLoopInstanceTakesItsType(spelling, "T(logic [4*i+3:0])");
  }
  for (const InstanceTypeSpelling& spelling : kWidthParameterReferences) {
    SCOPED_TRACE(spelling.declared);
    ExpectEachLoopInstanceTakesItsType(spelling, "W(4*i+4)");
  }
}

std::string ExpressionOperandModule(std::string_view kind,
                                    const InstanceTypeSpelling& spelling) {
  return std::format(
      "{0} w #({1});\n"
      "  {2} y;\n"
      "  var type(y + y) me;\n"
      "  typedef type(y + y) tt;\n"
      "  tt v;\n"
      "  initial begin\n"
      "    me = 300;\n"
      "    v = 300;\n"
      "    #1 $display(\"%m %0d %0d %0d %0d\", $bits(me), $bits(v), me, v);\n"
      "  end\n"
      "end{0}\n",
      kind, spelling.parameter, spelling.held);
}

TEST(DeclarationTypeRefInstanceSim, ExpressionOperandTakesEachInstancesType) {
  const std::array<std::array<std::string_view, 2>, 2> kActuals{
      {{"byte", "int"}, {"8", "32"}}};
  const std::vector<std::string> kExpected{"t.a 8 8 44 44",
                                           "t.b 32 32 300 300"};
  for (std::size_t p = 0; p < kActuals.size(); ++p) {
    const InstanceTypeSpelling& spelling =
        p == 0 ? kTypeParameterReferences[1] : kWidthParameterReferences[1];
    for (const char* kind : {"module", "interface", "program"}) {
      SCOPED_TRACE(std::format("{} {}", kind, spelling.held));
      const std::string kModule = ExpressionOperandModule(kind, spelling);
      const std::string kA = std::format("  w #({}) a();\n", kActuals[p][0]);
      const std::string kB = std::format("  w #({}) b();\n", kActuals[p][1]);
      EXPECT_EQ(SortedOutput(std::format("{}module t;\n{}{}endmodule\n",
                                         kModule, kA, kB)),
                kExpected);
      EXPECT_EQ(SortedOutput(std::format("{}module t;\n{}{}endmodule\n",
                                         kModule, kB, kA)),
                kExpected);
    }
  }
}

TEST(DeclarationTypeRefInstanceSim, EachLoopIterationDeclaresWithItsWidth) {
  EXPECT_EQ(
      SortedOutput("module t;\n"
                   "  for (genvar i = 0; i < 2; i++) begin : g\n"
                   "    logic [4*i+3:0] y;\n"
                   "    var type(y) z;\n"
                   "    var type(y + y) me;\n"
                   "    typedef type(y + y) tt;\n"
                   "    tt v;\n"
                   "    function automatic int f();\n"
                   "      var type(y + y) l;\n"
                   "      return $bits(l);\n"
                   "    endfunction\n"
                   "    initial begin\n"
                   "      var type(y) l;\n"
                   "      var type(y + y) e;\n"
                   "      #1 $display(\"%m %0d %0d %0d %0d %0d %0d\", "
                   "$bits(z), $bits(me),\n"
                   "                  $bits(v), $bits(l), $bits(e), f());\n"
                   "    end\n"
                   "  end\n"
                   "endmodule\n"),
      (std::vector<std::string>{"t.g[0] 4 4 4 4 4 4", "t.g[1] 8 8 8 8 8 8"}));
}

std::string AssociativeIndexSub(const InstanceTypeSpelling& spelling) {
  return std::format(
      "module sub #({0});\n"
      "  {1} y;\n"
      "  function automatic int fk();\n"
      "    int aa[{2}];\n"
      "    aa[300] = 1;\n"
      "    return aa.exists(44);\n"
      "  endfunction\n"
      "  initial begin\n"
      "    int aa[{2}];\n"
      "    aa[300] = 1;\n"
      "    #1 $display(\"%m %0d %0d\", aa.exists(44), fk());\n"
      "  end\n"
      "endmodule\n",
      spelling.parameter, spelling.held, spelling.declared);
}

void ExpectEachWidthInstanceKeysByItsIndex(const std::string& sub) {
  EXPECT_EQ(
      SortedOutput(sub + "module t; sub #(8) a(); sub #(16) b(); endmodule\n"),
      (std::vector<std::string>{"t.a 1 1", "t.b 0 0"}));
  EXPECT_EQ(SortedOutput(sub + "module t;\n"
                               "  for (genvar i = 0; i < 2; i++) begin : g\n"
                               "    sub #(8 * i + 8) s();\n"
                               "  end\n"
                               "endmodule\n"),
            (std::vector<std::string>{"t.g[0].s 1 1", "t.g[1].s 0 0"}));
}

TEST(ProceduralTypeRefInstanceSim, AssociativeIndexTakesEachInstancesType) {
  const std::vector<std::string> kExpected{"t.a 1 1", "t.b 0 0"};
  for (const InstanceTypeSpelling& spelling : kTypeParameterReferences) {
    SCOPED_TRACE(spelling.declared);
    const std::string kSub = AssociativeIndexSub(spelling);
    EXPECT_EQ(SortedOutput(kSub + "module t; sub #(byte) a(); sub #(int) b(); "
                                  "endmodule\n"),
              kExpected);
    EXPECT_EQ(SortedOutput(kSub + "module t; sub #(int) b(); sub #(byte) a(); "
                                  "endmodule\n"),
              kExpected);
  }
  ExpectEachWidthInstanceKeysByItsIndex(
      AssociativeIndexSub(kWidthParameterReferences[1]));
}

TEST(ProceduralTypeRefInstanceSim,
     DISABLED_IdentifierIndexTakesEachInstancesWidth) {
  ExpectEachWidthInstanceKeysByItsIndex(
      AssociativeIndexSub(kWidthParameterReferences[0]));
}

TEST(ProceduralTypeRefInstanceSim,
     DISABLED_CheckerProcedureTakesTheEnclosingVariablesType) {
  EXPECT_EQ(
      SortedOutput("module sub #(int W = 32);\n"
                   "  logic [W-1:0] y;\n"
                   "  checker ck;\n"
                   "    final begin\n"
                   "      var type(y) l;\n"
                   "      var type(y + y) e;\n"
                   "      l = 300;\n"
                   "      e = 300;\n"
                   "      $display(\"%m %0d %0d %0d %0d\", l, $bits(l), e, "
                   "$bits(e));\n"
                   "    end\n"
                   "  endchecker\n"
                   "  ck c();\n"
                   "endmodule\n"
                   "module t; sub #(8) a(); sub #(32) b(); endmodule\n"),
      (std::vector<std::string>{"t.a.c 44 8 44 8", "t.b.c 300 32 300 32"}));
}

class TypeRefBlockVariableVpi : public VpiDesignRun {
 protected:
  void ExpectEachInstancesKinds(const std::string& top) {
    Run(std::string("module sub #(type T = int);\n"
                    "  T y;\n"
                    "  initial begin : blk\n"
                    "    var type(y) v;\n"
                    "    T w;\n"
                    "  end\n"
                    "endmodule\n") +
        top);
    for (const char* name : {"t.a.blk.v", "t.a.blk.w"}) {
      ASSERT_NE(By(name), nullptr) << name;
      EXPECT_EQ(vpi_get(vpiType, By(name)), vpiByteVar) << name;
    }
    for (const char* name : {"t.b.blk.v", "t.b.blk.w"}) {
      ASSERT_NE(By(name), nullptr) << name;
      EXPECT_EQ(vpi_get(vpiType, By(name)), vpiIntVar) << name;
    }
  }
};

TEST_F(TypeRefBlockVariableVpi, EachInstanceHasItsKindWhenTheByteOneIsFirst) {
  ExpectEachInstancesKinds(
      "module t; sub #(byte) a(); sub #(int) b(); endmodule\n");
}

TEST_F(TypeRefBlockVariableVpi, EachInstanceHasItsKindWhenTheIntOneIsFirst) {
  ExpectEachInstancesKinds(
      "module t; sub #(int) b(); sub #(byte) a(); endmodule\n");
}

}  // namespace
