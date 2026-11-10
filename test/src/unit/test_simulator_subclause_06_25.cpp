#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(ParameterizedDataTypesSim, SpecializedClassArrayTypedefHoldsItsElements) {
  const std::string kSrc =
      "module t;\n"
      "  class C #(parameter type T = logic, parameter SIZE = 1);\n"
      "    typedef T t_array [SIZE-1:0];\n"
      "  endclass\n"
      "  typedef logic [7:0] t_t0;\n"
      "  C#(t_t0,3)::t_array a0;\n"
      "  int eb, e0, sz;\n"
      "  initial begin\n"
      "    a0[0] = 200;\n"
      "    eb = $bits(a0[0]);\n"
      "    e0 = a0[0];\n"
      "    sz = $size(a0);\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "eb"), 8u);
  EXPECT_EQ(RunAndGet(kSrc, "e0"), 200u);
  EXPECT_EQ(RunAndGet(kSrc, "sz"), 3u);
}

TEST(ParameterizedDataTypesSim,
     SpecializedClassStructTypedefSpecializesMembers) {
  const std::string kSrc =
      "module t;\n"
      "  class C #(parameter type T = logic, parameter SIZE = 1);\n"
      "    typedef logic [SIZE-1:0] t_vector;\n"
      "    typedef T t_array [SIZE-1:0];\n"
      "    typedef struct {\n"
      "      t_vector m0 [2*SIZE-1:0];\n"
      "      t_array m1;\n"
      "      bit [SIZE-1:0] m2;\n"
      "    } t_struct;\n"
      "  endclass\n"
      "  typedef struct { logic [3:0] m0 [7:0]; } plain_t;\n"
      "  C#(bit,4)::t_struct s0;\n"
      "  plain_t p0;\n"
      "  int b2, e2, same0, bs;\n"
      "  initial begin\n"
      "    s0.m2 = 4'hB;\n"
      "    b2 = $bits(s0.m2);\n"
      "    e2 = s0.m2;\n"
      "    same0 = $bits(s0.m0) == $bits(p0.m0);\n"
      "    bs = $bits(s0);\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "b2"), 4u);
  EXPECT_EQ(RunAndGet(kSrc, "e2"), 11u);
  EXPECT_EQ(RunAndGet(kSrc, "same0"), 1u);
  EXPECT_EQ(RunAndGet(kSrc, "bs"), 40u);
}

TEST(ParameterizedDataTypesSim, StructTypedefThroughATypedefOfASpecialization) {
  const std::string kSrc =
      "module t;\n"
      "  class Base #(parameter p = 1);\n"
      "    typedef struct { real r; bit [p-1:0] data; } S;\n"
      "  endclass\n"
      "  typedef Base#(32) MyBaseT;\n"
      "  MyBaseT::S s;\n"
      "  Base#(16)::S u;\n"
      "  int bs, bu;\n"
      "  longint v;\n"
      "  initial begin\n"
      "    s.data = 32'hDEADBEEF;\n"
      "    bs = $bits(s.data);\n"
      "    bu = $bits(u.data);\n"
      "    v = s.data;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "bs"), 32u);
  EXPECT_EQ(RunAndGet(kSrc, "bu"), 16u);
  EXPECT_EQ(RunAndGet(kSrc, "v"), 0xDEADBEEFu);
}

constexpr std::string_view kClauseClass =
    "virtual class C#(parameter type T = logic, parameter SIZE = 1);\n"
    "  typedef logic [SIZE-1:0] t_vector;\n"
    "  typedef T t_array [SIZE-1:0];\n"
    "  typedef struct {\n"
    "    t_vector m0 [2*SIZE-1:0];\n"
    "    t_array m1;\n"
    "  } t_struct;\n"
    "endclass\n";

TEST(ParameterizedDataTypesSim, ClauseExampleDeclaresItsThreeTypes) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(std::string(kClauseClass) +
                     "module top ();\n"
                     "  typedef logic [7:0] t_t0;\n"
                     "  C#(t_t0,3)::t_vector v0;\n"
                     "  C#(t_t0,3)::t_array a0;\n"
                     "  C#(bit,4)::t_struct s0;\n"
                     "  C#(.SIZE(1+1), .T(shortint))::t_array a2;\n"
                     "  initial $display(\"%0d %0d %0d %0d %b %b %b %0d\",\n"
                     "    $bits(v0), $bits(a0), $bits(s0), $bits(a2), v0,\n"
                     "    a0[2], s0.m0[7], s0.m1[3]);\n"
                     "endmodule\n",
                 f),
      "3 24 36 32 xxx xxxxxxxx xxxx 0\n");
}

TEST(ParameterizedDataTypesSim, SpecializationsTypesMatchAsTheirParametersDo) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          std::string(kClauseClass) +
              "module top ();\n"
              "  typedef logic [7:0] t_t0;\n"
              "  typedef t_t0 ref_array [2:0];\n"
              "  C#(t_t0,3)::t_array a0;\n"
              "  ref_array r0;\n"
              "  initial $display(\"%0d%0d%0d%0d %0d%0d %0d\",\n"
              "    type(C#(t_t0,3)::t_vector) == type(logic [2:0]),\n"
              "    type(C#(t_t0,3)::t_vector) == type(C#(byte,3)::t_vector),\n"
              "    type(C#(t_t0,3)::t_vector) == type(C#(t_t0,4)::t_vector),\n"
              "    type(C#(t_t0,3)::t_vector) == type(bit [2:0]),\n"
              "    type(C#(bit,4)::t_struct) == type(C#(bit,4)::t_struct),\n"
              "    type(C#(bit,4)::t_struct) == type(C#(bit,5)::t_struct),\n"
              "    type(a0) == type(r0));\n"
              "endmodule\n",
          f),
      "1100 10 1\n");
}

TEST(ParameterizedDataTypesSim,
     DISABLED_SpecializationsArrayTypeMatchesThroughATypeReference) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(std::string(kClauseClass) +
                     "module top ();\n"
                     "  typedef logic [7:0] t_t0;\n"
                     "  typedef t_t0 ref_array [2:0];\n"
                     "  typedef C#(t_t0,3)::t_array via;\n"
                     "  C#(t_t0,3)::t_array a0;\n"
                     "  initial $display(\"%0d %0d %0d\",\n"
                     "    type(via) == type(ref_array),\n"
                     "    type(a0) == type(C#(t_t0,3)::t_array),\n"
                     "    type(C#(t_t0,3)::t_array) == type(ref_array));\n"
                     "endmodule\n",
                 f),
      "1 1 1\n");
}

TEST(ParameterizedDataTypesSim,
     DISABLED_SpecializationsTypeDeclaresAVariableInEveryPlace) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(std::string(kClauseClass) +
                     "package p;\n"
                     "  C#(byte, 2)::t_vector pv;\n"
                     "  function automatic int pf();\n"
                     "    C#(int, 5)::t_vector l;\n"
                     "    return $bits(l);\n"
                     "  endfunction\n"
                     "  function automatic C#(int, 3)::t_vector pr();\n"
                     "    return 7'h7F;\n"
                     "  endfunction\n"
                     "endpackage\n"
                     "interface ifc; C#(bit, 6)::t_vector iv; endinterface\n"
                     "class K; C#(bit, 9)::t_vector kv; endclass\n"
                     "program prg;\n"
                     "  C#(bit, 7)::t_array ra;\n"
                     "  initial #1 $display(\"%0d\", $bits(ra));\n"
                     "endprogram\n"
                     "module top ();\n"
                     "  C#(C#(byte,2)::t_vector, 3)::t_array a3;\n"
                     "  ifc i();\n"
                     "  prg pg();\n"
                     "  K k = new;\n"
                     "  initial $display(\"%0d %0d %0d %0d %0d %0d\",\n"
                     "    $bits(p::pv), p::pf(), p::pr(), $bits(i.iv),\n"
                     "    $bits(k.kv), $bits(a3));\n"
                     "endmodule\n",
                 f),
      "2 5 7 6 9 6\n7\n");
}

}  // namespace
