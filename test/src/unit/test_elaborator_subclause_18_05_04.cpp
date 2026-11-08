#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(UniqueMemberForms, SingularVariableGroupAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand byte a;\n"
             "  rand byte b;\n"
             "  rand byte excluded;\n"
             "  constraint u { unique {a, b, excluded}; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(UniqueMemberForms, ArraySliceMemberAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand byte a[5];\n"
             "  rand byte b;\n"
             "  rand byte excluded;\n"
             "  constraint u { unique {b, a[2:3], excluded}; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(UniqueMemberForms, LiteralMemberRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand byte a;\n"
             "  constraint u { unique {a, 5}; }\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a uniqueness constraint member shall denote a "
                            "singular or array variable",
                            3, "18.5.4"));
}

TEST(UniqueMemberForms, ArithmeticExpressionMemberRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand byte a;\n"
             "  rand byte b;\n"
             "  constraint u { unique {a + b}; }\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a uniqueness constraint member shall denote a "
                            "singular or array variable",
                            4, "18.5.4"));
}

TEST(UniqueMemberForms, SingularRealVariableGroupAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand real a;\n"
             "  rand real b;\n"
             "  constraint u { unique {a, b}; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(UniqueMemberForms, WholeUnpackedArrayMemberAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand byte a[5];\n"
             "  rand byte b;\n"
             "  constraint u { unique {a, b}; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(UniqueMemberForms, QualifiedMemberReferenceAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand byte a;\n"
             "  rand byte b;\n"
             "  constraint u { unique {this.a, this.b}; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(UniqueMemberForms, NonIntegralNonRealMemberRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int a;\n"
             "  string s;\n"
             "  constraint u { unique {a, s}; }\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a uniqueness constraint member shall be of "
                            "integral or real type",
                            4, "18.5.4"));
}

TEST(UniqueMemberForms, RandcMemberRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  randc bit [1:0] a;\n"
             "  rand bit [1:0] b;\n"
             "  constraint u { unique {b, a}; }\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a uniqueness constraint member shall not be "
                            "a randc variable",
                            4, "18.5.4"));
}

TEST(UniqueMemberForms, InheritedRandcMemberRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class B;\n"
             "  randc bit [2:0] a;\n"
             "endclass\n"
             "class C extends B;\n"
             "  rand bit [2:0] b[2];\n"
             "  constraint u { unique {b, a}; }\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a uniqueness constraint member shall not be "
                            "a randc variable",
                            6, "18.5.4"));
}

TEST(UniqueMemberForms, InlineRandcMemberThroughHandleRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand bit [1:0] a;\n"
             "  randc bit [1:0] b;\n"
             "endclass\n"
             "module m;\n"
             "  C c = new;\n"
             "  initial begin\n"
             "    C d;\n"
             "    d = new;\n"
             "    void'(c.randomize() with { unique {a, b}; });\n"
             "    void'(d.randomize() with { unique {b, a}; });\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a uniqueness constraint member shall not be a randc variable", 10,
      "18.5.4"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a uniqueness constraint member shall not be a randc variable", 11,
      "18.5.4"));
}

TEST(UniqueMemberForms, InlineRandcMemberInMethodRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand bit [1:0] a;\n"
             "  randc bit [1:0] b;\n"
             "  function int f();\n"
             "    return randomize() with { unique {a, b}; };\n"
             "  endfunction\n"
             "  function int g();\n"
             "    return this.randomize() with { unique {b, a}; };\n"
             "  endfunction\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a uniqueness constraint member shall not be a randc variable", 5,
      "18.5.4"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a uniqueness constraint member shall not be a randc variable", 8,
      "18.5.4"));
}

TEST(UniqueMemberForms, InlineRandMembersAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand bit [1:0] a;\n"
             "  rand bit [1:0] b;\n"
             "  function int f();\n"
             "    return randomize() with { unique {a, b}; };\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c = new;\n"
             "  initial void'(c.randomize() with { unique {a, b}; });\n"
             "endmodule\n"));
}

TEST(UniqueMemberForms, InlineRandcMemberThroughReceiverExpressionRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand bit [1:0] a;\n"
             "  randc bit [1:0] b;\n"
             "  static C inst;\n"
             "  function C self(); return this; endfunction\n"
             "  static function C make(); return inst; endfunction\n"
             "endclass\n"
             "class W;\n"
             "  C sub;\n"
             "endclass\n"
             "class V;\n"
             "  W w;\n"
             "endclass\n"
             "module m;\n"
             "  C o[2][2];\n"
             "  initial begin\n"
             "    W w;\n"
             "    V vv;\n"
             "    void'(o[0][1].randomize() with { unique {a, b}; });\n"
             "    void'(w.sub.randomize() with { unique {a, b}; });\n"
             "    void'(o[1][0].self().randomize() with { unique {a, b}; });\n"
             "    void'(C::inst.randomize() with { unique {a, b}; });\n"
             "    void'(C::make().randomize() with { unique {a, b}; });\n"
             "    void'(vv.w.sub.randomize() with { unique {a, b}; });\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_EQ(f.diag.ErrorCount(), 6u);
  for (uint32_t line : {19u, 20u, 21u, 22u, 23u, 24u}) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "a uniqueness constraint member shall not be a randc variable", line,
        "18.5.4"));
  }
}

TEST(UniqueMemberForms, InlineRandcMemberThroughMethodHandleRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand bit [1:0] a;\n"
             "  randc bit [1:0] b;\n"
             "endclass\n"
             "class B;\n"
             "  C inherited;\n"
             "endclass\n"
             "class H extends B;\n"
             "  C p;\n"
             "  extern function int later();\n"
             "  function int go(C arg);\n"
             "    C x;\n"
             "    return x.randomize() with { unique {a, b}; }\n"
             "         + arg.randomize() with { unique {a, b}; }\n"
             "         + p.randomize() with { unique {a, b}; }\n"
             "         + inherited.randomize() with { unique {a, b}; };\n"
             "  endfunction\n"
             "endclass\n"
             "function int H::later();\n"
             "  return p.randomize() with { unique {a, b}; };\n"
             "endfunction\n"
             "class Outer;\n"
             "  class Inner;\n"
             "    function int go(C h);\n"
             "      return h.randomize() with { unique {a, b}; };\n"
             "    endfunction\n"
             "  endclass\n"
             "endclass\n"
             "class E extends C;\n"
             "  function int go();\n"
             "    return super.randomize() with { unique {a, b}; };\n"
             "  endfunction\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_EQ(f.diag.ErrorCount(), 7u);
  for (uint32_t line : {13u, 14u, 15u, 16u, 20u, 25u, 31u}) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "a uniqueness constraint member shall not be a randc variable", line,
        "18.5.4"));
  }
}

TEST(UniqueMemberForms, InlineRandcMemberOutsideModuleProcedureRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand bit [1:0] a;\n"
             "  randc bit [1:0] b;\n"
             "endclass\n"
             "package p;\n"
             "  C g;\n"
             "  function int f();\n"
             "    return g.randomize() with { unique {a, b}; };\n"
             "  endfunction\n"
             "endpackage\n"
             "module m(input logic clk);\n"
             "  C c = new;\n"
             "  int r = c.randomize() with { unique {a, b}; };\n"
             "  function int f(C arg);\n"
             "    return arg.randomize() with { unique {a, b}; };\n"
             "  endfunction\n"
             "  task t();\n"
             "    void'(c.randomize() with { unique {a, b}; });\n"
             "  endtask\n"
             "  if (1) begin : g\n"
             "    C d;\n"
             "    initial void'(d.randomize() with { unique {a, b}; });\n"
             "  end\n"
             "  case (1)\n"
             "    1: begin : k\n"
             "      initial void'(c.randomize() with { unique {a, b}; });\n"
             "    end\n"
             "  endcase\n"
             "endmodule\n",
             f));
  EXPECT_EQ(f.diag.ErrorCount(), 6u);
  for (uint32_t line : {8u, 13u, 15u, 18u, 22u, 26u}) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "a uniqueness constraint member shall not be a randc variable", line,
        "18.5.4"));
  }
}

TEST(UniqueMemberForms, InlineReceiverResolvesInInnermostScope) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand bit [1:0] a;\n"
             "  randc bit [1:0] b;\n"
             "endclass\n"
             "class D;\n"
             "  rand bit [1:0] a;\n"
             "  rand bit [1:0] b;\n"
             "endclass\n"
             "module m;\n"
             "  C x;\n"
             "  C y;\n"
             "  class H;\n"
             "    function int go();\n"
             "      D x;\n"
             "      return x.randomize() with { unique {a, b}; }\n"
             "           + y.randomize() with { unique {a, b}; };\n"
             "    endfunction\n"
             "  endclass\n"
             "endmodule\n",
             f));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a uniqueness constraint member shall not be a randc variable", 16,
      "18.5.4"));
}

TEST(UniqueMemberForms, InlineRandGroupAcceptedWhateverTheReceiver) {
  EXPECT_TRUE(
      ElabOk("class D;\n"
             "  rand bit [1:0] a;\n"
             "  rand bit [1:0] b;\n"
             "endclass\n"
             "module child;\n"
             "  D d = new;\n"
             "  initial void'(m.x.randomize() with { unique {a, b}; });\n"
             "endmodule\n"
             "module m;\n"
             "  D x;\n"
             "  D q[$];\n"
             "  bit [1:0] v;\n"
             "  bit [1:0] w;\n"
             "  child u();\n"
             "  initial begin\n"
             "    void'(u.d.randomize() with { unique {a, b}; });\n"
             "    void'(q.pop_front().randomize() with { unique {a, b}; });\n"
             "    void'(std::randomize(v, w) with { unique {v, w}; });\n"
             "    void'(randomize(v, w) with { unique {v, w}; });\n"
             "  end\n"
             "endmodule\n"));
}

TEST(UniqueMemberForms, InlineRandcMemberThroughTypedefHandleRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("typedef class C;\n"
             "class C;\n"
             "  rand bit [1:0] a;\n"
             "  randc bit [1:0] b;\n"
             "endclass\n"
             "typedef C CT;\n"
             "typedef CT CT2;\n"
             "class W;\n"
             "  typedef C T;\n"
             "  T sub;\n"
             "endclass\n"
             "module m;\n"
             "  typedef C MT;\n"
             "  MT y;\n"
             "  initial begin\n"
             "    CT2 x;\n"
             "    W w;\n"
             "    C z;\n"
             "    void'(x.randomize() with { unique {a, b}; });\n"
             "    void'(y.randomize() with { unique {a, b}; });\n"
             "    void'(w.sub.randomize() with { unique {a, b}; });\n"
             "    void'(z.randomize() with { unique {a, b}; });\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_EQ(f.diag.ErrorCount(), 4u);
  for (uint32_t line : {19u, 20u, 21u, 22u}) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "a uniqueness constraint member shall not be a randc variable", line,
        "18.5.4"));
  }
}

TEST(UniqueMemberForms, InlineRandcMemberThroughInstanceHandleRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand bit [1:0] a;\n"
             "  randc bit [1:0] b;\n"
             "endclass\n"
             "module leaf;\n"
             "  C d;\n"
             "endmodule\n"
             "module mid;\n"
             "  C d;\n"
             "  leaf v();\n"
             "endmodule\n"
             "module m;\n"
             "  mid u();\n"
             "  mid ua[2] ();\n"
             "  initial begin\n"
             "    void'(u.d.randomize() with { unique {a, b}; });\n"
             "    void'(u.v.d.randomize() with { unique {a, b}; });\n"
             "    void'(ua[1].d.randomize() with { unique {a, b}; });\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_EQ(f.diag.ErrorCount(), 3u);
  for (uint32_t line : {16u, 17u, 18u}) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "a uniqueness constraint member shall not be a randc variable", line,
        "18.5.4"));
  }
}

TEST(UniqueMemberForms, InlineRandcMemberThroughPackageHandleRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand bit [1:0] a;\n"
             "  randc bit [1:0] b;\n"
             "endclass\n"
             "package p;\n"
             "  C g;\n"
             "  C h;\n"
             "endpackage\n"
             "package q;\n"
             "  C k;\n"
             "endpackage\n"
             "module m;\n"
             "  import p::*;\n"
             "  import q::k;\n"
             "  initial begin\n"
             "    void'(p::g.randomize() with { unique {a, b}; });\n"
             "    void'(h.randomize() with { unique {a, b}; });\n"
             "    void'(k.randomize() with { unique {a, b}; });\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_EQ(f.diag.ErrorCount(), 3u);
  for (uint32_t line : {16u, 17u, 18u}) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "a uniqueness constraint member shall not be a randc variable", line,
        "18.5.4"));
  }
}

TEST(UniqueMemberForms, InlineRandcMemberThroughUpwardReferenceRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand bit [1:0] a;\n"
             "  randc bit [1:0] b;\n"
             "endclass\n"
             "class W;\n"
             "  C sub;\n"
             "endclass\n"
             "module child;\n"
             "  initial void'(t.x.randomize() with { unique {a, b}; });\n"
             "endmodule\n"
             "module t;\n"
             "  C x;\n"
             "  W wm;\n"
             "  child u();\n"
             "  class H;\n"
             "    W own;\n"
             "    function int go();\n"
             "      return own.sub.randomize() with { unique {a, b}; }\n"
             "           + wm.sub.randomize() with { unique {a, b}; };\n"
             "    endfunction\n"
             "  endclass\n"
             "endmodule\n",
             f));
  EXPECT_EQ(f.diag.ErrorCount(), 3u);
  for (uint32_t line : {9u, 18u, 19u}) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "a uniqueness constraint member shall not be a randc variable", line,
        "18.5.4"));
  }
}

TEST(UniqueMemberForms, InlineRandcMemberThroughGenerateBlockHandleRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand bit [1:0] a;\n"
             "  randc bit [1:0] b;\n"
             "endclass\n"
             "module mid;\n"
             "  if (1) begin : gb\n"
             "    C h;\n"
             "  end\n"
             "endmodule\n"
             "module m;\n"
             "  if (1) begin : g\n"
             "    C h;\n"
             "  end else begin : ge\n"
             "    C h;\n"
             "  end\n"
             "  case (1)\n"
             "    1: begin : k\n"
             "      C h;\n"
             "    end\n"
             "  endcase\n"
             "  for (genvar i = 0; i < 2; i++) begin : gl\n"
             "    C h;\n"
             "  end\n"
             "  mid u();\n"
             "  initial begin\n"
             "    void'(g.h.randomize() with { unique {a, b}; });\n"
             "    void'(k.h.randomize() with { unique {a, b}; });\n"
             "    void'(gl[1].h.randomize() with { unique {a, b}; });\n"
             "    void'(u.gb.h.randomize() with { unique {a, b}; });\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_EQ(f.diag.ErrorCount(), 4u);
  for (uint32_t line : {26u, 27u, 28u, 29u}) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "a uniqueness constraint member shall not be a randc variable", line,
        "18.5.4"));
  }
}

TEST(UniqueMemberForms, InlineReceiverNamingNothingGetsNoUniquenessReport) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  rand bit [1:0] a;\n"
      "  randc bit [1:0] b;\n"
      "endclass\n"
      "module m;\n"
      "  initial void'(nosuch.x.randomize() with { unique {a, b}; });\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(ReportedError(
      f.diag.Diagnostics(),
      "a uniqueness constraint member shall not be a randc variable", 6,
      "18.5.4"));
}

TEST(UniqueMemberForms, InequivalentMemberTypesRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand byte a;\n"
             "  rand int b;\n"
             "  constraint u { unique {a, b}; }\n"
             "endclass\n"
             "module m;\n"
             "  C c = new;\n"
             "  initial void'(c.randomize() with { unique {b, a}; });\n"
             "endmodule\n",
             f));
  constexpr char kMessage[] =
      "the members of a uniqueness constraint shall be of equivalent types";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kMessage, 4, "18.5.4"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kMessage, 8, "18.5.4"));
}

TEST(UniqueMemberForms, EquivalentMemberTypesAccepted) {
  EXPECT_TRUE(
      ElabOk("typedef int int_t;\n"
             "class C;\n"
             "  rand byte b;\n"
             "  rand byte arr[5];\n"
             "  rand bit signed [7:0] s8;\n"
             "  rand bit [7:0] x;\n"
             "  rand int_t n;\n"
             "  constraint u { unique {b, arr[2:3], arr, s8}; }\n"
             "  constraint v { unique {b, x[3:0]}; unique {n, b}; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

}  // namespace
