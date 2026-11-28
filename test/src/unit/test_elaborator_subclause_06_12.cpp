#include <gtest/gtest.h>

#include <initializer_list>
#include <string>
#include <string_view>

#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "helpers_generate_block_items.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(RealDataType, RealNegedgeError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  real a;\n"
      "  always @(negedge a)\n"
      "    $display(\"negedge\");\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "edge event on real type is illegal", 3, "6.12"));
}

TEST(RealDataType, RealTypesNotIntegral) {
  EXPECT_FALSE(IsIntegralType(DataTypeKind::kReal));
  EXPECT_FALSE(IsIntegralType(DataTypeKind::kShortreal));
  EXPECT_FALSE(IsIntegralType(DataTypeKind::kRealtime));
}

TEST(RealDataType, RealPosedgeError) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  real a = 0.5;\n"
      "  always @(posedge a)\n"
      "    $display(\"posedge\");\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "edge event on real type is illegal", 3, "6.12"));
}

TEST(RealDataType, RealIndexInBitSelectError) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  real a = 0.5;\n"
      "  wire [3:0] b;\n"
      "  wire c;\n"
      "  assign c = b[a];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "real type used as index is illegal", 5, "6.12"));
}

TEST(RealDataType, AllRealTypesElaborateWithIsReal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  shortreal sr;\n"
      "  realtime rt;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 3u);
  EXPECT_TRUE(mod->variables[0].is_real) << "real";
  EXPECT_EQ(mod->variables[0].width, 64u) << "real width";
  EXPECT_TRUE(mod->variables[1].is_real) << "shortreal";
  EXPECT_EQ(mod->variables[1].width, 32u) << "shortreal width";
  EXPECT_TRUE(mod->variables[2].is_real) << "realtime";
  EXPECT_EQ(mod->variables[2].width, 64u) << "realtime width";
}

TEST(RealDataType, RealtimePosedgeError) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  realtime a;\n"
      "  always @(posedge a)\n"
      "    $display(\"posedge\");\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "edge event on real type is illegal", 3, "6.12"));
}

TEST(RealDataType, RealAssignmentOk) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  real a = 0.5;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(RealDataType, RealEdgeKeywordError) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  real a;\n"
      "  always @(edge a)\n"
      "    $display(\"edge\");\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "edge event on real type is illegal", 3, "6.12"));
}

TEST(RealDataType, RealBitSelectError) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  real a = 0.5;\n"
      "  wire b;\n"
      "  assign b = a[2];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select of a real variable is illegal", 4,
                            "6.12"));
}

TEST(RealDataType, RealPartSelectError) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  real a = 0.5;\n"
      "  wire [3:0] b;\n"
      "  assign b = a[3:0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "part-select of a real variable is illegal", 4,
                            "6.12"));
}

TEST(RealDataType, ShortrealBitSelectError) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  shortreal a = 1.0;\n"
      "  wire b;\n"
      "  assign b = a[0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select of a real variable is illegal", 4,
                            "6.12"));
}

TEST(RealDataType, ShortrealEdgeControlError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  shortreal a;\n"
      "  always @(posedge a)\n"
      "    $display(\"posedge\");\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "edge event on real type is illegal", 3, "6.12"));
}

TEST(RealDataType, RealtimeBitSelectError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  realtime a;\n"
      "  wire b;\n"
      "  assign b = a[0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select of a real variable is illegal", 4,
                            "6.12"));
}

TEST(RealDataType, RealIndexInPartSelectError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  real a = 1.0;\n"
      "  wire [7:0] b;\n"
      "  wire [1:0] c;\n"
      "  assign c = b[a +: 2];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "real type used as index is illegal", 5, "6.12"));
}

TEST(RealDataType, RealAndRealtimeInterchangeable) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  real r;\n"
      "  realtime rt;\n"
      "  initial begin\n"
      "    r = 1.5;\n"
      "    rt = r;\n"
      "    r = rt;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(RealDataType, RealEdgeInAProceduralEventControlError) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r = 0.0;\n"
      "  initial begin\n"
      "    fork\n"
      "      @(posedge r) $display(\"edge\");\n"
      "      #1 r = 1.0;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "edge event on real type is illegal", 5, "6.12"));
}

TEST(RealDataType, RealEdgeOnABlockLocalRealError) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real m;\n"
      "  task tk;\n"
      "    real x;\n"
      "    @(m);\n"
      "    @(negedge x);\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "edge event on real type is illegal", 6, "6.12"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

TEST(RealDataType, EdgeAndSelectOfARealInsideGenerateBlocksAreRejected) {
  EXPECT_TRUE(RejectedInsideGenerateBlocks(
      {"", "real r; logic y;", "always @(posedge r) y = 0;"},
      "edge event on real type is illegal", "6.12"));
  EXPECT_TRUE(RejectedInsideGenerateBlocks(
      {"", "real r; wire y;", "assign y = r[0];"},
      "bit-select of a real variable is illegal", "6.12"));
  EXPECT_TRUE(RejectedInsideGenerateBlocks(
      {"", "real r; logic y;", "initial y = r[0];"},
      "bit-select of a real variable is illegal", "6.12"));
  EXPECT_TRUE(AcceptedInsideGenerateBlocks(
      {"", "real r; logic y;", "always @(r) y = 0;"}));
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  real r;\n"
             "  logic y;\n"
             "  if (1) begin : g\n"
             "    logic [3:0] r;\n"
             "    initial y = r[0];\n"
             "  end\n"
             "endmodule\n"));
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [3:0] r;\n"
             "  logic y;\n"
             "  if (1) begin : g1\n"
             "    real r;\n"
             "  end\n"
             "  if (1) begin : g2\n"
             "    initial y = r[0];\n"
             "  end\n"
             "endmodule\n"));
}

::testing::AssertionResult RealUseReported(const std::string& src,
                                           std::string_view marker,
                                           std::string_view message) {
  ElabFixture f;
  ElaborateSrc(src, f);
  return ReportedError(f.diag.Diagnostics(), message, LineHolding(src, marker),
                       "6.12");
}

constexpr std::string_view kEdge = "edge event on real type is illegal";
constexpr std::string_view kBitSelect =
    "bit-select of a real variable is illegal";
constexpr std::string_view kPartSelect =
    "part-select of a real variable is illegal";
constexpr std::string_view kIndex = "real type used as index is illegal";

TEST(RealDataType, EdgeOfARealInAnInterfaceProgramAndCheckerIsReported) {
  EXPECT_TRUE(RealUseReported(
      "interface i;\n  real r;\n  logic y;\n  always @(posedge r) y = 0;\n"
      "endinterface\nmodule t;\n  i u();\nendmodule\n",
      "posedge r", kEdge));
  EXPECT_TRUE(RealUseReported(
      "program p;\n  real r;\n  initial @(negedge r);\nendprogram\n"
      "module t;\n  p u();\nendmodule\n",
      "negedge r", kEdge));
  EXPECT_TRUE(
      RealUseReported("checker c(logic clk);\n  real r;\n  logic z;\n"
                      "  always_ff @(edge r) z <= 0;\nendchecker\n"
                      "module t;\n  logic clk;\n  c u(clk);\nendmodule\n",
                      "edge r", kEdge));
}

TEST(RealDataType, EdgeOfARealInAClassPackageOrUnitTaskIsReported) {
  EXPECT_TRUE(RealUseReported(
      "class C;\n  real r;\n  task tk();\n    @(posedge r);\n  endtask\n"
      "endclass\nmodule t;\nendmodule\n",
      "posedge r", kEdge));
  EXPECT_TRUE(RealUseReported(
      "package k;\n  real r;\n  task automatic tk();\n    @(negedge r);\n"
      "  endtask\nendpackage\nmodule t;\nendmodule\n",
      "negedge r", kEdge));
  EXPECT_TRUE(
      RealUseReported("real r;\ntask automatic tk();\n  @(edge r);\nendtask\n"
                      "module t;\nendmodule\n",
                      "edge r", kEdge));
}

TEST(RealDataType, AnyChangeOfARealInAClassPackageOrUnitTaskIsAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n  real r;\n  task tk();\n    @(r);\n  endtask\n"
             "endclass\npackage k;\n  real r;\n  task automatic tk();\n"
             "    @(r);\n  endtask\nendpackage\nreal r;\n"
             "task automatic tk();\n  @(r);\nendtask\nmodule t;\nendmodule\n"));
}

TEST(RealDataType, EdgeOfAnInheritedThisNestedOrOutOfBlockRealIsReported) {
  EXPECT_TRUE(RealUseReported(
      "class B;\n  real p;\nendclass\nclass D extends B;\n  task tk();\n"
      "    @(posedge p);\n  endtask\nendclass\nmodule t;\nendmodule\n",
      "posedge p", kEdge));
  EXPECT_TRUE(RealUseReported(
      "class C;\n  real p;\n  task tk();\n    @(negedge this.p);\n"
      "  endtask\nendclass\nmodule t;\nendmodule\n",
      "negedge this.p", kEdge));
  EXPECT_TRUE(RealUseReported(
      "class C;\n  real p;\n  extern task tk();\nendclass\n"
      "task C::tk();\n  @(edge p);\nendtask\nmodule t;\nendmodule\n",
      "edge p", kEdge));
  EXPECT_TRUE(
      RealUseReported("class O;\n  class I;\n    real p;\n    task tk();\n"
                      "      @(posedge p);\n    endtask\n  endclass\nendclass\n"
                      "module t;\nendmodule\n",
                      "posedge p", kEdge));
}

TEST(RealDataType, AnyChangeOfAnInheritedThisNestedOrOutOfBlockRealIsAccepted) {
  EXPECT_TRUE(
      ElabOk("class B;\n  real p;\nendclass\nclass D extends B;\n"
             "  task tk();\n    @(p or this.p);\n  endtask\nendclass\n"
             "class C;\n  real p;\n  extern task tk();\nendclass\n"
             "task C::tk();\n  @(p);\nendtask\nclass O;\n  class I;\n"
             "    real p;\n    task tk();\n      @(p);\n    endtask\n"
             "  endclass\nendclass\nmodule t;\nendmodule\n"));
}

TEST(RealDataType,
     EdgeAndSelectOfAnElementOfATypedefRealArrayFormalAreReported) {
  const std::string kSrc =
      "module t;\n  typedef real RB[2];\n  logic y;\n  task tk(RB a);\n"
      "    @(negedge a[1]);\n    y = a[0][0];\n  endtask\nendmodule\n";
  EXPECT_TRUE(RealUseReported(kSrc, "negedge a[1]", kEdge));
  EXPECT_TRUE(RealUseReported(kSrc, "a[0][0]", kBitSelect));
}

TEST(RealDataType, AnyChangeOfAnElementOfATypedefRealArrayFormalIsAccepted) {
  EXPECT_TRUE(
      ElabOk("module t;\n  typedef real RB[2];\n  logic y;\n"
             "  task tk(RB a);\n    @(a[1]);\n    y = a[0] > 0.0;\n"
             "  endtask\nendmodule\n"));
}

std::string RealOperands(std::string_view use) {
  return std::string(
             "package k;\n  real pr;\nendpackage\nmodule t;\n"
             "  typedef struct { real m; } S;\n  S st;\n  real ra[2];\n"
             "  class C;\n    real p;\n  endclass\n  C c = new;\n"
             "  logic y;\n  task tk(real a);\n    ")
      .append(use)
      .append("\n  endtask\nendmodule\n");
}

TEST(RealDataType, EdgeOfARealFormalMemberElementOrPropertyIsReported) {
  const char* const kUses[] = {
      "@(posedge a);",   "@(negedge st.m);",  "@(edge ra[0]);",
      "@(posedge c.p);", "@(negedge k::pr);", "@(posedge t.ra[1]);",
  };
  for (const char* use : kUses) {
    SCOPED_TRACE(use);
    EXPECT_TRUE(RealUseReported(RealOperands(use), use, kEdge));
  }
}

TEST(RealDataType, AnyChangeOfARealFormalMemberElementOrPropertyIsAccepted) {
  EXPECT_TRUE(ElabOk(
      RealOperands("@(a or st.m or ra[0] or c.p or k::pr or t.ra[1]);")));
}

TEST(RealDataType, EdgeOfARealInEveryProceduralEventControlIsReported) {
  const char* const kUses[] = {
      "always_ff @(posedge r) y <= 0;",
      "always @(posedge x or negedge r) y = 0;",
      "initial y = @(posedge r) 1;",
      "initial repeat (2) @(edge r) y = 1;",
      "initial @(posedge r iff x);",
      "initial y <= @(negedge r) 0;",
  };
  for (const char* use : kUses) {
    SCOPED_TRACE(use);
    std::string src = std::string("module t;\n  real r;\n  logic x, y;\n  ")
                          .append(use)
                          .append("\nendmodule\n");
    EXPECT_TRUE(RealUseReported(src, use, kEdge));
  }
}

TEST(RealDataType, EdgeOfARealAsAClockingOrAssertionEventIsReported) {
  const char* const kUses[] = {
      "clocking cb @(posedge r); endclocking",
      "a1: assert property (@(posedge r) x);",
      "sequence sq; @(negedge r) x; endsequence",
      "property pp; @(edge r) x; endproperty",
  };
  for (const char* use : kUses) {
    SCOPED_TRACE(use);
    std::string src = std::string("module t;\n  real r;\n  logic x;\n  ")
                          .append(use)
                          .append("\nendmodule\n");
    EXPECT_TRUE(RealUseReported(src, use, kEdge));
  }
}

TEST(RealDataType, AClockingOrAssertionEventOnABitIsAccepted) {
  EXPECT_TRUE(
      ElabOk("module t;\n  real r;\n  logic x, k;\n"
             "  clocking cb @(posedge k); endclocking\n"
             "  a1: assert property (@(posedge k) x);\n"
             "  sequence sq; @(negedge k) x; endsequence\n"
             "  property pp; @(edge k) x; endproperty\nendmodule\n"));
}

TEST(RealDataType, SelectOfARealInAnInterfaceProgramAndCheckerIsReported) {
  EXPECT_TRUE(
      RealUseReported("interface i;\n  real r;\n  wire y;\n  assign y = r[0];\n"
                      "endinterface\nmodule t;\n  i u();\nendmodule\n",
                      "r[0]", kBitSelect));
  EXPECT_TRUE(RealUseReported(
      "program p;\n  real r;\n  logic [1:0] y;\n  initial y = r[1:0];\n"
      "endprogram\nmodule t;\n  p u();\nendmodule\n",
      "r[1:0]", kPartSelect));
  EXPECT_TRUE(RealUseReported(
      "checker c(logic clk);\n  real r;\n  logic y;\n  assign y = r[0];\n"
      "endchecker\nmodule t;\n  logic clk;\n  c u(clk);\nendmodule\n",
      "r[0]", kBitSelect));
}

TEST(RealDataType, SelectOfARealInAClassPackageOrUnitFunctionIsReported) {
  EXPECT_TRUE(RealUseReported(
      "class C;\n  real r;\n  function logic f();\n    return r[0];\n"
      "  endfunction\nendclass\nmodule t;\nendmodule\n",
      "r[0]", kBitSelect));
  EXPECT_TRUE(RealUseReported(
      "package k;\n  real r;\n  function automatic logic f();\n"
      "    return r[0];\n  endfunction\nendpackage\nmodule t;\nendmodule\n",
      "r[0]", kBitSelect));
  EXPECT_TRUE(RealUseReported(
      "real r;\nfunction automatic logic [1:0] f();\n  return r[1:0];\n"
      "endfunction\nmodule t;\nendmodule\n",
      "r[1:0]", kPartSelect));
}

TEST(RealDataType, SelectOfAVectorInAClassPackageOrUnitFunctionIsAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n  logic [3:0] r;\n  function logic f();\n"
             "    return r[0];\n  endfunction\nendclass\npackage k;\n"
             "  logic [3:0] r;\n  function automatic logic f();\n"
             "    return r[0];\n  endfunction\nendpackage\nlogic [3:0] r;\n"
             "function automatic logic [1:0] f();\n  return r[1:0];\n"
             "endfunction\nmodule t;\nendmodule\n"));
}

TEST(RealDataType, EverySelectFormOfARealIsReported) {
  struct Use {
    const char* text;
    std::string_view message;
  };
  const Use kUses[] = {
      {"initial r[0] = 1;", kBitSelect},
      {"assign r[1] = 1;", kBitSelect},
      {"initial y = r[0+:2];", kPartSelect},
      {"initial y = r[3-:2];", kPartSelect},
      {"initial y = s[1:0];", kPartSelect},
      {"initial y = q[3+:2];", kPartSelect},
      {"initial y = ra[0][0];", kBitSelect},
  };
  for (const Use& use : kUses) {
    SCOPED_TRACE(use.text);
    std::string src = std::string(
                          "module t;\n  real r;\n  shortreal s;\n"
                          "  realtime q;\n  real ra[2];\n  logic [1:0] y;\n  ")
                          .append(use.text)
                          .append("\nendmodule\n");
    EXPECT_TRUE(RealUseReported(src, use.text, use.message));
  }
}

TEST(RealDataType, SelectOfARealFormalMemberPropertyOrPackageVarIsReported) {
  const char* const kUses[] = {
      "y = a[0];",
      "y = st.m[0];",
      "y = c.p[0];",
      "y = k::pr[0];",
  };
  for (const char* use : kUses) {
    SCOPED_TRACE(use);
    EXPECT_TRUE(RealUseReported(RealOperands(use), use, kBitSelect));
  }
}

TEST(RealDataType, ElementOfARealArrayAndWholeRealOperandsAreAccepted) {
  EXPECT_TRUE(ElabOk(
      RealOperands("y = ra[1] > 0.0 || a > 0.0 || st.m > 0.0 || c.p > 0.0 || "
                   "k::pr > 0.0;")));
}

std::string RealNames(std::string_view use) {
  return std::string(
             "real ur;\npackage k;\n  real ir;\nendpackage\nmodule s;\n"
             "  real r;\nendmodule\nclass G;\n  static real sp;\nendclass\n"
             "module t;\n  import k::ir;\n  struct { real m; } is;\n"
             "  typedef real RA[2];\n  RA ta;\n  typedef struct { RA m; } T;\n"
             "  T tt;\n  s u();\n  logic y;\n  initial begin\n    ")
      .append(use)
      .append("\n  end\nendmodule\n");
}

TEST(RealDataType, EdgeOfARealReachedThroughEveryNameIsReported) {
  const char* const kUses[] = {
      "@(posedge is.m);",    "@(negedge u.r);",   "@(edge $unit::ur);",
      "@(posedge ir);",      "@(negedge G::sp);", "@(edge ta[0]);",
      "@(posedge tt.m[1]);",
  };
  for (const char* use : kUses) {
    SCOPED_TRACE(use);
    EXPECT_TRUE(RealUseReported(RealNames(use), use, kEdge));
  }
}

TEST(RealDataType, AnyChangeOfARealReachedThroughEveryNameIsAccepted) {
  EXPECT_TRUE(ElabOk(RealNames(
      "@(is.m or u.r or $unit::ur or ir or G::sp or ta[0] or tt.m[1]);")));
}

TEST(RealDataType, SelectOfARealReachedThroughEveryNameIsReported) {
  const char* const kUses[] = {
      "y = is.m[0];",  "y = u.r[0];",   "y = $unit::ur[0];", "y = ir[0];",
      "y = G::sp[0];", "y = ta[0][0];", "y = tt.m[1][0];",
  };
  for (const char* use : kUses) {
    SCOPED_TRACE(use);
    EXPECT_TRUE(RealUseReported(RealNames(use), use, kBitSelect));
  }
}

TEST(RealDataType, ARealReachedThroughEveryNameIsAcceptedWhole) {
  EXPECT_TRUE(ElabOk(
      RealNames("y = ta[0] > 0.0 || tt.m[1] > 0.0 || is.m > 0.0 || "
                "u.r > 0.0 || $unit::ur > 0.0 || ir > 0.0 || G::sp > 0.0;")));
}

TEST(RealDataType, RealIndexInAProgramAndCheckerIsReported) {
  EXPECT_TRUE(RealUseReported(
      "program p;\n  real r;\n  logic [3:0] v;\n  logic y;\n"
      "  initial y = v[r];\nendprogram\nmodule t;\n  p u();\nendmodule\n",
      "v[r]", kIndex));
  EXPECT_TRUE(RealUseReported(
      "checker c(logic clk);\n  real r;\n  logic [3:0] v;\n  logic y;\n"
      "  assign y = v[r];\nendchecker\n"
      "module t;\n  logic clk;\n  c u(clk);\nendmodule\n",
      "v[r]", kIndex));
}

TEST(RealDataType, RealIndexInAClassPackageOrUnitFunctionIsReported) {
  EXPECT_TRUE(RealUseReported(
      "class C;\n  real r;\n  logic [3:0] v;\n  function logic f();\n"
      "    return v[r];\n  endfunction\nendclass\nmodule t;\nendmodule\n",
      "v[r]", kIndex));
  EXPECT_TRUE(RealUseReported(
      "package k;\n  real r;\n  logic [3:0] v;\n"
      "  function automatic logic f();\n    return v[r];\n  endfunction\n"
      "endpackage\nmodule t;\nendmodule\n",
      "v[r]", kIndex));
  EXPECT_TRUE(RealUseReported(
      "real r;\nlogic [3:0] v;\nfunction automatic logic [1:0] f();\n"
      "  return v[r+:2];\nendfunction\nmodule t;\nendmodule\n",
      "v[r+:2]", kIndex));
}

TEST(RealDataType, IntegralIndexInAClassPackageOrUnitFunctionIsAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n  real r;\n  logic [3:0] v;\n  function logic f();\n"
             "    return v[int'(r)];\n  endfunction\nendclass\npackage k;\n"
             "  real r;\n  logic [3:0] v;\n  function automatic logic f();\n"
             "    return v[$rtoi(r)];\n  endfunction\nendpackage\nreal r;\n"
             "logic [3:0] v;\nfunction automatic logic [1:0] f();\n"
             "  return v[int'(r)+:2];\nendfunction\nmodule t;\nendmodule\n"));
}

std::string IndexUse(std::string_view use) {
  return std::string(
             "module t;\n  real r = 1.0;\n  shortreal s = 1.0;\n"
             "  realtime q = 1.0;\n  logic [7:0] v;\n  logic [1:0] y;\n  ")
      .append(use)
      .append("\nendmodule\n");
}

void ExpectIndexUsesReported(std::initializer_list<const char*> uses) {
  for (const char* use : uses) {
    SCOPED_TRACE(use);
    EXPECT_TRUE(RealUseReported(IndexUse(use), use, kIndex));
  }
}

TEST(RealDataType, RealIndexOfEveryRealTypeReadOrAssignedIsReported) {
  ExpectIndexUsesReported({"initial y = v[s];", "initial y = v[q];",
                           "initial y = v[r -: 2];", "initial v[r] = 1;",
                           "initial v[r+:2] = 0;"});
}

TEST(RealDataType, RealLiteralRealExpressionAndRealRangeIndexAreReported) {
  ExpectIndexUsesReported({"initial y = v[1.5];", "initial y = v[r * 2];",
                           "initial y = v[2.0:1];"});
}

TEST(RealDataType, ConvertedRealIndexFormsAreAccepted) {
  EXPECT_TRUE(ElabOk(
      IndexUse("initial begin\n    y = v[int'(1.5)];\n    y = v[int'(q)];\n"
               "    y = v[$rtoi(r * 2)];\n    v[int'(r)] = 1;\n"
               "    v[int'(r)+:2] = 0;\n    y = v[int'(s)];\n  end")));
}

TEST(RealDataType, EveryRealValuedIndexExpressionIsReported) {
  ExpectIndexUsesReported({
      "initial y = v[-r];",
      "initial y = v[y ? r : 1];",
      "initial y = v[real'(y)];",
      "initial y = v[shortreal'(1)];",
      "initial y = v[$itor(1)];",
      "initial y = v[$realtime];",
      "initial y = v[1ns];",
      "parameter real P = 1.5; initial y = v[P];",
      "function real g(); return 1.5; endfunction initial y = v[g()];",
      "initial y = v[1:r];",
  });
}

TEST(RealDataType, EveryIntegralIndexExpressionIsAccepted) {
  EXPECT_TRUE(
      ElabOk(IndexUse("parameter int P = 1;\n  function int g(); return 1; "
                      "endfunction\n  initial begin\n    y = v[~y];\n"
                      "    y = v[y ? 1 : 0];\n    y = v[int'(r)];\n"
                      "    y = v[$rtoi(1.5)];\n    y = v[$time];\n"
                      "    y = v[P];\n    y = v[g()];\n    y = v[1:0];\n"
                      "  end")));
}

TEST(RealDataType, ARealtimeArrayAssignsToARealArrayAndBack) {
  EXPECT_TRUE(
      ElabOk("module t;\n  real a[2];\n  realtime b[2];\n"
             "  initial begin\n    a = b;\n    b = a;\n  end\nendmodule\n"));
}

TEST(RealDataType, ARealArrayAssignsToARealArray) {
  EXPECT_TRUE(
      ElabOk("module t;\n  real a[2];\n  real b[2];\n"
             "  initial begin\n    a = b;\n    b = a;\n  end\nendmodule\n"));
}

TEST(RealDataType, AShortrealArrayDoesNotAssignToARealArray) {
  EXPECT_FALSE(
      ElabOk("module t;\n  real a[2];\n  shortreal b[2];\n"
             "  initial a = b;\nendmodule\n"));
}

}  // namespace
