#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"

using namespace delta;

namespace {

int64_t ParamOfModule(const std::string& src, std::string_view mod,
                      std::string_view name, ElabFixture& f) {
  auto* design = ElaborateSrc(src, f, "top");
  if (design == nullptr) return -1;
  const auto* p = FindParam(design, mod, name);
  return p != nullptr && p->is_resolved ? p->resolved_value : -1;
}

std::string TypedefRangedModule(std::string_view name, std::string_view range) {
  std::string src = "module ";
  src += name;
  src +=
      ";\n"
      "  parameter int TOP = 15;\n"
      "  typedef logic [";
  src += range;
  src +=
      "] vec_t;\n"
      "  parameter vec_t P = 0;\n"
      "  localparam int B = $bits(P);\n"
      "endmodule\n";
  return src;
}

TEST(DefparamElaboration, SizesEachModulesTypedefParameterByItsOwnTypedef) {
  const std::string kSrc = TypedefRangedModule("a", "TOP:0") +
                           TypedefRangedModule("b", "TOP*4+3:0") +
                           "module top;\n"
                           "  a ua();\n"
                           "  b ub();\n"
                           "  defparam ua.TOP = 7;\n"
                           "  defparam ub.TOP = 3;\n"
                           "endmodule\n";
  ElabFixture fa;
  EXPECT_EQ(ParamOfModule(kSrc, "a", "B", fa), 8);
  EXPECT_FALSE(fa.has_errors);
  ElabFixture fb;
  EXPECT_EQ(ParamOfModule(kSrc, "b", "B", fb), 16);
}

TEST(DefparamElaboration, ResizesAGenerateBlocksParameterByTheBlocksTypedef) {
  ElabFixture f;
  EXPECT_EQ(ParamOfModule("module m;\n"
                          "  parameter int TOP = 15;\n"
                          "  typedef logic [3:0] vec_t;\n"
                          "  if (1) begin : g\n"
                          "    typedef logic [TOP:0] vec_t;\n"
                          "    parameter vec_t P = 0;\n"
                          "    localparam int B = $bits(P);\n"
                          "  end\n"
                          "endmodule\n"
                          "module top;\n"
                          "  m u();\n"
                          "  defparam u.TOP = 7;\n"
                          "endmodule\n",
                          "m", "B", f),
            8);
  EXPECT_FALSE(f.has_errors);
}

TEST(DefparamElaboration, SizesByTheSelectedAlternativesTypedefAlone) {
  ElabFixture f;
  EXPECT_EQ(ParamOfModule("module m;\n"
                          "  parameter int TOP = 15;\n"
                          "  if (1) begin : g\n"
                          "    typedef logic [TOP:0] vec_t;\n"
                          "    parameter vec_t P = 0;\n"
                          "    localparam int B = $bits(P);\n"
                          "  end else begin : g\n"
                          "    typedef logic [3:0] vec_t;\n"
                          "  end\n"
                          "endmodule\n"
                          "module top;\n"
                          "  m u();\n"
                          "  defparam u.TOP = 7;\n"
                          "endmodule\n",
                          "m", "B", f),
            8);
  EXPECT_FALSE(f.has_errors);
}

int64_t BlockParamOfM(RtlirDesign* design, std::string_view prefix,
                      std::string_view name) {
  const auto* m = FindModule(design, "m");
  if (m == nullptr) return -1;
  for (const auto& p : m->params) {
    if (p.name == name && p.gen_block_prefix == prefix) return p.resolved_value;
  }
  return -1;
}

TEST(DefparamElaboration, SizesEachLoopInstancesParameterByItsOwnTypedef) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int TOP = 15;\n"
      "  for (genvar i = 0; i < 2; i++) begin : g\n"
      "    typedef logic [TOP:0] vec_t;\n"
      "    parameter vec_t P = 0;\n"
      "    localparam int B = $bits(P);\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  m u();\n"
      "  defparam u.TOP = 7;\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(BlockParamOfM(design, "g_1_", "B"), 8);
  EXPECT_EQ(BlockParamOfM(design, "g_0_", "B"), 8);
  EXPECT_FALSE(f.has_errors);
}

constexpr std::string_view kWideningC =
    "module c;\n"
    "  parameter int W = 32;\n"
    "  parameter logic [W-1:0] P = 0;\n"
    "  localparam int H = P[95:64], M = P[47:32];\n"
    "endmodule\n";

int64_t WideParamOfC(std::string_view top_items, std::string_view name,
                     ElabFixture& f) {
  std::string src(kWideningC);
  src += "module top;\n";
  src += top_items;
  src += "endmodule\n";
  return ParamOfModule(src, "c", name, f);
}

void ExpectEveryWordOfP(std::string_view top_items) {
  ElabFixture fh;
  EXPECT_EQ(WideParamOfC(top_items, "H", fh), 1);
  EXPECT_FALSE(fh.has_errors);
  ElabFixture fm;
  EXPECT_EQ(WideParamOfC(top_items, "M", fm), 3);
}

TEST(DefparamElaboration, RefoldsAGenerateBlocksDefparamValueWithItsNames) {
  constexpr std::string_view kTop =
      "  if (1) begin : g\n"
      "    localparam logic [95:0] V = 96'h1_0000_0003_0000_0005;\n"
      "    c u();\n"
      "    defparam u.P = V;\n"
      "    defparam u.W = 96;\n"
      "  end\n";
  ExpectEveryWordOfP(kTop);
}

TEST(DefparamElaboration, ChildAssignmentReadsTheDefparamsValue) {
  ElabFixture f;
  EXPECT_EQ(ParamOfModule("module leaf #(parameter W = 8); endmodule\n"
                          "module mid;\n"
                          "  parameter WIDTH = 32;\n"
                          "  leaf #(.W(WIDTH)) l();\n"
                          "endmodule\n"
                          "module top;\n"
                          "  mid m();\n"
                          "  defparam m.WIDTH = 64;\n"
                          "endmodule\n",
                          "leaf", "W", f),
            64);
}

TEST(DefparamElaboration, DefparamsValueReachesAGrandchildsAssignment) {
  ElabFixture f;
  EXPECT_EQ(ParamOfModule("module leaf #(parameter W = 8); endmodule\n"
                          "module inner #(parameter V = 1);\n"
                          "  leaf #(.W(V + 1)) l();\n"
                          "endmodule\n"
                          "module mid;\n"
                          "  parameter WIDTH = 32;\n"
                          "  inner #(.V(WIDTH)) i();\n"
                          "endmodule\n"
                          "module top;\n"
                          "  mid m();\n"
                          "  defparam m.WIDTH = 64;\n"
                          "endmodule\n",
                          "leaf", "W", f),
            65);
}

TEST(DefparamElaboration, RefoldsAnInstanceOverrideALaterDefparamWidens) {
  constexpr std::string_view kTop =
      "  c #(.P(96'h1_0000_0003_0000_0005)) u();\n"
      "  defparam u.W = 96;\n";
  ExpectEveryWordOfP(kTop);
}

TEST(DefparamElaboration, RefoldsAnInstanceOverrideNamingTheParentsParameter) {
  constexpr std::string_view kTop =
      "  localparam logic [95:0] PP = 96'h1_0000_0003_0000_0005;\n"
      "  c #(.P(PP)) u();\n"
      "  defparam u.W = 96;\n";
  ExpectEveryWordOfP(kTop);
}

TEST(DefparamElaboration, WidensAnInstanceOverrideGivenInThePortList) {
  constexpr std::string_view kTop =
      "  c #(.W(96), .P(96'h1_0000_0003_0000_0005)) u();\n";
  ExpectEveryWordOfP(kTop);
}

::testing::AssertionResult EscapeReportedAt(const ElabFixture& f,
                                            uint32_t line) {
  return ReportedError(
      f.diag.Diagnostics(),
      "defparam inside a generate block or an array of instances "
      "reaches a parameter outside that hierarchy",
      line, "23.10.1");
}

TEST(DefparamElaboration, ModuleUnderAGenerateBlockCannotEscapeIt) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module c;\n"
      "  parameter int P = 1;\n"
      "endmodule\n"
      "module w;\n"
      "  defparam top.u2.P = 5;\n"
      "  defparam top.Q = 6;\n"
      "endmodule\n"
      "module top;\n"
      "  parameter int Q = 1;\n"
      "  c u2();\n"
      "  if (1) begin : g\n"
      "    w u();\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  const auto* p = FindParam(design, "c", "P");
  ASSERT_NE(p, nullptr);
  EXPECT_EQ(p->resolved_value, 1);
  const auto* q = FindParam(design, "top", "Q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->resolved_value, 1);
  EXPECT_TRUE(EscapeReportedAt(f, 5));
  EXPECT_TRUE(EscapeReportedAt(f, 6));
}

TEST(DefparamElaboration, ModuleUnderANestedGenerateBlockCannotEscapeIt) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module c;\n"
      "  parameter int P = 1;\n"
      "endmodule\n"
      "module x;\n"
      "  defparam top.u2.P = 5;\n"
      "endmodule\n"
      "module w;\n"
      "  x v();\n"
      "endmodule\n"
      "module mid;\n"
      "  if (1) begin : g\n"
      "    w u();\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  c u2();\n"
      "  mid m();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  const auto* p = FindParam(design, "c", "P");
  ASSERT_NE(p, nullptr);
  EXPECT_EQ(p->resolved_value, 1);
  EXPECT_TRUE(EscapeReportedAt(f, 5));
}

TEST(DefparamElaboration, ModuleUnderAGenerateBlockReachesItsSibling) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module c;\n"
      "  parameter int P = 1;\n"
      "endmodule\n"
      "module w;\n"
      "  defparam top.g.u3.P = 5;\n"
      "endmodule\n"
      "module top;\n"
      "  if (1) begin : g\n"
      "    c u3();\n"
      "    w u();\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  const auto* p = FindParam(design, "c", "P");
  ASSERT_NE(p, nullptr);
  EXPECT_EQ(p->resolved_value, 5);
  EXPECT_FALSE(f.has_errors);
}

TEST(DefparamElaboration, ModuleInAnInstanceArrayElementCannotEscapeIt) {
  ElabFixture f;
  ElaborateSrc(
      "module c;\n"
      "  parameter int P = 1;\n"
      "endmodule\n"
      "module cel;\n"
      "  c c();\n"
      "  defparam top.u[1].c.P = 5;\n"
      "endmodule\n"
      "module top;\n"
      "  cel u[0:1]();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(EscapeReportedAt(f, 6));
}

TEST(DefparamElaboration, ModuleInAnInstanceArrayElementReachesItsOwnChild) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module c;\n"
      "  parameter int P = 1;\n"
      "endmodule\n"
      "module cel;\n"
      "  c c();\n"
      "  defparam c.P = 5;\n"
      "endmodule\n"
      "module top;\n"
      "  cel u[0:1]();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  const auto* p = FindParam(design, "c", "P");
  ASSERT_NE(p, nullptr);
  EXPECT_EQ(p->resolved_value, 5);
  EXPECT_FALSE(f.has_errors);
}

TEST(DefparamElaboration, NamedBlockLocalparamTakesNoDefparam) {
  ElabFixture f;
  ElaborateSrc(
      "module c;\n"
      "  initial begin : blk\n"
      "    localparam L = 3;\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  defparam u.blk.L = 6;\n"
      "  c u();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "defparam cannot override a local parameter", 7,
                            "23.10.1"));
}

TEST(DefparamElaboration, NamedBlockParameterDefparamNeedsAConstant) {
  ElabFixture f;
  ElaborateSrc(
      "module c;\n"
      "  initial begin : blk\n"
      "    parameter Q = 3;\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  defparam u.blk.Q = $time;\n"
      "  c u();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "defparam value is not constant", 7, "23.10.1"));
}

TEST(DefparamElaboration, PathsReachingNoBlockParameterAreNotFound) {
  ElabFixture f;
  ElaborateSrc(
      "module c;\n"
      "  parameter P = 1;\n"
      "  task t;\n"
      "    int v;\n"
      "    parameter A = 1;\n"
      "    v = A;\n"
      "  endtask\n"
      "  initial begin : blk\n"
      "    parameter Q = 3;\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  c u();\n"
      "  defparam Nope = 1;\n"
      "  defparam u.blk[0].Q = 2;\n"
      "  defparam u.t[0].A = 2;\n"
      "  defparam u.t.Nope = 2;\n"
      "  defparam u[0].P = 2;\n"
      "endmodule\n",
      f, "top");
  for (int line = 14; line <= 18; ++line) {
    EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                                "defparam target not found", line, "23.10.1"))
        << "line " << line;
  }
}

TEST(DefparamElaboration, AnUnresolvedInstanceLeavesAnElementsDefparam) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module c;\n"
      "  parameter P = 1;\n"
      "  nope m();\n"
      "endmodule\n"
      "module top;\n"
      "  nope n();\n"
      "  c u[0:1]();\n"
      "  defparam u[1].P = 2;\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "unknown module 'nope'", 6,
                            "23.3.2"));
  EXPECT_EQ(f.diag.WarningCount(), 0u);
  ASSERT_NE(design, nullptr);
}

TEST(DefparamElaboration, ASelectOfOneIndexNamesNoElementOfATwoDimArray) {
  ElabFixture f;
  ElaborateSrc(
      "module sub; parameter P = 1; endmodule\n"
      "module top;\n"
      "  sub c[1:0][2:0] ();\n"
      "  defparam c[1].P = 5;\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(), "defparam target not found",
                              4, "23.10.1"));
}

constexpr std::string_view kPartScopes =
    "module child;\n  parameter int P = 0;\nendmodule\n"
    "package p;\n  typedef struct { int a; } s_t;\n"
    "  parameter s_t S = '{a: 1};\nendpackage\n"
    "module other;\n  typedef struct { int a; } s_t;\n"
    "  parameter s_t S = '{a: 2};\n  parameter int N = 1;\nendmodule\n";

constexpr std::string_view kPartTypes =
    "  typedef struct { int a; } in_t;\n"
    "  typedef struct { int arr [2]; in_t in; int a; } s_t;\n";

std::string PartParams(const std::string& indent) {
  return indent + "parameter s_t S = '{arr: '{4, 5}, in: '{a: 6}, a: 7};\n" +
         indent + "parameter in_t IA [2] = '{'{a: 8}, '{a: 9}};\n";
}

std::string TopWith(const std::string& body) {
  return std::string(kPartScopes) + "module top;\n  other o();\n" +
         std::string(kPartTypes) + body + "endmodule\n";
}

struct DefparamPlace {
  const char* where;
  std::string (*source)(const std::string& value);
  uint32_t line;
};

constexpr DefparamPlace kDefparamPlaces[] = {
    {"a module body defparam reading the module's parameter",
     [](const std::string& value) {
       return TopWith(PartParams("  ") +
                      "  child u();\n  defparam u.P = " + value + ";\n");
     },
     20},
    {"a generate block defparam reading the module's parameter",
     [](const std::string& value) {
       return TopWith(PartParams("  ") +
                      "  if (1) begin : g\n    child u();\n"
                      "    defparam u.P = " +
                      value + ";\n  end\n");
     },
     21},
    {"a generate block defparam reading the block's parameter",
     [](const std::string& value) {
       return TopWith("  if (1) begin : g\n" + PartParams("    ") +
                      "    child u();\n    defparam u.P = " + value +
                      ";\n  end\n");
     },
     21},
};

TEST(DefparamElaboration, RhsMayReadAPartOfAParameterOfItsOwnModule) {
  const char* const kValues[] = {"S.a", "S.in.a", "S.arr[1]", "IA[1].a"};
  for (const DefparamPlace& place : kDefparamPlaces) {
    for (const char* value : kValues) {
      SCOPED_TRACE(std::string(place.where) + ", " + value);
      ElabFixture f;
      ElaborateSrc(place.source(value), f, "top");
      EXPECT_FALSE(f.has_errors);
    }
  }
}

TEST(DefparamElaboration, RhsRejectsAPartOfAParameterOfAnotherScope) {
  const char* const kValues[] = {"o.S.a", "p::S", "p::S.a", "IA[o.N].a"};
  for (const DefparamPlace& place : kDefparamPlaces) {
    for (const char* value : kValues) {
      SCOPED_TRACE(std::string(place.where) + ", " + value);
      ElabFixture f;
      ElaborateSrc(place.source(value), f, "top");
      EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                                "defparam right-hand side may only reference "
                                "parameters declared in the same module",
                                place.line, "23.10.1"));
    }
  }
}

}  // namespace
