#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <limits>
#include <string>
#include <string_view>
#include <utility>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"

using namespace delta;

namespace {

constexpr std::string_view kPackage =
    "package pk;\n"
    "  parameter real R = 2.5;\n"
    "  parameter shortreal SR = 0.1;\n"
    "  parameter realtime RT = 1.5;\n"
    "  parameter U = 2.5;\n"
    "  parameter real RI = 2;\n"
    "  parameter string S = \"hey\";\n"
    "  parameter int N = 2;\n"
    "  parameter string S2 = {S, \"!\"};\n"
    "  parameter string S3 = {N{\"ab\"}};\n"
    "  parameter string SA [2] = '{\"ab\", \"cde\"};\n"
    "  parameter real RA [2] = '{1.25, 3.5};\n"
    "  parameter real R2 = R * 2;\n"
    "endpackage\n";

const double kShortrealTenthLess = static_cast<double>(0.1F) - 0.1;

double RealParam(RtlirDesign* design, std::string_view mod,
                 std::string_view name) {
  const RtlirParamDecl* p = FindParam(design, mod, name);
  return p != nullptr && p->is_real_value ? p->resolved_real : -1.0;
}

std::string StringParam(RtlirDesign* design, std::string_view mod,
                        std::string_view name) {
  const RtlirParamDecl* p = FindParam(design, mod, name);
  return p != nullptr && p->is_string_value ? std::string(p->resolved_string)
                                            : "<no string>";
}

int64_t IntParam(RtlirDesign* design, std::string_view mod,
                 std::string_view name) {
  const RtlirParamDecl* p = FindParam(design, mod, name);
  return p != nullptr && p->is_resolved ? p->resolved_value : -1;
}

int64_t BlockIntParam(RtlirDesign* design, std::string_view mod,
                      std::string_view prefix, std::string_view name) {
  const RtlirModule* m = FindModule(design, mod);
  if (m == nullptr) return -1;
  for (const auto& p : m->params) {
    if (p.name == name && p.gen_block_prefix == prefix)
      return p.is_resolved && !p.is_real_value ? p.resolved_value : -1;
  }
  return -1;
}

void ExpectReals(
    RtlirDesign* design, std::string_view mod,
    std::initializer_list<std::pair<std::string_view, double>> reals) {
  for (auto [name, value] : reals)
    EXPECT_DOUBLE_EQ(RealParam(design, mod, name), value) << name;
}

void ExpectStrings(
    RtlirDesign* design, std::string_view mod,
    std::initializer_list<std::pair<std::string_view, std::string_view>>
        strings) {
  for (auto [name, value] : strings)
    EXPECT_EQ(StringParam(design, mod, name), value) << name;
}

void ExpectInts(
    RtlirDesign* design, std::string_view mod,
    std::initializer_list<std::pair<std::string_view, int64_t>> ints) {
  for (auto [name, value] : ints)
    EXPECT_EQ(IntParam(design, mod, name), value) << name;
}

void ExpectWidth(RtlirDesign* design, std::string_view name, uint32_t width) {
  const RtlirVariable* v = FindVar(design, "m", name);
  ASSERT_NE(v, nullptr) << name;
  EXPECT_EQ(v->width, width) << name;
}

TEST(UnitParamValueRead, PackageParameterByItsScopedName) {
  ElabFixture f;
  auto* design = ElaborateSrc(std::string(kPackage) +
                                  "module m;\n"
                                  "  localparam real X1 = pk::R * 2;\n"
                                  "  localparam int I1 = $rtoi(pk::R * 4);\n"
                                  "  localparam int I2 = pk::R * 2;\n"
                                  "  localparam real X2 = pk::SR - 0.1;\n"
                                  "  localparam real X3 = pk::RT * 2;\n"
                                  "  localparam real X4 = pk::U * 2;\n"
                                  "  localparam real X5 = pk::R2;\n"
                                  "  localparam real X6 = pk::RA[0] * 2;\n"
                                  "  localparam real X7 = pk::RI / 4;\n"
                                  "  localparam string T1 = pk::S;\n"
                                  "  localparam string T2 = pk::SA[1];\n"
                                  "  localparam int L1 = pk::S.len();\n"
                                  "  localparam int L2 = pk::SA[1].len();\n"
                                  "  localparam int G1 = pk::S.getc(1);\n"
                                  "  localparam int E1 = pk::S == \"hey\";\n"
                                  "  localparam string T3 = pk::S2;\n"
                                  "  localparam string T4 = pk::S3;\n"
                                  "  localparam int L3 = pk::S3.len();\n"
                                  "  localparam int E2 = pk::S3 == \"abab\";\n"
                                  "  logic [$rtoi(pk::R * 4)-1:0] v1;\n"
                                  "  logic [pk::S.len()-1:0] v2;\n"
                                  "  if ($rtoi(pk::R * 4) == 10) begin : g1\n"
                                  "    logic taken_real;\n"
                                  "  end\n"
                                  "  if (pk::S == \"hey\") begin : g2\n"
                                  "    logic taken_string;\n"
                                  "  end\n"
                                  "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ExpectReals(design, "m",
              {{"X1", 5.0},
               {"X2", kShortrealTenthLess},
               {"X3", 3.0},
               {"X4", 5.0},
               {"X5", 5.0},
               {"X6", 2.5},
               {"X7", 0.5}});
  ExpectStrings(design, "m",
                {{"T1", "hey"}, {"T2", "cde"}, {"T3", "hey!"}, {"T4", "abab"}});
  ExpectInts(design, "m",
             {{"I1", 10},
              {"I2", 5},
              {"L1", 3},
              {"L2", 3},
              {"L3", 4},
              {"G1", 'e'},
              {"E1", 1},
              {"E2", 1}});
  ExpectWidth(design, "v1", 10);
  ExpectWidth(design, "v2", 3);
  EXPECT_EQ(CountVarsEndingIn(design, "m", "taken_real"), 1u);
  EXPECT_EQ(CountVarsEndingIn(design, "m", "taken_string"), 1u);
}

TEST(UnitParamValueRead, PackageParameterImportedIntoAModuleBody) {
  for (const char* imports :
       {"  import pk::*;\n",
        "  import pk::R;\n  import pk::S;\n  import pk::SR;\n"
        "  import pk::SA;\n  import pk::RI;\n  import pk::S3;\n"}) {
    ElabFixture f;
    auto* design =
        ElaborateSrc(std::string(kPackage) + "module m;\n" + imports +
                         "  localparam real X1 = R * 2;\n"
                         "  localparam real X2 = SR - 0.1;\n"
                         "  localparam real X3 = RI / 4;\n"
                         "  localparam int I1 = $rtoi(R * 4);\n"
                         "  localparam int I2 = R * 2;\n"
                         "  localparam int I3 = RI * 3;\n"
                         "  localparam string T1 = S;\n"
                         "  localparam string T2 = SA[1];\n"
                         "  localparam string T3 = S3;\n"
                         "  localparam int L1 = S.len();\n"
                         "  logic [$rtoi(R * 4)-1:0] v1;\n"
                         "  logic [S.len()-1:0] v2;\n"
                         "  if ($rtoi(R * 4) == 10) begin : g\n"
                         "    logic taken_real;\n"
                         "  end\n"
                         "endmodule\n",
                     f);
    ASSERT_NE(design, nullptr);
    EXPECT_FALSE(f.has_errors) << imports;
    ExpectReals(design, "m",
                {{"X1", 5.0}, {"X2", kShortrealTenthLess}, {"X3", 0.5}});
    ExpectStrings(design, "m", {{"T1", "hey"}, {"T2", "cde"}, {"T3", "abab"}});
    ExpectInts(design, "m", {{"I1", 10}, {"I2", 5}, {"I3", 6}, {"L1", 3}});
    ExpectWidth(design, "v1", 10);
    ExpectWidth(design, "v2", 3);
    EXPECT_EQ(CountVarsEndingIn(design, "m", "taken_real"), 1u) << imports;
  }
}

TEST(UnitParamValueRead, PackageParameterImportedInAModuleHeader) {
  ElabFixture f;
  auto* design =
      ElaborateSrc(std::string(kPackage) +
                       "module m import pk::*; #(parameter real P = R * 2,\n"
                       "                         parameter string Q = S) ();\n"
                       "  localparam real X1 = SR - 0.1;\n"
                       "  localparam int L1 = Q.len();\n"
                       "endmodule\n",
                   f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ExpectReals(design, "m", {{"P", 5.0}, {"X1", kShortrealTenthLess}});
  ExpectStrings(design, "m", {{"Q", "hey"}});
  ExpectInts(design, "m", {{"L1", 3}});
}

TEST(UnitParamValueRead, LocalNameHidesAnImportedRealParameter) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      std::string(kPackage) +
          "class E #(int R = 1);\n"
          "  parameter int H = R / 2;\n"
          "  parameter string S = \"zzz\";\n"
          "  parameter string Q = pk::S2;\n"
          "endclass\n"
          "class F #(real R = 1.0);\n"
          "  parameter real P = pk::R2;\n"
          "endclass\n"
          "module c;\n"
          "  import pk::*;\n"
          "  localparam int W = R * 2;\n"
          "endmodule\n"
          "module g;\n"
          "  import pk::*;\n"
          "  for (genvar R = 0; R < 4; R++) begin : l\n"
          "    localparam int Q = R / 2;\n"
          "    localparam Q2 = R / 2;\n"
          "    if ($rtoi(R * 4.0) == 12) begin : h\n"
          "      logic taken;\n"
          "    end\n"
          "    c ci();\n"
          "  end\n"
          "endmodule\n"
          "module m;\n"
          "  import pk::*;\n"
          "  g u();\n"
          "  function automatic int twice(int R);\n"
          "    return R * 2;\n"
          "  endfunction\n"
          "  function automatic int halve(int R);\n"
          "    return R / 2;\n"
          "  endfunction\n"
          "  function automatic int halve_local(int x);\n"
          "    int R;\n"
          "    R = x;\n"
          "    return R / 2;\n"
          "  endfunction\n"
          "  function automatic int halve_loop(int x);\n"
          "    halve_loop = 0;\n"
          "    for (int R = x; R == x; R = R + 1) halve_loop = R / 2;\n"
          "  endfunction\n"
          "  function automatic int RT(int x);\n"
          "    return (RT + x) / 2;\n"
          "  endfunction\n"
          "  function automatic real half(int R);\n"
          "    return R / 2.0;\n"
          "  endfunction\n"
          "  localparam int F1 = twice(4);\n"
          "  localparam int F2 = twice(3);\n"
          "  localparam int F3 = halve(3);\n"
          "  localparam int F4 = halve_local(3);\n"
          "  localparam int F5 = halve_loop(3);\n"
          "  localparam int F6 = RT(3);\n"
          "  localparam int F7 = E#(3)::H;\n"
          "  localparam real H1 = half(3);\n"
          "  localparam real H2 = F#(7.0)::P;\n"
          "  localparam string T = E#(3)::Q;\n"
          "  localparam real X = R * 2;\n"
          "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ExpectInts(design, "m",
             {{"F1", 8},
              {"F2", 6},
              {"F3", 1},
              {"F4", 1},
              {"F5", 1},
              {"F6", 1},
              {"F7", 1}});
  ExpectReals(design, "m", {{"H1", 1.5}, {"H2", 5.0}, {"X", 5.0}});
  ExpectStrings(design, "m", {{"T", "hey!"}});
  ExpectInts(design, "c", {{"W", 5}});
  EXPECT_EQ(CountVarsEndingIn(design, "g", "taken"), 1u);
  EXPECT_EQ(BlockIntParam(design, "g", "l_3_", "Q"), 1);
  EXPECT_EQ(BlockIntParam(design, "g", "l_3_", "Q2"), 1);
}

TEST(UnitParamValueRead, PackageParameterReadFromAnotherPackage) {
  ElabFixture f;
  auto* design = ElaborateSrc(std::string(kPackage) +
                                  "package q;\n"
                                  "  import pk::*;\n"
                                  "  parameter real Q1 = R * 2;\n"
                                  "  parameter real Q2 = pk::R * 2;\n"
                                  "  parameter string QS = S;\n"
                                  "  parameter string QT = pk::S;\n"
                                  "endpackage\n"
                                  "package q2;\n"
                                  "  import pk::R;\n"
                                  "  parameter real Q3 = R * 4;\n"
                                  "endpackage\n"
                                  "module m;\n"
                                  "  localparam real X1 = q::Q1;\n"
                                  "  localparam real X2 = q::Q2;\n"
                                  "  localparam real X3 = q2::Q3;\n"
                                  "  localparam string T1 = q::QS;\n"
                                  "  localparam string T2 = q::QT;\n"
                                  "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ExpectReals(design, "m", {{"X1", 5.0}, {"X2", 5.0}, {"X3", 10.0}});
  ExpectStrings(design, "m", {{"T1", "hey"}, {"T2", "hey"}});
}

TEST(UnitParamValueRead, CompilationUnitParameter) {
  ElabFixture f;
  auto* design = ElaborateSrc(std::string(kPackage) +
                                  "package pc;\n"
                                  "  parameter real PR = 0.75;\n"
                                  "  parameter string PS = \"yo\";\n"
                                  "endpackage\n"
                                  "import pc::*;\n"
                                  "parameter real R = 2.5;\n"
                                  "parameter string S = \"hey\";\n"
                                  "parameter real W = pk::R * 2;\n"
                                  "parameter real W2 = PR * 4;\n"
                                  "parameter V = 1.25;\n"
                                  "parameter int CN = 2;\n"
                                  "parameter string CS = {CN{S}};\n"
                                  "module n;\n"
                                  "  localparam int R = 9;\n"
                                  "  localparam real X = $unit::R * 2;\n"
                                  "endmodule\n"
                                  "module m;\n"
                                  "  n u();\n"
                                  "  localparam real X1 = $unit::R * 2;\n"
                                  "  localparam real X2 = R * 2;\n"
                                  "  localparam real X3 = $unit::W;\n"
                                  "  localparam real X4 = V * 2;\n"
                                  "  localparam real X5 = W2;\n"
                                  "  localparam real X6 = PR * 2;\n"
                                  "  localparam string T1 = $unit::S;\n"
                                  "  localparam string T2 = S;\n"
                                  "  localparam string T3 = PS;\n"
                                  "  localparam string T4 = CS;\n"
                                  "  localparam int L1 = S.len();\n"
                                  "  localparam int L2 = $unit::S.len();\n"
                                  "  logic [$rtoi($unit::R * 4)-1:0] v1;\n"
                                  "  if ($rtoi(R * 4) == 10) begin : g\n"
                                  "    logic taken_real;\n"
                                  "  end\n"
                                  "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ExpectReals(design, "m",
              {{"X1", 5.0},
               {"X2", 5.0},
               {"X3", 5.0},
               {"X4", 2.5},
               {"X5", 3.0},
               {"X6", 1.5}});
  ExpectReals(design, "n", {{"X", 5.0}});
  ExpectStrings(design, "m",
                {{"T1", "hey"}, {"T2", "hey"}, {"T3", "yo"}, {"T4", "heyhey"}});
  ExpectInts(design, "m", {{"L1", 3}, {"L2", 3}});
  ExpectWidth(design, "v1", 10);
  EXPECT_EQ(CountVarsEndingIn(design, "m", "taken_real"), 1u);
}

TEST(UnitParamValueRead, ClassParameterAndSpecialization) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  parameter real R = 2.5;\n"
      "  parameter string S = \"hey\";\n"
      "  parameter real R2 = R * 2;\n"
      "  parameter int N = 2;\n"
      "  parameter string S2 = {S, \"!\"};\n"
      "  parameter string S3 = {N{\"ab\"}};\n"
      "endclass\n"
      "class D #(int N = 1, string T = \"a\");\n"
      "  parameter real RZ = 1.0 / (N - 2);\n"
      "  parameter real R = N * 1.25;\n"
      "  parameter real R2 = R * 2;\n"
      "  parameter U = N * 0.5;\n"
      "  parameter K = N + 1;\n"
      "  parameter shortreal SR = N * 0.05;\n"
      "  parameter string S = \"hey\";\n"
      "  parameter string S2 = {S, \"!\"};\n"
      "  parameter string S3 = {N{\"ab\"}};\n"
      "  parameter string TT = {T, \"x\"};\n"
      "  parameter int L = S3.len();\n"
      "  parameter int K2 = R * 2;\n"
      "  parameter real BIG = 1.0e308 * N;\n"
      "endclass\n"
      "module m;\n"
      "  localparam real X1 = C::R * 2;\n"
      "  localparam real X2 = C::R2;\n"
      "  localparam real X3 = D#(2)::R;\n"
      "  localparam real X4 = D#(2)::R * 2;\n"
      "  localparam real X5 = D#(2)::R2;\n"
      "  localparam real X6 = D#(2)::U;\n"
      "  localparam real X7 = D#(2)::K * 0.5;\n"
      "  localparam real X8 = D#(2)::N * 1.5;\n"
      "  localparam real X9 = D#(2)::SR - 0.1;\n"
      "  localparam real X10 = D#(10)::BIG;\n"
      "  localparam string T1 = C::S;\n"
      "  localparam string T2 = D#(2)::S;\n"
      "  localparam int L1 = C::S.len();\n"
      "  localparam int L2 = D#(2)::S.len();\n"
      "  localparam string T3 = C::S2;\n"
      "  localparam string T4 = C::S3;\n"
      "  localparam string T5 = D#(2)::S2;\n"
      "  localparam string T6 = D#(2)::S3;\n"
      "  localparam string T7 = D#(2, \"b\")::TT;\n"
      "  localparam string T8 = D#(2)::TT;\n"
      "  localparam int L3 = D#(3)::L;\n"
      "  localparam int K1 = D#(2)::K2;\n"
      "  localparam int I1 = D#(2)::R;\n"
      "  logic [$rtoi(C::R * 4)-1:0] v1;\n"
      "  logic [$rtoi(D#(2)::R * 4)-1:0] v2;\n"
      "  if ($rtoi(C::R * 4) == 10) begin : g\n"
      "    logic taken_real;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ExpectReals(design, "m",
              {{"X1", 5.0},
               {"X2", 5.0},
               {"X3", 2.5},
               {"X4", 5.0},
               {"X5", 5.0},
               {"X6", 1.0},
               {"X7", 1.5},
               {"X8", 3.0},
               {"X9", kShortrealTenthLess},
               {"X10", std::numeric_limits<double>::infinity()}});
  ExpectStrings(design, "m",
                {{"T1", "hey"},
                 {"T2", "hey"},
                 {"T3", "hey!"},
                 {"T4", "abab"},
                 {"T5", "hey!"},
                 {"T6", "abab"},
                 {"T7", "bx"},
                 {"T8", "ax"}});
  ExpectInts(design, "m",
             {{"L1", 3}, {"L2", 3}, {"L3", 6}, {"K1", 5}, {"I1", 3}});
  ExpectWidth(design, "v1", 10);
  ExpectWidth(design, "v2", 10);
  EXPECT_EQ(CountVarsEndingIn(design, "m", "taken_real"), 1u);
}

TEST(UnitParamValueRead, ReadInAGenerateBlockInterfaceAndProgram) {
  ElabFixture f;
  auto* design = ElaborateSrc(std::string(kPackage) +
                                  "interface i;\n"
                                  "  localparam real X1 = pk::R * 2;\n"
                                  "  localparam string T1 = pk::S;\n"
                                  "endinterface\n"
                                  "program pr;\n"
                                  "  localparam real X1 = pk::R * 2;\n"
                                  "  localparam string T1 = pk::S;\n"
                                  "endprogram\n"
                                  "module m;\n"
                                  "  i u();\n"
                                  "  pr w();\n"
                                  "  if (1) begin : g\n"
                                  "    localparam real X1 = pk::R * 2;\n"
                                  "    if ($rtoi(X1 * 2) == 10) begin : h\n"
                                  "      logic taken_real;\n"
                                  "    end\n"
                                  "    if (pk::S == \"hey\") begin : k\n"
                                  "      logic taken_string;\n"
                                  "    end\n"
                                  "  end\n"
                                  "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  for (std::string_view mod : {"i", "pr"}) {
    ExpectReals(design, mod, {{"X1", 5.0}});
    ExpectStrings(design, mod, {{"T1", "hey"}});
  }
  EXPECT_EQ(CountVarsEndingIn(design, "m", "taken_real"), 1u);
  EXPECT_EQ(CountVarsEndingIn(design, "m", "taken_string"), 1u);
}

TEST(UnitParamValueRead, VariableByItsScopedNameIsNoConstant) {
  ElabFixture f;
  ElaborateSrc(
      "package pk;\n"
      "  real v = 2.5;\n"
      "  string s = \"hey\";\n"
      "endpackage\n"
      "class D #(int N = 1);\n"
      "  static real w = 1.0;\n"
      "  static string sw = \"x\";\n"
      "endclass\n"
      "module m;\n"
      "  localparam real X = pk::v * 2;\n"
      "  localparam string T = pk::s;\n"
      "  localparam real Y = D#(2)::w * 2;\n"
      "  localparam string Z = D#(2)::sw;\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(
      diags, "localparam 'X' initializer is not a constant expression", 10,
      "6.20.4"));
  EXPECT_TRUE(ReportedError(
      diags, "localparam 'T' initializer is not a constant expression", 11,
      "6.20.4"));
  EXPECT_TRUE(ReportedError(
      diags, "localparam 'Y' initializer is not a constant expression", 12,
      "6.20.4"));
  EXPECT_TRUE(ReportedError(
      diags, "localparam 'Z' initializer is not a constant expression", 13,
      "6.20.4"));
}

TEST(UnitParamValueRead, PackageParameterReadingItselfIsNoConstant) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package pk;\n"
      "  parameter real R = R * 2;\n"
      "  parameter string S = S;\n"
      "endpackage\n"
      "module m;\n"
      "  localparam real X = pk::R;\n"
      "  localparam string T = pk::S;\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(
      diags, "localparam 'R' initializer is not a constant expression", 2,
      "6.20.4"));
  EXPECT_TRUE(ReportedError(
      diags, "localparam 'S' initializer is not a constant expression", 3,
      "6.20.4"));
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(RealParam(design, "m", "X"), -1.0);
  EXPECT_EQ(StringParam(design, "m", "T"), "<no string>");
}

}  // namespace
