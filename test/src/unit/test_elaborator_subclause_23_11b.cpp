#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(BindVisibility, ImportedNamesOfTheTargetAreSeen) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  int q = 1;\n"
      "  int z = 2;\n"
      "  int e = 3;\n"
      "endpackage\n"
      "module mon(input var int v);\n"
      "endmodule\n"
      "module cpu;\n"
      "  import p::*;\n"
      "  import p::e;\n"
      "  int a;\n"
      "  initial a = q;\n"
      "endmodule\n"
      "module top;\n"
      "  cpu c();\n"
      "endmodule\n"
      "bind cpu mon r1(q);\n"
      "bind cpu mon r2(z);\n"
      "bind cpu mon r3(e);\n",
      f, "top");
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "undeclared signal 'q'", 17,
                             "23.11"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "undeclared signal 'z'", 18,
                            "23.11"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "undeclared signal 'e'", 19,
                             "23.11"));
}

TEST(BindVisibility, AnOrderedConnectionIsReportedByItsPort) {
  ElabFixture f;
  ElaborateSrc(
      "module mon(input var int v);\n"
      "endmodule\n"
      "module cpu;\n"
      "  int a;\n"
      "endmodule\n"
      "module top;\n"
      "  cpu c();\n"
      "endmodule\n"
      "bind cpu mon r(g);\n"
      "bind cpu mon s(a, h);\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bind port connection 'v' references undeclared "
                            "signal 'g'",
                            9, "23.11"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "undeclared signal 'h'", 10,
                            "23.11"));
}

TEST(BindVisibility, ABoundInstancesParameterIsNoConstantOutsideIt) {
  ElabFixture f;
  ElaborateSrc(
      "package pk;\n"
      "  parameter int PW = 3;\n"
      "endpackage\n"
      "module mon #(parameter int W = 4) ();\n"
      "endmodule\n"
      "module cpu;\n"
      "  mon #(.W(2)) q();\n"
      "endmodule\n"
      "module top;\n"
      "  cpu c();\n"
      "  cpu d[1:0]();\n"
      "  logic [c.r.W-1:0] v;\n"
      "  logic [1:0][c.r.W:0] w;\n"
      "  logic [c.q.W:0] ok1;\n"
      "  logic [pk::PW:0] ok2;\n"
      "  logic [c.nosuch.W:0] ok3;\n"
      "endmodule\n"
      "bind cpu mon #(.W(8)) r();\n",
      f, "top");
  const char* message = "a parameter of an instance a bind made is reached";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, 12, "23.11"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, 13, "23.11"));
  for (uint32_t line : {14u, 15u, 16u}) {
    EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), message, line, "23.11"))
        << line;
  }
}

int BoundInElement(const RtlirDesign* design, std::string_view elem,
                   std::string_view bound) {
  int count = 0;
  for (const auto& ch : design->top_modules[0]->children) {
    if (ch.inst_name != elem || ch.resolved == nullptr) continue;
    for (const auto& gch : ch.resolved->children) {
      if (gch.inst_name == bound) ++count;
    }
  }
  return count;
}

constexpr const char* kArrayOfLeaf =
    "module chk; endmodule\n"
    "module leaf; endmodule\n"
    "module top;\n"
    "  leaf u[0:1] ();\n"
    "endmodule\n";

TEST(BindDirective, ABindIntoOneArrayElementBindsThereAlone) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      std::string(kArrayOfLeaf) + "bind top.u[1] chk c1();\n", f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(BoundInElement(design, "u[1]", "c1"), 1);
  EXPECT_EQ(BoundInElement(design, "u[0]", "c1"), 0);
}

TEST(BindDirective, AnInstanceListEntryNamingOneArrayElementBindsThereAlone) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      std::string(kArrayOfLeaf) + "bind leaf : top.u[1] chk c3();\n", f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(BoundInElement(design, "u[1]", "c3"), 1);
  EXPECT_EQ(BoundInElement(design, "u[0]", "c3"), 0);
}

TEST(BindDirective, AScopeBindReachesEveryArrayElement) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      std::string(kArrayOfLeaf) + "bind leaf chk c4();\n", f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(BoundInElement(design, "u[1]", "c4"), 1);
  EXPECT_EQ(BoundInElement(design, "u[0]", "c4"), 1);
}

TEST(BindDirective, AScopeBindAndAnElementBindTogether) {
  ElabFixture f;
  auto* design = ElaborateSrc(std::string(kArrayOfLeaf) +
                                  "bind leaf chk c4();\n"
                                  "bind top.u[1] chk c1();\n",
                              f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(BoundInElement(design, "u[1]", "c4"), 1);
  EXPECT_EQ(BoundInElement(design, "u[0]", "c4"), 1);
  EXPECT_EQ(BoundInElement(design, "u[1]", "c1"), 1);
  EXPECT_EQ(BoundInElement(design, "u[0]", "c1"), 0);
}

}  // namespace
