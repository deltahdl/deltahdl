#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

namespace {

constexpr const char* kHierarchical =
    "package item contains a hierarchical reference 'top'";
constexpr const char* kNetInitializer =
    "net declaration with implicit continuous assignment is not allowed in a "
    "package";

void ExpectHierarchicalRefusedAt(const std::string& package_items, int line) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module top;\n"
             "  logic c;\n"
             "  int x;\n"
             "endmodule\n"
             "package p;\n"
             "  logic d;\n"
             "  int y;\n" +
                 package_items + "endpackage\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kHierarchical, line, "26.2"));
}

void ExpectPackageAccepted(const std::string& src) {
  ElabFixture f;
  EXPECT_TRUE(ElabOk(src, f));
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PackageHierarchicalReference, InATaskBodyIsRefused) {
  ExpectHierarchicalRefusedAt("  task t(); top.x = 1; endtask\n", 8);
  ExpectPackageAccepted(
      "package p;\n"
      "  int y;\n"
      "  task t(); y = 1; p::y = 2; endtask\n"
      "endpackage\n");
}

TEST(PackageHierarchicalReference, InALetBodyIsRefused) {
  ExpectHierarchicalRefusedAt("  let l = top.x + 1;\n", 8);
  ExpectPackageAccepted(
      "package p;\n"
      "  int y;\n"
      "  let l = y + p::y;\n"
      "endpackage\n");
}

TEST(PackageHierarchicalReference, InAParameterValueIsRefused) {
  ExpectHierarchicalRefusedAt("  parameter int P = top.x;\n", 8);
  ExpectPackageAccepted(
      "package q;\n"
      "  parameter int Q = 3;\n"
      "endpackage\n"
      "package p;\n"
      "  parameter int R = 2;\n"
      "  parameter int P = R + q::Q;\n"
      "endpackage\n");
}

TEST(PackageHierarchicalReference, DISABLED_InACovergroupEventIsRefused) {
  ExpectHierarchicalRefusedAt(
      "  covergroup cg @(posedge top.c); coverpoint y; endgroup\n", 8);
  ExpectPackageAccepted(
      "package p;\n"
      "  logic d;\n"
      "  int y;\n"
      "  covergroup cg @(posedge d); coverpoint y; endgroup\n"
      "endpackage\n");
}

TEST(PackageHierarchicalReference, DISABLED_InACoverpointIsRefused) {
  ExpectHierarchicalRefusedAt(
      "  covergroup cg @(posedge d); coverpoint top.x; endgroup\n", 8);
}

TEST(PackageHierarchicalReference, DISABLED_InAPackageCheckersAssertion) {
  ExpectHierarchicalRefusedAt(
      "  checker ck(logic clk);\n"
      "    a: assert property (@(posedge clk) top.x == 0);\n"
      "  endchecker\n",
      9);
  ExpectPackageAccepted(
      "package p;\n"
      "  int y;\n"
      "  checker ck(logic clk);\n"
      "    a: assert property (@(posedge clk) y == 0);\n"
      "  endchecker\n"
      "endpackage\n");
}

void ExpectCompilationUnitRefused(const std::string& src,
                                  const std::string& message, int line) {
  ElabFixture f;
  EXPECT_FALSE(ElabOk(src, f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, line, "26.2"));
}

TEST(PackageCompilationUnitReference, AUnitScopedNameIsRefused) {
  ExpectCompilationUnitRefused(
      "int x;\n"
      "package p;\n"
      "  function int f(); return $unit::x; endfunction\n"
      "endpackage\n",
      "package item uses scope prefix '$unit', which targets a scope outside "
      "the package",
      3);
}

TEST(PackageCompilationUnitReference, ACallOfAUnitFunctionIsRefused) {
  ExpectCompilationUnitRefused(
      "function int g(); return 1; endfunction\n"
      "package p;\n"
      "  function int f(); return g(); endfunction\n"
      "endpackage\n",
      "package item references 'g' from the compilation-unit scope", 3);
  ExpectPackageAccepted(
      "package p;\n"
      "  function int g(); return 1; endfunction\n"
      "  function int f(); return g(); endfunction\n"
      "endpackage\n");
}

TEST(PackageCompilationUnitReference, AWriteOfAUnitVariableIsRefused) {
  ExpectCompilationUnitRefused(
      "int x;\n"
      "package p;\n"
      "  task t(); x = 1; endtask\n"
      "endpackage\n",
      "package item references 'x' from the compilation-unit scope", 3);
  ExpectPackageAccepted(
      "package p;\n"
      "  int x;\n"
      "  task t(); x = 1; endtask\n"
      "endpackage\n");
}

TEST(PackageCompilationUnitReference, DISABLED_AUnitTypedefAsATypeIsRefused) {
  ExpectCompilationUnitRefused(
      "typedef int cu_t;\n"
      "package p;\n"
      "  cu_t v;\n"
      "endpackage\n",
      "package item references 'cu_t' from the compilation-unit scope", 3);
  ExpectPackageAccepted(
      "package p;\n"
      "  typedef int cu_t;\n"
      "  cu_t v;\n"
      "endpackage\n");
}

TEST(PackageCompilationUnitReference, DISABLED_AUnitClassAsATypeIsRefused) {
  ExpectCompilationUnitRefused(
      "class cu_c; endclass\n"
      "package p;\n"
      "  cu_c h;\n"
      "endpackage\n",
      "package item references 'cu_c' from the compilation-unit scope", 3);
  ExpectPackageAccepted(
      "package p;\n"
      "  class cu_c; endclass\n"
      "  cu_c h;\n"
      "endpackage\n");
}

TEST(PackageNetInitializer, EveryBuiltInNetKindIsRefused) {
  for (const char* kind : {"tri", "uwire", "wand", "wor", "triand", "trior",
                           "tri0", "tri1", "trireg", "supply0", "supply1"}) {
    SCOPED_TRACE(kind);
    ElabFixture f;
    EXPECT_FALSE(ElabOk(std::string("package p;\n  ") + kind + " w = 1;\n  " +
                            kind + " u;\nendpackage\n",
                        f));
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kNetInitializer, 2, "26.2"));
    EXPECT_FALSE(
        ReportedError(f.diag.Diagnostics(), kNetInitializer, 3, "26.2"));
  }
}

TEST(PackageNetInitializer, AStrengthOrADelayBeforeTheInitializerIsRefused) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package p;\n"
             "  wire (strong0, weak1) w2 = 1;\n"
             "  wire #5 w3 = 1;\n"
             "  wire (strong0, weak1) w4;\n"
             "  wire #5 w5;\n"
             "endpackage\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNetInitializer, 2, "26.2"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNetInitializer, 3, "26.2"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kNetInitializer, 4, "26.2"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kNetInitializer, 5, "26.2"));
}

}  // namespace
