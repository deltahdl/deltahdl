#include <gtest/gtest.h>

#include <cstddef>
#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr const char* kAlreadyDeclared =
    "DPI import name 'dup' already declared in this scope";
constexpr const char* kTaskOperand =
    "task 't' is enabled from a statement and cannot be an operand of an "
    "expression";

bool ElaboratesClean(const std::string& src) {
  ElabFixture f;
  ElaborateSrc(src, f);
  return !f.diag.HasErrors();
}

bool Reports(const std::string& src, const char* message, int line,
             const char* subclause) {
  ElabFixture f;
  ElaborateSrc(src, f);
  return ReportedError(f.diag.Diagnostics(), message, line, subclause);
}

size_t ErrorsOf(const std::string& src) {
  ElabFixture f;
  ElaborateSrc(src, f);
  return f.diag.ErrorCount();
}

TEST(DpiImportDefinesItsName, AnImportTakingANativeTasksNameIsARedeclaration) {
  std::string src =
      "module m;\n"
      "  task sv_t(); endtask\n"
      "  import \"DPI-C\" task sv_t();\n"
      "endmodule\n";
  EXPECT_TRUE(Reports(src, "redeclaration of 'sv_t'", 3, "23.9")) << src;
}

TEST(DpiImportDefinesItsName,
     AnImportBesideANativeTaskOfAnotherNameIsAccepted) {
  EXPECT_TRUE(
      ElaboratesClean("module m;\n"
                      "  task sv_t(); endtask\n"
                      "  import \"DPI-C\" task sv_u();\n"
                      "endmodule\n"));
}

struct ImportScope {
  const char* head;
  const char* tail;
  int line;
};

constexpr ImportScope kScopesOfTwoImports[] = {
    {"interface ifc;\n", "endinterface\nmodule m; ifc i(); endmodule\n", 3},
    {"program pr;\n", "endprogram\nmodule m; pr p(); endmodule\n", 3},
    {"module m;\n  if (1) begin : g\n", "  end\nendmodule\n", 4},
    {"", "module m; endmodule\n", 2}};

std::string TwoImportsIn(const ImportScope& scope, const char* second) {
  std::string src = scope.head;
  src.append("  import \"DPI-C\" a = function int dup(input int x);\n");
  src.append("  import \"DPI-C\" b = function int ").append(second);
  src.append("(input int x);\n").append(scope.tail);
  return src;
}

TEST(DpiImportDefinesItsName, TwoImportsOfOneNameInEachScopeAreRefused) {
  for (const auto& scope : kScopesOfTwoImports) {
    std::string src = TwoImportsIn(scope, "dup");
    EXPECT_TRUE(Reports(src, kAlreadyDeclared, scope.line, "35.5.4")) << src;
  }
}

TEST(DpiImportDefinesItsName, TwoImportsOfDistinctNamesInEachScopeAreAccepted) {
  for (const auto& scope : kScopesOfTwoImports) {
    std::string src = TwoImportsIn(scope, "other");
    EXPECT_TRUE(ElaboratesClean(src)) << src;
  }
}

TEST(DpiImportDefinesItsName, DISABLED_TwoUnitImportsOfOneNameDrawOneReport) {
  EXPECT_EQ(ErrorsOf(TwoImportsIn(kScopesOfTwoImports[3], "dup")), 1U);
}

TEST(DpiSharedForeignSubroutine, TwoNamesOfOneSubroutineInOneScopeAreAccepted) {
  EXPECT_TRUE(
      ElaboratesClean("module m;\n"
                      "  import \"DPI-C\" link = function int a(input int x);\n"
                      "  import \"DPI-C\" link = function int b(input int x);\n"
                      "  int r;\n"
                      "  initial r = a(1) + b(2);\n"
                      "endmodule\n"));
}

TEST(DpiSharedForeignSubroutine, TwoNamesDifferingOnlyInDefaultsAreAccepted) {
  EXPECT_TRUE(ElaboratesClean(
      "module m;\n"
      "  import \"DPI-C\" link = function int a(input int x = 1);\n"
      "  import \"DPI-C\" link = function int b(input int x = 2);\n"
      "  int r;\n"
      "  initial r = a() + b();\n"
      "endmodule\n"));
}

constexpr const char* kPackageTask =
    "package pk;\n"
    "  import \"DPI-C\" task t(input int a);\n"
    "endpackage\n";

TEST(DpiImportedTaskEnable, APackageTaskEnabledAsAStatementIsAccepted) {
  std::string src = kPackageTask;
  src.append("module m;\n  initial pk::t(1);\nendmodule\n");
  EXPECT_TRUE(ElaboratesClean(src)) << src;
}

TEST(DpiImportedTaskEnable, AUnitTaskEnabledAsAStatementIsAccepted) {
  EXPECT_TRUE(
      ElaboratesClean("import \"DPI-C\" task t(input int a);\n"
                      "module m;\n  initial t(1);\nendmodule\n"));
}

TEST(DpiImportedTaskEnable, DISABLED_APackageTaskAsAnOperandIsReported) {
  std::string src = kPackageTask;
  src.append("module m;\n  int x;\n  initial x = pk::t(1);\nendmodule\n");
  EXPECT_TRUE(Reports(src, kTaskOperand, 6, "13.3")) << src;
}

TEST(DpiImportedTaskEnable,
     DISABLED_AWildcardImportedPackageTaskAsAnOperandIsReported) {
  std::string src = kPackageTask;
  src.append(
      "module m;\n  import pk::*;\n  int x;\n  initial x = t(1);\n"
      "endmodule\n");
  EXPECT_TRUE(Reports(src, kTaskOperand, 7, "13.3")) << src;
}

TEST(DpiImportedTaskEnable, DISABLED_AUnitTaskAsAnOperandIsReported) {
  std::string src =
      "import \"DPI-C\" task t(input int a);\n"
      "module m;\n  int x;\n  initial x = t(1);\nendmodule\n";
  EXPECT_TRUE(Reports(src, kTaskOperand, 4, "13.3")) << src;
}

TEST(DpiImportedTaskEnable, TooManyActualsToAnImportedTaskAreReported) {
  std::string src =
      "module m;\n"
      "  import \"DPI-C\" task t(input int a);\n"
      "  initial t(1, 2);\n"
      "endmodule\n";
  EXPECT_TRUE(
      Reports(src, "too many arguments to 't': expected 1, got 2", 3, "13.5"))
      << src;
}

TEST(DpiImportedTaskEnable, ANamedActualNamingNoFormalOfATaskIsReported) {
  std::string src =
      "module m;\n"
      "  import \"DPI-C\" task t(input int a);\n"
      "  initial t(.nosuch(1));\n"
      "endmodule\n";
  EXPECT_TRUE(Reports(src, "no parameter 'nosuch' in 't'", 3, "13.5.4")) << src;
}

TEST(DpiImportedTaskEnable, AWellFormedNamedTaskEnableIsAccepted) {
  EXPECT_TRUE(ElaboratesClean(
      "module m;\n"
      "  import \"DPI-C\" task t(input int a, input int b = 7);\n"
      "  initial t(.b(2), .a(1));\n"
      "endmodule\n"));
}

TEST(DpiImportDeclaration,
     DISABLED_ACallToAnUndeclaredForeignSubroutineIsReported) {
  std::string src =
      "module m;\n"
      "  int r;\n"
      "  initial r = c_add(1);\n"
      "endmodule\n";
  EXPECT_TRUE(Reports(src, "undeclared identifier 'c_add'", 3, "23.9")) << src;
}

TEST(DpiImportDeclaration, TheSameCallWithItsImportDeclaredIsAccepted) {
  EXPECT_TRUE(
      ElaboratesClean("module m;\n"
                      "  import \"DPI-C\" function int c_add(input int a);\n"
                      "  int r;\n"
                      "  initial r = c_add(1);\n"
                      "endmodule\n"));
}

}  // namespace
