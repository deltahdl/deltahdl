#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(PureDpiImportRestrictions, PureFunctionAcceptedWhenWellFormed) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  import \"DPI-C\" pure function int p(input int a, input int b);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(PureDpiImportRestrictions, PureFunctionRejectsVoidReturnType) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  import \"DPI-C\" pure function void p(input int a);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "pure imported function must have a non-void "
                            "return type",
                            2, "35.5.2"));
}

TEST(PureDpiImportRestrictions, PureFunctionRejectsOutputArgument) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  import \"DPI-C\" pure function int p(output int o);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "pure imported function cannot have output or "
                            "inout arguments",
                            2, "35.5.2"));
}

TEST(PureDpiImportRestrictions, PureFunctionRejectsInoutArgument) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  import \"DPI-C\" pure function int p(inout int io);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "pure imported function cannot have output or "
                            "inout arguments",
                            2, "35.5.2"));
}

TEST(PureDpiImportRestrictions, PureCannotApplyToImportedTask) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  import \"DPI-C\" pure task t(input int x);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "imported task cannot be declared pure", 2,
                            "35.5.2"));
}

TEST(PureDpiImportRestrictions, PureFunctionWithNoArgumentsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  import \"DPI-C\" pure function int p();\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(PureDpiImportRestrictions, PureFunctionRejectsLateOutputArgument) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  import \"DPI-C\" pure function int p(input int x, output int o);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "pure imported function cannot have output or "
                            "inout arguments",
                            2, "35.5.2"));
}

TEST(PureDpiImportRestrictions, PureTaskNames35_5_2) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  import \"DPI-C\" pure task t(input int x);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "imported task cannot be declared pure", 2,
                            "35.5.2"));
}

TEST(PureDpiImportRestrictions, PureTaskMessageDropsTheProseSubclause) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  import \"DPI-C\" pure task t(input int x);\n"
      "endmodule\n",
      f);
  ASSERT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "imported task cannot be declared pure", 2,
                            "35.5.2"));
  for (const auto& diag : f.diag.Diagnostics()) {
    EXPECT_EQ(diag.message.find("§"), std::string::npos);
  }
}

TEST(PureDpiImportRestrictions, NonPureFunctionUnrestrictedShapeAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  import \"DPI-C\" function void f(output int o, inout int io);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

constexpr const char* kVoidResult =
    "  import \"DPI-C\" pure function void p(input int a);\n";
constexpr const char* kOutputFormal =
    "  import \"DPI-C\" pure function int p(output int o);\n";
constexpr const char* kInoutFormal =
    "  import \"DPI-C\" pure function int p(inout int io);\n";
constexpr const char* kPureTask =
    "  import \"DPI-C\" pure task t(input int x);\n";
constexpr const char* kWellFormed =
    "  import \"DPI-C\" pure function int p(input int a);\n";
constexpr const char* kNonVoidMessage =
    "pure imported function must have a non-void return type";
constexpr const char* kNoOutputMessage =
    "pure imported function cannot have output or inout arguments";

std::string InPackage(const char* decl) {
  return std::string("package pk;\n") + decl +
         "endpackage\nmodule m;\nendmodule\n";
}

std::string InUnit(const char* decl) {
  return std::string(decl) + "module m;\nendmodule\n";
}

std::string InInterface(const char* decl) {
  return std::string("interface ifc;\n") + decl +
         "endinterface\nmodule m;\n  ifc i();\nendmodule\n";
}

std::string InProgram(const char* decl) {
  return std::string("program p;\n") + decl +
         "endprogram\nmodule m;\n  p u();\nendmodule\n";
}

std::string InGenerateBlock(const char* decl) {
  return std::string("module m;\n  if (1) begin : g\n") + decl +
         "  end\nendmodule\n";
}

void ExpectRefused(const std::string& src, const char* message, int line,
                   const char* subclause) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, line, subclause));
}

void ExpectPureRefused(const std::string& src, const char* message, int line) {
  ExpectRefused(src, message, line, "35.5.2");
}

void ExpectPureTaskRefused(const std::string& src, int line) {
  ExpectRefused(src, "an imported task cannot be declared pure", line,
                "35.5.4");
}

void ExpectPureAccepted(const std::string& src) {
  ElabFixture f;
  Elaborate(src, f);
  EXPECT_FALSE(f.has_errors);
}

TEST(PureDpiImportScopes, DISABLED_APackageRefusesAVoidPureResult) {
  ExpectPureRefused(InPackage(kVoidResult), kNonVoidMessage, 2);
}

TEST(PureDpiImportScopes, DISABLED_APackageRefusesAPureOutputFormal) {
  ExpectPureRefused(InPackage(kOutputFormal), kNoOutputMessage, 2);
}

TEST(PureDpiImportScopes, DISABLED_APackageRefusesAPureInoutFormal) {
  ExpectPureRefused(InPackage(kInoutFormal), kNoOutputMessage, 2);
}

TEST(PureDpiImportScopes, APackageRefusesAPureTask) {
  ExpectPureTaskRefused(InPackage(kPureTask), 2);
}

TEST(PureDpiImportScopes, APackageAcceptsAWellFormedPureImport) {
  ExpectPureAccepted(InPackage(kWellFormed));
}

TEST(PureDpiImportScopes, DISABLED_TheCompilationUnitRefusesAVoidPureResult) {
  ExpectPureRefused(InUnit(kVoidResult), kNonVoidMessage, 1);
}

TEST(PureDpiImportScopes, DISABLED_TheCompilationUnitRefusesAPureOutputFormal) {
  ExpectPureRefused(InUnit(kOutputFormal), kNoOutputMessage, 1);
}

TEST(PureDpiImportScopes, DISABLED_TheCompilationUnitRefusesAPureInoutFormal) {
  ExpectPureRefused(InUnit(kInoutFormal), kNoOutputMessage, 1);
}

TEST(PureDpiImportScopes, TheCompilationUnitRefusesAPureTask) {
  ExpectPureTaskRefused(InUnit(kPureTask), 1);
}

TEST(PureDpiImportScopes, TheCompilationUnitAcceptsAWellFormedPureImport) {
  ExpectPureAccepted(InUnit(kWellFormed));
}

TEST(PureDpiImportScopes, AnInterfaceRefusesAVoidPureResult) {
  ExpectPureRefused(InInterface(kVoidResult), kNonVoidMessage, 2);
}

TEST(PureDpiImportScopes, AnInterfaceRefusesAPureOutputFormal) {
  ExpectPureRefused(InInterface(kOutputFormal), kNoOutputMessage, 2);
}

TEST(PureDpiImportScopes, AnInterfaceRefusesAPureInoutFormal) {
  ExpectPureRefused(InInterface(kInoutFormal), kNoOutputMessage, 2);
}

TEST(PureDpiImportScopes, AnInterfaceRefusesAPureTask) {
  ExpectPureTaskRefused(InInterface(kPureTask), 2);
}

TEST(PureDpiImportScopes, AnInterfaceAcceptsAWellFormedPureImport) {
  ExpectPureAccepted(InInterface(kWellFormed));
}

TEST(PureDpiImportScopes, AProgramRefusesAVoidPureResult) {
  ExpectPureRefused(InProgram(kVoidResult), kNonVoidMessage, 2);
}

TEST(PureDpiImportScopes, AProgramRefusesAPureOutputFormal) {
  ExpectPureRefused(InProgram(kOutputFormal), kNoOutputMessage, 2);
}

TEST(PureDpiImportScopes, AProgramRefusesAPureInoutFormal) {
  ExpectPureRefused(InProgram(kInoutFormal), kNoOutputMessage, 2);
}

TEST(PureDpiImportScopes, AProgramRefusesAPureTask) {
  ExpectPureTaskRefused(InProgram(kPureTask), 2);
}

TEST(PureDpiImportScopes, AProgramAcceptsAWellFormedPureImport) {
  ExpectPureAccepted(InProgram(kWellFormed));
}

TEST(PureDpiImportScopes, AGenerateBlockRefusesAVoidPureResult) {
  ExpectPureRefused(InGenerateBlock(kVoidResult), kNonVoidMessage, 3);
}

TEST(PureDpiImportScopes, AGenerateBlockRefusesAPureOutputFormal) {
  ExpectPureRefused(InGenerateBlock(kOutputFormal), kNoOutputMessage, 3);
}

TEST(PureDpiImportScopes, AGenerateBlockRefusesAPureInoutFormal) {
  ExpectPureRefused(InGenerateBlock(kInoutFormal), kNoOutputMessage, 3);
}

TEST(PureDpiImportScopes, AGenerateBlockRefusesAPureTask) {
  ExpectPureTaskRefused(InGenerateBlock(kPureTask), 3);
}

TEST(PureDpiImportScopes, AGenerateBlockAcceptsAWellFormedPureImport) {
  ExpectPureAccepted(InGenerateBlock(kWellFormed));
}

}  // namespace
