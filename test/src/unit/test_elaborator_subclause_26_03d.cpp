#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

namespace {

constexpr const char* kPackages =
    "package p; int v = 1; function int f(); return 1; endfunction "
    "task t(); endtask typedef int T; parameter int K = 3; "
    "typedef enum {A, FALSE} bool_t; endpackage\n"
    "package p2; int v = 2; endpackage\n";

void ExpectRefused(const std::string& src, const std::string& message, int line,
                   const char* subclause) {
  SCOPED_TRACE(src);
  ElabFixture f;
  EXPECT_FALSE(ElabOk(src, f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, line, subclause));
}

void ExpectAccepted(const std::string& src) {
  SCOPED_TRACE(src);
  ElabFixture f;
  EXPECT_TRUE(ElabOk(src, f));
  EXPECT_FALSE(f.diag.HasErrors());
}

constexpr const char* kNoPackage =
    "reference to unresolved package or scope 'nopkg'";

TEST(UndeclaredPackageReference, DISABLED_ADataTypeIsReportedEverywhere) {
  for (const char* src :
       {"module top; nopkg::T w; endmodule\n",
        "module top; initial begin nopkg::T w; end endmodule\n",
        "module top(input nopkg::T a); endmodule\n",
        "module top; typedef nopkg::T U; endmodule\n",
        "module top; function void f(nopkg::T a); endfunction endmodule\n"}) {
    ExpectRefused(src, kNoPackage, 1, "26.3");
  }
}

TEST(UndeclaredPackageReference, ADeclaredPackagesTypeIsAccepted) {
  ExpectAccepted(
      "package q; typedef logic [3:0] T; endpackage\n"
      "module top(input q::T a); q::T w; typedef q::T U; "
      "function void f(q::T b); endfunction "
      "initial begin q::T l; end endmodule\n");
}

TEST(UndeclaredPackageReference, DISABLED_ACallStatementIsReported) {
  ExpectRefused("module top; initial nopkg::f(); endmodule\n", kNoPackage, 1,
                "26.3");
}

TEST(UndeclaredPackageReference, ACallInAnExpressionIsReported) {
  ExpectRefused("module top; int x; initial x = nopkg::g(); endmodule\n",
                kNoPackage, 1, "26.3");
}

TEST(ShadowedImportConstant,
     DISABLED_AVariableOrNetShadowingAParameterIsNoConstant) {
  for (const char* decl : {"int V = 7;", "wire [7:0] V = 7;"}) {
    ExpectRefused(std::string("package pk; parameter int V = 1; endpackage\n"
                              "module top; import pk::*; ") +
                      decl + " localparam int L = V; endmodule\n",
                  "localparam 'L' initializer is not a constant expression", 2,
                  "6.20.4");
  }
}

constexpr const char* kClaimed =
    "declaration of 'c' follows a reference resolved through a wildcard "
    "package import";
constexpr const char* kClaimingPackage = "package q; int c = 1; endpackage\n";

TEST(DeclarationAfterWildcardClaim, IsReportedInEachDesignElementScope) {
  for (const char* src :
       {"interface ifc; import q::*; int d = c; int c; endinterface\n"
        "module top; ifc i(); endmodule\n",
        "program pg; import q::*; int d = c; int c; endprogram\n"
        "module top; pg u(); endmodule\n",
        "module top; function automatic int f(); import q::*; int d = c; "
        "int c; return d; endfunction endmodule\n",
        "module top; if (1) begin : g import q::*; int d = c; int c; end "
        "endmodule\n"}) {
    ExpectRefused(std::string(kClaimingPackage) + src, kClaimed, 2, "26.3");
  }
}

TEST(DeclarationAfterWildcardClaim,
     DISABLED_IsReportedInAPackageTheUnitAndABlock) {
  for (const char* src :
       {"package r; import q::*; int d = c; int c; endpackage\n",
        "import q::*; int d = c; int c;\n",
        "module top; initial begin import q::*; automatic int d = c; int c; "
        "end endmodule\n"}) {
    ExpectRefused(std::string(kClaimingPackage) + src, kClaimed, 2, "26.3");
  }
}

TEST(DeclarationAfterWildcardClaim, ADeclarationBeforeTheReferenceIsAccepted) {
  for (const char* src :
       {"package r; import q::*; int c; int d = c; endpackage\n",
        "import q::*; int c; int d = c;\n",
        "module top; initial begin import q::*; int c; automatic int d = c; "
        "end endmodule\n"}) {
    ExpectAccepted(std::string(kClaimingPackage) + src);
  }
}

std::string InScope(const char* scope, const std::string& items) {
  const std::string kName(scope);
  if (kName == "unit") return items + "\nmodule top; endmodule\n";
  if (kName == "generate") {
    return "module top; if (1) begin : g " + items + " end endmodule\n";
  }
  const std::string kTop =
      kName == "package" ? "" : "module top; s u(); endmodule\n";
  return kName + " s; " + items + " end" + kName + "\n" + kTop;
}

constexpr const char* kCollides =
    "explicit import of 'p::v' collides with existing declaration of 'v'";
constexpr const char* kConflicts =
    "explicit import of 'p2::v' conflicts with earlier explicit import from "
    "'p'";

TEST(ExplicitImportCollision, InADesignElementOrGenerateBlock) {
  for (const char* scope : {"interface", "program", "checker", "generate"}) {
    ExpectRefused(kPackages + InScope(scope, "int v; import p::v;"), kCollides,
                  3, "26.3");
    ExpectRefused(kPackages + InScope(scope, "import p::v; import p2::v;"),
                  kConflicts, 3, "26.3");
  }
}

TEST(ExplicitImportCollision, DISABLED_InAPackageOrTheUnit) {
  for (const char* scope : {"package", "unit"}) {
    ExpectRefused(kPackages + InScope(scope, "int v; import p::v;"), kCollides,
                  3, "26.3");
    ExpectRefused(kPackages + InScope(scope, "import p::v; import p2::v;"),
                  kConflicts, 3, "26.3");
  }
}

TEST(ExplicitImportCollision, DISABLED_ADeclarationAfterTheImport) {
  for (const char* scope :
       {"interface", "program", "checker", "package", "generate", "unit"}) {
    ExpectRefused(kPackages + InScope(scope, "import p::v; int v;"),
                  "explicit import of 'p::v'", 3, "26.3");
  }
}

TEST(ExplicitImportCollision, DISABLED_EveryKindOfImportedName) {
  for (const char* name : {"t", "T", "K", "FALSE"}) {
    const std::string kName(name);
    std::string src(kPackages);
    src += "module top; import p::";
    src += kName;
    src += "; int ";
    src += kName;
    src += "; endmodule\n";
    ExpectRefused(src, "explicit import of 'p::" + kName + "'", 3, "26.3");
  }
}

TEST(ExplicitImportCollision, DISABLED_InAFunctionOrTaskBody) {
  for (const char* sub : {"function automatic void g(); import p::v; int v; "
                          "endfunction",
                          "task automatic g(); import p::v; int v; endtask"}) {
    ExpectRefused(
        std::string(kPackages) + "module top; " + sub + " endmodule\n",
        "explicit import of 'p::v'", 3, "26.3");
  }
}

TEST(ExplicitImportCollision, AWildcardImportBesideADeclarationIsAccepted) {
  for (const char* scope : {"module", "interface", "program", "checker",
                            "package", "generate", "unit"}) {
    ExpectAccepted(kPackages + InScope(scope, "import p::*; int v;"));
  }
}

TEST(SubroutineCallBinding, DISABLED_ACallBeforeItsOnlyWildcardImport) {
  ExpectRefused(
      "package p; function int f(); return 1; endfunction endpackage\n"
      "module top; int x; initial x = f(); import p::*; endmodule\n",
      "reference to 'f' precedes the wildcard import of package 'p' that "
      "declares it",
      2, "26.3");
}

constexpr const char* kLater =
    "import from package 'later', which is declared after the scope "
    "importing it";

TEST(ImportOfALaterPackage, IsReportedFromAFunctionInterfaceOrProgram) {
  for (const char* src :
       {"module top; function automatic int f(); import later::*; return 0; "
        "endfunction endmodule\n",
        "interface ifc; import later::*; endinterface\nmodule top; ifc i(); "
        "endmodule\n",
        "program pg; import later::*; endprogram\nmodule top; pg u(); "
        "endmodule\n"}) {
    ExpectRefused(std::string(src) + "package later; int x; endpackage\n",
                  kLater, 1, "26.3");
  }
}

TEST(ImportOfALaterPackage, DISABLED_IsReportedFromAPackageOrTheUnit) {
  for (const char* src :
       {"package a; import later::*; endpackage\n", "import later::*;\n"}) {
    ExpectRefused(std::string(src) + "package later; int x; endpackage\n",
                  kLater, 1, "26.3");
  }
}

TEST(ImportOfALaterPackage, AnImportNamingAModuleIsReported) {
  ExpectRefused(
      "module m; int x; endmodule\n"
      "module top; import m::x; endmodule\n",
      "import from unknown package 'm'", 2, "26.3");
}

TEST(ImportedNameVisibility, AHierarchicalReferenceIntoAnInterfaceIsRefused) {
  ExpectRefused(std::string(kPackages) +
                    "interface ifc; import p::*; endinterface\n"
                    "module top; ifc i(); int y; initial y = i.v; endmodule\n",
                "hierarchical reference 'i.v' targets a name imported into "
                "'ifc' from a package",
                4, "26.3");
}

TEST(ImportedNameVisibility, DISABLED_AnInterfacePortReferenceIsRefused) {
  ExpectRefused(std::string(kPackages) +
                    "interface ifc; import p::*; endinterface\n"
                    "module m(ifc port); int y; initial y = port.v; "
                    "endmodule\n"
                    "module top; ifc i(); m u(i); endmodule\n",
                "hierarchical reference 'port.v' targets a name imported "
                "into 'ifc' from a package",
                4, "26.3");
}

TEST(NonCallReferenceBinding, DISABLED_TheSectionsTop1LiteralIsPs) {
  ExpectRefused(
      "package p; typedef enum { FALSE, TRUE } bool_t; endpackage\n"
      "package q; typedef enum { ORIGINAL, FALSE } teeth_t; endpackage\n"
      "module top1; import p::*; import q::teeth_t; teeth_t myteeth;\n"
      "  initial myteeth = FALSE; endmodule\n",
      "value of enum type 'bool_t' assigned to enum variable of type "
      "'teeth_t' without cast",
      4, "6.19.3");
}

TEST(NonCallReferenceBinding, DISABLED_ANestedScopeNameHidesAWildcardName) {
  ExpectRefused(
      "package p; int b = 5; endpackage\n"
      "module top; import p::*; if (1) begin : b int z; end int y;\n"
      "  initial y = b; endmodule\n",
      "reference to unresolved identifier 'b'", 3, "23.9");
}

TEST(NonCallReferenceBinding, DISABLED_AReferenceBeforeTheImportIsReported) {
  for (const char* src :
       {"module top; initial begin automatic int y = x; import p::*; end "
        "endmodule\n",
        "module top; function automatic int f(); int y = x; import p::*; "
        "return y; endfunction endmodule\n"}) {
    ExpectRefused(std::string("package p; int x = 1; endpackage\n") + src,
                  "reference to 'x' precedes the wildcard import of package "
                  "'p' that declares it",
                  2, "26.3");
  }
  ExpectRefused(
      "package p; int x = 1; endpackage\n"
      "module top; int y = x; import p::x; endmodule\n",
      "reference to 'x' precedes the", 2, "26.3");
}

constexpr const char* kAmbiguous =
    "reference to 'v' is ambiguous between wildcard imports of packages 'p' "
    "and 'p2'";

TEST(WildcardImportAmbiguity, IsReportedInAnInterfaceOrProgram) {
  for (const char* scope : {"interface", "program"}) {
    ExpectRefused(kPackages + InScope(scope,
                                      "import p::*; import p2::*; "
                                      "int y = v;"),
                  kAmbiguous, 3, "26.3");
  }
}

TEST(WildcardImportAmbiguity, DISABLED_IsReportedInAPackageOrTheUnit) {
  for (const char* scope : {"package", "unit"}) {
    ExpectRefused(kPackages + InScope(scope,
                                      "import p::*; import p2::*; "
                                      "int y = v;"),
                  kAmbiguous, 3, "26.3");
  }
}

TEST(WildcardImportAmbiguity, AnUnreferencedNameOfBothIsAccepted) {
  for (const char* scope : {"interface", "program", "package", "unit"}) {
    ExpectAccepted(kPackages + InScope(scope, "import p::*; import p2::*;"));
  }
}

}  // namespace
