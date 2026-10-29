#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <initializer_list>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/elaborator.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "helpers_separate_units.h"

using namespace delta;

namespace {

// Package p, written after the reference in each forbidden form and before it
// in each allowed one.
constexpr const char* kPackageP =
    "package p;\n"
    "  parameter int K = 3;\n"
    "  typedef logic [7:0] t;\n"
    "  function automatic int f();\n"
    "    return 5;\n"
    "  endfunction\n"
    "endpackage\n";

constexpr const char* kLaterPackage =
    "reference to package 'p', which is declared after the reference";

// The module the design is elaborated under, written last.
constexpr const char* kTop = "module top; endmodule\n";

// Whether elaborating `src` draws `message` at `line` under `subclause`.
::testing::AssertionResult ElabReports(const std::string& src,
                                       const char* message, uint32_t line,
                                       const char* subclause) {
  ElabFixture f;
  ElabOk(src, f);
  return ReportedError(f.diag.Diagnostics(), message, line, subclause);
}

// §3.12 (printed page 55) requires a package's compilation to precede the
// references to it. Each of `items`, written on one line after `header` and
// closed by `footer`, names p by the scope resolution operator: it is reported
// where p follows it, and accepted where p precedes it.
void ExpectReportedBeforeThePackage(std::string_view header,
                                    std::initializer_list<const char*> items,
                                    std::string_view footer) {
  const auto kLine =
      static_cast<uint32_t>(1 + std::count(header.begin(), header.end(), '\n'));
  for (const char* item : items) {
    std::string element =
        std::string(header) + item + "\n" + std::string(footer);
    EXPECT_TRUE(
        ElabReports(element + kPackageP + kTop, kLaterPackage, kLine, "3.12"))
        << element;
    EXPECT_TRUE(ElabOk(std::string(kPackageP) + element + kTop)) << element;
  }
}

// In a module: a variable's initializer, a continuous assignment, a procedural
// assignment, a variable's type, a parameter's value, a call of p's function,
// a function's body and a generate block's item.
TEST(PackageBeforeReference, EachFormInAModule) {
  ExpectReportedBeforeThePackage("module m;\n",
                                 {
                                     "  int r = p::K;",
                                     "  wire [31:0] w; assign w = p::K;",
                                     "  int r; initial r = p::K;",
                                     "  p::t v;",
                                     "  parameter int Q = p::K;",
                                     "  int r; initial r = p::f();",
                                     "  function int g(); return p::K; "
                                     "endfunction",
                                     "  if (1) begin : b int r = p::K; end",
                                 },
                                 "endmodule\n");
}

TEST(PackageBeforeReference, EachFormInAnInterface) {
  ExpectReportedBeforeThePackage("interface i;\n",
                                 {
                                     "  localparam int Q = p::K;",
                                     "  p::t v;",
                                     "  int r = p::K;",
                                     "  wire [31:0] w; assign w = p::K;",
                                     "  int r; initial r = p::f();",
                                     "  function int g(); return p::K; "
                                     "endfunction",
                                 },
                                 "endinterface\n");
}

TEST(PackageBeforeReference, EachFormInAProgram) {
  ExpectReportedBeforeThePackage("program pr;\n",
                                 {
                                     "  localparam int Q = p::K;",
                                     "  p::t v;",
                                     "  int r = p::K;",
                                     "  int r; initial r = p::f();",
                                     "  function int g(); return p::K; "
                                     "endfunction",
                                 },
                                 "endprogram\n");
}

TEST(PackageBeforeReference, EachFormInAChecker) {
  ExpectReportedBeforeThePackage("checker c;\n",
                                 {
                                     "  p::t v;",
                                     "  function int g(); return p::K; "
                                     "endfunction",
                                 },
                                 "endchecker\n");
}

// Another package, compiled ahead of p where written ahead of it.
TEST(PackageBeforeReference, EachFormInAnotherPackage) {
  ExpectReportedBeforeThePackage("package q;\n",
                                 {
                                     "  localparam int Q = p::K;",
                                     "  p::t v;",
                                     "  int r = p::K;",
                                     "  function int g(); return p::K; "
                                     "endfunction",
                                 },
                                 "endpackage\n");
}

TEST(PackageBeforeReference, EachFormInAClass) {
  ExpectReportedBeforeThePackage("class C;\n",
                                 {
                                     "  localparam int Q = p::K;",
                                     "  p::t v;",
                                     "  int r = p::K;",
                                     "  function int g(); return p::K; "
                                     "endfunction",
                                 },
                                 "endclass\n");
}

TEST(PackageBeforeReference, EachFormInTheCompilationUnit) {
  ExpectReportedBeforeThePackage("",
                                 {
                                     "localparam int Q = p::K;",
                                     "p::t v;",
                                     "int r = p::K;",
                                     "function int g(); return p::K; "
                                     "endfunction",
                                 },
                                 "");
}

// §26.3 reports an import of the later package, as an import, and the scope
// resolution operator in it draws no second report.
TEST(PackageBeforeReference, AnImportIsReportedOnceAsAnImport) {
  for (const char* import : {"  import p::K;", "  import p::*;"}) {
    std::string element = std::string("module m;\n") + import + "\nendmodule\n";
    ElabFixture f;
    ElabOk(element + kPackageP + kTop, f);
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "import from package 'p', which is declared after the scope importing "
        "it",
        2, "26.3"))
        << import;
    EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kLaterPackage, 2, "3.12"))
        << import;
    EXPECT_TRUE(ElabOk(std::string(kPackageP) + element + kTop)) << import;
  }
}

// A class the reference can see names a class scope, not the package, whatever
// package of the name is written after it.
TEST(PackageBeforeReference, AClassOfTheNameIsNoPackageReference) {
  ElabFixture f;
  ElabOk(std::string("module m;\n"
                     "  class p;\n"
                     "    static int K = 1;\n"
                     "  endclass\n"
                     "  int r = p::K;\n"
                     "endmodule\n") +
             kPackageP + kTop,
         f);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kLaterPackage, 5, "3.12"));
}

// A reference inside p itself follows p's own declaration.
TEST(PackageBeforeReference, ThePackagesOwnReferenceToItself) {
  EXPECT_TRUE(
      ElabOk("package p;\n"
             "  parameter int K = 3;\n"
             "  localparam int Q = p::K + 1;\n"
             "endpackage\n"
             "module top; endmodule\n"));
}

// Elaborates `srcs` together, each a compilation unit of its own.
void ElaborateUnits(const std::vector<std::string>& srcs, ElabFixture& f) {
  Elaborator elab(f.arena, f.diag,
                  ParseUnitsApart(srcs, f.mgr, f.arena, f.diag));
  elab.Elaborate("top");
  f.has_errors = f.diag.HasErrors();
}

// §3.12.1's units are compiled in the order they are given, so a package of a
// later unit is compiled after a reference an earlier unit makes to it, and
// one of an earlier unit before it.
TEST(PackageBeforeReference, APackageOfALaterUnit) {
  ElabFixture later;
  ElaborateUnits({"module top;\n"
                  "  int r = p::K;\n"
                  "endmodule\n",
                  kPackageP},
                 later);
  EXPECT_TRUE(
      ReportedError(later.diag.Diagnostics(), kLaterPackage, 2, "3.12"));
  ElabFixture earlier;
  ElaborateUnits({kPackageP,
                  "module top;\n"
                  "  int r = p::K;\n"
                  "endmodule\n"},
                 earlier);
  EXPECT_FALSE(earlier.has_errors);
}

}  // namespace
