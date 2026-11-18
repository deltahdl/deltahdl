#include <gtest/gtest.h>

#include <string>
#include <utility>

#include "fixture_simulator.h"

using namespace delta;

namespace {

void ExpectOutput(const std::string& src, const std::string& expected) {
  SCOPED_TRACE(src);
  SimFixture f;
  EXPECT_EQ(RunCaptureThroughFinals(ElaborateSrc, src, f), expected);
  EXPECT_FALSE(f.diag.HasErrors());
}

constexpr const char* kConstants =
    "package pk; parameter int V = 1; parameter int G = 100; "
    "parameter real R = 1.5; function int F(); return 1; endfunction "
    "typedef logic [1:0] T; endpackage\n";

TEST(LocalNameHidingAWildcardName, ALocalparamInAConstantAndAProcess) {
  ExpectOutput(std::string(kConstants) +
                   "module top; import pk::*; localparam int V = 7; "
                   "localparam int L = V; int r; initial begin r = V; "
                   "$display(\"%0d %0d\", L, r); end endmodule\n",
               "7 7\n");
}

TEST(LocalNameHidingAWildcardName, AVariableOrNetInAProcess) {
  for (const char* decl : {"int V = 7;", "wire [7:0] V = 7;"}) {
    ExpectOutput(std::string(kConstants) + "module top; import pk::*; " + decl +
                     " initial #1 $display(\"%0d\", V); endmodule\n",
                 "7\n");
  }
}

TEST(LocalNameHidingAWildcardName, DISABLED_AFunctionCalledInAConstant) {
  ExpectOutput(std::string(kConstants) +
                   "module top; import pk::*; function int F(); return 7; "
                   "endfunction localparam int L = F(); "
                   "initial $display(\"%0d %0d\", L, F()); endmodule\n",
               "7 7\n");
}

TEST(LocalNameHidingAWildcardName, ATypedefInAConstantAndADeclaration) {
  ExpectOutput(std::string(kConstants) +
                   "module top; import pk::*; typedef logic [5:0] T; "
                   "localparam int L = $bits(T); T v; "
                   "initial $display(\"%0d %0d\", L, $bits(v)); endmodule\n",
               "6 6\n");
}

TEST(LocalNameHidingAWildcardName, AGenvarHidingAnIntegerParameter) {
  ExpectOutput(std::string(kConstants) +
                   "module top; import pk::*; "
                   "for (genvar G = 0; G < 2; G++) begin : b "
                   "localparam int L = G; initial $display(\"%0d %0d\", G, L); "
                   "end endmodule\n",
               "0 0\n1 1\n");
}

TEST(LocalNameHidingAWildcardName, DISABLED_AGenvarHidingARealParameter) {
  ExpectOutput(std::string(kConstants) +
                   "module top; import pk::*; "
                   "for (genvar R = 0; R < 2; R++) begin : b "
                   "localparam int L = R; initial $display(\"%0d %0d\", R, L); "
                   "end endmodule\n",
               "0 0\n1 1\n");
}

TEST(LocalNameHidingAWildcardName, ALocalparamInEachOtherScope) {
  ExpectOutput(std::string(kConstants) +
                   "interface ifc; import pk::*; localparam int V = 7; "
                   "localparam int L = V; initial $display(\"%0d %0d\", L, V); "
                   "endinterface\n"
                   "module top; ifc i(); endmodule\n",
               "7 7\n");
  ExpectOutput(std::string(kConstants) +
                   "program pg; import pk::*; localparam int V = 7; "
                   "localparam int L = V; initial $display(\"%0d %0d\", L, V); "
                   "endprogram\n"
                   "module top; pg u(); endmodule\n",
               "7 7\n");
  ExpectOutput(std::string(kConstants) +
                   "package q; import pk::*; localparam int V = 7; "
                   "localparam int L = V; endpackage\n"
                   "module top; initial $display(\"%0d\", q::L); endmodule\n",
               "7\n");
  ExpectOutput(std::string(kConstants) +
                   "module top; import pk::*; if (1) begin : g "
                   "localparam int V = 7; localparam int L = V; "
                   "initial $display(\"%0d %0d\", L, V); end endmodule\n",
               "7 7\n");
}

TEST(LocalNameHidingAWildcardName, DISABLED_AUnitLocalparamReadFromAModule) {
  ExpectOutput(std::string(kConstants) +
                   "import pk::*; localparam int V = 7; localparam int L = V;\n"
                   "module top; initial $display(\"%0d %0d\", L, V); "
                   "endmodule\n",
               "7 7\n");
}

constexpr const char* kShadowPackages =
    "package p; int c = 1; typedef enum {A, FALSE} bool_t; endpackage\n"
    "package p2; int c = 2; endpackage\n"
    "package p3; int c = 3; endpackage\n";

TEST(LocalNameHidingAWildcardName, AVariableInEachScopeHidesIt) {
  for (const char* src :
       {"module top; function automatic int f(); import p::*; int c = 5; "
        "return c; endfunction initial $display(\"%0d\", f()); endmodule\n",
        "module top; task automatic t(output int o); import p::*; int c = 5; "
        "o = c; endtask int r; initial begin t(r); $display(\"%0d\", r); end "
        "endmodule\n",
        "module top; import p::*; function automatic int f(); int c = 5; "
        "return c; endfunction initial $display(\"%0d\", f()); endmodule\n",
        "interface ifc; import p::*; int c = 5; "
        "initial $display(\"%0d\", c); endinterface\n"
        "module top; ifc i(); endmodule\n",
        "program pg; import p::*; int c = 5; "
        "initial $display(\"%0d\", c); endprogram\n"
        "module top; pg u(); endmodule\n"}) {
    ExpectOutput(std::string(kShadowPackages) + src, "5\n");
  }
}

TEST(LocalNameHidingAWildcardName, OtherNamesStillComeFromThePackage) {
  ExpectOutput(std::string(kShadowPackages) +
                   "module top; import p::*; int c = 5; "
                   "initial $display(\"%0d %0d\", c, FALSE); endmodule\n",
               "5 1\n");
}

TEST(ExplicitImportBinding, AnExplicitImportBeatsTwoWildcardImports) {
  ExpectOutput(std::string(kShadowPackages) +
                   "module top; import p::*; import p2::*; import p3::c; "
                   "initial $display(\"%0d\", c); endmodule\n",
               "3\n");
}

TEST(SubroutineCallBinding, TheSectionsExample3BindsToTheOuterFunction) {
  ExpectOutput(
      "package p; function int f(); return 1; endfunction endpackage\n"
      "module top; int x; if (1) begin : b initial x = f(); import p::*; "
      "end function int f(); return 2; endfunction "
      "initial #1 $display(\"%0d\", x); endmodule\n",
      "2\n");
}

TEST(SubroutineCallBinding, TheSectionsExample4BindsToTheFirstPackage) {
  ExpectOutput(
      "package p; function int f(); return 1; endfunction endpackage\n"
      "package p2; function int f(); return 2; endfunction endpackage\n"
      "module top; import p::*; int x; if (1) begin : b initial x = f(); "
      "end import p2::*; initial #1 $display(\"%0d\", x); endmodule\n",
      "1\n");
}

TEST(ExplicitImportBinding, ImportedLiteralsMakeTheSectionsTop1Legal) {
  ExpectOutput(
      "package p; typedef enum { FALSE, TRUE } bool_t; endpackage\n"
      "package q; typedef enum { ORIGINAL, FALSE } teeth_t; endpackage\n"
      "module top; import p::*; import q::teeth_t, q::ORIGINAL, q::FALSE; "
      "teeth_t myteeth; initial begin myteeth = FALSE; "
      "$display(\"%0d\", myteeth); end endmodule\n",
      "1\n");
}

constexpr const char* kVal =
    "package pkg; parameter int VAL = 99; endpackage\n"
    "package pkg2; parameter int VAL = 77; endpackage\n";

TEST(ImportIntoADesignElement, AnInterfaceProgramAndChecker) {
  for (const auto& [import, value] :
       {std::pair<const char*, const char*>{"import pkg::*;", "99\n"},
        {"import pkg2::VAL;", "77\n"}}) {
    const std::string kImport(import);
    ExpectOutput(kVal + ("interface ifc; " + kImport +
                         " int x = VAL; endinterface\n"
                         "module top; ifc i(); "
                         "initial #1 $display(\"%0d\", i.x); endmodule\n"),
                 value);
    ExpectOutput(kVal + ("program pg; " + kImport +
                         " int x; initial begin x = VAL; "
                         "$display(\"%0d\", x); end endprogram\n"
                         "module top; pg u(); endmodule\n"),
                 value);
    ExpectOutput(kVal + ("checker chk; " + kImport +
                         " int x = VAL; final $display(\"%0d\", x); "
                         "endchecker\n"
                         "module top; chk c(); endmodule\n"),
                 value);
  }
}

}  // namespace
