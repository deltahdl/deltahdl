#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// A source and the line of the report it should draw.
struct Written {
  const char* src;
  uint32_t line;
};

// §3.12.1 (printed page 56): outside every design element a compilation unit
// holds what a package may hold (§26.2), bind directives (§23.11) and the
// design elements themselves. A procedure, an instance of a module, gate,
// switch, pull source or primitive, a genvar, a concurrent assertion, a
// defparam and an alias are items of a module and of none of these, so each
// written there is reported where it starts, the primitive's instance beside
// the primitive's own declaration, which the unit may hold.
TEST(CompilationUnitItems, ModuleItemOutsideEveryDesignElement) {
  const Written kCases[] = {
      {"logic x;\n"
       "initial x = 1;\n",
       2},
      {"final $display(\"done\");\n", 1},
      {"module sub; endmodule\n"
       "sub u();\n",
       2},
      {"wire y, a, b;\n"
       "and g1 (y, a, b);\n",
       2},
      {"genvar i;\n", 1},
      {"logic clk, a;\n"
       "assert property (@(posedge clk) a);\n",
       2},
      {"defparam top.u.P = 2;\n", 1},
      {"wire a, b;\n"
       "alias a = b;\n",
       2},
      {"wire y, d, c;\n"
       "nmos n1 (y, d, c);\n",
       2},
      {"wire a, b;\n"
       "tran t1 (a, b);\n",
       2},
      {"wire y;\n"
       "pullup p (y);\n",
       2},
      {"primitive inv(output z, input a);\n"
       "  table 0 : 1; 1 : 0; endtable\n"
       "endprimitive\n"
       "wire z, a;\n"
       "inv u1 (z, a);\n",
       5},
  };
  for (const Written& c : kCases) {
    auto r = Parse(c.src);
    EXPECT_TRUE(ReportedError(r.diags, "expected top-level declaration", c.line,
                              "3.12.1"))
        << c.src;
  }
}

// The nearest allowed forms: each of those items inside a module, a module
// instance bound into one from the unit, and a property declared in the unit,
// which a concurrent assertion of a module then asserts.
TEST(CompilationUnitItems, TheSameItemsInsideAModule) {
  EXPECT_TRUE(
      ParseOk("module sub #(parameter P = 1); endmodule\n"
              "primitive inv(output z, input a);\n"
              "  table 0 : 1; 1 : 0; endtable\n"
              "endprimitive\n"
              "property pr(c, s); @(posedge c) s; endproperty\n"
              "module top;\n"
              "  logic x, clk, a;\n"
              "  wire y, wa, wb, d, c, z;\n"
              "  initial x = 1;\n"
              "  final $display(\"done\");\n"
              "  sub u();\n"
              "  and g1 (y, wa, wb);\n"
              "  genvar i;\n"
              "  assert property (pr(clk, a));\n"
              "  defparam u.P = 2;\n"
              "  alias wa = wb;\n"
              "  nmos n1 (y, d, c);\n"
              "  tran t1 (wa, wb);\n"
              "  pullup p (y);\n"
              "  inv u1 (z, wa);\n"
              "endmodule\n"
              "bind top sub b();\n"));
}

// §3.12.1 with §26.6: a package export declaration is an item a package may
// hold, so the unit may hold one, naming a package the unit imports.
TEST(CompilationUnitItems, PackageExportInTheUnit) {
  EXPECT_TRUE(
      ParseOk("package p;\n"
              "  int x;\n"
              "endpackage\n"
              "import p::*;\n"
              "export p::*;\n"
              "module m; endmodule\n"));
}

// §3.12.1 (printed page 57): the compilation-unit scope has no name, so no
// import declaration can name it, wherever the declaration stands: a module's
// item or header, an interface's, program's, checker's or package's item, or
// a declaration of a function or of a begin-end block. The report is
// ParseImportItem's, under §26.3, whose package_import_item takes a
// package_identifier where `$unit` stands.
TEST(CompilationUnitImport, DollarUnitImportedInEachPlace) {
  const Written kCases[] = {
      {"module m;\n"
       "  import $unit::*;\n"
       "endmodule\n",
       2},
      {"module m\n"
       "  import $unit::*;\n"
       "  ();\n"
       "endmodule\n",
       2},
      {"interface i;\n"
       "  import $unit::*;\n"
       "endinterface\n",
       2},
      {"program p;\n"
       "  import $unit::*;\n"
       "endprogram\n",
       2},
      {"checker c;\n"
       "  import $unit::*;\n"
       "endchecker\n",
       2},
      {"package q;\n"
       "  import $unit::*;\n"
       "endpackage\n",
       2},
      {"module m;\n"
       "  function void f();\n"
       "    import $unit::*;\n"
       "  endfunction\n"
       "endmodule\n",
       3},
      {"module m;\n"
       "  initial begin\n"
       "    import $unit::*;\n"
       "  end\n"
       "endmodule\n",
       3},
  };
  for (const Written& c : kCases) {
    auto r = Parse(c.src);
    EXPECT_TRUE(ReportedError(r.diags,
                              "the compilation-unit scope cannot be used with "
                              "an import declaration",
                              c.line, "26.3"))
        << c.src;
  }
}

// The nearest allowed form: a named package imported in each of those places.
TEST(CompilationUnitImport, NamedPackageImportedInEachPlace) {
  EXPECT_TRUE(
      ParseOk("package p;\n"
              "  int x;\n"
              "endpackage\n"
              "module m\n"
              "  import p::*;\n"
              "  ();\n"
              "  import p::*;\n"
              "  function void f();\n"
              "    import p::*;\n"
              "  endfunction\n"
              "  initial begin\n"
              "    import p::*;\n"
              "  end\n"
              "endmodule\n"
              "interface i;\n"
              "  import p::*;\n"
              "endinterface\n"
              "program pr;\n"
              "  import p::*;\n"
              "endprogram\n"
              "checker c;\n"
              "  import p::*;\n"
              "endchecker\n"
              "package q;\n"
              "  import p::*;\n"
              "endpackage\n"));
}

}  // namespace
