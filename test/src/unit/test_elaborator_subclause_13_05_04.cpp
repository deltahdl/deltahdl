#include <gtest/gtest.h>

#include <string>
#include <utility>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(SubroutineCallElaborationSyntax, NamedArgCallElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int add(int a, int b); return a + b; endfunction\n"
      "  logic [31:0] x;\n"
      "  initial x = add(.b(2), .a(1));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ArgumentBindingElaboration, UnknownNamedArgError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int add(int a, int b); return a + b; endfunction\n"
      "  int x;\n"
      "  initial x = add(.c(1), .a(2));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "no parameter 'c' in 'add'",
                            4, "13.5.4"));
}

TEST(ArgumentBindingElaboration, NamedArgumentNamesNoFormalNames13_5_4) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int add(int a, int b); return a + b; endfunction\n"
      "  int x;\n"
      "  initial x = add(.c(1), .a(2));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "no parameter 'c' in 'add'",
                            4, "13.5.4"));
}

TEST(ArgumentBindingElaboration, MixedPositionalNamedOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int add3(int a, int b, int c);\n"
      "    return a + b + c;\n"
      "  endfunction\n"
      "  int x;\n"
      "  initial x = add3(1, .c(3), .b(2));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ArgumentBindingElaboration, MissingRequiredNamedArgError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int add(int a, int b); return a + b; endfunction\n"
      "  int x;\n"
      "  initial x = add(.a(1));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "missing argument 'b' in call to 'add'", 4,
                            "13.5.3"));
}

TEST(ArgumentBindingElaboration, OmitDefaultedArgWithNamedBindingOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int scale(int val, int factor = 3);\n"
      "    return val * factor;\n"
      "  endfunction\n"
      "  int x;\n"
      "  initial x = scale(.val(7));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

std::string ScopedCalleesSrc(const std::string& calls) {
  return "package pk;\n"
         "  function automatic int pf(int a, int b = 4); return a; "
         "endfunction\n"
         "endpackage\n"
         "interface ifc;\n"
         "  function automatic int f(int a, int b = 6); return a; endfunction\n"
         "endinterface\n"
         "class C;\n"
         "  function int me(int a, int b = 5); return a + b; endfunction\n"
         "  static function int sm(int a, int b = 7); return a; endfunction\n"
         "  task tm(int a, int b = 8); endtask\n"
         "  function int inner(); return me(.b(1)); endfunction\n"
         "endclass\n"
         "module m;\n"
         "  C c = new();\n"
         "  ifc i();\n"
         "  int x;\n"
         "  task automatic t(int a, int b = 3); endtask\n"
         "  initial begin\n" +
         calls +
         "  end\n"
         "endmodule\n";
}

TEST(ArgumentBindingElaboration, ANamedTaskCallOmittingAFormalWithoutADefault) {
  const std::string kSrc = ScopedCalleesSrc(
      "    t(.b(1));\n"
      "    t(.a(1));\n");
  ElabFixture f;
  ElaborateSrc(kSrc, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "missing argument 'a' in call to 't'",
                            LineHolding(kSrc, "t(.b(1));"), "13.5.3"));
  EXPECT_FALSE(
      ErrorOnLine(f.diag.Diagnostics(), LineHolding(kSrc, "t(.a(1));")));
}

TEST(ArgumentBindingElaboration,
     DISABLED_ANamedScopedCallOmittingAFormalWithoutADefault) {
  const std::string kSrc = ScopedCalleesSrc(
      "    x = c.me(.b(2));\n"
      "    x = C::sm(.b(2));\n"
      "    c.tm(.b(2));\n"
      "    x = pk::pf(.b(2));\n"
      "    x = i.f(.b(2));\n"
      "    x = c.me(.a(2));\n"
      "    x = pk::pf(.a(2));\n"
      "    x = i.f(.a(2));\n");
  ElabFixture f;
  ElaborateSrc(kSrc, f);
  for (const auto& [text, callee] :
       {std::pair<const char*, const char*>{"c.me(.b(2));", "me"},
        {"C::sm(.b(2));", "sm"},
        {"c.tm(.b(2));", "tm"},
        {"pk::pf(.b(2));", "pf"},
        {"i.f(.b(2));", "f"},
        {"return me(.b(1));", "me"}}) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        std::string("missing argument 'a' in call to '") + callee + "'",
        LineHolding(kSrc, text), "13.5.3"))
        << text;
  }
  for (const char* text : {"c.me(.a(2));", "pk::pf(.a(2));", "i.f(.a(2));"}) {
    EXPECT_FALSE(ErrorOnLine(f.diag.Diagnostics(), LineHolding(kSrc, text)))
        << text;
  }
}

}  // namespace
