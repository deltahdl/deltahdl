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

// §13.5.4: a named argument binds to the formal of that name, so a name no
// formal carries binds to nothing. The report that rejects it names the
// subclause stating the rule, so a caller learns which rule was enforced
// without matching the wording of the message.
TEST(ArgumentBindingElaboration, NamedArgumentNamesNoFormalNames13_5_4) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int add(int a, int b); return a + b; endfunction\n"
      "  int x;\n"
      "  initial x = add(.c(1), .a(2));\n"
      "endmodule\n",
      f);
  const Diagnostic* rep = FindDiag(f, "no parameter 'c' in 'add'");
  ASSERT_NE(rep, nullptr);
  EXPECT_EQ(rep->subclause, "13.5.4");
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
  // A formal left unbound and carrying no default is reported under §13.5.3,
  // which is the rule that gives an omitted argument its value, rather than
  // under §13.5.4, which only decides which formal a name binds to.
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

}  // namespace
