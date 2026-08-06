#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ModportExpressionElaboration, SamePortIdInDifferentModports) {
  EXPECT_TRUE(
      ElabOk("interface I;\n"
             "  logic [7:0] r;\n"
             "  modport A(output .P(r[3:0]));\n"
             "  modport B(output .P(r[7:4]));\n"
             "endinterface\n"
             "module top;\n"
             "  I inst();\n"
             "endmodule\n"));
}

TEST(ModportExpressionElaboration, DuplicatePortIdInSameModportErrors) {
  ElabFixture f;
  ElaborateSrc(
      "interface I;\n"
      "  logic a, b;\n"
      "  modport mp(input .P(a), input .P(b));\n"
      "endinterface\n"
      "module top;\n"
      "  I inst();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ModportExpressionElaboration,
     ConstantPortExpressionWithOutputDirectionErrors) {
  ElabFixture f;
  ElaborateSrc(
      "interface I;\n"
      "  modport mp(output .P(2));\n"
      "endinterface\n"
      "module top;\n"
      "  I inst();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ModportExpressionElaboration,
     ConstantPortExpressionWithInputDirectionAccepted) {
  EXPECT_TRUE(
      ElabOk("interface I;\n"
             "  modport mp(input .P(2));\n"
             "endinterface\n"
             "module top;\n"
             "  I inst();\n"
             "endmodule\n"));
}

// §25.5.4 + §11.2.1: a parameter is a constant, so a modport expression that
// names an interface parameter is a constant port expression and cannot be an
// output — the same rule the LRM applies to its `.Q` port, extended past the
// literal form to the parameter constant form.
TEST(ModportExpressionElaboration,
     ParameterPortExpressionWithOutputDirectionErrors) {
  ElabFixture f;
  ElaborateSrc(
      "interface I #(parameter K = 3) ();\n"
      "  modport mp(output .P(K));\n"
      "endinterface\n"
      "module top;\n"
      "  I inst();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §25.5.4 + §11.2.1: a localparam is a constant, so it is likewise illegal as
// an output modport port expression.
TEST(ModportExpressionElaboration,
     LocalparamPortExpressionWithOutputDirectionErrors) {
  ElabFixture f;
  ElaborateSrc(
      "interface I;\n"
      "  localparam L = 5;\n"
      "  modport mp(inout .P(L));\n"
      "endinterface\n"
      "module top;\n"
      "  I inst();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §25.5.4 + §11.2.1: a const variable is a constant. This is the LRM's own
// `const int x=1` form; binding it to an output port is illegal.
TEST(ModportExpressionElaboration,
     ConstVariablePortExpressionWithOutputDirectionErrors) {
  ElabFixture f;
  ElaborateSrc(
      "interface I;\n"
      "  const int x = 1;\n"
      "  modport mp(output .Q(x));\n"
      "endinterface\n"
      "module top;\n"
      "  I inst();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §25.5.4: the constant restriction applies only to output/inout. A parameter
// bound to an input port is a legal constant port expression (as the LRM's
// input `.Q` port shows).
TEST(ModportExpressionElaboration,
     ParameterPortExpressionWithInputDirectionAccepted) {
  EXPECT_TRUE(
      ElabOk("interface I #(parameter K = 3) ();\n"
             "  modport mp(input .P(K));\n"
             "endinterface\n"
             "module top;\n"
             "  I inst();\n"
             "endmodule\n"));
}

// §25.5.4: the same const-variable interface as the output-error case above,
// but bound to an input port, elaborates cleanly. Pairing the two confirms the
// output error is the direction rule firing, not the `const int` declaration.
TEST(ModportExpressionElaboration,
     ConstVariablePortExpressionWithInputDirectionAccepted) {
  EXPECT_TRUE(
      ElabOk("interface I;\n"
             "  const int x = 1;\n"
             "  modport mp(input .Q(x));\n"
             "endinterface\n"
             "module top;\n"
             "  I inst();\n"
             "endmodule\n"));
}

// §25.5.4: a writable interface signal (here a part-select of a plain vector)
// is not a constant and remains a legal output modport port expression, so the
// constant check must not misfire on it. Part-select is the LRM's own array-
// element form of a modport expression.
TEST(ModportExpressionElaboration,
     PartSelectOfVariablePortExpressionWithOutputAccepted) {
  EXPECT_TRUE(
      ElabOk("interface I;\n"
             "  logic [7:0] r;\n"
             "  modport mp(output .P(r[3:0]));\n"
             "endinterface\n"
             "module top;\n"
             "  I inst();\n"
             "endmodule\n"));
}

// §25.5.4 para 1: a modport expression may be a concatenation of interface
// elements. A concatenation of writable signals is not a constant, so it
// elaborates as a legal output port expression.
TEST(ModportExpressionElaboration,
     ConcatenationPortExpressionWithOutputAccepted) {
  EXPECT_TRUE(
      ElabOk("interface I;\n"
             "  logic a, b;\n"
             "  modport mp(output .P({a, b}));\n"
             "endinterface\n"
             "module top;\n"
             "  I inst();\n"
             "endmodule\n"));
}

// §25.5.4 para 1: a modport expression may name an element of a structure. A
// member of a writable struct is not a constant and elaborates as a legal
// output port expression.
TEST(ModportExpressionElaboration,
     StructElementPortExpressionWithOutputAccepted) {
  EXPECT_TRUE(
      ElabOk("interface I;\n"
             "  struct packed { logic x; logic y; } s;\n"
             "  modport mp(output .P(s.x));\n"
             "endinterface\n"
             "module top;\n"
             "  I inst();\n"
             "endmodule\n"));
}

// §25.5.4 para 4: the port expression is optional — `.P()` defines a port that
// connects to nothing internal. Because it is a named port, its identifier is a
// fresh port name and need NOT be a declared interface item, so it elaborates
// even though the interface declares no `P`.
TEST(ModportExpressionElaboration, EmptyNamedPortNeedNotBeDeclared) {
  EXPECT_TRUE(
      ElabOk("interface I;\n"
             "  modport mp(input .P());\n"
             "endinterface\n"
             "module top;\n"
             "  I inst();\n"
             "endmodule\n"));
}

// §25.5.4 para 2 (contrast to the above): a BARE simple port identifier is both
// a port name and a reference to an interface item, so it must name something
// the interface declares. An undeclared bare identifier is rejected — this is
// what distinguishes it from the exempt `.P()` named-port form.
TEST(ModportExpressionElaboration, BareSimplePortMustBeDeclared) {
  ElabFixture f;
  ElaborateSrc(
      "interface I;\n"
      "  modport mp(input P);\n"
      "endinterface\n"
      "module top;\n"
      "  I inst();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §25.5.4 para 1: a modport expression may be an assignment pattern of
// interface elements. The form is admitted and elaborates.
TEST(ModportExpressionElaboration, AssignmentPatternPortExpressionAccepted) {
  EXPECT_TRUE(
      ElabOk("interface I;\n"
             "  logic a, b;\n"
             "  modport mp(input .P('{a, b}));\n"
             "endinterface\n"
             "module top;\n"
             "  I inst();\n"
             "endmodule\n"));
}

// §25.5.4 + §11.2.1: accepting-path pairing for the localparam constant form —
// a localparam bound to an input port is legal (only output/inout is barred).
TEST(ModportExpressionElaboration,
     LocalparamPortExpressionWithInputDirectionAccepted) {
  EXPECT_TRUE(
      ElabOk("interface I;\n"
             "  localparam L = 5;\n"
             "  modport mp(input .P(L));\n"
             "endinterface\n"
             "module top;\n"
             "  I inst();\n"
             "endmodule\n"));
}

// §25.5.4 (SHALL, no duplicate port definition): the duplicate may arise
// between a bare simple port identifier and a named `.name(...)` port sharing
// that name, not only between two named ports. Here declared `R` is used as a
// simple port and again as a named port id — a second definition of `R` — and
// is rejected.
TEST(ModportExpressionElaboration, SimplePortIdCollidingWithNamedPortIdErrors) {
  ElabFixture f;
  ElaborateSrc(
      "interface I;\n"
      "  logic R, a;\n"
      "  modport mp(input R, output .R(a));\n"
      "endinterface\n"
      "module top;\n"
      "  I inst();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ModportExpressionElaboration,
     HierarchicalAccessThroughModportSelectsBoundExpression) {
  EXPECT_TRUE(
      ElabOk("interface I;\n"
             "  logic [7:0] r;\n"
             "  modport A(output .P(r[3:0]));\n"
             "endinterface\n"
             "module child(I i);\n"
             "endmodule\n"
             "module top;\n"
             "  I inst();\n"
             "  child u(inst.A);\n"
             "endmodule\n"));
}

}  // namespace
