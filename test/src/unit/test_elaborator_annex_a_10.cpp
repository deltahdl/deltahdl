#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(BnfClarificationElaboration, RefPortOnModule) {
  EXPECT_TRUE(
      ElabOk("module m(ref int x);\n"
             "endmodule\n"));
}

TEST(BnfClarificationElaboration, InoutPortOnModule) {
  EXPECT_TRUE(
      ElabOk("module m(inout wire a);\n"
             "endmodule\n"));
}

TEST(BnfClarificationElaboration, TimeunitAndPrecisionOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  timeunit 1ns;\n"
             "  timeprecision 1ps;\n"
             "endmodule\n"));
}

TEST(BnfClarificationElaboration, AutomaticInInitialBlockOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  initial begin\n"
             "    automatic int x = 5;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(BnfClarificationElaboration, StructPackedWithDimOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  typedef struct packed {\n"
             "    logic [7:0] a;\n"
             "    logic [7:0] b;\n"
             "  } my_t;\n"
             "  my_t data;\n"
             "endmodule\n"));
}

TEST(BnfClarificationElaboration, ReplicationWithConstantOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [7:0] x;\n"
             "  assign x = {4{2'b01}};\n"
             "endmodule\n"));
}

TEST(BnfClarificationElaboration, EmptyUnpackedArrayConcatOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int q[$];\n"
             "  initial q = {};\n"
             "endmodule\n"));
}

TEST(BnfClarificationElaboration, DollarInQueueSelectOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int q[$];\n"
             "  initial q[$] = 5;\n"
             "endmodule\n"));
}

TEST(BnfClarificationElaboration, FinalOnPureVirtualError) {
  ElabFixture f;
  ElaborateSrc(
      "virtual class c;\n"
      "  pure virtual function void do_it() final;\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §A.10 item 4: when the bind target is an interface, the bound instance must
// be an interface or checker instantiation, not a module instantiation.
TEST(BnfClarificationElaboration, BindCheckerIntoInterfaceOk) {
  EXPECT_TRUE(ElabOk(
      "checker chk; endchecker\n"
      "interface ifc; endinterface\n"
      "module top;\n"
      "  ifc i();\n"
      "endmodule\n"
      "bind ifc chk c();\n"));
}

TEST(BnfClarificationElaboration, BindModuleIntoInterfaceError) {
  ElabFixture f;
  ElaborateSrc(
      "module mod; endmodule\n"
      "interface ifc; endinterface\n"
      "module top;\n"
      "  ifc i();\n"
      "endmodule\n"
      "bind ifc mod m();\n",
      f, "top");
  EXPECT_TRUE(f.diag.HasErrors());
}

// §A.10 item 11: a dynamic_override_specifier may not be used on a static
// constraint.
TEST(BnfClarificationElaboration, DynamicOverrideOnStaticConstraintError) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  static constraint :initial c { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// §A.10 item 25: a dynamic_override_specifier is legal only on a method
// declared inside a (non-interface) class; on a free subroutine it is illegal.
TEST(BnfClarificationElaboration, DynamicOverrideOutsideClassError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function :initial void f();\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §A.10 item 41: every argument of a constant_function_call must itself be a
// constant expression.
TEST(BnfClarificationElaboration, ConstantFunctionCallConstantArgOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  function int calc(int n); return n * 2; endfunction\n"
             "  localparam int P = calc(4);\n"
             "endmodule\n"));
}

TEST(BnfClarificationElaboration, ConstantFunctionCallNonConstantArgError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int x;\n"
      "  function int calc(int n); return n * 2; endfunction\n"
      "  localparam int P = calc(x);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §A.10 item 16: when the vectored or scalared keyword is used there must be at
// least one packed dimension.
TEST(BnfClarificationElaboration, VectoredWithPackedDimensionOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  wire vectored [3:0] w;\n"
             "endmodule\n"));
}

TEST(BnfClarificationElaboration, VectoredWithoutPackedDimensionError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire vectored w;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §A.10 item 19: a named type used as an enum base type must denote an
// integer_atom_type or integer_vector_type.
TEST(BnfClarificationElaboration, EnumIntegerBaseTypeOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  typedef int base_t;\n"
             "  enum base_t { A = 0, B = 1 } e;\n"
             "endmodule\n"));
}

TEST(BnfClarificationElaboration, EnumRealBaseTypeError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef real base_t;\n"
      "  enum base_t { A = 0, B = 1 } e;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §A.10 item 20: a void member is legal only within a tagged union.
TEST(BnfClarificationElaboration, VoidMemberInTaggedUnionOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  union tagged { void Invalid; int Valid; } u;\n"
             "endmodule\n"));
}

TEST(BnfClarificationElaboration, VoidMemberInUntaggedUnionError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  union { void Invalid; int Valid; } u;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §A.10 item 21: an expression used as the argument of a type_reference must
// not contain hierarchical references or references to dynamic-object elements.
TEST(BnfClarificationElaboration, TypeRefArgHierarchicalRefError) {
  EXPECT_FALSE(
      ElabOk("module sub;\n"
             "  int q;\n"
             "endmodule\n"
             "module m;\n"
             "  sub s();\n"
             "  var type(s.q) v;\n"
             "endmodule\n"));
}

TEST(BnfClarificationElaboration, TypeRefArgDynamicElementError) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  int d[];\n"
             "  var type(d[0]) v;\n"
             "endmodule\n"));
}

// §A.10 item 46: `this` may only appear within a class scope (or out-of-block
// method); using it in a module procedural context is illegal.
TEST(BnfClarificationElaboration, ThisInClassMethodOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  int y;\n"
             "  function int f();\n"
             "    return this.y;\n"
             "  endfunction\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(BnfClarificationElaboration, ThisInModuleInitialError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int y;\n"
      "  initial begin\n"
      "    y = this.y;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §A.10 item 43: in a scope randomize_call (one that is not a method on a
// class object), `null` is not a legal argument.
TEST(BnfClarificationElaboration, ScopeRandomizeNullArgumentError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial begin randomize(null); end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §A.10 item 43: a scope randomize_call may not carry a parenthesized
// identifier_list after `with`.
TEST(BnfClarificationElaboration, ScopeRandomizeParenIdentifierListError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial begin randomize() with (a) { a > 0; }; end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §A.10 item 43 edge: the restriction is specific to scope randomize; a class
// object's randomize method may take the parenthesized identifier list.
TEST(BnfClarificationElaboration, MethodRandomizeParenIdentifierListOk) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial begin obj.randomize() with (a) { a > 0; }; end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §A.10 item 45: a type_reference primary may only be used with the equality,
// inequality, and case equality/inequality operators. Applying any other
// operator to it is illegal.
TEST(BnfClarificationElaboration, TypeRefWithArithmeticOperatorError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int a;\n"
      "  logic [31:0] w;\n"
      "  assign w = type(a) + 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §A.10 item 45: an equality comparison between type references remains legal
// and must not be rejected by the operator restriction.
TEST(BnfClarificationElaboration, TypeRefEqualityComparisonOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int a;\n"
             "  logic r;\n"
             "  assign r = type(a) == type(a);\n"
             "endmodule\n"));
}

}
