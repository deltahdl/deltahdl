#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <string_view>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(BnfClarificationElaboration, VariableOutputPortInitializerOk) {
  ElabFixture f;
  EXPECT_TRUE(ElabOk(
      "module m(output logic [3:0] q = 4'd9, output var int c = 3); endmodule",
      f));
}

TEST(BnfClarificationElaboration, NetOutputPortInitializerError) {
  ElabFixture f;
  ElaborateSrc("module m(output q = 1'b0); endmodule", f, "m");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "initializer on output port 'q', which is a net and no variable", 1,
      "23.2.2.2"));
}

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
      "  pure virtual function :final void do_it();\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "':final' shall not be specified on a pure virtual method", 2, "8.20"));
}

TEST(BnfClarificationElaboration, BindCheckerIntoInterfaceOk) {
  EXPECT_TRUE(
      ElabOk("checker chk; endchecker\n"
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot bind non-interface/non-checker 'mod' into "
                            "interface 'ifc'",
                            6, "23.11"));
}

TEST(BnfClarificationElaboration, DynamicOverrideOnStaticConstraintError) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  rand int x;\n"
      "  static constraint :initial c { x > 0; }\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "static constraint 'c' shall not carry a dynamic override specifier", 3,
      "18.5.10"));
}

TEST(BnfClarificationElaboration, DynamicOverrideOutsideClassError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function :initial void f();\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a function's dynamic_override_specifiers belong on a class "
      "method declaration, and an interface class takes none",
      2, "13.4"));
}

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
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "constant function call 'calc' has a non-constant argument",
                    4, "13.4.3"));
}

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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "vectored or scalared requires at least one packed "
                            "dimension",
                            2, "6.9.2"));
}

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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "enum base type 'base_t' is not an "
                            "integer_atom_type or integer_vector_type",
                            3, "6.19"));
}

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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "void member is only allowed in tagged unions", 2,
                            "7.2"));
}

TEST(BnfClarificationElaboration, TypeRefArgHierarchicalRefError) {
  ElabFixture f;
  ElabOk(
      "module sub;\n"
      "  int q;\n"
      "endmodule\n"
      "module m;\n"
      "  sub s();\n"
      "  var type(s.q) v;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "type operator argument uses a hierarchical reference, "
                    "which the type operator does not accept",
                    6, "6.23"));
}

TEST(BnfClarificationElaboration, TypeRefArgDynamicElementError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  int d[];\n"
      "  var type(d[0]) v;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "type operator argument shall not reference "
                            "elements of dynamic objects",
                            3, "6.23"));
}

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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'this' has no object to refer to outside a non-static class method", 3,
      "8.11"));
}

TEST(BnfClarificationElaboration, ScopeRandomizeNullArgumentError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial begin randomize(null); end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'null' is not a legal argument to a scope randomize call", 2, "A.8.2"));
}

TEST(BnfClarificationElaboration, ScopeRandomizeParenIdentifierListError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial begin randomize() with (a) { a > 0; }; end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "scope randomize call cannot use a parenthesized "
                            "identifier list after 'with'",
                            2, "A.8.2"));
}

TEST(BnfClarificationElaboration, MethodRandomizeParenIdentifierListOk) {
  ElabFixture f;
  ElaborateSrc(
      "class C;\n"
      "  rand int a;\n"
      "endclass\n"
      "module m;\n"
      "  C obj = new;\n"
      "  initial begin obj.randomize() with (a) { a > 0; }; end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(BnfClarificationElaboration, TypeRefWithArithmeticOperatorError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int a;\n"
      "  logic [31:0] w;\n"
      "  assign w = type(a) + 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a type reference may only be used with the "
                            "equality, inequality, and case "
                            "equality/inequality operators",
                            4, "6.23"));
}

TEST(BnfClarificationElaboration, TypeRefEqualityComparisonOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int a;\n"
             "  logic r;\n"
             "  assign r = type(a) == type(a);\n"
             "endmodule\n"));
}

TEST(BnfClarificationElaboration, DollarInTheSelectOfANonQueueError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef int q_t [$];\n"
      "  int a [0:3];\n"
      "  logic [7:0] v;\n"
      "  int d [];\n"
      "  int q [$];\n"
      "  q_t t;\n"
      "  int x;\n"
      "  int s [0:2];\n"
      "  initial begin\n"
      "    x = a[$];\n"
      "    x = v[$];\n"
      "    s = a[1:$];\n"
      "    x = d[$-1];\n"
      "    x = q[$];\n"
      "    x = t[$];\n"
      "    x = int'(x inside {[0:$]});\n"
      "  end\n"
      "endmodule\n",
      f);
  constexpr std::string_view kMessage =
      "'$' may stand only in a queue's dimension or select";
  for (uint32_t line : {11U, 12U, 13U, 14U}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kMessage, line, "6.20.7"))
        << line;
  }
  for (uint32_t line : {15U, 16U, 17U}) {
    EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kMessage, line, "6.20.7"))
        << line;
  }
}

TEST(BnfClarificationElaboration, TypeRefAsAnInsideOperandError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int a;\n"
      "  bit b;\n"
      "  initial begin\n"
      "    b = type(a) inside {1, 2};\n"
      "    b = a inside {type(int)};\n"
      "  end\n"
      "endmodule\n",
      f);
  for (uint32_t line : {5U, 6U}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "a type reference may only be used with the "
                              "equality, inequality, and case "
                              "equality/inequality operators",
                              line, "6.23"))
        << line;
  }
}

TEST(BnfClarificationElaboration, TypeRefOperatorAnywhereError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int a;\n"
      "  localparam bit P = type(a) & 1;\n"
      "  bit d = !type(a);\n"
      "  function bit f();\n"
      "    return type(a) + 1;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    automatic bit x = type(a) | 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  for (uint32_t line : {3U, 4U, 6U, 9U}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "a type reference may only be used with the "
                              "equality, inequality, and case "
                              "equality/inequality operators",
                              line, "6.23"))
        << line;
  }
}

}  // namespace
