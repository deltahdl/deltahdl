#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(BnfClarificationParsing, AutomaticInProceduralBlockOk) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    automatic int x = 5;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(BnfClarificationParsing, MatchesPrecedenceOverLogicalAnd) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    if (x matches 1 && y matches 2)\n"
              "      $display(\"ok\");\n"
              "  end\n"
              "endmodule\n"));
}

TEST(BnfClarificationParsing, EventExprInParensOk) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  event e1, e2;\n"
              "  initial @(e1 or e2) $display(\"ok\");\n"
              "endmodule\n"));
}

TEST(BnfClarificationParsing, EmptyUnpackedArrayConcat) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int q[$];\n"
              "  initial q = {};\n"
              "endmodule\n"));
}

TEST(BnfClarificationParsing, TaskCallWithoutParens) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  task my_task; endtask\n"
              "  initial my_task;\n"
              "endmodule\n"));
}

TEST(BnfClarificationParsing, VoidFunctionCallWithParens) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  function void my_func(); endfunction\n"
              "  initial my_func();\n"
              "endmodule\n"));
}

TEST(BnfClarificationParsing, DollarInQueueSelect) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int q[$];\n"
              "  initial q[$] = 5;\n"
              "endmodule\n"));
}

TEST(BnfClarificationParsing, ErrorRandAndRandc) {
  auto r = Parse(
      "class c;\n"
      "  rand randc int x;\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(BnfClarificationParsing, ErrorDuplicateRand) {
  auto r = Parse(
      "class c;\n"
      "  rand rand int x;\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(BnfClarificationParsing, ErrorDuplicateStatic) {
  auto r = Parse(
      "class c;\n"
      "  static static int x;\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(BnfClarificationParsing, NonvoidFunctionCallWithParens) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  function int my_func(); return 0; endfunction\n"
              "  int y;\n"
              "  initial y = my_func();\n"
              "endmodule\n"));
}

TEST(BnfClarificationParsing, CovergroupExtendsInClassOk) {
  EXPECT_TRUE(
      ParseOk("class c;\n"
              "  int val;\n"
              "  covergroup base_cg;\n"
              "    coverpoint val;\n"
              "  endgroup\n"
              "endclass\n"));
}

TEST(BnfClarificationParsing, PureVirtualMethodOk) {
  EXPECT_TRUE(
      ParseOk("virtual class c;\n"
              "  pure virtual function void do_it();\n"
              "endclass\n"));
}

// §A.10 item 1: a package_import_declaration in an ANSI
// module/interface/program header must be followed by a parameter_port_list
// and/or a list_of_port_declarations.
TEST(BnfClarificationParsing, HeaderImportFollowedByPortListOk) {
  EXPECT_TRUE(
      ParseOk("module m import pkg::*; (input logic a);\n"
              "endmodule\n"));
}

TEST(BnfClarificationParsing, ErrorHeaderImportWithoutPortList) {
  auto r = Parse(
      "module m import pkg::*; ;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §A.10 item 7: in a class scope the `parameter` keyword is accepted as a
// synonym for `localparam`.
TEST(BnfClarificationParsing, ClassParameterIsLocalparamSynonym) {
  EXPECT_TRUE(
      ParseOk("class C;\n"
              "  parameter int x = 1;\n"
              "endclass\n"));
}

// §A.10 item 9: the `default` keyword may appear at most once in a class
// constructor argument list.
TEST(BnfClarificationParsing, ErrorDuplicateDefaultInConstructorArgs) {
  auto r = Parse(
      "class C extends Base;\n"
      "  function new(default, int x, default);\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

// §A.10 item 18: a type_reference used in a variable declaration must be
// preceded by the `var` keyword; bare `type(...)` is rejected.
TEST(BnfClarificationParsing, TypeRefInVarDeclWithVarOk) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int a;\n"
              "  var type(a) b;\n"
              "endmodule\n"));
}

TEST(BnfClarificationParsing, TypeRefInNetDeclWithNetKeywordOk) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  wire x;\n"
              "  wire type(x) y;\n"
              "endmodule\n"));
}

TEST(BnfClarificationParsing, ErrorBareTypeRefWithoutVarOrNetKeyword) {
  auto r = Parse(
      "module m;\n"
      "  wire x;\n"
      "  type(x) y;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §A.10 item 22: a localparam in a parameter_port_list must carry a default;
// only a (non-localparam) parameter may omit it there.
TEST(BnfClarificationParsing, ParamPortListLocalparamHasDefaultOk) {
  EXPECT_TRUE(
      ParseOk("module m #(parameter int W, localparam int H = 32);\n"
              "endmodule\n"));
}

TEST(BnfClarificationParsing, ErrorParamPortListLocalparamWithoutDefault) {
  auto r = Parse(
      "module m #(localparam int W);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §A.10 item 28: a tf_port_item may omit its port_identifier only inside a
// function/task prototype; a full subroutine declaration must name each port.
TEST(BnfClarificationParsing, PrototypePortMayOmitIdentifierOk) {
  EXPECT_TRUE(
      ParseOk("virtual class C;\n"
              "  pure virtual function void foo(int);\n"
              "endclass\n"));
}

TEST(BnfClarificationParsing, ErrorFullSubroutinePortOmitsIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  function void foo(int);\n"
      "  endfunction\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §A.10 item 34: the `.*` token pair may appear at most once in a port
// connection list.
TEST(BnfClarificationParsing, ErrorDoubleWildcardPortConnection) {
  auto r = Parse(
      "module m;\n"
      "  sub u(.*, .*);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §A.10 item 15: a package import statement may not appear directly within a
// class scope.
TEST(BnfClarificationParsing, ErrorImportInClassScope) {
  auto r = Parse(
      "class c;\n"
      "  import p::*;\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

// §A.10 item 27: a DPI import prototype's formal arguments may not use the
// `ref` pass-by-reference mode.
TEST(BnfClarificationParsing, ErrorRefFormalInDpiImport) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" function void f(ref int x);\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
