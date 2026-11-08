#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

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
  EXPECT_TRUE(ReportedError(
      r.diags, "cannot combine 'rand' and 'randc' qualifiers", 2, "8.3"));
}

TEST(BnfClarificationParsing, ErrorDuplicateRand) {
  auto r = Parse(
      "class c;\n"
      "  rand rand int x;\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(r.diags, "duplicate 'rand' qualifier", 2, "8.3"));
}

TEST(BnfClarificationParsing, ErrorDuplicateStatic) {
  auto r = Parse(
      "class c;\n"
      "  static static int x;\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(r.diags, "duplicate 'static' qualifier", 2, "8.3"));
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

TEST(BnfClarificationParsing, HeaderImportFollowedByPortListOk) {
  EXPECT_TRUE(
      ParseOk("module m import pkg::*; (input logic a);\n"
              "endmodule\n"));
}

TEST(BnfClarificationParsing, ErrorHeaderImportWithoutPortList) {
  auto r = Parse(
      "module m import pkg::*; ;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "package_import_declaration in ansi header must be "
                            "followed by parameter_port_list or "
                            "list_of_port_declarations",
                            1, "23.2.1"));
}

TEST(BnfClarificationParsing, ClassParameterIsLocalparamSynonym) {
  EXPECT_TRUE(
      ParseOk("class C;\n"
              "  parameter int x = 1;\n"
              "endclass\n"));
}

TEST(BnfClarificationParsing, ErrorDuplicateDefaultInConstructorArgs) {
  auto r = Parse(
      "class C extends Base;\n"
      "  function new(default, int x, default);\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "'default' already appears earlier in this class "
                            "constructor argument list",
                            2, "8.17"));
}

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
  EXPECT_TRUE(ReportedError(r.diags,
                            "type_reference in a variable declaration must be "
                            "preceded by the 'var' keyword",
                            3, "6.8"));
}

TEST(BnfClarificationParsing, ParamPortListLocalparamHasDefaultOk) {
  EXPECT_TRUE(
      ParseOk("module m #(parameter int W, localparam int H = 32);\n"
              "endmodule\n"));
}

TEST(BnfClarificationParsing, ErrorParamPortListLocalparamWithoutDefault) {
  auto r = Parse(
      "module m #(localparam int W);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags,
      "localparam 'W' in parameter port list must have a default value", 1,
      "6.20.1"));
}

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
  EXPECT_TRUE(ReportedError(r.diags,
                            "tf_port_item shall include a port_identifier "
                            "outside of a function_prototype or task_prototype",
                            2, "13.3"));
}

TEST(BnfClarificationParsing, ErrorDoubleWildcardPortConnection) {
  auto r = Parse(
      "module m;\n"
      "  sub u(.*, .*);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, ".* already appears earlier in this port connection list", 2,
      "23.3.2"));
}

TEST(BnfClarificationParsing, ErrorImportInClassScope) {
  auto r = Parse(
      "class c;\n"
      "  import p::*;\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "package import declaration is not allowed in class scope", 2,
      "26.3"));
}

TEST(BnfClarificationParsing, ErrorRefFormalInDpiImport) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" function void f(ref int x);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "ref qualifier cannot be used in a DPI import declaration", 2,
      "35.5.4"));
}

}  // namespace
