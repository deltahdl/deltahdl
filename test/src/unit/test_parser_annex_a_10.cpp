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
  // §8.3 owns the class-property qualifier rules Parser::ParseClassQualifiers
  // enforces; A.10 states the grammar clarification and has no report of its
  // own.
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
  // §23.2.1 owns the ANSI header rule; the report stands at the `import`
  // keyword the header opened with.
  EXPECT_TRUE(ReportedError(r.diags,
                            "package_import_declaration in ansi header must be "
                            "followed by parameter_port_list or "
                            "list_of_port_declarations",
                            1, "23.2.1"));
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
  // §8.17 owns the `default` sentinel rule.
  EXPECT_TRUE(ReportedError(r.diags,
                            "'default' keyword shall appear at most once in a "
                            "class constructor argument list",
                            2, "8.17"));
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
  // §6.8 owns the rule that a type_reference in a variable declaration needs
  // the `var` keyword.
  EXPECT_TRUE(ReportedError(r.diags,
                            "type_reference in a variable declaration must be "
                            "preceded by the 'var' keyword",
                            3, "6.8"));
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
  // §6.20.1 owns the rule that a localparam is assigned where it is declared.
  EXPECT_TRUE(ReportedError(
      r.diags,
      "localparam 'W' in parameter port list must have a default value", 1,
      "6.20.1"));
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
  // §13.3 owns the tf_port_item rule.
  EXPECT_TRUE(ReportedError(r.diags,
                            "tf_port_item shall include a port_identifier "
                            "outside of a function_prototype or task_prototype",
                            2, "13.3"));
}

// §A.10 item 34: the `.*` token pair may appear at most once in a port
// connection list.
TEST(BnfClarificationParsing, ErrorDoubleWildcardPortConnection) {
  auto r = Parse(
      "module m;\n"
      "  sub u(.*, .*);\n"
      "endmodule\n");
  // §23.3.2 owns the port connection list rules.
  EXPECT_TRUE(ReportedError(r.diags,
                            ".* port connection shall appear at most once in a "
                            "port connection list",
                            2, "23.3.2"));
}

// §A.10 item 15: a package import statement may not appear directly within a
// class scope.
TEST(BnfClarificationParsing, ErrorImportInClassScope) {
  auto r = Parse(
      "class c;\n"
      "  import p::*;\n"
      "endclass\n");
  // §26.3 owns the package import declaration and its placement rule.
  EXPECT_TRUE(ReportedError(
      r.diags, "package import declaration is not allowed in class scope", 2,
      "26.3"));
}

// §A.10 item 27: a DPI import prototype's formal arguments may not use the
// `ref` pass-by-reference mode.
TEST(BnfClarificationParsing, ErrorRefFormalInDpiImport) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" function void f(ref int x);\n"
      "endmodule\n");
  // §35.5.4 owns the DPI import declaration rules; the report stands at the
  // declaration's own location, the "DPI-C" spec string.
  EXPECT_TRUE(ReportedError(
      r.diags, "ref qualifier cannot be used in a DPI import declaration", 2,
      "35.5.4"));
}

}  // namespace
