#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <utility>

#include "fixture_parser.h"
#include "helpers_generate_forms.h"
#include "helpers_reported_error.h"
#include "parser/ast_covergroup.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"

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

std::string WildcardTwiceIn(const std::string& instance) {
  return "interface ifc(input logic clk); endinterface\n"
         "program p(input logic clk); endprogram\n"
         "module m(input logic clk); endmodule\n"
         "module t;\n"
         "  logic clk;\n" +
         instance + "\nendmodule\n";
}

TEST(BnfClarificationParsing, WildcardTwiceInAnInterfaceOrProgramInstance) {
  for (const char* instance : {"  ifc i0(.*, .*);", "  p p0(.*, .*);"}) {
    auto r = Parse(WildcardTwiceIn(instance));
    EXPECT_TRUE(ReportedError(
        r.diags, ".* already appears earlier in this port connection list", 6,
        "23.3.2"))
        << instance;
  }
}

TEST(BnfClarificationParsing, WildcardOnceInAnInterfaceOrProgramInstance) {
  for (const char* instance : {"  ifc i0(.*);", "  p p0(.*);"}) {
    EXPECT_TRUE(ParseOk(WildcardTwiceIn(instance))) << instance;
  }
}

TEST(BnfClarificationParsing, WildcardTwiceInABindInstantiation) {
  auto r = Parse(
      "module m(input logic clk); endmodule\n"
      "module t; logic clk; endmodule\n"
      "bind t m b0(.*, .*);\n");
  EXPECT_TRUE(ReportedError(
      r.diags, ".* already appears earlier in this port connection list", 3,
      "23.3.2"));
}

TEST(BnfClarificationParsing, WildcardOnceInABindInstantiation) {
  EXPECT_TRUE(
      ParseOk("module m(input logic clk); endmodule\n"
              "module t; logic clk; endmodule\n"
              "bind t m b0(.*);\n"));
}

TEST(GenerateItemSetParsing, AnExternPrototypeInAModuleGenerateIsReported) {
  for (const char* form : {"if", "case"}) {
    auto r = Parse("module m;\n" + InGenerateForm(form, "extern task t();") +
                   "endmodule\n");
    EXPECT_TRUE(
        ReportedError(r.diags,
                      "an extern task or function prototype is an item of an "
                      "interface",
                      3, "A.1.6"))
        << form;
  }
}

TEST(GenerateItemSetParsing, AnExternPrototypeInAnInterfaceGenerateIsAccepted) {
  for (const char* form : {"if", "case"}) {
    EXPECT_TRUE(ParseOk("interface m;\n" +
                        InGenerateForm(form, "extern task t();") +
                        "endinterface\n"))
        << form;
  }
}

TEST(GenerateItemSetParsing, AGateInAnInterfaceNestedInAModuleIsReported) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, c;\n"
      "  interface ii;\n"
      "    if (1) begin\n"
      "      and g(a, b, c);\n"
      "    end\n"
      "  endinterface\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a gate instantiation is not an item of an interface", 5,
      "A.1.6"));
}

TEST(GenerateItemSetParsing, AGateInTheGenerateOfTheEnclosingModuleIsAccepted) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a, b, c;\n"
              "  interface ii;\n"
              "  endinterface\n"
              "  if (1) begin\n"
              "    and g(a, b, c);\n"
              "  end\n"
              "endmodule\n"));
}

std::string InCheckerGenerate(const std::string& form,
                              const std::string& item) {
  return "checker c(logic a, logic b, logic x);\n" +
         InGenerateForm(form, item) + "endchecker\n";
}

TEST(GenerateItemSetParsing, AnExternPrototypeOrGateInACheckerGenerate) {
  for (const char* form : kGenerateForms) {
    auto r = Parse(InCheckerGenerate(form, "extern task t();"));
    EXPECT_TRUE(
        ReportedError(r.diags,
                      "an extern task or function prototype is an item of an "
                      "interface",
                      3, "A.1.6"))
        << form;
    r = Parse(InCheckerGenerate(form, "and g(a, b, x);"));
    EXPECT_TRUE(ReportedError(r.diags,
                              "a gate instantiation is not an item of a "
                              "checker",
                              3, "A.1.8"))
        << form;
  }
}

TEST(GenerateItemSetParsing, ACheckerVariableInACheckerGenerateIsAccepted) {
  for (const char* form : kGenerateForms) {
    EXPECT_TRUE(ParseOk(InCheckerGenerate(form, "logic w;"))) << form;
  }
}

TEST(BnfClarificationParsing, DefaultOnceInConstructorArgsOk) {
  EXPECT_TRUE(
      ParseOk("class B; function new(int a); endfunction endclass\n"
              "class C extends B;\n"
              "  function new(default, int x);\n"
              "    super.new(default);\n"
              "  endfunction\n"
              "endclass\n"));
}

TEST(BnfClarificationParsing, ErrorDuplicateDefaultInExternConstructor) {
  auto r = Parse(
      "class B; function new(int a); endfunction endclass\n"
      "class C extends B;\n"
      "  extern function new(default, int x, default);\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "'default' already appears earlier in this class "
                            "constructor argument list",
                            3, "8.17"));
}

TEST(BnfClarificationParsing, ErrorDuplicateDefaultInOutOfBlockConstructor) {
  auto r = Parse(
      "class B; function new(int a); endfunction endclass\n"
      "class C extends B;\n"
      "  extern function new(default, int x);\n"
      "endclass\n"
      "function C::new(default, int x, default);\n"
      "  super.new(default);\n"
      "endfunction\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "'default' already appears earlier in this class "
                            "constructor argument list",
                            5, "8.17"));
}

TEST(BnfClarificationParsing, ErrorImportInEveryKindOfClassScope) {
  const std::string kPkg = "package p; int x = 4; endpackage\n";
  for (const std::string& body :
       {std::string("module m;\n  class c;\n    import p::x;\n  endclass\n"
                    "endmodule\n"),
        std::string("package q;\n  class c;\n    import p::*;\n  endclass\n"
                    "endpackage\n"),
        std::string("program g;\n  class c;\n    import p::*;\n  endclass\n"
                    "endprogram\n"),
        std::string("interface i;\n  class c;\n    import p::x;\n  endclass\n"
                    "endinterface\n"),
        std::string("class o;\n  class c;\n    import p::x;\n  endclass\n"
                    "endclass\n"),
        std::string("interface class ic;\n\n  import p::*;\nendclass\n")}) {
    SCOPED_TRACE(body);
    auto r = Parse(kPkg + body);
    EXPECT_TRUE(ReportedError(
        r.diags, "package import declaration is not allowed in class scope", 4,
        "26.3"));
  }
}

TEST(BnfClarificationParsing, ImportInAClassMethodOk) {
  EXPECT_TRUE(
      ParseOk("package p; int x = 4; endpackage\n"
              "class c;\n"
              "  function int f(); import p::x; return x; endfunction\n"
              "  task t(); import p::*; endtask\n"
              "endclass\n"));
}

TEST(BnfClarificationParsing, ErrorWhiteSpaceInsideANumber) {
  struct Case {
    const char* decl;
    const char* message;
    const char* subclause;
  };
  const Case kCases[] = {
      {"logic [7:0] a = 8' sh9;",
       "the apostrophe, any 's', and the base format character of a based "
       "number must be written together without white space",
       "5.7.1"},
      {"logic [7:0] a = 8'hF F;", "expected ';', got identifier", "6.8"},
      {"real r = 1. 5;",
       "real literal '1.' has no digit after its decimal "
       "point",
       "5.7.2"},
      {"real r = 1.5 e3;", "expected ';', got identifier", "6.8"},
      {"real r = 1.5e 3;", "expected ';', got identifier", "6.8"},
  };
  for (const Case& c : kCases) {
    SCOPED_TRACE(c.decl);
    auto r = Parse(std::string("module m;\n  ") + c.decl + "\nendmodule\n");
    EXPECT_TRUE(ReportedError(r.diags, c.message, 2, c.subclause));
  }
}

TEST(BnfClarificationParsing, NumbersWithoutWhiteSpaceOk) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic [7:0] a = 8'sh9;\n"
              "  logic [7:0] b = 8'hFF;\n"
              "  real r = 1.5;\n"
              "  real s = 1.5e3;\n"
              "endmodule\n"));
}

TEST(BnfClarificationParsing, DISABLED_TwoUnsizedPackedDimsOnADpiImportFormal) {
  for (const char* kind : {"function void f", "task t"}) {
    SCOPED_TRACE(kind);
    auto r = Parse(std::string("module m;\n  import \"DPI-C\" ") + kind +
                   "(input bit [] [] a);\nendmodule\n");
    EXPECT_TRUE(ReportedError(r.diags,
                              "a packed dimension left unspecified must be "
                              "the only packed dimension of the argument",
                              2, "35.5.6.1"));
  }
}

TEST(BnfClarificationParsing, ErrorSizedBesideUnsizedOnADpiImportTask) {
  for (const char* formal : {"input bit [7:0] [] a", "input bit [] [7:0] a"}) {
    SCOPED_TRACE(formal);
    auto r = Parse(std::string("module m;\n  import \"DPI-C\" task t(") +
                   formal + ");\nendmodule\n");
    EXPECT_TRUE(ReportedError(r.diags,
                              "a packed dimension left unspecified must be "
                              "the only packed dimension of the argument",
                              2, "35.5.6.1"));
  }
}

TEST(BnfClarificationParsing, UnsizedPackedDimAloneOnADpiImportTaskOk) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  import \"DPI-C\" task t(input bit [] a, logic [] b [3:1]);\n"
              "endmodule\n"));
}

TEST(BnfClarificationParsing, ErrorUnsizedPackedDimOutsideADpiImportFormal) {
  for (const char* item :
       {"function void f(input bit [] a); endfunction",
        "task t(input bit [] a); endtask", "typedef bit [] t;",
        "typedef struct packed { bit [] a; } s;", "wire [] w;",
        "parameter bit [] P = 0;"}) {
    SCOPED_TRACE(item);
    auto r = Parse(std::string("module m;\n  ") + item + "\nendmodule\n");
    EXPECT_TRUE(ReportedError(r.diags, "expected expression", 2, "11.2"));
  }
  auto exported = Parse(
      "module m;\n"
      "  export \"DPI-C\" function f;\n"
      "  function void f(input bit [] a); endfunction\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(exported.diags, "expected expression", 3, "11.2"));
  auto port = Parse("module m(input bit [] p);\nendmodule\n");
  EXPECT_TRUE(ReportedError(port.diags, "expected expression", 1, "11.2"));
}

TEST(BnfClarificationParsing, ErrorRefAndConstRefFormalsInDpiImports) {
  for (const char* proto :
       {"task t(ref int x)", "function void f(const ref int x)",
        "task t(const ref int x)"}) {
    SCOPED_TRACE(proto);
    auto r = Parse(std::string("module m;\n  import \"DPI-C\" ") + proto +
                   ";\nendmodule\n");
    EXPECT_TRUE(ReportedError(
        r.diags, "ref qualifier cannot be used in a DPI import declaration", 2,
        "35.5.4"));
  }
}

TEST(BnfClarificationParsing, DirectionFormalsInDpiImportsOk) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  import \"DPI-C\" task t(input int x, inout int y);\n"
              "  import \"DPI-C\" function void f(output int x);\n"
              "endmodule\n"));
}

TEST(BnfClarificationParsing, ErrorParameterWithoutValueOutsideAPortList) {
  for (const char* src :
       {"package p; parameter int K; endpackage\n", "parameter int K;\n",
        "class c; parameter int A; endclass\n"}) {
    SCOPED_TRACE(src);
    auto r = Parse(src);
    EXPECT_TRUE(ReportedError(r.diags,
                              "parameter declaration requires a default value",
                              1, "6.20.1"));
  }
  for (const char* src :
       {"package p; parameter type T; endpackage\n", "parameter type T;\n",
        "class c; parameter type T; endclass\n"}) {
    SCOPED_TRACE(src);
    auto r = Parse(src);
    EXPECT_TRUE(ReportedError(
        r.diags,
        "type parameter 'T' outside a parameter port list must have a default "
        "type",
        1, "6.20.1"));
  }
}

TEST(BnfClarificationParsing, ParameterWithValueOutsideAPortListOk) {
  EXPECT_TRUE(
      ParseOk("parameter int K = 1;\n"
              "parameter type U = int;\n"
              "package p; parameter int K = 1; parameter type T = int; "
              "endpackage\n"
              "class c; parameter int A = 1; parameter type T = int; "
              "endclass\n"));
}

std::string PortListHeader(const std::string& head, const char* item,
                           const std::string& end) {
  std::string src = head;
  src += item;
  src += "); ";
  src += end;
  src += "\n";
  return src;
}

TEST(BnfClarificationParsing, ErrorPortListLocalparamWithoutValue) {
  const std::pair<std::string, std::string> kHeads[] = {
      {"interface ifc #(parameter int W = 1, ", "endinterface"},
      {"program prg #(parameter int W = 1, ", "endprogram"},
      {"class C #(int W = 1, ", "endclass"}};
  for (const auto& [head, end] : kHeads) {
    SCOPED_TRACE(head);
    auto value = Parse(PortListHeader(head, "localparam int L", end));
    EXPECT_TRUE(ReportedError(
        value.diags,
        "localparam 'L' in parameter port list must have a default value", 1,
        "6.20.1"));
    auto type = Parse(PortListHeader(head, "localparam type T", end));
    EXPECT_TRUE(ReportedError(
        type.diags,
        "localparam type 'T' in parameter port list must have a default type",
        1, "6.20.1"));
  }
}

TEST(BnfClarificationParsing, PortListLocalparamWithValueOk) {
  EXPECT_TRUE(
      ParseOk("interface ifc #(parameter int W, localparam int L = 2);\n"
              "endinterface\n"
              "program prg #(parameter int W, localparam int L = 2);\n"
              "endprogram\n"
              "class C #(int W = 1, localparam int L = 2);\n"
              "endclass\n"));
}

TEST(BnfClarificationParsing, ErrorUnsizedPackedDimOnAPackedUnionMember) {
  auto r = Parse(
      "module m;\n"
      "  typedef union packed { bit [] a; bit [7:0] b; } u;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected expression", 2, "11.2"));
}

const SelectExpression* OnlyCrossBinSelect(const ParseResult& r) {
  for (const ModuleItem* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kCovergroupDecl) continue;
    return item->covergroup->items[2].cover_cross->body[0].bins.select;
  }
  return nullptr;
}

TEST(BnfClarificationParsing, CrossSelectMatchesBindsTighterThanAndOr) {
  struct Case {
    const char* select;
    SelectExpressionKind op;
    bool matches_on_left;
    SelectExpressionKind counted;
    bool dollar;
  };
  constexpr Case kCases[] = {
      {"X with (a < b) matches 2 || binsof(a) intersect {3}",
       SelectExpressionKind::kOr, true, SelectExpressionKind::kWith, false},
      {"X with (a < b) matches 2 && binsof(a) intersect {3}",
       SelectExpressionKind::kAnd, true, SelectExpressionKind::kWith, false},
      {"binsof(a) intersect {3} || X with (a < b) matches 2",
       SelectExpressionKind::kOr, false, SelectExpressionKind::kWith, false},
      {"binsof(a) intersect {3} && X with (a < b) matches 2",
       SelectExpressionKind::kAnd, false, SelectExpressionKind::kWith, false},
      {"cs matches 2 || binsof(a) intersect {3}", SelectExpressionKind::kOr,
       true, SelectExpressionKind::kCrossSet, false},
      {"cs matches 2 && binsof(a) intersect {3}", SelectExpressionKind::kAnd,
       true, SelectExpressionKind::kCrossSet, false},
      {"X with (a < b) matches $ || binsof(a) intersect {3}",
       SelectExpressionKind::kOr, true, SelectExpressionKind::kWith, true},
      {"cs matches $ && binsof(a) intersect {3}", SelectExpressionKind::kAnd,
       true, SelectExpressionKind::kCrossSet, true},
  };
  for (const auto& c : kCases) {
    std::string src =
        "module m;\n"
        "  logic [3:0] a, b;\n"
        "  covergroup cg;\n"
        "    coverpoint a;\n"
        "    coverpoint b;\n"
        "    X: cross a, b {\n"
        "      bins s = ";
    src += c.select;
    src +=
        ";\n"
        "    }\n"
        "  endgroup\n"
        "endmodule\n";
    auto r = Parse(src);
    ASSERT_FALSE(r.has_errors) << c.select;
    const SelectExpression* top = OnlyCrossBinSelect(r);
    ASSERT_NE(top, nullptr) << c.select;
    ASSERT_EQ(top->kind, c.op) << c.select;
    const SelectExpression* counted = c.matches_on_left ? top->lhs : top->rhs;
    const SelectExpression* other = c.matches_on_left ? top->rhs : top->lhs;
    EXPECT_EQ(counted->kind, c.counted) << c.select;
    if (c.dollar) {
      EXPECT_TRUE(counted->matches_dollar) << c.select;
    } else {
      ASSERT_NE(counted->matches, nullptr) << c.select;
      EXPECT_EQ(counted->matches->kind, ExprKind::kIntegerLiteral) << c.select;
    }
    EXPECT_EQ(other->kind, SelectExpressionKind::kBinsOf) << c.select;
    EXPECT_EQ(other->matches, nullptr) << c.select;
    EXPECT_FALSE(other->matches_dollar) << c.select;
  }
}

std::string DeclaredInEveryCheckerGenerateForm(const char* keyword,
                                               const char* end) {
  constexpr const char* kForms[] = {
      "  if (1) begin : g1\n    @\n  end else begin : g2\n    @\n  end\n",
      "  for (genvar i = 0; i < 1; i++) begin : g3\n    @\n  end\n",
      "  case (1)\n    1: begin : g4\n      @\n    end\n  endcase\n",
      "  generate\n    @\n  endgenerate\n",
      "  if (1) @\n",
      "  for (genvar j = 0; j < 1; j++) @\n"};
  std::string src = "checker c;\n";
  int n = 0;
  for (const char* form : kForms) {
    for (const char* p = form; *p != '\0'; ++p) {
      if (*p != '@') {
        src += *p;
        continue;
      }
      src += keyword;
      src += " inner";
      src += std::to_string(++n);
      src += "; ";
      src += end;
    }
  }
  src += "endchecker\n";
  return src;
}

constexpr uint32_t kCheckerGenerateLines[] = {3, 5, 8, 12, 16, 18, 19};

TEST(BnfClarificationParsing,
     DISABLED_DesignElementInEveryCheckerGenerateFormRejected) {
  const std::pair<const char*, const char*> kElements[] = {
      {"module", "endmodule"},
      {"interface", "endinterface"},
      {"program", "endprogram"}};
  for (const auto& [keyword, end] : kElements) {
    auto r = Parse(DeclaredInEveryCheckerGenerateForm(keyword, end));
    for (uint32_t line : kCheckerGenerateLines) {
      EXPECT_TRUE(ReportedError(r.diags,
                                "a module, interface, or program cannot be "
                                "declared inside checker 'c'",
                                line, "17.2"))
          << keyword << " " << line;
    }
  }
}

TEST(BnfClarificationParsing,
     DISABLED_PackageInEveryCheckerGenerateFormRejected) {
  auto r = Parse(DeclaredInEveryCheckerGenerateForm("package", "endpackage"));
  for (uint32_t line : kCheckerGenerateLines) {
    EXPECT_TRUE(ReportedError(r.diags,
                              "a package cannot be declared inside checker 'c'",
                              line, "17.2"))
        << line;
  }
  EXPECT_FALSE(ReportedError(r.diags, "unexpected token", 3, "23.2.4"));
}

TEST(BnfClarificationParsing, CheckerInEveryCheckerGenerateFormAccepted) {
  auto r = Parse(DeclaredInEveryCheckerGenerateForm("checker", "endchecker"));
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
