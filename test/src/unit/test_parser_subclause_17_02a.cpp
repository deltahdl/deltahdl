#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

#include "common/diagnostic.h"
#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

TEST_F(CheckerParseTest, EmptyChecker) {
  auto* unit = Parse("checker my_check; endchecker");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_EQ(unit->checkers[0]->name, "my_check");
  EXPECT_EQ(unit->checkers[0]->decl_kind, ModuleDeclKind::kChecker);
  EXPECT_TRUE(unit->checkers[0]->ports.empty());
  EXPECT_TRUE(unit->checkers[0]->items.empty());
}

TEST_F(VerifyParseTest, CheckerWithPorts) {
  auto* unit = Parse(R"(
    checker port_check(input logic clk, input logic rst);
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_EQ(unit->checkers[0]->name, "port_check");
  EXPECT_GE(unit->checkers[0]->ports.size(), 2u);
}

TEST_F(VerifyParseTest, MultipleCheckers) {
  auto* unit = Parse(R"(
    checker c1;
    endchecker
    checker c2;
    endchecker
  )");
  EXPECT_EQ(unit->checkers.size(), 2u);
}

TEST_F(VerifyParseTest, CheckerCoexistsWithModule) {
  auto* unit = Parse(R"(
    module m;
    endmodule
    checker c;
    endchecker
  )");
  EXPECT_EQ(unit->modules.size(), 1u);
  EXPECT_EQ(unit->checkers.size(), 1u);
}

TEST(CheckerDeclaration, EndLabelMatchesCheckerName) {
  auto r = Parse("checker ck; endchecker : ck\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->name, "ck");
}

TEST(CheckerDeclaration, MissingEndcheckerIsError) {
  auto r = Parse("checker c;");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'endchecker', got EOF", 1, "17.2"));
}

TEST(CheckerDeclaration, EndLabelMismatchIsError) {
  auto r = Parse("checker ck; endchecker : other\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(r.diags, "end label 'other' does not match 'ck'", 1,
                            "9.3.4"));
}

TEST(CheckerDeclaration, OutputDirectionFormalParses) {
  auto r = Parse("checker chk(output bit a, input bit b); endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  ASSERT_GE(r.cu->checkers[0]->ports.size(), 2u);
  EXPECT_EQ(r.cu->checkers[0]->ports[0].direction, Direction::kOutput);
  EXPECT_EQ(r.cu->checkers[0]->ports[1].direction, Direction::kInput);
}

TEST(CheckerDeclaration, WithAssertion) {
  auto r = Parse(
      "checker chk(input logic clk, input logic req, input logic gnt);\n"
      "  assert property (@(posedge clk) req |-> ##[1:3] gnt);\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kAssertProperty));
}

TEST(CheckerDeclaration, WithModelingCode) {
  auto r = Parse(
      "checker chk;\n"
      "  logic flag;\n"
      "  initial flag = 0;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kVarDecl));
  EXPECT_TRUE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kInitialBlock));
}

TEST(CheckerDeclaration, FirstFormalOmittedDirectionDefaultsToInput) {
  auto r = Parse("checker chk(logic a, logic b); endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  ASSERT_GE(r.cu->checkers[0]->ports.size(), 2u);
  EXPECT_EQ(r.cu->checkers[0]->ports[0].direction, Direction::kInput);
  EXPECT_EQ(r.cu->checkers[0]->ports[1].direction, Direction::kInput);
}

TEST(CheckerDeclaration, OmittedDirectionInheritsExplicitOutput) {
  auto r = Parse("checker chk(output bit a, bit b); endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  ASSERT_GE(r.cu->checkers[0]->ports.size(), 2u);
  EXPECT_EQ(r.cu->checkers[0]->ports[0].direction, Direction::kOutput);
  EXPECT_EQ(r.cu->checkers[0]->ports[1].direction, Direction::kOutput);
}

TEST(CheckerDeclaration, WithMixedContents) {
  EXPECT_TRUE(
      ParseOk("checker chk(input logic clk, input logic a, input logic b);\n"
              "  logic internal;\n"
              "  always_comb internal = a & b;\n"
              "  assert property (@(posedge clk) a |-> b);\n"
              "  cover property (@(posedge clk) a && b);\n"
              "endchecker\n"));
}

static bool HasNestedChecker(const std::vector<ModuleItem*>& items) {
  for (const auto* item : items) {
    if (item->kind == ModuleItemKind::kNestedModuleDecl &&
        item->nested_module_decl &&
        item->nested_module_decl->decl_kind == ModuleDeclKind::kChecker) {
      return true;
    }
  }
  return false;
}

TEST(CheckerDeclaration, DeclaredInsideModule) {
  auto r = Parse(
      "module m;\n"
      "  checker c; endchecker\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasNestedChecker(r.cu->modules[0]->items));
}

TEST(CheckerDeclaration, DeclaredInsideInterface) {
  auto r = Parse(
      "interface ifc;\n"
      "  checker c; endchecker\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_TRUE(HasNestedChecker(r.cu->interfaces[0]->items));
}

TEST(CheckerDeclaration, DeclaredInsideProgram) {
  auto r = Parse(
      "program prog;\n"
      "  checker c; endchecker\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_TRUE(HasNestedChecker(r.cu->programs[0]->items));
}

TEST(CheckerDeclaration, DeclaredInsidePackage) {
  auto r = Parse(
      "package pkg;\n"
      "  checker c; endchecker\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_TRUE(HasNestedChecker(r.cu->packages[0]->items));
}

TEST(CheckerDeclaration, DeclaredInsideGenerateBlock) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  if (1) begin : g\n"
              "    checker c; endchecker\n"
              "  end\n"
              "endmodule\n"));
}

TEST(CheckerDeclaration, BodyAllowsClockingAndDisableContexts) {
  EXPECT_TRUE(
      ParseOk("checker c(input logic clk, input logic rst);\n"
              "  clocking cb @(posedge clk); endclocking\n"
              "  default clocking cb;\n"
              "  default disable iff (rst);\n"
              "  a1: assert property (@(posedge clk) 1'b1);\n"
              "endchecker\n"));
}

TEST(CheckerDeclaration, BodyAllowsProcedureForms) {
  EXPECT_TRUE(
      ParseOk("checker c(input logic clk, input logic en);\n"
              "  logic a, b;\n"
              "  always_ff @(posedge clk) a <= b;\n"
              "  always_latch if (en) b = a;\n"
              "  final begin end\n"
              "endchecker\n"));
}

TEST(CheckerDeclaration, BodyAllowsDeferredAndAssumeAssertions) {
  EXPECT_TRUE(
      ParseOk("checker c(input logic clk, input logic a, input logic b);\n"
              "  a1: assert #0 ($onehot0({a, b}));\n"
              "  a2: assume property (@(posedge clk) a);\n"
              "endchecker\n"));
}

TEST(CheckerDeclaration, BodyAllowsVerificationDeclarations) {
  EXPECT_TRUE(
      ParseOk("checker c(input logic clk, input logic a);\n"
              "  genvar i;\n"
              "  let g = a;\n"
              "  sequence s; @(posedge clk) a; endsequence\n"
              "  property p; @(posedge clk) a; endproperty\n"
              "  function bit f(bit x); return x; endfunction\n"
              "  covergroup cg @(posedge clk); cp: coverpoint a; endgroup\n"
              "  cg cg1 = new();\n"
              "endchecker\n"));
}

TEST(CheckerDeclaration, BodyAllowsGenerateBlock) {
  EXPECT_TRUE(
      ParseOk("checker c(input logic a);\n"
              "  if (1) begin : g\n"
              "    logic x;\n"
              "    always_comb x = a;\n"
              "  end\n"
              "endchecker\n"));
}

TEST(CheckerDeclaration, BodyAllowsNestedCheckerInstantiation) {
  EXPECT_TRUE(
      ParseOk("checker inner(input logic x); endchecker\n"
              "checker outer(input logic clk);\n"
              "  inner i1(clk);\n"
              "endchecker\n"));
}

TEST(CheckerDeclaration, InputPortDefaultValueParses) {
  auto r = Parse("checker c(input logic a = 1'b1); endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  ASSERT_GE(r.cu->checkers[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->ports[0].direction, Direction::kInput);
  EXPECT_NE(r.cu->checkers[0]->ports[0].default_value, nullptr);
}

TEST(CheckerDeclaration, UntypedOutputFormalIsError) {
  auto r = Parse("checker c(output a); endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(r.diags,
                            "checker formal 'a' has an explicit direction, so "
                            "its type shall not be omitted",
                            1, "17.2"));
}

TEST(CheckerDeclaration, DirectedInputFormalWithoutTypeIsError) {
  auto r = Parse("checker c(input logic clk, input a); endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(r.diags,
                            "checker formal 'a' has an explicit direction, so "
                            "its type shall not be omitted",
                            1, "17.2"));
}

TEST(CheckerDeclaration, DirectedFormalWithImplicitTypeIsAccepted) {
  auto r = Parse("checker c(input [3:0] a, output signed b); endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(CheckerDeclaration, FirstFormalWithoutTypeIsInputUntyped) {
  auto r = Parse("checker c(a, b); endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  ASSERT_EQ(r.cu->checkers[0]->ports.size(), 2u);
  EXPECT_FALSE(r.cu->checkers[0]->is_non_ansi_ports);
  EXPECT_EQ(r.cu->checkers[0]->ports[0].direction, Direction::kInput);
  EXPECT_EQ(r.cu->checkers[0]->ports[0].formal_type,
            PropertyFormalType::kUntyped);
  EXPECT_EQ(r.cu->checkers[0]->ports[1].name, "b");
  EXPECT_EQ(r.cu->checkers[0]->ports[1].direction, Direction::kInput);
  EXPECT_EQ(r.cu->checkers[0]->ports[1].formal_type,
            PropertyFormalType::kUntyped);
}

TEST(CheckerDeclaration, OutputFormalOfKeywordTypeIsError) {
  auto r = Parse(
      "checker c(output sequence s, input bit x, untyped u, property p, "
      "output q);\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(r.diags,
                            "checker output formal 's' is declared 'sequence', "
                            "a type only an input formal can take",
                            1, "17.2"));
  EXPECT_FALSE(ReportedError(r.diags, "checker output formal 'u' is declared",
                             1, "17.2"));
  EXPECT_FALSE(ReportedError(r.diags, "checker output formal 'p' is declared",
                             1, "17.2"));
  EXPECT_TRUE(ReportedError(r.diags,
                            "checker formal 'q' has an explicit direction, so "
                            "its type shall not be omitted",
                            1, "17.2"));
}

TEST(CheckerDeclaration, OutputFormalInheritingDirectionOfKeywordTypeIsError) {
  auto r = Parse("checker c(output bit x, untyped u); endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(r.diags,
                            "checker output formal 'u' is declared 'untyped', "
                            "a type only an input formal can take",
                            1, "17.2"));
}

TEST(CheckerDeclaration, TypedOutputFormalIsAccepted) {
  auto r = Parse("checker c(output bit a); endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  ASSERT_GE(r.cu->checkers[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->ports[0].direction, Direction::kOutput);
}

TEST(CheckerDeclaration, OutputPortInitialValueParses) {
  auto r = Parse("checker c(output int ctr = 0); endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  ASSERT_GE(r.cu->checkers[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->ports[0].direction, Direction::kOutput);
  EXPECT_NE(r.cu->checkers[0]->ports[0].default_value, nullptr);
}

TEST(CheckerDeclaration, InoutOrRefFormalIsError) {
  auto r = Parse(
      "checker c(input logic a, inout logic b,\n"
      "          output bit o, ref logic d);\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(r.diags,
                            "checker formal 'b' is declared 'inout'; a "
                            "checker formal's direction is input or output",
                            1, "17.2"));
  EXPECT_TRUE(ReportedError(r.diags,
                            "checker formal 'd' is declared 'ref'; a "
                            "checker formal's direction is input or output",
                            2, "17.2"));
  EXPECT_FALSE(
      ReportedError(r.diags, "checker formal 'a' is declared", 1, "17.2"));
  EXPECT_FALSE(
      ReportedError(r.diags, "checker formal 'o' is declared", 2, "17.2"));
}

TEST(CheckerDeclaration, FormalInheritingInoutIsNotReportedAgain) {
  auto r = Parse("checker c(inout logic a, logic b); endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(r.diags, "checker formal 'a' is declared 'inout'",
                            1, "17.2"));
  EXPECT_FALSE(ReportedError(r.diags, "checker formal 'b' is declared 'inout'",
                             1, "17.2"));
}

TEST(CheckerDeclaration, NetOrVarFormalIsError) {
  auto r = Parse(
      "checker c(input wire a, input tri logic b,\n"
      "          input var logic v, input logic d);\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(r.diags,
                            "checker formal 'a' is declared as a net; its type "
                            "shall be one a property formal can take",
                            1, "17.2"));
  EXPECT_TRUE(ReportedError(r.diags, "checker formal 'b' is declared as a net",
                            1, "17.2"));
  EXPECT_TRUE(ReportedError(r.diags,
                            "checker formal 'v' is declared with 'var'; its "
                            "type shall be one a property formal can take",
                            2, "17.2"));
  EXPECT_FALSE(
      ReportedError(r.diags, "checker formal 'd' is declared", 2, "17.2"));
}

TEST(CheckerDeclaration, InterfacePortFormalIsError) {
  auto r = Parse(
      "interface ifc; logic s; modport mp(input s); endinterface\n"
      "checker c(interface i,\n"
      "          interface.mp j,\n"
      "          ifc.mp k);\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  struct Formal {
    const char* name;
    uint32_t line;
  };
  for (const Formal& formal :
       {Formal{"i", 2}, Formal{"j", 3}, Formal{"k", 4}}) {
    EXPECT_TRUE(ReportedError(r.diags,
                              std::string("checker formal '") + formal.name +
                                  "' is declared as an interface port; its "
                                  "type shall be one a property formal can "
                                  "take",
                              formal.line, "17.2"));
  }
}

TEST(CheckerDeclaration, FormalOfAnUnseenTypeNameIsNotAnInterfacePort) {
  auto r = Parse("checker c(T x); endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(
      ReportedError(r.diags, "is declared as an interface port", 1, "17.2"));
}

TEST(CheckerDeclaration, ModulePortsOfTheseKindsAreNotReported) {
  auto r = Parse(
      "interface ifc; endinterface\n"
      "module m(interface i, inout wire a, ref logic d, input var logic v);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

size_t ParseErrorCount(const std::vector<Diagnostic>& diags) {
  size_t n = 0;
  for (const auto& diag : diags) {
    if (diag.severity == DiagSeverity::kError) ++n;
  }
  return n;
}

TEST(CheckerClosing, ACheckerInACheckersGenerateBlockIsAccepted) {
  auto r = Parse(
      "checker o;\n"
      "  if (1) begin : g\n"
      "    checker c; endchecker\n"
      "  end\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(CheckerClosing, DISABLED_AnotherEndKeywordDoesNotCloseACheckerInTheUnit) {
  auto r = Parse("checker c;\nendmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected 'endchecker', got 'endmodule'",
                            2, "17.2"));
}

TEST(CheckerClosing, DISABLED_AContainersEndKeywordDoesNotCloseItsChecker) {
  const char* const kContainers[][2] = {{"module m;", "endmodule"},
                                        {"interface ifc;", "endinterface"},
                                        {"program prog;", "endprogram"},
                                        {"package pkg;", "endpackage"}};
  for (const auto& container : kContainers) {
    auto r = Parse(std::string(container[0]) + "\n  checker c;\n" +
                   container[1] + "\n");
    EXPECT_TRUE(ReportedError(
        r.diags,
        std::string("expected 'endchecker', got '") + container[1] + "'", 3,
        "17.2"))
        << container[0];
  }
}

TEST(CheckerClosing, DISABLED_AGenerateBlocksEndDoesNotCloseItsChecker) {
  auto r = Parse(
      "module m;\n"
      "  if (1) begin : g\n"
      "    checker c;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'endchecker', got 'end'", 4, "17.2"));
}

TEST(CheckerClosing, AnOuterCheckerLeftOpenIsReported) {
  auto r = Parse("checker outer;\n  checker inner; endchecker\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'endchecker', got EOF", 3, "17.2"));
}

TEST(CheckerClosing, AnEndcheckerWithNoCheckerOpenIsReported) {
  auto unit = Parse("endchecker\n");
  EXPECT_TRUE(
      ReportedError(unit.diags, "expected top-level declaration", 1, "3.12.1"));
  auto in_module = Parse("module m;\n  endchecker\nendmodule\n");
  EXPECT_TRUE(ReportedError(in_module.diags, "unexpected token in module body",
                            2, "23.2.4"));
}

const char* const kMisplacedCheckerBody = "    checker c; endchecker\n";

struct MisplacedChecker {
  const char* place;
  const char* open;
  const char* close;
};

const MisplacedChecker kMisplacedCheckers[] = {
    {"a class", "  class k;\n", "  endclass\n"},
    {"a function", "  function void f();\n", "  endfunction\n"},
    {"a task", "  task t();\n", "  endtask\n"},
    {"a procedure", "  initial begin\n", "  end\n"},
    {"a procedure", "  always begin\n", "  end\n"},
    {"a procedure", "  initial begin\n    begin\n", "    end\n  end\n"},
    {"a procedure", "  initial begin\n    fork\n", "    join\n  end\n"},
};

TEST(CheckerPlacement, DISABLED_ACheckerOutsideTheAllowedPlacesIsReported) {
  for (const auto& misplaced : kMisplacedCheckers) {
    std::string src = std::string("module m;\n") + misplaced.open +
                      kMisplacedCheckerBody + misplaced.close + "endmodule\n";
    auto r = Parse(src);
    EXPECT_TRUE(ReportedError(
        r.diags,
        std::string("checker 'c' may not be declared in ") + misplaced.place,
        LineHolding(src, "checker c;"), "17.2"))
        << src;
    EXPECT_EQ(ParseErrorCount(r.diags), 1u) << src;
  }
}

TEST(CheckerPlacement, TheSameCheckerInTheEnclosingModuleIsAccepted) {
  auto r = Parse(std::string("module m;\n") + kMisplacedCheckerBody +
                 "  initial begin end\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

const char* const kAttributedCheckerItems[] = {
    "logic v;",
    "rand bit r;",
    "function automatic bit f(); return 1; endfunction",
    "checker inner; endchecker",
    "inner u_inner();",
    "a1: assert property (@(posedge clk) a);",
    "m1: assume property (@(posedge clk) a);",
    "c1: cover property (@(posedge clk) a);",
    "c2: cover sequence (@(posedge clk) a);",
    "r1: restrict property (@(posedge clk) a);",
    "d1: assert #0 (a);",
    "d2: assert final (a);",
    "let l = a;",
    "sequence s; a; endsequence",
    "property p; a; endproperty",
    "covergroup cg @(posedge clk); coverpoint a; endgroup",
    "cg cg_inst = new();",
    "genvar gv;",
    "clocking cb @(posedge clk); endclocking",
    "default clocking cb;",
    "default disable iff (a);",
    "initial a3: assert property (@(posedge clk) a);",
    "always_comb begin end",
    "always_latch begin end",
    "always_ff @(posedge clk) begin end",
    "final begin end",
    "assign v = a;",
    "if (1) begin : gi bit gx; end else begin : ge bit gy; end",
    "for (genvar i = 0; i < 2; i++) begin : gf bit gz; end",
    "case (1) 1: begin : gc bit gw; end endcase",
    "generate bit gr; endgenerate",
    "$info(\"i\");",
    "$warning(\"w\");",
    "$error(\"e\");",
    "$fatal(0, \"f\");",
};

std::string CheckerHolding(const std::string& items) {
  return "checker inner; endchecker\n"
         "checker c(input logic clk, input logic a);\n" +
         items + "endchecker\n";
}

TEST(CheckerItemAttributes, EachCheckerBodyItemTakesAnAttribute) {
  for (const char* item : kAttributedCheckerItems) {
    std::string src = CheckerHolding(std::string("  (* k *) ") + item + "\n");
    auto r = Parse(src);
    ASSERT_NE(r.cu, nullptr) << item;
    EXPECT_EQ(ParseErrorCount(r.diags), 0u) << item;
  }
}

TEST(CheckerItemAttributes, DISABLED_TheNullItemTakesAnAttribute) {
  auto r = Parse(CheckerHolding("  (* k *) ;\n"));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(CheckerItemAttributes, AnAttributeLeavesTheItemAsWritten) {
  auto bare = Parse(CheckerHolding("  logic v;\n  assign v = a;\n"));
  auto attributed =
      Parse(CheckerHolding("  (* k *) logic v;\n  (* k *) assign v = a;\n"));
  ASSERT_NE(bare.cu, nullptr);
  ASSERT_NE(attributed.cu, nullptr);
  ASSERT_EQ(bare.cu->checkers.size(), attributed.cu->checkers.size());
  const auto& bare_items = bare.cu->checkers.back()->items;
  const auto& attributed_items = attributed.cu->checkers.back()->items;
  ASSERT_EQ(bare_items.size(), attributed_items.size());
  for (size_t i = 0; i < bare_items.size(); ++i) {
    EXPECT_EQ(bare_items[i]->kind, attributed_items[i]->kind);
    EXPECT_EQ(bare_items[i]->name, attributed_items[i]->name);
  }
}

TEST(CheckerItemAttributes, SeveralAttributesOnOneItemAreAccepted) {
  auto r =
      Parse(CheckerHolding("  (* k *) (* m = 1 *) logic v;\n"
                           "  (* k, m = 1 *) logic w;\n"));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

const char* const kCheckerGenerateOpens[][2] = {
    {"  if (1) begin : g\n", "  end\n"},
    {"  if (1)\n", ""},
    {"  for (genvar i = 0; i < 2; i++) begin : g\n", "  end\n"},
    {"  case (1) 1: begin : g\n", "  end endcase\n"},
    {"  generate\n", "  endgenerate\n"},
};

const char* const kAttributeInGenerateReport =
    "an item in a checker's generate block takes no attribute instance";

TEST(CheckerItemAttributes, DISABLED_AnItemInACheckersGenerateBlockTakesNone) {
  for (const auto& block : kCheckerGenerateOpens) {
    std::string src = CheckerHolding(std::string(block[0]) +
                                     "    (* k *) bit w;\n" + block[1]);
    auto r = Parse(src);
    EXPECT_TRUE(ReportedError(r.diags, kAttributeInGenerateReport,
                              LineHolding(src, "(* k *)"), "A.4.2"))
        << src;
  }
}

TEST(CheckerItemAttributes, TheSameItemsWithoutAttributesAreAccepted) {
  for (const auto& block : kCheckerGenerateOpens) {
    std::string src =
        CheckerHolding(std::string(block[0]) + "    bit w;\n" + block[1]);
    auto r = Parse(src);
    ASSERT_NE(r.cu, nullptr);
    EXPECT_EQ(ParseErrorCount(r.diags), 0u) << src;
  }
}

TEST(CheckerItemAttributes,
     DISABLED_AnAttributedNullItemInACheckersGenerateBlock) {
  std::string src =
      CheckerHolding("  if (1) begin : g\n    (* k *) ;\n  end\n");
  auto r = Parse(src);
  EXPECT_TRUE(ReportedError(r.diags, kAttributeInGenerateReport,
                            LineHolding(src, "(* k *)"), "A.4.2"));
}

TEST(CheckerItemAttributes, DISABLED_ABareNullItemInACheckersGenerateBlock) {
  auto r = Parse(CheckerHolding("  if (1) begin : g\n    ;\n  end\n"));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(ParseErrorCount(r.diags), 0u);
}

TEST(CheckerItemAttributes, AModulesGenerateItemTakesAnAttribute) {
  auto r = Parse(
      "module m;\n"
      "  if (1) begin : g\n"
      "    (* k *) logic w;\n"
      "  end\n"
      "  for (genvar i = 0; i < 2; i++) begin : f (* k *) logic v; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
