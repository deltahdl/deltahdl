#include <gtest/gtest.h>

#include <vector>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

const std::vector<ModuleItem*>& ProgItems(ParseResult& r) {
  static const std::vector<ModuleItem*> kEmpty;
  if (!r.cu || r.cu->programs.empty()) return kEmpty;
  return r.cu->programs[0]->items;
}

TEST(ProgramItem, NonAnsiPortDeclaration) {
  auto r = Parse(
      "program p(a);\n"
      "  input a;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  ASSERT_EQ(r.cu->programs[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->ports[0].name, "a");
  EXPECT_EQ(r.cu->programs[0]->ports[0].direction, Direction::kInput);
}

TEST(ProgramItem, NonAnsiPortDeclarationMissingSemicolonIsError) {
  auto r = Parse(
      "program p(a);\n"
      "  input a\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got 'endprogram'", 3, "23.2.2.1"));
}

TEST(ProgramItem, PortDeclarationAndNonPortItemsCoexist) {
  auto r = Parse(
      "program p(a);\n"
      "  input a;\n"
      "  wire w;\n"
      "  assign w = a;\n"
      "  initial x = 0;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  ASSERT_EQ(r.cu->programs[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->ports[0].direction, Direction::kInput);
  EXPECT_TRUE(HasItemOfKind(ProgItems(r), ModuleItemKind::kContAssign));
  EXPECT_TRUE(HasItemOfKind(ProgItems(r), ModuleItemKind::kInitialBlock));
}

TEST(ProgramItem, WildcardHeaderBodyPortDeclaration) {
  auto r = Parse(
      "extern program p(a);\n"
      "program p(.*);\n"
      "  input a;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 2u);
  ASSERT_EQ(r.cu->programs[1]->ports.size(), 1u);
  EXPECT_EQ(r.cu->programs[1]->ports[0].name, "a");
  EXPECT_EQ(r.cu->programs[1]->ports[0].direction, Direction::kInput);
}

TEST(ProgramItem, AttributedNonAnsiPortDeclaration) {
  auto r = Parse(
      "program p(a);\n"
      "  (* keep *) input a;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  ASSERT_EQ(r.cu->programs[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->ports[0].direction, Direction::kInput);
  ASSERT_EQ(r.cu->programs[0]->ports[0].attrs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->ports[0].attrs[0].name, "keep");
}

TEST(NonPortProgramItem, ContinuousAssign) {
  auto r = Parse(
      "program p;\n"
      "  wire w;\n"
      "  assign w = a;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(ProgItems(r), ModuleItemKind::kContAssign));
}

TEST(NonPortProgramItem, ModuleOrGenerateItemDeclaration) {
  auto r = Parse(
      "program p;\n"
      "  localparam int W = 2;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(ProgItems(r), ModuleItemKind::kParamDecl));
}

TEST(NonPortProgramItem, InitialConstruct) {
  auto r = Parse(
      "program p;\n"
      "  initial x = 0;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(ProgItems(r), ModuleItemKind::kInitialBlock));
}

TEST(NonPortProgramItem, FinalConstruct) {
  auto r = Parse(
      "program p;\n"
      "  final x = 1;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(ProgItems(r), ModuleItemKind::kFinalBlock));
}

TEST(NonPortProgramItem, ConcurrentAssertionItem) {
  auto r = Parse(
      "program p;\n"
      "  assert property (@(posedge clk) a |-> b);\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(ProgItems(r), ModuleItemKind::kAssertProperty));
}

TEST(NonPortProgramItem, TimeunitsDeclaration) {
  auto r = Parse(
      "program p;\n"
      "  timeunit 1ns;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_TRUE(r.cu->programs[0]->has_timeunit);
}

TEST(NonPortProgramItem, TimeunitsAfterPortDeclarationRejected) {
  auto r = Parse(
      "program p(a);\n"
      "  input a;\n"
      "  timeunit 10ns;\n"
      "endprogram\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "timeunit as a later item requires a matching "
                            "prior declaration in the same time scope",
                            3, "3.14.2.2"));
}

TEST(NonPortProgramItem, TimeunitsBeforePortDeclarationAccepted) {
  auto r = Parse(
      "program p(a);\n"
      "  timeunit 10ns;\n"
      "  input a;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(NonPortProgramItem, AttributeInstancePrefix) {
  auto r = Parse(
      "program p;\n"
      "  (* keep *) assign w = a;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(ProgItems(r), ModuleItemKind::kContAssign);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->attrs.size(), 1u);
  EXPECT_EQ(item->attrs[0].name, "keep");
}

TEST(ProgramGenerateItem, LoopGenerateConstruct) {
  auto r = Parse(
      "program p;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 2; i = i + 1) begin\n"
      "    initial x = i;\n"
      "  end\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(ProgItems(r), ModuleItemKind::kGenerateFor));
}

TEST(ProgramGenerateItem, ConditionalGenerateConstructIf) {
  auto r = Parse(
      "program p;\n"
      "  if (1) initial x = 0;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(ProgItems(r), ModuleItemKind::kGenerateIf));
}

TEST(ProgramGenerateItem, ConditionalGenerateConstructCase) {
  auto r = Parse(
      "program p;\n"
      "  case (1)\n"
      "    0: initial x = 0;\n"
      "    default: initial y = 0;\n"
      "  endcase\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(ProgItems(r), ModuleItemKind::kGenerateCase));
}

TEST(ProgramGenerateItem, GenerateRegion) {
  auto r = Parse(
      "program p;\n"
      "  generate\n"
      "    initial x = 0;\n"
      "  endgenerate\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(ProgItems(r), ModuleItemKind::kInitialBlock));
}

TEST(ProgramGenerateItem, ElaborationSeveritySystemTask) {
  auto r = Parse(
      "program p;\n"
      "  $error(\"bad\");\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(ProgItems(r), ModuleItemKind::kElabSystemTask));
}

TEST(ProgramGenerateItem, AttributeBeforeAProgramGenerateItemRejected) {
  auto r = Parse(
      "program p;\n"
      "  (* a *) if (1) begin : g end\n"
      "  (* b *) for (genvar k = 0; k < 2; k++) begin : h end\n"
      "  (* c *) case (1) default: begin : c end endcase\n"
      "  (* d *) $info(\"x\");\n"
      "  (* e *) generate endgenerate\n"
      "endprogram\n");
  for (int line : {2, 3, 4, 5}) {
    EXPECT_TRUE(ReportedError(r.diags,
                              "a generate construct or elaboration system task "
                              "of a program takes no attribute instance",
                              line, "A.1.7"));
  }
  EXPECT_TRUE(ReportedError(
      r.diags, "a generate region takes no attribute instance", 6, "A.1.7"));
}

TEST(NonPortProgramItem, ErrorSpecifyBlockInProgramIsRejected) {
  auto r = Parse(
      "program p;\n"
      "  specify\n"
      "    (a => b) = 5;\n"
      "  endspecify\n"
      "  initial x = 0;\n"
      "endprogram\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "specify block must appear inside a module declaration", 2,
      "30.3"));
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->programs[0]->items, ModuleItemKind::kInitialBlock));
}

TEST(NonPortProgramItem, ErrorSpecparamInProgramIsRejected) {
  auto r = Parse(
      "program p;\n"
      "  specparam tRise = 150;\n"
      "endprogram\n");
  EXPECT_TRUE(ReportedError(
      r.diags,
      "specparam declaration must appear inside a module or a specify block", 2,
      "6.20.5"));
}

TEST(NonPortProgramItem, ErrorNetAliasInProgramIsRejected) {
  auto r = Parse(
      "program p;\n"
      "  alias a = b;\n"
      "  initial x = 0;\n"
      "endprogram\n");
  EXPECT_TRUE(ReportedError(r.diags, "a net alias is not an item of a program",
                            2, "A.1.7"));
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->programs[0]->items, ModuleItemKind::kInitialBlock));
}

TEST(NonPortProgramItem, ErrorBindDirectiveInProgramIsRejected) {
  auto r = Parse(
      "program p;\n"
      "  bind m chk c();\n"
      "endprogram\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a bind directive is not an item of a program", 2, "A.1.7"));
}

TEST(NonPortProgramItem, ErrorDefparamInProgramIsRejected) {
  auto r = Parse(
      "program p;\n"
      "  defparam u.w = 1;\n"
      "endprogram\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a defparam statement is not an item of a program", 2, "A.1.7"));
}

TEST(NonPortProgramItem, ErrorDeferredImmediateAssertionInProgramIsRejected) {
  auto r = Parse(
      "program p;\n"
      "  a1: assert #0 (x);\n"
      "  cover final (y);\n"
      "endprogram\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a deferred immediate assertion is not an item of a program", 2,
      "A.1.7"));
  EXPECT_TRUE(ReportedError(
      r.diags, "a deferred immediate assertion is not an item of a program", 3,
      "A.1.7"));
}

TEST(NonPortProgramItem, ErrorExternInterfaceOrProgramDeclarationIsRejected) {
  auto r = Parse(
      "program t;\n"
      "  extern interface i(input logic c);\n"
      "  extern program p(input logic d);\n"
      "endprogram\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "interface declarations not allowed in programs", 2, "24.3"));
  EXPECT_TRUE(ReportedError(
      r.diags, "program declarations not allowed in programs", 3, "24.3"));
  for (const auto& diag : r.diags) EXPECT_NE(diag.subclause, "A.1.6");
}

TEST(NonPortProgramItem, ConcurrentAssertionItemCheckerInstantiation) {
  auto r = Parse(
      "checker chk(input logic a);\n"
      "endchecker\n"
      "program p;\n"
      "  chk c(x);\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->programs[0]->items, ModuleItemKind::kModuleInst));
}

TEST(NonPortProgramItem, PackageScopedCheckerInstantiation) {
  EXPECT_TRUE(
      ParseOk("package pkg;\n"
              "  checker chk(input logic a);\n"
              "  endchecker\n"
              "endpackage\n"
              "program p;\n"
              "  pkg::chk c(x);\n"
              "endprogram\n"));
}

TEST(NonPortProgramItem, InstantiationOfCellDeclaredLaterIsLeftToElaboration) {
  auto r = Parse(
      "program p;\n"
      "  sub u0();\n"
      "endprogram\n"
      "module sub; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ProgramGenerateItem, AdmitsProgramItemsOnly) {
  auto r = Parse(
      "program p;\n"
      "  if (1) begin : g\n"
      "    defparam u.w = 1;\n"
      "  end\n"
      "endprogram\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a defparam statement is not an item of a program", 3, "A.1.7"));
}

}  // namespace
