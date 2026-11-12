#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <iterator>
#include <string>
#include <utility>
#include <vector>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

constexpr const char* kStatementForms[] = {
    "while (0) ;", "begin end", "fork join", "#1;",
    "return;",     "wait (1);", "-> e;"};

void ExpectEachFormRejected(const char* head, const char* tail,
                            const char* forms_extra, const char* message,
                            const char* subclause) {
  auto line = static_cast<uint32_t>(
      std::count(head, head + std::char_traits<char>::length(head), '\n') + 1);
  std::vector<std::string> forms(std::begin(kStatementForms),
                                 std::end(kStatementForms));
  if (forms_extra) forms.emplace_back(forms_extra);
  for (const auto& form : forms) {
    std::string src = std::string(head) + "  " + form + "\n" + tail;
    SCOPED_TRACE(src);
    auto r = Parse(src);
    EXPECT_TRUE(ReportedError(r.diags, message, line, subclause));
  }
}

void ExpectContainerHoldsStatement(const char* src, ModuleItemKind kind) {
  auto r = Parse(src);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_NE(FindItemByKind(r, kind), nullptr);
}

void ExpectRejectedAtModuleScope(const char* src, uint32_t line) {
  auto r = Parse(src);
  EXPECT_TRUE(ReportedError(r.diags, "unexpected token in module body", line,
                            "23.2.4"));
}

TEST(ProceduralStatementContainment, InitialHoldsStatement) {
  ExpectContainerHoldsStatement(
      "module m;\n"
      "  logic x;\n"
      "  initial x = 1;\n"
      "endmodule\n",
      ModuleItemKind::kInitialBlock);
}

TEST(ProceduralStatementContainment, AlwaysHoldsStatement) {
  ExpectContainerHoldsStatement(
      "module m;\n"
      "  logic x;\n"
      "  always #1 x = 1;\n"
      "endmodule\n",
      ModuleItemKind::kAlwaysBlock);
}

TEST(ProceduralStatementContainment, AlwaysCombHoldsStatement) {
  ExpectContainerHoldsStatement(
      "module m;\n"
      "  logic x, y;\n"
      "  always_comb x = y;\n"
      "endmodule\n",
      ModuleItemKind::kAlwaysCombBlock);
}

TEST(ProceduralStatementContainment, AlwaysLatchHoldsStatement) {
  ExpectContainerHoldsStatement(
      "module m;\n"
      "  logic en, x, y;\n"
      "  always_latch if (en) x = y;\n"
      "endmodule\n",
      ModuleItemKind::kAlwaysLatchBlock);
}

TEST(ProceduralStatementContainment, AlwaysFFHoldsStatement) {
  ExpectContainerHoldsStatement(
      "module m;\n"
      "  logic clk, x, y;\n"
      "  always_ff @(posedge clk) x <= y;\n"
      "endmodule\n",
      ModuleItemKind::kAlwaysFFBlock);
}

TEST(ProceduralStatementContainment, FinalHoldsStatement) {
  ExpectContainerHoldsStatement(
      "module m;\n"
      "  logic x;\n"
      "  final x = 1;\n"
      "endmodule\n",
      ModuleItemKind::kFinalBlock);
}

TEST(ProceduralStatementContainment, TaskHoldsStatement) {
  ExpectContainerHoldsStatement(
      "module m;\n"
      "  logic x;\n"
      "  task t;\n"
      "    x = 1;\n"
      "  endtask\n"
      "endmodule\n",
      ModuleItemKind::kTaskDecl);
}

TEST(ProceduralStatementContainment, FunctionHoldsStatement) {
  ExpectContainerHoldsStatement(
      "module m;\n"
      "  function int f;\n"
      "    return 1;\n"
      "  endfunction\n"
      "endmodule\n",
      ModuleItemKind::kFunctionDecl);
}

TEST(ProceduralStatementContainment, DelayControlAtModuleScopeRejected) {
  ExpectRejectedAtModuleScope(
      "module m;\n"
      "  logic x;\n"
      "  #5 x = 1;\n"
      "endmodule\n",
      3);
}

TEST(ProceduralStatementContainment, SequentialBlockAtModuleScopeRejected) {
  ExpectRejectedAtModuleScope(
      "module m;\n"
      "  logic x;\n"
      "  begin x = 1; end\n"
      "endmodule\n",
      3);
}

TEST(ProceduralStatementContainment, ParallelBlockAtModuleScopeRejected) {
  ExpectRejectedAtModuleScope(
      "module m;\n"
      "  logic x;\n"
      "  fork x = 1; join\n"
      "endmodule\n",
      3);
}

TEST(ProceduralStatementContainment, WhileLoopAtModuleScopeRejected) {
  ExpectRejectedAtModuleScope(
      "module m;\n"
      "  logic x;\n"
      "  while (1) x = 1;\n"
      "endmodule\n",
      3);
}

TEST(ProceduralStatementContainment, ReturnAtModuleScopeRejected) {
  ExpectRejectedAtModuleScope(
      "module m;\n"
      "  return;\n"
      "endmodule\n",
      2);
}

TEST(ProceduralStatementContainment,
     EachStatementFormInAnInterfaceProgramOrCheckerIsRejected) {
  ExpectEachFormRejected("interface s;\n  event e;\n", "endinterface\n",
                         nullptr, "unexpected token in module body", "23.2.4");
  ExpectEachFormRejected("program s;\n  event e;\n", "endprogram\n", nullptr,
                         "unexpected token in module body", "23.2.4");
  ExpectEachFormRejected("checker s;\n  event e;\n", "endchecker\n", nullptr,
                         "unexpected token in module body", "23.2.4");
}

TEST(ProceduralStatementContainment,
     EachStatementFormInAPackageOrTheCompilationUnitIsRejected) {
  ExpectEachFormRejected("package s;\n  event e;\n", "endpackage\n", nullptr,
                         "unexpected token in module body", "23.2.4");
  auto r = Parse(
      "package s;\n"
      "  case (1) default: ; endcase\n"
      "endpackage\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "a generate construct is not an item of a package",
                            2, "A.1.11"));
  ExpectEachFormRejected("event e;\n", "module top;\nendmodule\n",
                         "case (1) default: ; endcase",
                         "expected top-level declaration", "3.12.1");
}

TEST(ProceduralStatementContainment,
     DISABLED_EachStatementFormInAClassBodyIsReportedAsAProceduralStatement) {
  ExpectEachFormRejected(
      "class s;\n  event e;\n", "endclass\n", "case (1) default: ; endcase",
      "a procedural statement is not an item of a class", "12.2");
}

TEST(ProceduralStatementContainment,
     EachStatementFormInAGenerateBlockIsRejected) {
  ExpectEachFormRejected("module m;\n  event e;\n  if (1) begin : g\n",
                         "  end\nendmodule\n", nullptr,
                         "unexpected token in module body", "23.2.4");
  ExpectEachFormRejected(
      "module m;\n  event e;\n  for (genvar i = 0; i < 2; "
      "i++) begin : g\n",
      "  end\nendmodule\n", nullptr, "unexpected token in module body",
      "23.2.4");
}

TEST(ProceduralStatementContainment,
     WaitTriggerAndForkAtModuleScopeAreRejected) {
  ExpectRejectedAtModuleScope(
      "module m;\n"
      "  event e;\n"
      "  wait (1);\n"
      "endmodule\n",
      3);
  ExpectRejectedAtModuleScope(
      "module m;\n"
      "  event e;\n"
      "  -> e;\n"
      "endmodule\n",
      3);
  ExpectRejectedAtModuleScope(
      "module m;\n"
      "  event e;\n"
      "  fork join\n"
      "endmodule\n",
      3);
}

TEST(ProceduralStatementContainment,
     GenerateIfForAndCaseInEachDesignElementAreAccepted) {
  const std::pair<const char*, const char*> kElements[] = {
      {"module", "endmodule"},
      {"interface", "endinterface"},
      {"program", "endprogram"},
      {"checker", "endchecker"}};
  for (const auto& [open, close] : kElements) {
    std::string src = std::string(open) +
                      " s;\n"
                      "  if (1) begin : a end\n"
                      "  for (genvar i = 0; i < 2; i++) begin : b end\n"
                      "  case (1) default: begin : c end endcase\n" +
                      close + "\n";
    SCOPED_TRACE(src);
    auto r = Parse(src);
    ASSERT_NE(r.cu, nullptr);
    EXPECT_FALSE(r.has_errors);
  }
}

}  // namespace
