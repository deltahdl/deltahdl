#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

TEST(ExpectStatementElaboration, ATaskExpectTakesTheDefaultClocking) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic clk;\n"
      "  int data;\n"
      "  default clocking cb @(posedge clk); endclocking\n"
      "  property within_ten(int value);\n"
      "    ##[1:10] data == value;\n"
      "  endproperty\n"
      "  task automatic wait_for(integer value, output bit success);\n"
      "    expect (within_ten(value)) success = 1;\n"
      "      else success = 0;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->function_decls.size(), 1u);
  ASSERT_EQ(mod->function_decls[0]->func_body_stmts.size(), 1u);
  const Stmt* expect = mod->function_decls[0]->func_body_stmts[0];
  EXPECT_EQ(expect->kind, StmtKind::kExpect);
  EXPECT_TRUE(expect->is_concurrent_clocked);
  ASSERT_EQ(expect->assert_clock.size(), 1u);
  EXPECT_EQ(expect->assert_clock[0].edge, Edge::kPosedge);
}

struct ForbiddenPlace {
  const char* forbidden;
  const char* allowed;
  const char* message;
  const char* subclause;
};

constexpr ForbiddenPlace kForbiddenPlaces[] = {
    {"module m;\n  logic clk, a;\n  final expect (@(posedge clk) a);\n"
     "endmodule\n",
     "module m;\n  logic clk, a;\n  initial expect (@(posedge clk) a);\n"
     "endmodule\n",
     "final procedure shall not contain timing controls", "9.2.3"},
    {"program p;\n  logic clk, a;\n  final expect (@(posedge clk) a);\n"
     "endprogram\n",
     "program p;\n  logic clk, a;\n  initial expect (@(posedge clk) a);\n"
     "endprogram\n",
     "final procedure shall not contain timing controls", "9.2.3"},
    {"module m;\n  logic clk, a, q;\n  always_latch begin "
     "expect (@(posedge clk) a); if (a) q = 1; end\nendmodule\n",
     "module m;\n  logic clk, a, q;\n  always begin "
     "expect (@(posedge clk) a); if (a) q = 1; end\nendmodule\n",
     "always_latch shall not contain timing controls", "9.2.2.3"},
    {"module m;\n  logic clk, a, q;\n  always_ff @(posedge clk) begin "
     "expect (@(posedge clk) a); q <= 1; end\nendmodule\n",
     "module m;\n  logic clk, a, q;\n  always @(posedge clk) begin "
     "expect (@(posedge clk) a); q <= 1; end\nendmodule\n",
     "always_ff shall not contain blocking timing controls", "9.2.2.4"},
    {"checker chk(logic clk, logic a);\n"
     "  initial expect (@(posedge clk) a);\nendchecker\n"
     "module m;\n  logic clk, a;\n  chk c(clk, a);\nendmodule\n",
     "checker chk(logic clk, logic a);\n"
     "  initial begin @(posedge clk); assert property (@(posedge clk) a); "
     "end\nendchecker\n"
     "module m;\n  logic clk, a;\n  chk c(clk, a);\nendmodule\n",
     "this statement is none of those an initial procedure of checker 'chk' "
     "may hold",
     "17.5"},
};

int LineOfExpect(const std::string& src) {
  int line = 1;
  for (char ch : src.substr(0, src.find("expect"))) line += ch == '\n';
  return line;
}

TEST(ExpectPlacementElaboration, EachForbiddenPlaceBesideItsNearestAllowed) {
  for (const ForbiddenPlace& place : kForbiddenPlaces) {
    ElabFixture rejected;
    ElaborateSrc(place.forbidden, rejected);
    EXPECT_TRUE(ReportedError(rejected.diag.Diagnostics(), place.message,
                              LineOfExpect(place.forbidden), place.subclause))
        << place.forbidden;
    ElabFixture accepted;
    ElaborateSrc(place.allowed, accepted);
    EXPECT_TRUE(accepted.diag.Diagnostics().empty()) << place.allowed;
  }
}

}  // namespace
