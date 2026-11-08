#include <gtest/gtest.h>

#include "fixture_program.h"
#include "helpers_reported_error.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

TEST_F(VerifyParseTest, CheckerNestedWithClocking) {
  auto* unit = Parse(R"(
    checker c1(bit fclk, bit a, bit b);
      default clocking @(posedge fclk); endclocking
      checker c2(bit bclk, bit x, bit y);
        default clocking @(posedge bclk); endclocking
        rand bit m, n;
        u1: assume property (x != m);
        u2: assume property (y != n);
      endchecker
      rand bit q, r;
      c2 B1(fclk, q + r, r);
      always_ff @(posedge fclk)
        r <= a || q;
      u3: assume property (a != q);
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_EQ(unit->checkers[0]->name, "c1");
  EXPECT_FALSE(unit->checkers[0]->items.empty());
}

TEST_F(VerifyParseTest, CheckerInstantiationConnectionStyles) {
  auto* unit = Parse(R"(
    checker chk(bit clk, bit [31:0] sig);
      a1: assert property (@(posedge clk) sig);
    endchecker
    module m;
      bit clk;
      bit [31:0] sig;
      chk e1(.clk(clk), .sig(sig)); // fully explicit named
      chk i1(.clk, .sig);           // implicit named
      chk w1(.*);                   // wildcard port name
    endmodule
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_EQ(unit->checkers[0]->name, "chk");
  EXPECT_FALSE(diag_.HasErrors());
}

TEST_F(VerifyParseTest, CheckerInstantiationRejectsRepeatedWildcard) {
  auto* unit = Parse(R"(
    checker chk(bit clk, bit [31:0] sig);
      a1: assert property (@(posedge clk) sig);
    endchecker
    module m;
      bit clk;
      bit [31:0] sig;
      chk w1(.*, .*);
    endmodule
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_TRUE(ReportedError(
      diag_.Diagnostics(),
      ".* already appears earlier in this port connection list", 8, "23.3.2"));
}

TEST_F(VerifyParseTest, CheckerInstantiationEmptyConnectionList) {
  auto* unit = Parse(R"(
    checker chk(bit clk, bit sig);
      a1: assert property (@(posedge clk) sig);
    endchecker
    module m;
      bit clk;
      bit sig;
      chk c1(); // no port connections
    endmodule
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_FALSE(diag_.HasErrors());
}

TEST_F(VerifyParseTest, CheckerInstantiationOmittedOrderedConnection) {
  auto* unit = Parse(R"(
    checker chk3(bit clk, bit a, bit b);
      a1: assert property (@(posedge clk) a || b);
    endchecker
    module m;
      bit clk;
      bit sig;
      chk3 c1(clk, , sig); // middle formal 'a' left unconnected
    endmodule
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_FALSE(diag_.HasErrors());
}

TEST_F(VerifyParseTest, CheckerInstantiationEmptyNamedActual) {
  auto* unit = Parse(R"(
    checker chk3(bit clk, bit a, bit b);
      a1: assert property (@(posedge clk) a || b);
    endchecker
    module m;
      bit clk;
      bit sig;
      chk3 c1(.clk(clk), .a(), .b(sig)); // named connection with empty actual
    endmodule
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_FALSE(diag_.HasErrors());
}

TEST_F(VerifyParseTest, CheckerInstantiationPackageScopedIdentifier) {
  Parse(R"(
    module m;
      bit clk;
      bit sig;
      p::chk c1(clk, sig); // package-scoped checker identifier
    endmodule
  )");
  EXPECT_FALSE(diag_.HasErrors());
}

const Stmt* FirstProcedureStmt(const CompilationUnit* unit,
                               ModuleItemKind kind) {
  if (unit == nullptr || unit->modules.empty()) return nullptr;
  for (const ModuleItem* item : unit->modules.back()->items) {
    if (item->kind != kind || item->body == nullptr) continue;
    const Stmt* body = item->body;
    if (body->kind != StmtKind::kBlock) return body;
    return body->stmts.empty() ? nullptr : body->stmts.front();
  }
  return nullptr;
}

TEST_F(VerifyParseTest, CheckerInstantiationAsTheBranchOfAnIf) {
  auto* unit = Parse(R"(
    checker chk(logic a, logic clk);
      a1: assert property (@(posedge clk) a);
    endchecker
    module m;
      logic clk, a, en;
      always @(posedge clk) begin
        if (en) chk c(a, clk);
      end
    endmodule
  )");
  EXPECT_FALSE(diag_.HasErrors());
  const Stmt* branch = FirstProcedureStmt(unit, ModuleItemKind::kAlwaysBlock);
  ASSERT_NE(branch, nullptr);
  ASSERT_EQ(branch->kind, StmtKind::kIf);
  const Stmt* inst = branch->then_branch;
  ASSERT_NE(inst, nullptr);
  ASSERT_EQ(inst->kind, StmtKind::kCheckerInstantiation);
  ASSERT_NE(inst->decl_item, nullptr);
  EXPECT_EQ(inst->decl_item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(inst->decl_item->inst_module, "chk");
  EXPECT_EQ(inst->decl_item->inst_name, "c");
  EXPECT_EQ(inst->decl_item->inst_ports.size(), 2u);
}

TEST_F(VerifyParseTest, PackageScopedCheckerInstantiationInAnInitialBlock) {
  auto* unit = Parse(R"(
    module m;
      logic clk, a;
      initial begin
        p::chk c(.a(a), .clk(clk));
        @(posedge clk);
      end
    endmodule
  )");
  EXPECT_FALSE(diag_.HasErrors());
  const Stmt* inst = FirstProcedureStmt(unit, ModuleItemKind::kInitialBlock);
  ASSERT_NE(inst, nullptr);
  ASSERT_EQ(inst->kind, StmtKind::kCheckerInstantiation);
  ASSERT_NE(inst->decl_item, nullptr);
  EXPECT_EQ(inst->decl_item->inst_scope, "p");
  EXPECT_EQ(inst->decl_item->inst_module, "chk");
  EXPECT_EQ(inst->decl_item->inst_name, "c");
}

TEST_F(VerifyParseTest, CheckerInstantiationInATaskIsRejected) {
  Parse(R"(
    module m;
      logic clk, a;
      task t;
        chk c(a, clk);
      endtask
    endmodule
  )");
  EXPECT_TRUE(ReportedError(diag_.Diagnostics(),
                            "a checker instantiation in procedural code shall "
                            "be in an always or an initial procedure",
                            5, "17.3"));
}

TEST_F(VerifyParseTest, CheckerInstantiationInAFinalProcedureIsRejected) {
  Parse(R"(
    module m;
      logic clk, a;
      final begin
        chk c(a, clk);
      end
    endmodule
  )");
  EXPECT_TRUE(ReportedError(diag_.Diagnostics(),
                            "a checker instantiation in procedural code shall "
                            "be in an always or an initial procedure",
                            5, "17.3"));
}

}  // namespace
