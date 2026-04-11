

#include <initializer_list>
#include <string_view>
#include <unordered_set>

#include "builders_ast.h"
#include "builders_sensitivity.h"
#include "common/arena.h"
#include "common/types.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

void ExpectSensitivityContains(
    const RtlirProcess& proc,
    std::initializer_list<std::string_view> expected) {
  for (const auto& name : expected) {
    bool found = false;
    for (const auto& ev : proc.sensitivity) {
      if (ev.signal && ev.signal->text == name) {
        found = true;
        break;
      }
    }
    EXPECT_TRUE(found) << "missing sensitivity signal: " << name;
  }
}

void ExpectSensitivityExcludes(
    const RtlirProcess& proc,
    std::initializer_list<std::string_view> excluded) {
  for (const auto& name : excluded) {
    bool found = false;
    for (const auto& ev : proc.sensitivity) {
      if (ev.signal && ev.signal->text == name) {
        found = true;
        break;
      }
    }
    EXPECT_FALSE(found) << "unexpected sensitivity signal: " << name;
  }
}

TEST(AlwaysCombSensitivityInference, BasicReadInferred) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] a, b;\n"
      "  always_comb b = a + 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->processes.empty());
  const auto& proc = mod->processes[0];
  EXPECT_EQ(proc.kind, RtlirProcessKind::kAlwaysComb);
  EXPECT_FALSE(proc.sensitivity.empty());

  bool found_a = false;
  for (const auto& ev : proc.sensitivity) {
    if (ev.signal && ev.signal->text == "a") found_a = true;
  }
  EXPECT_TRUE(found_a);
}

TEST(AlwaysCombSensitivityInference, WrittenVarsExcludedFromSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a, b, temp;\n"
      "  always_comb begin\n"
      "    temp = a;\n"
      "    b = temp;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  auto& proc = design->top_modules[0]->processes[0];
  EXPECT_EQ(proc.kind, RtlirProcessKind::kAlwaysComb);
  bool found_a = false, found_temp = false;
  for (const auto& ev : proc.sensitivity) {
    if (ev.signal && ev.signal->text == "a") found_a = true;
    if (ev.signal && ev.signal->text == "temp") found_temp = true;
  }
  EXPECT_TRUE(found_a);
  EXPECT_FALSE(found_temp);
}

TEST(AlwaysCombSensitivityInference, BlockLocalVarsExcludedFromSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a, b;\n"
      "  always_comb begin\n"
      "    logic local_var;\n"
      "    local_var = a;\n"
      "    b = local_var;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  auto& proc = design->top_modules[0]->processes[0];
  bool found_a = false, found_local = false;
  for (const auto& ev : proc.sensitivity) {
    if (ev.signal && ev.signal->text == "a") found_a = true;
    if (ev.signal && ev.signal->text == "local_var") found_local = true;
  }
  EXPECT_TRUE(found_a);
  EXPECT_FALSE(found_local);
}

TEST(AlwaysCombSensitivityInference, MultipleReadsInSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a, b, c, y;\n"
      "  always_comb y = a & b | c;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  auto& proc = design->top_modules[0]->processes[0];
  bool found_a = false, found_b = false, found_c = false;
  for (const auto& ev : proc.sensitivity) {
    if (ev.signal && ev.signal->text == "a") found_a = true;
    if (ev.signal && ev.signal->text == "b") found_b = true;
    if (ev.signal && ev.signal->text == "c") found_c = true;
  }
  EXPECT_TRUE(found_a);
  EXPECT_TRUE(found_b);
  EXPECT_TRUE(found_c);
}

TEST(AlwaysCombSensitivityInference, OutputOnlyVarNotInSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a, y;\n"
      "  always_comb y = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  auto& proc = design->top_modules[0]->processes[0];
  bool found_y = false;
  for (const auto& ev : proc.sensitivity) {
    if (ev.signal && ev.signal->text == "y") found_y = true;
  }
  EXPECT_FALSE(found_y);
}

TEST(AlwaysCombSensitivityInference, ArrayAccessLongestStaticPrefix) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] mem [0:3];\n"
      "  logic [1:0] addr;\n"
      "  logic [7:0] data;\n"
      "  always_comb data = mem[addr];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  auto& proc = design->top_modules[0]->processes[0];
  bool found_mem = false, found_addr = false;
  for (const auto& ev : proc.sensitivity) {
    if (ev.signal && ev.signal->text == "mem") found_mem = true;
    if (ev.signal && ev.signal->text == "addr") found_addr = true;
  }
  EXPECT_TRUE(found_mem);
  EXPECT_TRUE(found_addr);
}

TEST(AlwaysCombSensitivityInference, IfConditionInSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic sel, a, b, y;\n"
      "  always_comb\n"
      "    if (sel) y = a;\n"
      "    else y = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  ExpectSensitivityContains(design->top_modules[0]->processes[0],
                            {"sel", "a", "b"});
}

TEST(AlwaysCombSensitivityInference, SensitivityEdgesAreNone) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a, b;\n"
      "  always_comb b = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  auto& proc = design->top_modules[0]->processes[0];
  for (const auto& ev : proc.sensitivity) {
    EXPECT_EQ(ev.edge, Edge::kNone);
  }
}

TEST(AlwaysCombSensitivityInference, CaseBodyReadsInSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [1:0] sel;\n"
      "  logic a, b, y;\n"
      "  always_comb\n"
      "    case (sel)\n"
      "      2'b00: y = a;\n"
      "      2'b01: y = b;\n"
      "      default: y = 0;\n"
      "    endcase\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  ExpectSensitivityContains(design->top_modules[0]->processes[0],
                            {"sel", "a", "b"});
}

TEST(AlwaysCombSensitivityInference, AssertExprInSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a, b, c, y;\n"
      "  always_comb begin\n"
      "    y = a & b;\n"
      "    assert (c);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  auto& proc = design->top_modules[0]->processes[0];
  bool found_c = false;
  for (const auto& ev : proc.sensitivity) {
    if (ev.signal && ev.signal->text == "c") found_c = true;
  }
  EXPECT_TRUE(found_c);
}

TEST(AlwaysCombSensitivityInference, MultipleAlwaysCombProcessesIndependentSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b, c, d;\n"
      "  always_comb c = a;\n"
      "  always_comb d = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 2u);
  EXPECT_FALSE(mod->processes[0].sensitivity.empty());
  EXPECT_FALSE(mod->processes[1].sensitivity.empty());
}

Expr* MakeMember(Arena& arena, Expr* obj, std::string_view field) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kMemberAccess;
  e->lhs = obj;
  e->rhs = MakeId(arena, field);
  return e;
}

TEST(AlwaysCombSensitivityCollection, SelectConstIdxUsesLSP) {
  Arena arena;
  auto* expr = SensSelect(arena, SensId(arena, "a"), SensIntLit(arena, 1));
  std::unordered_set<std::string> reads;
  CollectExprReads(expr, reads);
  EXPECT_TRUE(reads.count("a[1]"));
  EXPECT_FALSE(reads.count("a"));
}

TEST(AlwaysCombSensitivityCollection, NestedSelectUsesLSP) {
  Arena arena;
  auto* inner = SensSelect(arena, SensId(arena, "a"), SensIntLit(arena, 1));
  auto* outer = SensSelect(arena, inner, SensId(arena, "i"));
  std::unordered_set<std::string> reads;
  CollectExprReads(outer, reads);
  EXPECT_TRUE(reads.count("a[1]"));
  EXPECT_TRUE(reads.count("i"));
  EXPECT_FALSE(reads.count("a"));
}

TEST(AlwaysCombSensitivityCollection, SelectVarIdxUsesLSP) {
  Arena arena;
  auto* expr = SensSelect(arena, SensId(arena, "a"), SensId(arena, "i"));
  std::unordered_set<std::string> reads;
  CollectExprReads(expr, reads);
  EXPECT_TRUE(reads.count("a"));
  EXPECT_TRUE(reads.count("i"));
}

TEST(AlwaysCombSensitivityCollection, FieldSelectVarIdxUsesLSP) {
  Arena arena;
  auto* field = MakeMember(arena, SensId(arena, "s"), "field");
  auto* expr = SensSelect(arena, field, SensId(arena, "i"));
  std::unordered_set<std::string> reads;
  CollectExprReads(expr, reads);
  EXPECT_TRUE(reads.count("s.field"));
  EXPECT_TRUE(reads.count("i"));
}

TEST(AlwaysCombSensitivityInference, AssertActionBlockExcludedFromSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a, b, c, d, y;\n"
      "  always_comb begin\n"
      "    y = a & b;\n"
      "    assert (c) else $display(\"%0d\", d);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  auto& proc = design->top_modules[0]->processes[0];
  bool found_c = false, found_d = false;
  for (const auto& ev : proc.sensitivity) {
    if (ev.signal && ev.signal->text == "c") found_c = true;
    if (ev.signal && ev.signal->text == "d") found_d = true;
  }
  EXPECT_TRUE(found_c);
  EXPECT_FALSE(found_d);
}

TEST(AlwaysCombSensitivityInference, AssertPassActionExcludedFromSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a, c, d, y;\n"
      "  always_comb begin\n"
      "    y = a;\n"
      "    assert (c) $display(\"%0d\", d);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  auto& proc = design->top_modules[0]->processes[0];
  bool found_c = false, found_d = false;
  for (const auto& ev : proc.sensitivity) {
    if (ev.signal && ev.signal->text == "c") found_c = true;
    if (ev.signal && ev.signal->text == "d") found_d = true;
  }
  EXPECT_TRUE(found_c);
  EXPECT_FALSE(found_d);
}

TEST(AlwaysCombSensitivityInference, ForLoopVarExcludedFromSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr [0:3];\n"
      "  logic [7:0] sum;\n"
      "  always_comb begin\n"
      "    sum = 0;\n"
      "    for (int i = 0; i < 4; i++)\n"
      "      sum = sum + arr[i];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  auto& proc = design->top_modules[0]->processes[0];
  bool found_arr = false, found_i = false;
  for (const auto& ev : proc.sensitivity) {
    if (ev.signal && ev.signal->text == "arr") found_arr = true;
    if (ev.signal && ev.signal->text == "i") found_i = true;
  }
  EXPECT_TRUE(found_arr);
  EXPECT_FALSE(found_i);
}

TEST(AlwaysCombSensitivityInference, EmptyBlockProducesNoSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  always_comb begin\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  auto& proc = design->top_modules[0]->processes[0];
  EXPECT_TRUE(proc.sensitivity.empty());
}

TEST(AlwaysCombSensitivityCollection, AssertExprCollectedButActionBlocksNot) {
  Arena arena;
  auto* assert_stmt = arena.Create<Stmt>();
  assert_stmt->kind = StmtKind::kAssertImmediate;
  assert_stmt->assert_expr = SensId(arena, "cond");
  assert_stmt->assert_pass_stmt = MakeExprStmt(
      arena, MakeSysCall(arena, "$display", {SensId(arena, "pass_var")}));
  assert_stmt->assert_fail_stmt = MakeExprStmt(
      arena, MakeSysCall(arena, "$display", {SensId(arena, "fail_var")}));

  std::unordered_set<std::string> reads;
  CollectStmtReads(assert_stmt, reads);
  EXPECT_TRUE(reads.count("cond"));
  EXPECT_FALSE(reads.count("pass_var"));
  EXPECT_FALSE(reads.count("fail_var"));
}

TEST(AlwaysCombSensitivityCollection, CallArgsCollectedButCalleeNameNot) {
  Arena arena;
  auto* call = MakeCall(arena, "my_func", {SensId(arena, "x"), SensId(arena, "y")});
  std::unordered_set<std::string> reads;
  CollectExprReads(call, reads);
  EXPECT_TRUE(reads.count("x"));
  EXPECT_TRUE(reads.count("y"));
  EXPECT_FALSE(reads.count("my_func"));
}

TEST(AlwaysCombSensitivityInference, FunctionBodyReadsContributeToSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] ext, a, result;\n"
      "  function automatic logic [7:0] add_ext(input logic [7:0] x);\n"
      "    return x + ext;\n"
      "  endfunction\n"
      "  always_comb result = add_ext(a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  ExpectSensitivityContains(design->top_modules[0]->processes[0],
                            {"a", "ext"});
}

TEST(AlwaysCombSensitivityInference, FunctionLocalVarsExcludedFromSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] ext, a, result;\n"
      "  function automatic logic [7:0] transform(input logic [7:0] x);\n"
      "    logic [7:0] tmp;\n"
      "    tmp = x + ext;\n"
      "    return tmp;\n"
      "  endfunction\n"
      "  always_comb result = transform(a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  ExpectSensitivityExcludes(design->top_modules[0]->processes[0], {"tmp"});
}

TEST(AlwaysCombSensitivityInference, TaskCallArgsInSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, ext;\n"
      "  task automatic log_val(input logic [7:0] x);\n"
      "    logic [7:0] tmp;\n"
      "    tmp = x + ext;\n"
      "  endtask\n"
      "  always_comb log_val(a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  ExpectSensitivityContains(design->top_modules[0]->processes[0], {"a"});
}

TEST(AlwaysCombSensitivityInference, TaskCallBodyExcludedFromSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, ext;\n"
      "  task automatic log_val(input logic [7:0] x);\n"
      "    logic [7:0] tmp;\n"
      "    tmp = x + ext;\n"
      "  endtask\n"
      "  always_comb log_val(a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  ExpectSensitivityExcludes(design->top_modules[0]->processes[0], {"ext"});
}

TEST(AlwaysCombSensitivityInference, AssertBothPassAndFailActionsExcluded) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a, b, c, d, y;\n"
      "  always_comb begin\n"
      "    y = a;\n"
      "    assert (b) $display(\"%0d\", c); else $display(\"%0d\", d);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  auto& proc = design->top_modules[0]->processes[0];
  ExpectSensitivityContains(proc, {"a", "b"});
  ExpectSensitivityExcludes(proc, {"c", "d"});
}

TEST(AlwaysCombSensitivityCollection, WaitConditionExcludedFromSensitivity) {
  Arena arena;
  auto* wait_stmt = arena.Create<Stmt>();
  wait_stmt->kind = StmtKind::kWait;
  wait_stmt->condition = SensId(arena, "x");

  std::unordered_set<std::string> reads;
  CollectStmtReads(wait_stmt, reads);
  EXPECT_FALSE(reads.count("x"));
}

}  // namespace
