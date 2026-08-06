

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

TEST(AlwaysCombSensitivityInference,
     MultipleAlwaysCombProcessesIndependentSensitivity) {
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

TEST(AlwaysCombSensitivityCollection, CallArgsCollectedButCalleeNameNot) {
  Arena arena;
  auto* call =
      MakeCall(arena, "my_func", {SensId(arena, "x"), SensId(arena, "y")});
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
  ExpectSensitivityContains(design->top_modules[0]->processes[0], {"a", "ext"});
}

// Functions are analyzed as normal functions, so a read reached through a chain
// of calls (the block calls f, which in turn calls g) still contributes to the
// sensitivity list.
TEST(AlwaysCombSensitivityInference, TransitiveFunctionCallReadsInSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, deep, result;\n"
      "  function automatic logic [7:0] g(input logic [7:0] x);\n"
      "    return x + deep;\n"
      "  endfunction\n"
      "  function automatic logic [7:0] ff(input logic [7:0] x);\n"
      "    return g(x);\n"
      "  endfunction\n"
      "  always_comb result = ff(a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  ExpectSensitivityContains(design->top_modules[0]->processes[0],
                            {"a", "deep"});
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

// A variable that is written within a called function is excluded from the
// sensitivity list even though it is also read within that function.
TEST(AlwaysCombSensitivityInference,
     FunctionWrittenVarExcludedFromSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, shared, result;\n"
      "  function automatic logic [7:0] f(input logic [7:0] x);\n"
      "    shared = x;\n"
      "    return shared + a;\n"
      "  endfunction\n"
      "  always_comb result = f(a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  auto& proc = design->top_modules[0]->processes[0];
  ExpectSensitivityContains(proc, {"a"});
  ExpectSensitivityExcludes(proc, {"shared"});
}

// An expression used in an immediate assertion inside a called function
// contributes to the sensitivity list as if it were an if condition.
TEST(AlwaysCombSensitivityInference, AssertExprInCalledFunctionInSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a, c, result;\n"
      "  function automatic logic check(input logic x);\n"
      "    assert (c);\n"
      "    return x;\n"
      "  endfunction\n"
      "  always_comb result = check(a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  ExpectSensitivityContains(design->top_modules[0]->processes[0], {"a", "c"});
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

// §9.2.2.2.1 exception (c), driven from real source: a nonblocking assignment
// with an intra-assignment delay is legal in an always_comb (see the §9.2.2.2
// `d <= #... b & c;` example). An identifier that appears only inside that
// delay control is excluded from the inferred list, while the right-hand-side
// reads are kept. Full parse+elaborate observes the rule as production applies
// it.
TEST(AlwaysCombSensitivityInference,
     IntraAssignDelayIdentifierExcludedFromSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic b, c, d;\n"
      "  logic [7:0] dly;\n"
      "  always_comb d <= #(dly) (b & c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  auto& proc = design->top_modules[0]->processes[0];
  ExpectSensitivityContains(proc, {"b", "c"});
  ExpectSensitivityExcludes(proc, {"dly"});
}

// An identifier appearing only in a delay control expression contributes
// nothing to the implicit sensitivity list.
TEST(AlwaysCombSensitivityCollection, DelayExprExcludedFromSensitivity) {
  Arena arena;
  auto* delay_stmt = arena.Create<Stmt>();
  delay_stmt->kind = StmtKind::kDelay;
  delay_stmt->delay = SensId(arena, "d");

  std::unordered_set<std::string> reads;
  CollectStmtReads(delay_stmt, reads);
  EXPECT_FALSE(reads.count("d"));
}

// An identifier appearing only in an event control expression contributes
// nothing to the implicit sensitivity list.
TEST(AlwaysCombSensitivityCollection, EventControlExcludedFromSensitivity) {
  Arena arena;
  auto* event_stmt = arena.Create<Stmt>();
  event_stmt->kind = StmtKind::kEventControl;
  event_stmt->events.push_back({Edge::kNone, SensId(arena, "e")});

  std::unordered_set<std::string> reads;
  CollectStmtReads(event_stmt, reads);
  EXPECT_FALSE(reads.count("e"));
}

// A method call on a class object (or a class scope-resolved call) contributes
// only through its argument expressions; the object reference and method name
// add nothing to the implicit sensitivity list.
TEST(AlwaysCombSensitivityCollection, MethodCallObjectReferenceExcluded) {
  Arena arena;
  auto* callee = MakeMember(arena, SensId(arena, "obj"), "method");
  auto* call = arena.Create<Expr>();
  call->kind = ExprKind::kCall;
  call->lhs = callee;
  call->args.push_back(SensId(arena, "arg"));

  std::unordered_set<std::string> reads;
  CollectExprReads(call, reads);
  EXPECT_TRUE(reads.count("arg"));
  EXPECT_FALSE(reads.count("obj"));
  EXPECT_FALSE(reads.count("method"));
}

// §9.2.2.2.1: only nets and variables populate the implicit sensitivity list. A
// localparam read as a direct operand is a constant (11.2.1), not a net or
// variable, so it is excluded while the real variable operand is kept.
TEST(AlwaysCombSensitivityInference, LocalparamOperandExcludedFromSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  localparam int P = 3;\n"
      "  logic [7:0] a, y;\n"
      "  always_comb y = a + P;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  auto& proc = design->top_modules[0]->processes[0];
  ExpectSensitivityContains(proc, {"a"});
  ExpectSensitivityExcludes(proc, {"P"});
}

// A module parameter used as a constant select index (11.2.1) does not become a
// separate sensitivity read; the addressed variable's base name is kept.
TEST(AlwaysCombSensitivityInference,
     ParameterSelectIndexExcludedFromSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t #(parameter int IDX = 1);\n"
      "  logic [7:0] arr [0:3];\n"
      "  logic [7:0] y;\n"
      "  always_comb y = arr[IDX];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  auto& proc = design->top_modules[0]->processes[0];
  ExpectSensitivityContains(proc, {"arr"});
  ExpectSensitivityExcludes(proc, {"IDX"});
}

// §11.5.3 dependency, real source: an indexed part-select read (`a[i +: 2]`)
// expands to the longest static prefix `a` while its variable offset `i` is a
// distinct net/variable read, so both belong to the inferred list.
TEST(AlwaysCombSensitivityInference, IndexedPartSelectOffsetInSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [1:0] i;\n"
      "  logic [1:0] y;\n"
      "  always_comb y = a[i +: 2];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  ExpectSensitivityContains(design->top_modules[0]->processes[0], {"a", "i"});
}

// §11.5.3 dependency, real source: a constant part-select (`a[3:1]`) has a
// static prefix, so the addressed variable's base name is watched and no
// constant bound is added as its own read.
TEST(AlwaysCombSensitivityInference, ConstantPartSelectBaseInSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [2:0] y;\n"
      "  always_comb y = a[3:1];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  ExpectSensitivityContains(design->top_modules[0]->processes[0], {"a"});
}

// Constant-expression select index, literal form (11.2.1): a bit-select with a
// literal index keeps the addressed variable's base name and adds no separate
// index read. Complements the parameter and localparam index forms, which reach
// the constant-exclusion path through a different declaration.
TEST(AlwaysCombSensitivityInference, LiteralBitSelectIndexBaseInSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic y;\n"
      "  always_comb y = a[1];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  ExpectSensitivityContains(design->top_modules[0]->processes[0], {"a"});
}

// Constant-expression select index, localparam form (11.2.1): a localparam
// declared as a module item reaches the constant-name set through a different
// path than a parameter port, yet is likewise excluded as a select index while
// the addressed array's base name is kept.
TEST(AlwaysCombSensitivityInference,
     LocalparamSelectIndexExcludedFromSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  localparam int LP = 2;\n"
      "  logic [7:0] arr [0:3];\n"
      "  logic [7:0] y;\n"
      "  always_comb y = arr[LP];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  auto& proc = design->top_modules[0]->processes[0];
  ExpectSensitivityContains(proc, {"arr"});
  ExpectSensitivityExcludes(proc, {"LP"});
}

// Member-select read form (§11.5.3 dependency, real source): reading a packed
// struct member (`p.lo`) contributes the struct variable's base name to the
// inferred list.
TEST(AlwaysCombSensitivityInference, StructMemberReadInSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed {\n"
      "    logic [7:0] hi;\n"
      "    logic [7:0] lo;\n"
      "  } pair_t;\n"
      "  pair_t p;\n"
      "  logic [7:0] r;\n"
      "  always_comb r = p.lo;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  ExpectSensitivityContains(design->top_modules[0]->processes[0], {"p"});
}

// §8.23 dependency, real source: a call to a static method reached through the
// class scope resolution operator contributes to the list only through its
// argument expressions; the scope-resolved callee reference itself adds
// nothing.
TEST(AlwaysCombSensitivityInference, ClassScopeResolvedCallArgInSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  virtual class C #(parameter W = 8);\n"
      "    static function int add1(input int x);\n"
      "      add1 = x + 1;\n"
      "    endfunction\n"
      "  endclass\n"
      "  int a, y;\n"
      "  always_comb y = C#(8)::add1(a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  auto& proc = design->top_modules[0]->processes[0];
  ExpectSensitivityContains(proc, {"a"});
  ExpectSensitivityExcludes(proc, {"C"});
}

}  // namespace
