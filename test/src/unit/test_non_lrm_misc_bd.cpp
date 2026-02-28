// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

struct ParseResult4d {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult4d Parse(const std::string& src) {
  ParseResult4d result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// Returns the first module item from the first module.
static ModuleItem* FirstItem(ParseResult4d& r) {
  if (!r.cu || r.cu->modules.empty() || r.cu->modules[0]->items.empty())
    return nullptr;
  return r.cu->modules[0]->items[0];
}

// Returns the first function/task body statement from a ModuleItem.
static Stmt* FirstBodyStmt(ModuleItem* item) {
  if (!item || item->func_body_stmts.empty()) return nullptr;
  return item->func_body_stmts[0];
}

static Stmt* FindStmtByKind(ModuleItem* item, StmtKind kind) {
  for (auto* stmt : item->func_body_stmts) {
    if (stmt->kind == kind) return stmt;
  }
  return nullptr;
}

namespace {

// =============================================================================
// §4.6: priority if statement
// =============================================================================
TEST(ParserSection4, Sec4_6_PriorityIf) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    priority if (a) x = 1;\n"
      "    else if (b) x = 2;\n"
      "    else x = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kPriority);
}

// =============================================================================
// §4.6: Program block for deterministic test scheduling
// =============================================================================
TEST(ParserSection4, Sec4_6_ProgramBlockDeterministicScheduling) {
  auto r = Parse(
      "program p;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->name, "p");
  EXPECT_EQ(r.cu->programs[0]->decl_kind, ModuleDeclKind::kProgram);
}

// =============================================================================
// §4.6: Program block with initial block
// =============================================================================
TEST(ParserSection4, Sec4_6_ProgramWithInitialBlock) {
  auto r = Parse(
      "program p;\n"
      "  initial begin\n"
      "    $display(\"test\");\n"
      "  end\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  ASSERT_EQ(r.cu->programs[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->items[0]->kind, ModuleItemKind::kInitialBlock);
}

// =============================================================================
// §4.6: Program block with final block
// =============================================================================
TEST(ParserSection4, Sec4_6_ProgramWithFinalBlock) {
  auto r = Parse(
      "program p;\n"
      "  final begin\n"
      "    $display(\"done\");\n"
      "  end\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  ASSERT_EQ(r.cu->programs[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->items[0]->kind, ModuleItemKind::kFinalBlock);
}

// =============================================================================
// §4.6: Blocking assignment ordering — sequential within block
// =============================================================================
TEST(ParserSection4, Sec4_6_BlockingAssignOrdering) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a = 1;\n"
      "    b = a;\n"
      "    c = b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  ASSERT_GE(body->stmts.size(), 3u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(body->stmts[2]->kind, StmtKind::kBlockingAssign);
}

// =============================================================================
// §4.6: Non-blocking assignment ordering
// =============================================================================
TEST(ParserSection4, Sec4_6_NonblockingAssignOrdering) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a <= 1;\n"
      "    b <= 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  ASSERT_GE(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kNonblockingAssign);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kNonblockingAssign);
}

// =============================================================================
// §4.6: Named begin-end block for deterministic scoping
// =============================================================================
TEST(ParserSection4, Sec4_6_NamedBeginEndScope) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : seq_blk\n"
      "    x = 1;\n"
      "    y = 2;\n"
      "  end : seq_blk\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  EXPECT_EQ(body->label, "seq_blk");
}

// =============================================================================
// §4.6: Ordered (positional) port connections — deterministic mapping
// =============================================================================
TEST(ParserSection4, Sec4_6_OrderedPortConnections) {
  auto r = Parse(
      "module top;\n"
      "  sub u1 (a, b, c);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  ASSERT_EQ(item->inst_ports.size(), 3u);
  // Positional ports have empty name (first element of pair).
  EXPECT_TRUE(item->inst_ports[0].first.empty());
  EXPECT_TRUE(item->inst_ports[1].first.empty());
  EXPECT_TRUE(item->inst_ports[2].first.empty());
  EXPECT_NE(item->inst_ports[0].second, nullptr);
  EXPECT_NE(item->inst_ports[1].second, nullptr);
  EXPECT_NE(item->inst_ports[2].second, nullptr);
}

// =============================================================================
// §4.6: Named port connections — deterministic mapping
// =============================================================================
TEST(ParserSection4, Sec4_6_NamedPortConnections) {
  auto r = Parse(
      "module top;\n"
      "  sub u1 (.clk(clk), .rst(rst), .d(data));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  ASSERT_EQ(item->inst_ports.size(), 3u);
  EXPECT_EQ(item->inst_ports[0].first, "clk");
  EXPECT_EQ(item->inst_ports[1].first, "rst");
  EXPECT_EQ(item->inst_ports[2].first, "d");
}

// =============================================================================
// §4.6: Variable initialization at declaration — static lifetime determinism
// =============================================================================
TEST(ParserSection4, Sec4_6_VarInitAtDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  int x = 42;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInt);
  EXPECT_NE(item->init_expr, nullptr);
}

// =============================================================================
// §4.6: Automatic variable initialization per entry
// =============================================================================
TEST(ParserSection4, Sec4_6_AutomaticVarInitPerEntry) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    automatic int count = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kVarDecl);
  EXPECT_TRUE(stmt->var_is_automatic);
  EXPECT_NE(stmt->var_init, nullptr);
}

// =============================================================================
// §4.6: always_comb with case inside
// =============================================================================
TEST(ParserSection4, Sec4_6_AlwaysCombWithCaseInside) {
  auto r = Parse(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic [3:0] y;\n"
      "  always_comb begin\n"
      "    case (sel)\n"
      "      2'b00: y = 4'h0;\n"
      "      2'b01: y = 4'h1;\n"
      "      2'b10: y = 4'h2;\n"
      "      default: y = 4'hf;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysComb);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_GE(item->body->stmts.size(), 1u);
  EXPECT_EQ(item->body->stmts[0]->kind, StmtKind::kCase);
}

// =============================================================================
// §4.6: always_ff with if-else chain
// =============================================================================
TEST(ParserSection4, Sec4_6_AlwaysFfWithIfElseChain) {
  auto r = Parse(
      "module m;\n"
      "  logic clk, rst, d, q;\n"
      "  always_ff @(posedge clk or posedge rst) begin\n"
      "    if (rst) q <= 0;\n"
      "    else q <= d;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysFF);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_GE(item->body->stmts.size(), 1u);
  EXPECT_EQ(item->body->stmts[0]->kind, StmtKind::kIf);
}

// =============================================================================
// §4.6: always_latch with if (no else)
// =============================================================================
TEST(ParserSection4, Sec4_6_AlwaysLatchIfNoElse) {
  auto r = Parse(
      "module m;\n"
      "  logic en, d, q;\n"
      "  always_latch\n"
      "    if (en) q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysLatch);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kIf);
  EXPECT_EQ(item->body->else_branch, nullptr);
}

// =============================================================================
// §4.6: Fork-join ordering — all branches complete
// =============================================================================
TEST(ParserSection4, Sec4_6_ForkJoinAllComplete) {
  auto r = Parse(
      "module m;\n"
      "  initial fork\n"
      "    a = 1;\n"
      "    b = 2;\n"
      "  join\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kFork);
  EXPECT_EQ(body->join_kind, TokenKind::kKwJoin);
}

// =============================================================================
// §4.6: Fork-join_any ordering — first branch completes
// =============================================================================
TEST(ParserSection4, Sec4_6_ForkJoinAnyFirstComplete) {
  auto r = Parse(
      "module m;\n"
      "  initial fork\n"
      "    a = 1;\n"
      "    b = 2;\n"
      "  join_any\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kFork);
  EXPECT_EQ(body->join_kind, TokenKind::kKwJoinAny);
}

// =============================================================================
// §4.6: Fork-join_none ordering — all branches concurrent
// =============================================================================
TEST(ParserSection4, Sec4_6_ForkJoinNoneConcurrent) {
  auto r = Parse(
      "module m;\n"
      "  initial fork\n"
      "    a = 1;\n"
      "    b = 2;\n"
      "  join_none\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kFork);
  EXPECT_EQ(body->join_kind, TokenKind::kKwJoinNone);
}

// =============================================================================
// §4.6: Priority case with default
// =============================================================================
TEST(ParserSection4, Sec4_6_PriorityCaseWithDefault) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    priority case (opcode)\n"
      "      4'h0: result = a + b;\n"
      "      4'h1: result = a - b;\n"
      "      4'h2: result = a & b;\n"
      "      default: result = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kPriority);
  EXPECT_TRUE(HasDefaultCaseItem(stmt));
}

// =============================================================================
// §4.6: Unique case with multiple matches listed
// =============================================================================
TEST(ParserSection4, Sec4_6_UniqueCaseMultipleItems) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    unique case (state)\n"
      "      IDLE: x = 0;\n"
      "      RUN: x = 1;\n"
      "      DONE: x = 2;\n"
      "      ERR: x = 3;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kUnique);
  EXPECT_EQ(stmt->case_items.size(), 4u);
}

// =============================================================================
// §4.6: always_comb with multiple outputs
// =============================================================================
TEST(ParserSection4, Sec4_6_AlwaysCombMultipleOutputs) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, sum, carry;\n"
      "  always_comb begin\n"
      "    sum = a ^ b;\n"
      "    carry = a & b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysComb);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  EXPECT_GE(item->body->stmts.size(), 2u);
}

// =============================================================================
// §4.6: Program block with clocking block reference
// =============================================================================
TEST(ParserSection4, Sec4_6_ProgramWithClockingBlock) {
  EXPECT_TRUE(
      ParseOk("program p(input logic clk);\n"
              "  clocking cb @(posedge clk);\n"
              "    input data;\n"
              "    output valid;\n"
              "  endclocking\n"
              "  initial begin\n"
              "    @(cb);\n"
              "    $display(\"synced\");\n"
              "  end\n"
              "endprogram\n"));
}

// =============================================================================
// §4.6: Static vs automatic function lifetime
// =============================================================================
TEST(ParserSection4, Sec4_6_StaticVsAutomaticFunctionLifetime) {
  auto r = Parse(
      "module m;\n"
      "  function automatic int auto_fn();\n"
      "    return 1;\n"
      "  endfunction\n"
      "  function static int static_fn();\n"
      "    return 2;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
  auto* auto_fn = r.cu->modules[0]->items[0];
  auto* static_fn = r.cu->modules[0]->items[1];
  EXPECT_EQ(auto_fn->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_TRUE(auto_fn->is_automatic);
  EXPECT_FALSE(auto_fn->is_static);
  EXPECT_EQ(static_fn->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_TRUE(static_fn->is_static);
  EXPECT_FALSE(static_fn->is_automatic);
}

// =============================================================================
// 1. Automatic function declaration parses (function automatic ...)
// =============================================================================
TEST(ParserSection4, Sec4_9_3_AutomaticFunctionDecl) {
  auto r = Parse(
      "module m;\n"
      "  function automatic int add(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_TRUE(item->is_automatic);
  EXPECT_FALSE(item->is_static);
  EXPECT_EQ(item->name, "add");
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kInt);
}

// =============================================================================
// 2. Static function declaration parses (function static ...)
// =============================================================================
TEST(ParserSection4, Sec4_9_3_StaticFunctionDecl) {
  auto r = Parse(
      "module m;\n"
      "  function static int counter();\n"
      "    return 0;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_TRUE(item->is_static);
  EXPECT_FALSE(item->is_automatic);
  EXPECT_EQ(item->name, "counter");
}

// =============================================================================
// 3. Automatic task declaration
// =============================================================================
TEST(ParserSection4, Sec4_9_3_AutomaticTaskDecl) {
  auto r = Parse(
      "module m;\n"
      "  task automatic do_work(input int n);\n"
      "    $display(\"work %0d\", n);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  EXPECT_TRUE(item->is_automatic);
  EXPECT_FALSE(item->is_static);
  EXPECT_EQ(item->name, "do_work");
}

// =============================================================================
// 4. Static task declaration
// =============================================================================
TEST(ParserSection4, Sec4_9_3_StaticTaskDecl) {
  auto r = Parse(
      "module m;\n"
      "  task static wait_cycles(input int n);\n"
      "    repeat (n) #1;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  EXPECT_TRUE(item->is_static);
  EXPECT_FALSE(item->is_automatic);
  EXPECT_EQ(item->name, "wait_cycles");
}

// =============================================================================
// 5. Automatic function with local variable declarations
// =============================================================================
TEST(ParserSection4, Sec4_9_3_AutomaticFuncWithLocalVars) {
  auto r = Parse(
      "module m;\n"
      "  function automatic int compute(int x);\n"
      "    int temp;\n"
      "    int result;\n"
      "    temp = x * 2;\n"
      "    result = temp + 1;\n"
      "    return result;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_TRUE(item->is_automatic);
  ASSERT_GE(item->func_body_stmts.size(), 2u);
  EXPECT_EQ(item->func_body_stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(item->func_body_stmts[1]->kind, StmtKind::kVarDecl);
}

// =============================================================================
// 6. Automatic function with recursive call (factorial)
// =============================================================================
TEST(ParserSection4, Sec4_9_3_AutomaticFuncRecursiveCall) {
  auto r = Parse(
      "module m;\n"
      "  function automatic int factorial(int n);\n"
      "    if (n <= 1)\n"
      "      return 1;\n"
      "    else\n"
      "      return n * factorial(n - 1);\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_TRUE(item->is_automatic);
  EXPECT_EQ(item->name, "factorial");
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kInt);
  ASSERT_GE(item->func_body_stmts.size(), 1u);
  EXPECT_EQ(item->func_body_stmts[0]->kind, StmtKind::kIf);
}

// =============================================================================
// 7. Static function with static local variable
// =============================================================================
TEST(ParserSection4, Sec4_9_3_StaticFuncWithStaticLocalVar) {
  auto r = Parse(
      "module m;\n"
      "  function static int call_count();\n"
      "    static int cnt = 0;\n"
      "    cnt = cnt + 1;\n"
      "    return cnt;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_static);
  auto* var_stmt = FirstBodyStmt(item);
  ASSERT_NE(var_stmt, nullptr);
  EXPECT_EQ(var_stmt->kind, StmtKind::kVarDecl);
  EXPECT_TRUE(var_stmt->var_is_static);
  EXPECT_FALSE(var_stmt->var_is_automatic);
  EXPECT_NE(var_stmt->var_init, nullptr);
}

// =============================================================================
// 8. Automatic function in automatic module
// =============================================================================
TEST(ParserSection4, Sec4_9_3_AutomaticFuncInAutoModule) {
  auto r = Parse(
      "module automatic m;\n"
      "  function int add(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(item->name, "add");
  // In an automatic module, functions without explicit qualifier inherit
  // automatic lifetime; the parser accepts this but does not set the flag
  // on the function itself (that is a semantic concern).
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kInt);
}

// =============================================================================
// 9. Function in program block (automatic by default)
// =============================================================================
TEST(ParserSection4, Sec4_9_3_FunctionInProgramBlock) {
  auto r = Parse(
      "program p;\n"
      "  function int get_value();\n"
      "    int local_v;\n"
      "    local_v = 42;\n"
      "    return local_v;\n"
      "  endfunction\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->decl_kind, ModuleDeclKind::kProgram);
  ASSERT_GE(r.cu->programs[0]->items.size(), 1u);
  auto* item = r.cu->programs[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(item->name, "get_value");
}

// =============================================================================
// 10. Explicit automatic var in static function
// =============================================================================
TEST(ParserSection4, Sec4_9_3_AutoVarInStaticFunc) {
  auto r = Parse(
      "module m;\n"
      "  function static int process(int x);\n"
      "    automatic int temp;\n"
      "    temp = x + 1;\n"
      "    return temp;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_static);
  auto* var_stmt = FirstBodyStmt(item);
  ASSERT_NE(var_stmt, nullptr);
  EXPECT_EQ(var_stmt->kind, StmtKind::kVarDecl);
  EXPECT_TRUE(var_stmt->var_is_automatic);
  EXPECT_FALSE(var_stmt->var_is_static);
}

// =============================================================================
// 11. Explicit static var in automatic function
// =============================================================================
TEST(ParserSection4, Sec4_9_3_StaticVarInAutoFunc) {
  auto r = Parse(
      "module m;\n"
      "  function automatic int accumulate(int x);\n"
      "    static int sum = 0;\n"
      "    sum = sum + x;\n"
      "    return sum;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_automatic);
  auto* var_stmt = FirstBodyStmt(item);
  ASSERT_NE(var_stmt, nullptr);
  EXPECT_EQ(var_stmt->kind, StmtKind::kVarDecl);
  EXPECT_TRUE(var_stmt->var_is_static);
  EXPECT_FALSE(var_stmt->var_is_automatic);
  EXPECT_EQ(var_stmt->var_name, "sum");
  EXPECT_NE(var_stmt->var_init, nullptr);
}

// =============================================================================
// 12. Automatic task with fork-join
// =============================================================================
TEST(ParserSection4, Sec4_9_3_AutomaticTaskWithForkJoin) {
  auto r = Parse(
      "module m;\n"
      "  task automatic parallel_work(input int a, input int b);\n"
      "    fork\n"
      "      $display(\"a=%0d\", a);\n"
      "      $display(\"b=%0d\", b);\n"
      "    join\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  EXPECT_TRUE(item->is_automatic);
  ASSERT_GE(item->func_body_stmts.size(), 1u);
  auto* fork_stmt = item->func_body_stmts[0];
  EXPECT_EQ(fork_stmt->kind, StmtKind::kFork);
  EXPECT_EQ(fork_stmt->join_kind, TokenKind::kKwJoin);
  EXPECT_GE(fork_stmt->fork_stmts.size(), 2u);
}

// =============================================================================
// 13. Automatic function with for loop variable
// =============================================================================
TEST(ParserSection4, Sec4_9_3_AutomaticFuncWithForLoop) {
  auto r = Parse(
      "module m;\n"
      "  function automatic int sum_to_n(int n);\n"
      "    int total;\n"
      "    total = 0;\n"
      "    for (int i = 0; i < n; i = i + 1)\n"
      "      total = total + i;\n"
      "    return total;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_automatic);
  auto* for_stmt = FindStmtByKind(item, StmtKind::kFor);
  ASSERT_NE(for_stmt, nullptr);
  EXPECT_NE(for_stmt->for_cond, nullptr);
  EXPECT_NE(for_stmt->for_body, nullptr);
}

// =============================================================================
// 14. Automatic function with multiple local vars of different types
// =============================================================================
TEST(ParserSection4, Sec4_9_3_AutoFuncMultiTypedLocalVars) {
  auto r = Parse(
      "module m;\n"
      "  function automatic int mixed_locals(int x);\n"
      "    int a;\n"
      "    logic [7:0] b;\n"
      "    real c;\n"
      "    a = x;\n"
      "    b = x;\n"
      "    c = x;\n"
      "    return a;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_automatic);
  ASSERT_GE(item->func_body_stmts.size(), 3u);
  EXPECT_EQ(item->func_body_stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(item->func_body_stmts[0]->var_decl_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(item->func_body_stmts[1]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(item->func_body_stmts[1]->var_decl_type.kind, DataTypeKind::kLogic);
  EXPECT_EQ(item->func_body_stmts[2]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(item->func_body_stmts[2]->var_decl_type.kind, DataTypeKind::kReal);
}

// =============================================================================
// 15. Automatic function with output argument
// =============================================================================
TEST(ParserSection4, Sec4_9_3_AutoFuncWithOutputArg) {
  auto r = Parse(
      "module m;\n"
      "  function automatic void compute(input int a, output int b);\n"
      "    b = a * 3;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_automatic);
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kVoid);
  ASSERT_EQ(item->func_args.size(), 2u);
  EXPECT_EQ(item->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(item->func_args[0].name, "a");
  EXPECT_EQ(item->func_args[1].direction, Direction::kOutput);
  EXPECT_EQ(item->func_args[1].name, "b");
}

}  // namespace
