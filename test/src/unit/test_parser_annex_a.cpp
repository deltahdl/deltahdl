#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// --- Test helpers ---

namespace {

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string& src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

Stmt* FirstInitialStmt(ParseResult& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

}  // namespace

// =============================================================================
// A.1 -- Source text productions
// =============================================================================

TEST(ParserAnnexA, A1ModuleDecl) {
  auto r = Parse("module m; endmodule");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
  EXPECT_TRUE(r.cu->modules[0]->items.empty());
}

TEST(ParserAnnexA, A1ModuleWithParams) {
  auto r = Parse(
      "module m #(parameter W = 8, parameter D = 4)(\n"
      "  input logic [W-1:0] data\n"
      ");\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->params.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->ports.size(), 1u);
}

TEST(ParserAnnexA, A1InterfaceDecl) {
  auto r = Parse(
      "interface bus_if;\n"
      "  logic [7:0] data;\n"
      "  modport master(output data);\n"
      "  modport slave(input data);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->name, "bus_if");
  EXPECT_EQ(r.cu->interfaces[0]->modports.size(), 2u);
}

TEST(ParserAnnexA, A1ProgramDecl) {
  auto r = Parse(
      "program test_prog(input logic clk);\n"
      "  initial $display(\"Hello\");\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->name, "test_prog");
}

TEST(ParserAnnexA, A1PackageDecl) {
  auto r = Parse(
      "package pkg;\n"
      "  parameter int W = 8;\n"
      "  typedef logic [W-1:0] word_t;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "pkg");
}

TEST(ParserAnnexA, A1CheckerDecl) {
  auto r = Parse("checker chk; endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->name, "chk");
}

TEST(ParserAnnexA, A1CompilationUnitMultipleItems) {
  auto r = Parse(
      "package p; endpackage\n"
      "module m; endmodule\n"
      "interface i; endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->interfaces.size(), 1u);
}

TEST(ParserAnnexA, A1ModulePortDirections) {
  auto r = Parse(
      "module m(input logic a, output logic b,\n"
      "         inout wire c, ref logic d);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& ports = r.cu->modules[0]->ports;
  ASSERT_EQ(ports.size(), 4u);
  EXPECT_EQ(ports[0].direction, Direction::kInput);
  EXPECT_EQ(ports[1].direction, Direction::kOutput);
  EXPECT_EQ(ports[2].direction, Direction::kInout);
  EXPECT_EQ(ports[3].direction, Direction::kRef);
}

// =============================================================================
// A.2 -- Declarations
// =============================================================================

TEST(ParserAnnexA, A2NetDeclWire) {
  auto r = Parse("module m; wire [3:0] w; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kNetDecl);
}

TEST(ParserAnnexA, A2NetDeclTriWandWor) {
  auto r = Parse("module m; tri t; wand wa; wor wo; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items.size(), 3u);
}

TEST(ParserAnnexA, A2VarDeclWithInit) {
  auto r = Parse("module m; logic [7:0] data = 8'hFF; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kVarDecl);
  EXPECT_NE(r.cu->modules[0]->items[0]->init_expr, nullptr);
}

TEST(ParserAnnexA, A2ParamDecl) {
  auto r = Parse(
      "module m;\n"
      "  parameter int WIDTH = 16;\n"
      "  localparam int DEPTH = 32;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(r.cu->modules[0]->items[1]->kind, ModuleItemKind::kParamDecl);
}

TEST(ParserAnnexA, A2TypedefEnumWithBase) {
  auto r = Parse(
      "module m;\n"
      "  typedef enum logic [1:0] {IDLE, RUN, DONE} state_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kTypedef);
}

TEST(ParserAnnexA, A2TypedefStructPacked) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct packed {\n"
      "    logic [7:0] addr;\n"
      "    logic [31:0] data;\n"
      "  } req_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kTypedef);
}

TEST(ParserAnnexA, A2FunctionDeclAutomatic) {
  auto r = Parse(
      "module m;\n"
      "  function automatic int add(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(item->name, "add");
  EXPECT_TRUE(item->is_automatic);
  EXPECT_EQ(item->func_args.size(), 2u);
}

TEST(ParserAnnexA, A2TaskDecl) {
  auto r = Parse(
      "module m;\n"
      "  task automatic drive(input logic [7:0] val);\n"
      "    data = val;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  EXPECT_EQ(item->name, "drive");
}

TEST(ParserAnnexA, A2ClassDecl) {
  auto r = Parse(
      "class Packet;\n"
      "  rand bit [7:0] payload;\n"
      "  function void display();\n"
      "    $display(\"pkt\");\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "Packet");
  EXPECT_EQ(r.cu->classes[0]->members.size(), 2u);
}

TEST(ParserAnnexA, A2ClassWithConstraint) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c1 { x > 0; x < 100; }\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ParserAnnexA, A2CovergroupDecl) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg @(posedge clk);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserAnnexA, A2ContinuousAssignWithDelay) {
  auto r = Parse("module m; wire y; assign #5 y = a; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      EXPECT_NE(item->assign_delay, nullptr);
    }
  }
}

// =============================================================================
// A.3 -- Primitive instances (gate_instantiation)
// =============================================================================

TEST(ParserAnnexA, A3GateInstNInput) {
  auto r = Parse(
      "module m;\n"
      "  and g1(y, a, b, c);\n"
      "  nand g2(y2, a, b);\n"
      "  xor g3(y3, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int gate_count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kGateInst) gate_count++;
  }
  EXPECT_EQ(gate_count, 3);
}

TEST(ParserAnnexA, A3GateInstWithStrengthAndDelay) {
  auto r = Parse("module m; and (strong0, weak1) #5 g(y, a, b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.4 -- Instantiations
// =============================================================================

TEST(ParserAnnexA, A4ModuleInstPositional) {
  auto r = Parse("module m; sub u0(a, b, c); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "sub");
  EXPECT_EQ(item->inst_name, "u0");
}

TEST(ParserAnnexA, A4ModuleInstNamed) {
  auto r = Parse("module m; sub u0(.clk(clk), .data(data)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_ports.size(), 2u);
}

TEST(ParserAnnexA, A4ModuleInstWithParams) {
  auto r = Parse("module m; sub #(8, 4) u0(.clk(clk)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_params.size(), 2u);
}

TEST(ParserAnnexA, A4GenerateForBlock) {
  auto r = Parse(
      "module m;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 4; i = i + 1) begin\n"
      "    wire w;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kGenerateFor) found = true;
  }
  EXPECT_TRUE(found);
}

TEST(ParserAnnexA, A4GenerateIfElse) {
  auto r = Parse(
      "module m;\n"
      "  if (WIDTH > 8) begin\n"
      "    wire [15:0] bus;\n"
      "  end else begin\n"
      "    wire [7:0] bus;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kGenerateIf) {
      found = true;
      EXPECT_NE(item->gen_else, nullptr);
    }
  }
  EXPECT_TRUE(found);
}

TEST(ParserAnnexA, A4GenerateCase) {
  auto r = Parse(
      "module m;\n"
      "  case (WIDTH)\n"
      "    8: begin\n"
      "      wire [7:0] d;\n"
      "    end\n"
      "    default: begin\n"
      "      wire [31:0] d;\n"
      "    end\n"
      "  endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGenerateCase);
  EXPECT_EQ(item->gen_case_items.size(), 2u);
}

TEST(ParserAnnexA, A4GenerateRegion) {
  auto r = Parse(
      "module m;\n"
      "  generate\n"
      "    wire w;\n"
      "  endgenerate\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.5 -- UDP declarations
// =============================================================================

TEST(ParserAnnexA, A5UdpCombinational) {
  auto r = Parse(
      "primitive mux2(output y, input a, input b, input s);\n"
      "  table\n"
      "    0 ? 0 : 0 ;\n"
      "    1 ? 0 : 1 ;\n"
      "    ? 0 1 : 0 ;\n"
      "    ? 1 1 : 1 ;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_EQ(r.cu->udps[0]->name, "mux2");
  EXPECT_FALSE(r.cu->udps[0]->is_sequential);
}

TEST(ParserAnnexA, A5UdpSequential) {
  auto r = Parse(
      "primitive dff(output reg q, input d, input clk);\n"
      "  table\n"
      "    0 r : ? : 0 ;\n"
      "    1 r : ? : 1 ;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_TRUE(r.cu->udps[0]->is_sequential);
}

// =============================================================================
// A.6 -- Behavioral statements
// =============================================================================

TEST(ParserAnnexA, A6AlwaysFFWithSensitivity) {
  auto r = Parse(
      "module m;\n"
      "  always_ff @(posedge clk) q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysBlock &&
        item->always_kind == AlwaysKind::kAlwaysFF)
      found = true;
  }
  EXPECT_TRUE(found);
}

TEST(ParserAnnexA, A6AlwaysLatch) {
  auto r = Parse(
      "module m;\n"
      "  always_latch if (en) q = d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserAnnexA, A6InitialAndFinalBlocks) {
  auto r = Parse(
      "module m;\n"
      "  initial $display(\"start\");\n"
      "  final $display(\"end\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  bool found_init = false, found_final = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kInitialBlock) found_init = true;
    if (item->kind == ModuleItemKind::kFinalBlock) found_final = true;
  }
  EXPECT_TRUE(found_init);
  EXPECT_TRUE(found_final);
}

TEST(ParserAnnexA, A6BlockingAndNonblocking) {
  auto r = Parse(
      "module m;\n"
      "  initial begin a = 1; b <= 2; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* blk = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(blk, nullptr);
  ASSERT_EQ(blk->stmts.size(), 2u);
  EXPECT_EQ(blk->stmts[0]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(blk->stmts[1]->kind, StmtKind::kNonblockingAssign);
}

TEST(ParserAnnexA, A6IfElseStmt) {
  auto r = Parse(
      "module m;\n"
      "  initial begin if (a) x = 1; else x = 0; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_NE(stmt->else_branch, nullptr);
}

TEST(ParserAnnexA, A6ForLoop) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; i++) x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_NE(stmt->for_init, nullptr);
  EXPECT_NE(stmt->for_cond, nullptr);
  EXPECT_NE(stmt->for_step, nullptr);
}

TEST(ParserAnnexA, A6WhileLoop) {
  auto r = Parse(
      "module m;\n"
      "  initial begin while (x > 0) x = x - 1; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWhile);
}

TEST(ParserAnnexA, A6DoWhileLoop) {
  auto r = Parse(
      "module m;\n"
      "  initial begin do x = x - 1; while (x > 0); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDoWhile);
}

TEST(ParserAnnexA, A6ForeverLoop) {
  auto r = Parse(
      "module m;\n"
      "  initial begin forever #5 clk = ~clk; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForever);
}

TEST(ParserAnnexA, A6RepeatLoop) {
  auto r = Parse(
      "module m;\n"
      "  initial begin repeat (10) @(posedge clk); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRepeat);
}

TEST(ParserAnnexA, A6CaseStmt) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case(x) 0: y = 1; default: y = 0; endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  ASSERT_EQ(stmt->case_items.size(), 2u);
  EXPECT_FALSE(stmt->case_items[0].is_default);
  EXPECT_TRUE(stmt->case_items[1].is_default);
}

TEST(ParserAnnexA, A6ForkJoinVariants) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork #10 a = 1; #20 b = 1; join\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->join_kind, TokenKind::kKwJoin);
}

TEST(ParserAnnexA, A6ForkJoinAny) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork #10 a = 1; join_any\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  EXPECT_EQ(stmt->join_kind, TokenKind::kKwJoinAny);
}

TEST(ParserAnnexA, A6ForkJoinNone) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork #10 a = 1; join_none\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  EXPECT_EQ(stmt->join_kind, TokenKind::kKwJoinNone);
}

TEST(ParserAnnexA, A6EventTrigger) {
  auto r = Parse("module m; initial begin -> ev; end endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventTrigger);
}

TEST(ParserAnnexA, A6WaitStmt) {
  auto r = Parse("module m; initial begin wait (ready) x = 1; end endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  EXPECT_EQ(stmt->kind, StmtKind::kWait);
}

TEST(ParserAnnexA, A6DelayControl) {
  auto r = Parse("module m; initial begin #10 x = 1; end endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  EXPECT_EQ(stmt->kind, StmtKind::kDelay);
}

TEST(ParserAnnexA, A6EventControl) {
  auto r =
      Parse("module m; initial begin @(posedge clk) x = 1; end endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
}

TEST(ParserAnnexA, A6ProceduralAssignForce) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assign x = 1; deassign x;\n"
      "    force y = 0; release y;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* blk = r.cu->modules[0]->items[0]->body;
  ASSERT_EQ(blk->stmts.size(), 4u);
  EXPECT_EQ(blk->stmts[0]->kind, StmtKind::kAssign);
  EXPECT_EQ(blk->stmts[1]->kind, StmtKind::kDeassign);
  EXPECT_EQ(blk->stmts[2]->kind, StmtKind::kForce);
  EXPECT_EQ(blk->stmts[3]->kind, StmtKind::kRelease);
}

TEST(ParserAnnexA, A6ReturnStmt) {
  auto r = Parse(
      "module m;\n"
      "  function int f(); return 42; endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_body_stmts.size(), 1u);
  EXPECT_EQ(item->func_body_stmts[0]->kind, StmtKind::kReturn);
}

TEST(ParserAnnexA, A6ForeachStmt) {
  auto r = Parse(
      "module m;\n"
      "  initial begin foreach (arr[i]) $display(arr[i]); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  EXPECT_EQ(stmt->kind, StmtKind::kForeach);
}

TEST(ParserAnnexA, A6DisableStmt) {
  auto r = Parse("module m; initial begin disable blk; end endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  EXPECT_EQ(stmt->kind, StmtKind::kDisable);
}

// =============================================================================
// A.7 -- Specify section
// =============================================================================

TEST(ParserAnnexA, A7SpecifyParallelPath) {
  auto r = Parse("module m; specify (a => b) = 5; endspecify endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kSpecifyBlock);
  ASSERT_GE(r.cu->modules[0]->items[0]->specify_items.size(), 1u);
}

TEST(ParserAnnexA, A7SpecifyFullPath) {
  auto r =
      Parse("module m; specify (a, b *> c, d) = 10; endspecify endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserAnnexA, A7TimingCheckSetup) {
  auto r = Parse(
      "module m;\n"
      "  specify $setup(data, posedge clk, 10); endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserAnnexA, A7TimingCheckHold) {
  auto r = Parse(
      "module m;\n"
      "  specify $hold(posedge clk, data, 5); endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserAnnexA, A7SpecparamInSpecify) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam tRISE = 100;\n"
      "    (a => b) = tRISE;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.8 -- Expressions
// =============================================================================

TEST(ParserAnnexA, A8TernaryExpr) {
  auto r = Parse("module m; initial x = (a > b) ? a : b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kTernary);
}

TEST(ParserAnnexA, A8Concatenation) {
  auto r = Parse("module m; initial x = {a, b, c}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(stmt->rhs->elements.size(), 3u);
}

TEST(ParserAnnexA, A8Replication) {
  auto r = Parse("module m; initial x = {4{a}}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kReplicate);
}

TEST(ParserAnnexA, A8SystemFunctionCall) {
  auto r = Parse(
      "module m; initial begin $display(\"v=%0d\", x); $finish; end "
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserAnnexA, A8MemberAccess) {
  auto r = Parse("module m; initial x = s.field; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kMemberAccess);
}

TEST(ParserAnnexA, A8BitAndPartSelect) {
  auto r = Parse(
      "module m;\n"
      "  initial begin x = data[3]; y = data[7:4]; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserAnnexA, A8FunctionCallExpr) {
  auto r = Parse("module m; initial x = func(a, b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kCall);
}

TEST(ParserAnnexA, A8IntegerLiterals) {
  auto r = Parse(
      "module m;\n"
      "  initial begin a = 42; b = 8'hFF; c = 4'b1010; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.9 -- General (attributes, identifiers)
// =============================================================================

TEST(ParserAnnexA, A9AttributeOnContAssign) {
  auto r = Parse("module m; wire y; (* synthesis *) assign y = 1; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserAnnexA, A9AttributeWithValue) {
  auto r = Parse("module m; (* max_fanout = 8 *) wire w; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserAnnexA, A9DefparamDecl) {
  auto r = Parse("module m; defparam u.WIDTH = 16; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kDefparam) found = true;
  }
  EXPECT_TRUE(found);
}

// =============================================================================
// Annex D -- Optional system tasks
// =============================================================================

TEST(ParserAnnexD, AnnexDCountdrivers) {
  auto r = Parse("module m; initial $countdrivers(sig); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSystemCall);
}

TEST(ParserAnnexD, AnnexDList) {
  auto r = Parse("module m; initial $list; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSystemCall);
}

TEST(ParserAnnexD, AnnexDLog) {
  auto r = Parse(
      "module m;\n"
      "  initial begin $log(\"sim.log\"); $nolog; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserAnnexD, AnnexDSave) {
  auto r = Parse(
      "module m;\n"
      "  initial begin $save(\"s.sav\"); $restart(\"s.sav\"); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserAnnexD, AnnexDScope) {
  auto r = Parse(
      "module m;\n"
      "  initial begin $scope(m); $showscopes; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

// =============================================================================
// Annex E -- Optional compiler directives
// =============================================================================

TEST(ParserAnnexE, AnnexEDefaultDecayTime) {
  auto r = Parse("`default_decay_time 10\nmodule m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  if (r.cu->modules.size() >= 1u) {
    EXPECT_EQ(r.cu->modules[0]->name, "m");
  }
}

TEST(ParserAnnexE, AnnexEDelayModeZero) {
  auto r = Parse("`delay_mode_zero\nmodule m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  if (r.cu->modules.size() >= 1u) {
    EXPECT_EQ(r.cu->modules[0]->name, "m");
  }
}

TEST(ParserAnnexE, AnnexEMultipleDirectives) {
  auto r = Parse(
      "`default_decay_time 100\n"
      "`delay_mode_distributed\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  if (r.cu->modules.size() >= 1u) {
    EXPECT_EQ(r.cu->modules[0]->name, "m");
  }
}
