#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// These unit tests embed SystemVerilog source as inline C++ string literals
// rather than loading external .sv files. This is intentional: each test is
// fully self-contained with the input source and structural assertions in one
// place, so a reader can understand what is being tested without
// cross-referencing a second file. When a test fails, the input and expected
// AST shape are visible together in the test output. Integration and
// conformance testing uses external .sv files instead: the CHIPS Alliance
// sv-tests suite validates broad language coverage, and the sim-tests under
// test/src/e2e/ verify end-to-end simulation behavior against .expected output
// files. This inline pattern is standard practice for compiler parser unit
// tests (used by LLVM, Clang, rustc, etc.).

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
};

static ParseResult Parse(const std::string &src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

TEST(Parser, EmptyModule) {
  auto r = Parse("module empty; endmodule");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  EXPECT_EQ(r.cu->modules[0]->name, "empty");
  EXPECT_TRUE(r.cu->modules[0]->items.empty());
}

TEST(Parser, ModuleWithInitialBlock) {
  auto r = Parse("module hello;\n"
                 "  initial $display(\"Hello\");\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  ASSERT_EQ(r.cu->modules[0]->items.size(), 1);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kInitialBlock);
}

TEST(Parser, ModuleWithPorts) {
  auto r = Parse(
      "module mux(input logic a, input logic b, input logic sel, output logic "
      "y);\n"
      "  assign y = sel ? b : a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *mod = r.cu->modules[0];
  struct Expected {
    Direction dir;
    const char *name;
  };
  Expected expected[] = {
      {Direction::kInput, "a"},
      {Direction::kInput, "b"},
      {Direction::kInput, "sel"},
      {Direction::kOutput, "y"},
  };
  ASSERT_EQ(mod->ports.size(), std::size(expected));
  for (size_t i = 0; i < std::size(expected); ++i) {
    EXPECT_EQ(mod->ports[i].direction, expected[i].dir) << "port " << i;
    EXPECT_EQ(mod->ports[i].name, expected[i].name) << "port " << i;
  }
}

TEST(Parser, ContinuousAssignment) {
  auto r = Parse("module top;\n"
                 "  logic a, b;\n"
                 "  assign a = b;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  bool found_assign = false;
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      found_assign = true;
    }
  }
  EXPECT_TRUE(found_assign);
}

TEST(Parser, AlwaysFFBlock) {
  auto r = Parse("module counter(input logic clk, rst);\n"
                 "  logic [7:0] count;\n"
                 "  always_ff @(posedge clk or posedge rst)\n"
                 "    if (rst) count <= '0;\n"
                 "    else count <= count + 1;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *mod = r.cu->modules[0];
  bool found_ff = false;
  for (auto *item : mod->items) {
    if (item->kind == ModuleItemKind::kAlwaysBlock &&
        item->always_kind == AlwaysKind::kAlwaysFF) {
      found_ff = true;
    }
  }
  EXPECT_TRUE(found_ff);
}

TEST(Parser, ExpressionPrecedence) {
  auto r = Parse("module expr;\n"
                 "  logic a;\n"
                 "  assign a = 1 + 2 * 3;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

// Helper to extract the first statement from an initial block.
static Stmt *FirstInitialStmt(ParseResult &r) {
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kInitialBlock) {
      if (item->body && item->body->kind == StmtKind::kBlock) {
        return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
      }
      return item->body;
    }
  }
  return nullptr;
}

TEST(Parser, DoWhileStatement) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    do x = x + 1; while (x < 10);\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDoWhile);
  EXPECT_NE(stmt->body, nullptr);
  EXPECT_NE(stmt->condition, nullptr);
}

TEST(Parser, BreakStatement) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    break;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBreak);
}

TEST(Parser, ContinueStatement) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    continue;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kContinue);
}

TEST(Parser, ReturnStatement) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    return;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kReturn);
}

TEST(Parser, ReturnWithValue) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    return 42;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kReturn);
  EXPECT_NE(stmt->expr, nullptr);
}

TEST(Parser, WaitStatement) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    wait (ready) x = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWait);
  EXPECT_NE(stmt->condition, nullptr);
  EXPECT_NE(stmt->body, nullptr);
}

TEST(Parser, DisableStatement) {
  auto r = Parse("module t;\n"
                 "  initial begin\n"
                 "    disable blk;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDisable);
  EXPECT_NE(stmt->expr, nullptr);
}

TEST(Parser, TypedefEnum) {
  auto r = Parse("module t;\n"
                 "  typedef enum { A, B, C } state_t;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(item->name, "state_t");
  EXPECT_EQ(item->typedef_type.kind, DataTypeKind::kEnum);
  std::string expected[] = {"A", "B", "C"};
  ASSERT_EQ(item->typedef_type.enum_members.size(), std::size(expected));
  for (size_t i = 0; i < std::size(expected); ++i) {
    EXPECT_EQ(item->typedef_type.enum_members[i].name, expected[i])
        << "member " << i;
  }
}

TEST(Parser, EnumWithValues) {
  auto r = Parse("module t;\n"
                 "  typedef enum { IDLE=0, RUN=1, STOP=2 } cmd_t;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto &members = r.cu->modules[0]->items[0]->typedef_type.enum_members;
  std::string expected[] = {"IDLE", "RUN", "STOP"};
  ASSERT_EQ(members.size(), std::size(expected));
  for (size_t i = 0; i < std::size(expected); ++i) {
    EXPECT_EQ(members[i].name, expected[i]) << "member " << i;
    EXPECT_NE(members[i].value, nullptr) << "member " << i;
  }
}

TEST(Parser, InlineEnumVar) {
  auto r = Parse("module t;\n"
                 "  enum { X, Y } my_var;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->name, "my_var");
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kEnum);
  ASSERT_EQ(item->data_type.enum_members.size(), 2);
}

TEST(Parser, FunctionDecl) {
  auto r = Parse("module t;\n"
                 "  function int add(input int a, input int b);\n"
                 "    return a + b;\n"
                 "  endfunction\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(item->name, "add");
  std::string expected[] = {"a", "b"};
  ASSERT_EQ(item->func_args.size(), std::size(expected));
  for (size_t i = 0; i < std::size(expected); ++i) {
    EXPECT_EQ(item->func_args[i].name, expected[i]) << "arg " << i;
  }
}

TEST(Parser, TaskDecl) {
  auto r = Parse("module t;\n"
                 "  task my_task(input int x);\n"
                 "    $display(\"%d\", x);\n"
                 "  endtask\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1);
  EXPECT_EQ(mod->items[0]->kind, ModuleItemKind::kTaskDecl);
  EXPECT_EQ(mod->items[0]->name, "my_task");
  ASSERT_EQ(mod->items[0]->func_args.size(), 1);
}

TEST(Parser, MultipleModules) {
  auto r = Parse("module a; endmodule\n"
                 "module b; endmodule\n"
                 "module c; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 3);
  EXPECT_EQ(r.cu->modules[0]->name, "a");
  EXPECT_EQ(r.cu->modules[1]->name, "b");
  EXPECT_EQ(r.cu->modules[2]->name, "c");
}

TEST(Parser, TypedefStruct) {
  auto r = Parse("module t;\n"
                 "  typedef struct {\n"
                 "    logic [7:0] a;\n"
                 "    int b;\n"
                 "  } my_struct_t;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(item->name, "my_struct_t");
  EXPECT_EQ(item->typedef_type.kind, DataTypeKind::kStruct);
  struct Expected {
    const char *name;
    DataTypeKind type_kind;
  };
  Expected expected[] = {
      {"a", DataTypeKind::kLogic},
      {"b", DataTypeKind::kInt},
  };
  auto &members = item->typedef_type.struct_members;
  ASSERT_EQ(members.size(), std::size(expected));
  for (size_t i = 0; i < std::size(expected); ++i) {
    EXPECT_EQ(members[i].name, expected[i].name) << "member " << i;
    EXPECT_EQ(members[i].type_kind, expected[i].type_kind) << "member " << i;
  }
}

TEST(Parser, TypedefUnion) {
  auto r = Parse("module t;\n"
                 "  typedef union {\n"
                 "    int i;\n"
                 "    real r;\n"
                 "  } my_union_t;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(item->typedef_type.kind, DataTypeKind::kUnion);
  ASSERT_EQ(item->typedef_type.struct_members.size(), 2);
}

TEST(Parser, TypedefStructPacked) {
  auto r = Parse("module t;\n"
                 "  typedef struct packed {\n"
                 "    logic [3:0] hi;\n"
                 "    logic [3:0] lo;\n"
                 "  } byte_t;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->typedef_type.kind, DataTypeKind::kStruct);
  EXPECT_TRUE(item->typedef_type.is_packed);
  ASSERT_EQ(item->typedef_type.struct_members.size(), 2);
}

TEST(Parser, InlineStructVar) {
  auto r = Parse("module t;\n"
                 "  struct { int x; int y; } point;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->name, "point");
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kStruct);
  ASSERT_EQ(item->data_type.struct_members.size(), 2);
}

TEST(Parser, EmptyPackage) {
  auto r = Parse("package my_pkg; endpackage");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->packages.size(), 1);
  EXPECT_EQ(r.cu->packages[0]->name, "my_pkg");
  EXPECT_TRUE(r.cu->packages[0]->items.empty());
}

TEST(Parser, PackageWithParam) {
  auto r = Parse("package my_pkg;\n"
                 "  parameter int WIDTH = 8;\n"
                 "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->packages.size(), 1);
  ASSERT_EQ(r.cu->packages[0]->items.size(), 1);
  EXPECT_EQ(r.cu->packages[0]->items[0]->kind, ModuleItemKind::kParamDecl);
}

TEST(Parser, ImportSpecific) {
  auto r = Parse("module t;\n"
                 "  import my_pkg::WIDTH;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kImportDecl);
  EXPECT_EQ(item->import_item.package_name, "my_pkg");
  EXPECT_EQ(item->import_item.item_name, "WIDTH");
  EXPECT_FALSE(item->import_item.is_wildcard);
}

TEST(Parser, ImportWildcard) {
  auto r = Parse("module t;\n"
                 "  import my_pkg::*;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kImportDecl);
  EXPECT_EQ(item->import_item.package_name, "my_pkg");
  EXPECT_TRUE(item->import_item.is_wildcard);
}

TEST(Parser, PackageAndModule) {
  auto r = Parse("package pkg; endpackage\n"
                 "module top; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->packages.size(), 1);
  ASSERT_EQ(r.cu->modules.size(), 1);
  EXPECT_EQ(r.cu->packages[0]->name, "pkg");
  EXPECT_EQ(r.cu->modules[0]->name, "top");
}

TEST(Parser, GenerateFor) {
  auto r = Parse("module t;\n"
                 "  genvar i;\n"
                 "  for (i = 0; i < 4; i = i + 1) begin\n"
                 "    assign a[i] = b[i];\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *mod = r.cu->modules[0];
  ModuleItem *gen = nullptr;
  for (auto *item : mod->items) {
    if (item->kind == ModuleItemKind::kGenerateFor) {
      gen = item;
    }
  }
  ASSERT_NE(gen, nullptr);
  EXPECT_NE(gen->gen_init, nullptr);
  EXPECT_NE(gen->gen_cond, nullptr);
  EXPECT_NE(gen->gen_step, nullptr);
  EXPECT_FALSE(gen->gen_body.empty());
}

TEST(Parser, GenerateIf) {
  auto r = Parse("module t;\n"
                 "  if (WIDTH > 8) begin\n"
                 "    assign a = b;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1);
  EXPECT_EQ(mod->items[0]->kind, ModuleItemKind::kGenerateIf);
  EXPECT_NE(mod->items[0]->gen_cond, nullptr);
  EXPECT_FALSE(mod->items[0]->gen_body.empty());
}

TEST(Parser, GenerateIfElse) {
  auto r = Parse("module t;\n"
                 "  if (WIDTH > 8) begin\n"
                 "    assign a = b;\n"
                 "  end else begin\n"
                 "    assign a = c;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGenerateIf);
  EXPECT_NE(item->gen_else, nullptr);
}

TEST(Parser, GenerateRegion) {
  auto r = Parse("module t;\n"
                 "  generate\n"
                 "    if (WIDTH > 8) begin\n"
                 "      assign a = b;\n"
                 "    end\n"
                 "  endgenerate\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *mod = r.cu->modules[0];
  bool found_gen = false;
  for (auto *item : mod->items) {
    if (item->kind == ModuleItemKind::kGenerateIf) {
      found_gen = true;
    }
  }
  EXPECT_TRUE(found_gen);
}

TEST(Parser, GenerateCase) {
  auto r = Parse("module t;\n"
                 "  case (WIDTH)\n"
                 "    1: begin\n"
                 "      assign a = b;\n"
                 "    end\n"
                 "    2: begin\n"
                 "      assign a = c;\n"
                 "    end\n"
                 "  endcase\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGenerateCase);
  EXPECT_NE(item->gen_cond, nullptr);
  ASSERT_EQ(item->gen_case_items.size(), 2);
  for (size_t i = 0; i < 2; ++i) {
    EXPECT_FALSE(item->gen_case_items[i].is_default) << "case item " << i;
    EXPECT_EQ(item->gen_case_items[i].patterns.size(), 1) << "case item " << i;
    EXPECT_FALSE(item->gen_case_items[i].body.empty()) << "case item " << i;
  }
}

TEST(Parser, GenerateCaseDefault) {
  auto r = Parse("module t;\n"
                 "  case (WIDTH)\n"
                 "    1: begin\n"
                 "      assign a = b;\n"
                 "    end\n"
                 "    default: begin\n"
                 "      assign a = c;\n"
                 "    end\n"
                 "  endcase\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->gen_case_items.size(), 2);
  EXPECT_TRUE(item->gen_case_items[1].is_default);
}

TEST(Parser, GenerateCaseMultiPattern) {
  auto r = Parse("module t;\n"
                 "  case (WIDTH)\n"
                 "    1, 2: begin\n"
                 "      assign a = b;\n"
                 "    end\n"
                 "  endcase\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->gen_case_items.size(), 1);
  EXPECT_EQ(item->gen_case_items[0].patterns.size(), 2);
}

TEST(Parser, GenerateCaseInRegion) {
  auto r = Parse("module t;\n"
                 "  generate\n"
                 "    case (WIDTH)\n"
                 "      1: begin\n"
                 "        assign a = b;\n"
                 "      end\n"
                 "    endcase\n"
                 "  endgenerate\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  bool found = false;
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kGenerateCase) {
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

// --- Gate primitive tests ---

TEST(Parser, GateAndInst) {
  auto r = Parse("module t; and g1(out, a, b); endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGateInst);
  EXPECT_EQ(item->gate_kind, GateKind::kAnd);
  EXPECT_EQ(item->gate_inst_name, "g1");
  EXPECT_EQ(item->gate_terminals.size(), 3u);
}

TEST(Parser, GateNandWithDelay) {
  auto r = Parse("module t; nand #(5) g2(out, a, b); endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->gate_kind, GateKind::kNand);
  EXPECT_EQ(item->gate_inst_name, "g2");
  EXPECT_NE(item->gate_delay, nullptr);
  EXPECT_EQ(item->gate_terminals.size(), 3u);
}

TEST(Parser, GateBufMultiOutput) {
  auto r = Parse("module t; buf (o1, o2, in); endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGateInst);
  EXPECT_EQ(item->gate_kind, GateKind::kBuf);
  EXPECT_TRUE(item->gate_inst_name.empty());
  EXPECT_EQ(item->gate_terminals.size(), 3);
}

TEST(Parser, GateBufif0) {
  auto r = Parse("module t; bufif0 b1(out, in, en); endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGateInst);
  EXPECT_EQ(item->gate_kind, GateKind::kBufif0);
  EXPECT_EQ(item->gate_terminals.size(), 3);
}

TEST(Parser, GateTran) {
  auto r = Parse("module t; tran (a, b); endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGateInst);
  EXPECT_EQ(item->gate_kind, GateKind::kTran);
  EXPECT_EQ(item->gate_terminals.size(), 2);
}

TEST(Parser, GateNmos) {
  auto r = Parse("module t; nmos (out, in, ctrl); endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGateInst);
  EXPECT_EQ(item->gate_kind, GateKind::kNmos);
  EXPECT_EQ(item->gate_terminals.size(), 3);
}

TEST(Parser, GateCmos) {
  auto r = Parse("module t; cmos (out, in, nctrl, pctrl); endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGateInst);
  EXPECT_EQ(item->gate_kind, GateKind::kCmos);
  EXPECT_EQ(item->gate_terminals.size(), 4);
}

TEST(Parser, GatePullup) {
  auto r = Parse("module t; pullup (o); endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGateInst);
  EXPECT_EQ(item->gate_kind, GateKind::kPullup);
  EXPECT_EQ(item->gate_terminals.size(), 1);
}

TEST(Parser, GateNoInstanceName) {
  auto r = Parse("module t; and (out, a, b); endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGateInst);
  EXPECT_EQ(item->gate_kind, GateKind::kAnd);
  EXPECT_TRUE(item->gate_inst_name.empty());
  EXPECT_EQ(item->gate_terminals.size(), 3);
}

// --- Interface/modport tests ---

TEST(Parser, EmptyInterface) {
  auto r = Parse("interface simple_bus; endinterface");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->interfaces.size(), 1);
  EXPECT_EQ(r.cu->interfaces[0]->name, "simple_bus");
  EXPECT_EQ(r.cu->interfaces[0]->decl_kind, ModuleDeclKind::kInterface);
}

TEST(Parser, InterfaceWithPorts) {
  auto r = Parse("interface bus(input logic clk, input logic rst);\n"
                 "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->interfaces.size(), 1);
  EXPECT_EQ(r.cu->interfaces[0]->ports.size(), 2);
}

TEST(Parser, InterfaceWithModport) {
  auto r = Parse("interface bus;\n"
                 "  logic [7:0] data;\n"
                 "  modport master(output data);\n"
                 "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->interfaces[0]->modports.size(), 1);
  auto *mp = r.cu->interfaces[0]->modports[0];
  EXPECT_EQ(mp->name, "master");
  struct Expected {
    Direction dir;
    const char *name;
  };
  Expected expected[] = {{Direction::kOutput, "data"}};
  ASSERT_EQ(mp->ports.size(), std::size(expected));
  for (size_t i = 0; i < std::size(expected); ++i) {
    EXPECT_EQ(mp->ports[i].direction, expected[i].dir) << "port " << i;
    EXPECT_EQ(mp->ports[i].name, expected[i].name) << "port " << i;
  }
}

TEST(Parser, ModportMultipleGroups) {
  auto r = Parse("interface bus;\n"
                 "  logic addr;\n"
                 "  logic data;\n"
                 "  modport slave(input addr, input data);\n"
                 "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  auto *mp = r.cu->interfaces[0]->modports[0];
  EXPECT_EQ(mp->name, "slave");
  ASSERT_EQ(mp->ports.size(), 2);
  EXPECT_EQ(mp->ports[0].direction, Direction::kInput);
  EXPECT_EQ(mp->ports[1].direction, Direction::kInput);
}

// --- Program tests ---

TEST(Parser, EmptyProgram) {
  auto r = Parse("program test_prog; endprogram");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->programs.size(), 1);
  EXPECT_EQ(r.cu->programs[0]->name, "test_prog");
  EXPECT_EQ(r.cu->programs[0]->decl_kind, ModuleDeclKind::kProgram);
}

TEST(Parser, ProgramWithInitial) {
  auto r = Parse("program test_prog;\n"
                 "  initial $display(\"hello\");\n"
                 "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->programs.size(), 1);
  EXPECT_EQ(r.cu->programs[0]->items.size(), 1);
  EXPECT_EQ(r.cu->programs[0]->items[0]->kind, ModuleItemKind::kInitialBlock);
}

TEST(Parser, InterfaceAndModule) {
  auto r = Parse("interface bus; endinterface\n"
                 "module top; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->interfaces.size(), 1);
  EXPECT_EQ(r.cu->modules.size(), 1);
}

// --- Class tests ---

TEST(Parser, EmptyClass) {
  auto r = Parse("class empty_cls; endclass");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1);
  EXPECT_EQ(r.cu->classes[0]->name, "empty_cls");
  EXPECT_FALSE(r.cu->classes[0]->is_virtual);
}

TEST(Parser, ClassWithProperty) {
  auto r = Parse("class pkt; int data; endclass");
  ASSERT_NE(r.cu, nullptr);
  auto *cls = r.cu->classes[0];
  ASSERT_EQ(cls->members.size(), 1);
  EXPECT_EQ(cls->members[0]->kind, ClassMemberKind::kProperty);
  EXPECT_EQ(cls->members[0]->name, "data");
  EXPECT_EQ(cls->members[0]->data_type.kind, DataTypeKind::kInt);
}

TEST(Parser, ClassWithMethod) {
  auto r = Parse("class pkt;\n"
                 "  function int get_data();\n"
                 "    return data;\n"
                 "  endfunction\n"
                 "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  auto *cls = r.cu->classes[0];
  ASSERT_EQ(cls->members.size(), 1);
  EXPECT_EQ(cls->members[0]->kind, ClassMemberKind::kMethod);
  EXPECT_NE(cls->members[0]->method, nullptr);
}

TEST(Parser, ClassExtends) {
  auto r = Parse("class child extends parent; endclass");
  ASSERT_NE(r.cu, nullptr);
  auto *cls = r.cu->classes[0];
  EXPECT_EQ(cls->name, "child");
  EXPECT_EQ(cls->base_class, "parent");
}

TEST(Parser, VirtualClass) {
  auto r = Parse("virtual class base; endclass");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.cu->classes[0]->is_virtual);
}

TEST(Parser, ClassPropertyQualifiers) {
  auto r = Parse("class pkt;\n"
                 "  rand int data;\n"
                 "  local int secret;\n"
                 "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  auto *cls = r.cu->classes[0];
  ASSERT_EQ(cls->members.size(), 2);
  EXPECT_TRUE(cls->members[0]->is_rand);
  EXPECT_TRUE(cls->members[1]->is_local);
}

// --- Defparam tests ---

TEST(Parser, DefparamSingle) {
  auto r = Parse("module top;\n"
                 "  defparam u0.WIDTH = 8;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kDefparam);
  ASSERT_EQ(item->defparam_assigns.size(), 1);
  EXPECT_NE(item->defparam_assigns[0].first, nullptr);
  EXPECT_NE(item->defparam_assigns[0].second, nullptr);
}

TEST(Parser, DefparamMultiple) {
  auto r = Parse("module top;\n"
                 "  defparam u0.WIDTH = 8, u1.DEPTH = 16;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kDefparam);
  EXPECT_EQ(item->defparam_assigns.size(), 2);
}

// --- Named event tests ---

TEST(Parser, EventDeclaration) {
  auto r = Parse("module t;\n"
                 "  event ev;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kEvent);
  EXPECT_EQ(item->name, "ev");
}

TEST(Parser, EventTrigger) {
  auto r = Parse("module t;\n"
                 "  event ev;\n"
                 "  initial ->ev;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = r.cu->modules[0]->items[1]->body;
  EXPECT_EQ(stmt->kind, StmtKind::kEventTrigger);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kIdentifier);
  EXPECT_EQ(stmt->expr->text, "ev");
}

TEST(Parser, EventWaitWithParens) {
  auto r = Parse("module t;\n"
                 "  event ev;\n"
                 "  initial @(ev) ;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[1];
  auto *stmt = item->body;
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_EQ(stmt->events.size(), 1);
  EXPECT_EQ(stmt->events[0].edge, Edge::kNone);
  EXPECT_EQ(stmt->events[0].signal->text, "ev");
}

TEST(Parser, EventWaitBareIdentifier) {
  auto r = Parse("module t;\n"
                 "  event ev;\n"
                 "  initial @ev ;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[1];
  auto *stmt = item->body;
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_EQ(stmt->events.size(), 1);
  EXPECT_EQ(stmt->events[0].edge, Edge::kNone);
  EXPECT_EQ(stmt->events[0].signal->text, "ev");
}

// --- User-defined nettype tests ---

TEST(Parser, NettypeDeclaration) {
  auto r = Parse("module t;\n"
                 "  nettype logic [7:0] mynet;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNettypeDecl);
  EXPECT_EQ(item->name, "mynet");
}

TEST(Parser, NettypeWithResolutionFunction) {
  auto r = Parse("module t;\n"
                 "  nettype logic [7:0] mynet with resolve_fn;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNettypeDecl);
  EXPECT_EQ(item->name, "mynet");
  EXPECT_EQ(item->nettype_resolve_func, "resolve_fn");
}

TEST(Parser, NettypeUsedInDecl) {
  auto r = Parse("module t;\n"
                 "  nettype logic [7:0] mynet;\n"
                 "  mynet x;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  // nettype registers as known type, so 'mynet x;' parses as a VarDecl.
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
  auto *item = r.cu->modules[0]->items[1];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->name, "x");
}
