#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult Parse(const std::string& src) {
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
  auto r = Parse(
      "module hello;\n"
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
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 4);
  EXPECT_EQ(mod->ports[0].direction, Direction::kInput);
  EXPECT_EQ(mod->ports[0].name, "a");
  EXPECT_EQ(mod->ports[3].direction, Direction::kOutput);
  EXPECT_EQ(mod->ports[3].name, "y");
}

TEST(Parser, ContinuousAssignment) {
  auto r = Parse(
      "module top;\n"
      "  logic a, b;\n"
      "  assign a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  bool found_assign = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      found_assign = true;
    }
  }
  EXPECT_TRUE(found_assign);
}

TEST(Parser, AlwaysFFBlock) {
  auto r = Parse(
      "module counter(input logic clk, rst);\n"
      "  logic [7:0] count;\n"
      "  always_ff @(posedge clk or posedge rst)\n"
      "    if (rst) count <= '0;\n"
      "    else count <= count + 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  bool found_ff = false;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kAlwaysBlock &&
        item->always_kind == AlwaysKind::kAlwaysFF) {
      found_ff = true;
    }
  }
  EXPECT_TRUE(found_ff);
}

TEST(Parser, ExpressionPrecedence) {
  auto r = Parse(
      "module expr;\n"
      "  logic a;\n"
      "  assign a = 1 + 2 * 3;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

// Helper to extract the first statement from an initial block.
static Stmt* FirstInitialStmt(ParseResult& r) {
  for (auto* item : r.cu->modules[0]->items) {
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
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    do x = x + 1; while (x < 10);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDoWhile);
  EXPECT_NE(stmt->body, nullptr);
  EXPECT_NE(stmt->condition, nullptr);
}

TEST(Parser, BreakStatement) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    break;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBreak);
}

TEST(Parser, ContinueStatement) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    continue;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kContinue);
}

TEST(Parser, ReturnStatement) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    return;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kReturn);
}

TEST(Parser, ReturnWithValue) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    return 42;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kReturn);
  EXPECT_NE(stmt->expr, nullptr);
}

TEST(Parser, WaitStatement) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    wait (ready) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWait);
  EXPECT_NE(stmt->condition, nullptr);
  EXPECT_NE(stmt->body, nullptr);
}

TEST(Parser, DisableStatement) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    disable blk;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDisable);
  EXPECT_NE(stmt->expr, nullptr);
}

TEST(Parser, TypedefEnum) {
  auto r = Parse(
      "module t;\n"
      "  typedef enum { A, B, C } state_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1);
  EXPECT_EQ(mod->items[0]->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(mod->items[0]->name, "state_t");
  EXPECT_EQ(mod->items[0]->typedef_type.kind, DataTypeKind::kEnum);
  ASSERT_EQ(mod->items[0]->typedef_type.enum_members.size(), 3);
  EXPECT_EQ(mod->items[0]->typedef_type.enum_members[0].name, "A");
  EXPECT_EQ(mod->items[0]->typedef_type.enum_members[1].name, "B");
  EXPECT_EQ(mod->items[0]->typedef_type.enum_members[2].name, "C");
}

TEST(Parser, EnumWithValues) {
  auto r = Parse(
      "module t;\n"
      "  typedef enum { IDLE=0, RUN=1, STOP=2 } cmd_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto& members = r.cu->modules[0]->items[0]->typedef_type.enum_members;
  ASSERT_EQ(members.size(), 3);
  EXPECT_EQ(members[0].name, "IDLE");
  EXPECT_NE(members[0].value, nullptr);
  EXPECT_EQ(members[1].name, "RUN");
  EXPECT_NE(members[1].value, nullptr);
}

TEST(Parser, InlineEnumVar) {
  auto r = Parse(
      "module t;\n"
      "  enum { X, Y } my_var;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1);
  EXPECT_EQ(mod->items[0]->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(mod->items[0]->name, "my_var");
  EXPECT_EQ(mod->items[0]->data_type.kind, DataTypeKind::kEnum);
  ASSERT_EQ(mod->items[0]->data_type.enum_members.size(), 2);
}

TEST(Parser, FunctionDecl) {
  auto r = Parse(
      "module t;\n"
      "  function int add(input int a, input int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1);
  EXPECT_EQ(mod->items[0]->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(mod->items[0]->name, "add");
  ASSERT_EQ(mod->items[0]->func_args.size(), 2);
  EXPECT_EQ(mod->items[0]->func_args[0].name, "a");
  EXPECT_EQ(mod->items[0]->func_args[1].name, "b");
}

TEST(Parser, TaskDecl) {
  auto r = Parse(
      "module t;\n"
      "  task my_task(input int x);\n"
      "    $display(\"%d\", x);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1);
  EXPECT_EQ(mod->items[0]->kind, ModuleItemKind::kTaskDecl);
  EXPECT_EQ(mod->items[0]->name, "my_task");
  ASSERT_EQ(mod->items[0]->func_args.size(), 1);
}

TEST(Parser, MultipleModules) {
  auto r = Parse(
      "module a; endmodule\n"
      "module b; endmodule\n"
      "module c; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 3);
  EXPECT_EQ(r.cu->modules[0]->name, "a");
  EXPECT_EQ(r.cu->modules[1]->name, "b");
  EXPECT_EQ(r.cu->modules[2]->name, "c");
}

TEST(Parser, TypedefStruct) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct {\n"
      "    logic [7:0] a;\n"
      "    int b;\n"
      "  } my_struct_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1);
  EXPECT_EQ(mod->items[0]->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(mod->items[0]->name, "my_struct_t");
  EXPECT_EQ(mod->items[0]->typedef_type.kind, DataTypeKind::kStruct);
  auto& members = mod->items[0]->typedef_type.struct_members;
  ASSERT_EQ(members.size(), 2);
  EXPECT_EQ(members[0].name, "a");
  EXPECT_EQ(members[0].type_kind, DataTypeKind::kLogic);
  EXPECT_EQ(members[1].name, "b");
  EXPECT_EQ(members[1].type_kind, DataTypeKind::kInt);
}

TEST(Parser, TypedefUnion) {
  auto r = Parse(
      "module t;\n"
      "  typedef union {\n"
      "    int i;\n"
      "    real r;\n"
      "  } my_union_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(item->typedef_type.kind, DataTypeKind::kUnion);
  ASSERT_EQ(item->typedef_type.struct_members.size(), 2);
}

TEST(Parser, TypedefStructPacked) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct packed {\n"
      "    logic [3:0] hi;\n"
      "    logic [3:0] lo;\n"
      "  } byte_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->typedef_type.kind, DataTypeKind::kStruct);
  EXPECT_TRUE(item->typedef_type.is_packed);
  ASSERT_EQ(item->typedef_type.struct_members.size(), 2);
}

TEST(Parser, InlineStructVar) {
  auto r = Parse(
      "module t;\n"
      "  struct { int x; int y; } point;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1);
  EXPECT_EQ(mod->items[0]->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(mod->items[0]->name, "point");
  EXPECT_EQ(mod->items[0]->data_type.kind, DataTypeKind::kStruct);
  ASSERT_EQ(mod->items[0]->data_type.struct_members.size(), 2);
}

TEST(Parser, EmptyPackage) {
  auto r = Parse("package my_pkg; endpackage");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->packages.size(), 1);
  EXPECT_EQ(r.cu->packages[0]->name, "my_pkg");
  EXPECT_TRUE(r.cu->packages[0]->items.empty());
}

TEST(Parser, PackageWithParam) {
  auto r = Parse(
      "package my_pkg;\n"
      "  parameter int WIDTH = 8;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->packages.size(), 1);
  ASSERT_EQ(r.cu->packages[0]->items.size(), 1);
  EXPECT_EQ(r.cu->packages[0]->items[0]->kind, ModuleItemKind::kParamDecl);
}

TEST(Parser, ImportSpecific) {
  auto r = Parse(
      "module t;\n"
      "  import my_pkg::WIDTH;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1);
  EXPECT_EQ(mod->items[0]->kind, ModuleItemKind::kImportDecl);
  EXPECT_EQ(mod->items[0]->import_item.package_name, "my_pkg");
  EXPECT_EQ(mod->items[0]->import_item.item_name, "WIDTH");
  EXPECT_FALSE(mod->items[0]->import_item.is_wildcard);
}

TEST(Parser, ImportWildcard) {
  auto r = Parse(
      "module t;\n"
      "  import my_pkg::*;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kImportDecl);
  EXPECT_EQ(item->import_item.package_name, "my_pkg");
  EXPECT_TRUE(item->import_item.is_wildcard);
}

TEST(Parser, PackageAndModule) {
  auto r = Parse(
      "package pkg; endpackage\n"
      "module top; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->packages.size(), 1);
  ASSERT_EQ(r.cu->modules.size(), 1);
  EXPECT_EQ(r.cu->packages[0]->name, "pkg");
  EXPECT_EQ(r.cu->modules[0]->name, "top");
}

TEST(Parser, GenerateFor) {
  auto r = Parse(
      "module t;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 4; i = i + 1) begin\n"
      "    assign a[i] = b[i];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  bool found_gen = false;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kGenerateFor) {
      found_gen = true;
      EXPECT_NE(item->gen_init, nullptr);
      EXPECT_NE(item->gen_cond, nullptr);
      EXPECT_NE(item->gen_step, nullptr);
      EXPECT_FALSE(item->gen_body.empty());
    }
  }
  EXPECT_TRUE(found_gen);
}

TEST(Parser, GenerateIf) {
  auto r = Parse(
      "module t;\n"
      "  if (WIDTH > 8) begin\n"
      "    assign a = b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1);
  EXPECT_EQ(mod->items[0]->kind, ModuleItemKind::kGenerateIf);
  EXPECT_NE(mod->items[0]->gen_cond, nullptr);
  EXPECT_FALSE(mod->items[0]->gen_body.empty());
}

TEST(Parser, GenerateIfElse) {
  auto r = Parse(
      "module t;\n"
      "  if (WIDTH > 8) begin\n"
      "    assign a = b;\n"
      "  end else begin\n"
      "    assign a = c;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGenerateIf);
  EXPECT_NE(item->gen_else, nullptr);
}

TEST(Parser, GenerateRegion) {
  auto r = Parse(
      "module t;\n"
      "  generate\n"
      "    if (WIDTH > 8) begin\n"
      "      assign a = b;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  bool found_gen = false;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kGenerateIf) {
      found_gen = true;
    }
  }
  EXPECT_TRUE(found_gen);
}
