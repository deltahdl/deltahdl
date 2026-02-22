#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

namespace {

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string &src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

struct ElabFixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
};

RtlirDesign *Elaborate(const std::string &src, ElabFixture &f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

}  // namespace

// =============================================================================
// A.2.7 Task declarations
// =============================================================================

// ---------------------------------------------------------------------------
// task_declaration ::=
//   task [ dynamic_override_specifiers ] [ lifetime ] task_body_declaration
// ---------------------------------------------------------------------------

TEST(ParserA27, TaskLifetimeAutomatic) {
  auto r = Parse(
      "module m;\n"
      "  task automatic my_task();\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  EXPECT_TRUE(item->is_automatic);
  EXPECT_FALSE(item->is_static);
}

TEST(ParserA27, TaskLifetimeStatic) {
  auto r = Parse(
      "module m;\n"
      "  task static my_task();\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_FALSE(item->is_automatic);
  EXPECT_TRUE(item->is_static);
}

TEST(ParserA27, TaskLifetimeDefault) {
  auto r = Parse(
      "module m;\n"
      "  task my_task();\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_FALSE(item->is_automatic);
  EXPECT_FALSE(item->is_static);
}

TEST(ParserA27, TaskDynamicOverrideInitial) {
  auto r = Parse(
      "class C;\n"
      "  virtual task :initial my_task(); endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA27, TaskDynamicOverrideExtends) {
  auto r = Parse(
      "class C;\n"
      "  virtual task :extends my_task(); endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA27, TaskDynamicOverrideFinal) {
  auto r = Parse(
      "class C;\n"
      "  virtual task :final my_task(); endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA27, TaskDynamicOverrideInitialFinal) {
  auto r = Parse(
      "class C;\n"
      "  virtual task :initial :final my_task(); endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA27, TaskDynamicOverrideExtendsFinal) {
  auto r = Parse(
      "class C;\n"
      "  virtual task :extends :final my_task(); endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// ---------------------------------------------------------------------------
// task_body_declaration (new-style ports)
// ---------------------------------------------------------------------------

TEST(ParserA27, TaskBodyNewStyleEmptyPorts) {
  auto r = Parse(
      "module m;\n"
      "  task my_task();\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  EXPECT_TRUE(item->func_args.empty());
}

TEST(ParserA27, TaskBodyNewStyleWithArgs) {
  auto r = Parse(
      "module m;\n"
      "  task my_task(input int a, input int b);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 2u);
  EXPECT_EQ(item->func_args[0].name, "a");
  EXPECT_EQ(item->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(item->func_args[1].name, "b");
}

TEST(ParserA27, TaskBodyNewStyleDefaultValue) {
  auto r = Parse(
      "module m;\n"
      "  task my_task(input int x = 5);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_NE(item->func_args[0].default_value, nullptr);
}

TEST(ParserA27, TaskBodyNewStyleMultipleDirections) {
  auto r = Parse(
      "module m;\n"
      "  task xfer(input int a, output int b, inout int c, ref int d);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 4u);
  EXPECT_EQ(item->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(item->func_args[1].direction, Direction::kOutput);
  EXPECT_EQ(item->func_args[2].direction, Direction::kInout);
  EXPECT_EQ(item->func_args[3].direction, Direction::kRef);
}

TEST(ParserA27, TaskBodyNewStyleConstRef) {
  auto r = Parse(
      "module m;\n"
      "  task my_task(const ref int x);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_TRUE(item->func_args[0].is_const);
  EXPECT_EQ(item->func_args[0].direction, Direction::kRef);
}

TEST(ParserA27, TaskBodyNewStyleStickyDirection) {
  auto r = Parse(
      "module m;\n"
      "  task my_task(input int a, int b, int c);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 3u);
  EXPECT_EQ(item->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(item->func_args[1].direction, Direction::kInput);
  EXPECT_EQ(item->func_args[2].direction, Direction::kInput);
}

TEST(ParserA27, TaskBodyNewStyleBlockItemDecl) {
  auto r = Parse(
      "module m;\n"
      "  task my_task(input int x);\n"
      "    int temp;\n"
      "    temp = x + 1;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  EXPECT_GE(item->func_body_stmts.size(), 1u);
}

TEST(ParserA27, TaskBodyWithEndLabel) {
  auto r = Parse(
      "module m;\n"
      "  task my_task();\n"
      "  endtask : my_task\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->name, "my_task");
}

TEST(ParserA27, TaskBodyWithStatements) {
  auto r = Parse(
      "module m;\n"
      "  task my_task(input int x);\n"
      "    #10;\n"
      "    $display(\"x=%0d\", x);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_GE(item->func_body_stmts.size(), 2u);
}

// ---------------------------------------------------------------------------
// task_body_declaration (old-style ports — tf_item_declaration)
// ---------------------------------------------------------------------------

TEST(ParserA27, TaskBodyOldStylePorts) {
  auto r = Parse(
      "module m;\n"
      "  task my_task;\n"
      "    input int a;\n"
      "    input int b;\n"
      "    $display(\"a=%0d b=%0d\", a, b);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 2u);
  EXPECT_EQ(item->func_args[0].name, "a");
  EXPECT_EQ(item->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(item->func_args[1].name, "b");
}

TEST(ParserA27, TaskBodyOldStyleOutputPort) {
  auto r = Parse(
      "module m;\n"
      "  task my_task;\n"
      "    input int a;\n"
      "    output int b;\n"
      "    b = a * 2;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 2u);
  EXPECT_EQ(item->func_args[1].direction, Direction::kOutput);
}

// ---------------------------------------------------------------------------
// task_body_declaration (scope qualifiers)
// ---------------------------------------------------------------------------

TEST(ParserA27, TaskBodyClassScope) {
  auto r = Parse(
      "class C;\n"
      "  extern task my_task(input int x);\n"
      "endclass\n"
      "task C::my_task(input int x);\n"
      "  $display(\"x=%0d\", x);\n"
      "endtask\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA27, TaskBodyOutOfBlockMethod) {
  auto r = Parse(
      "class C;\n"
      "  extern task run();\n"
      "endclass\n"
      "task C::run();\n"
      "endtask\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA27, TaskBodyInterfaceScope) {
  auto r = Parse(
      "interface intf;\n"
      "  extern task my_task();\n"
      "endinterface\n"
      "task intf.my_task();\n"
      "endtask\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// ---------------------------------------------------------------------------
// task_prototype ::=
//   task [ dynamic_override_specifiers ] task_identifier
//     [ ( [ tf_port_list ] ) ]
// ---------------------------------------------------------------------------

TEST(ParserA27, TaskPrototypeExtern) {
  auto r = Parse(
      "module m;\n"
      "  extern task my_task(input int x);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  EXPECT_TRUE(item->is_extern);
  EXPECT_EQ(item->name, "my_task");
}

TEST(ParserA27, TaskPrototypeExternNoPorts) {
  auto r = Parse(
      "module m;\n"
      "  extern task run;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->is_extern);
  EXPECT_TRUE(item->func_args.empty());
}

TEST(ParserA27, TaskPrototypePureVirtual) {
  auto r = Parse(
      "class C;\n"
      "  pure virtual task do_work(input int x);\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// ---------------------------------------------------------------------------
// tf_port_item: [ var ] data_type_or_implicit
// ---------------------------------------------------------------------------

TEST(ParserA27, TfPortItemVar) {
  auto r = Parse(
      "module m;\n"
      "  task my_task(var int x);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].name, "x");
}

TEST(ParserA27, TfPortItemVarWithDirection) {
  auto r = Parse(
      "module m;\n"
      "  task my_task(input var int x);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(item->func_args[0].name, "x");
}

// ---------------------------------------------------------------------------
// tf_port_direction: [ const ] ref [ static ]
// ---------------------------------------------------------------------------

TEST(ParserA27, TfPortDirectionRefStatic) {
  auto r = Parse(
      "module m;\n"
      "  task my_task(ref static int x);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].direction, Direction::kRef);
}

TEST(ParserA27, TfPortDirectionConstRefStatic) {
  auto r = Parse(
      "module m;\n"
      "  task my_task(const ref static int x);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_TRUE(item->func_args[0].is_const);
  EXPECT_EQ(item->func_args[0].direction, Direction::kRef);
}

// ---------------------------------------------------------------------------
// tf_port_declaration (old-style): const ref and var
// ---------------------------------------------------------------------------

TEST(ParserA27, TfPortDeclOldStyleConstRef) {
  auto r = Parse(
      "module m;\n"
      "  task my_task;\n"
      "    const ref int x;\n"
      "    $display(\"%0d\", x);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_TRUE(item->func_args[0].is_const);
  EXPECT_EQ(item->func_args[0].direction, Direction::kRef);
}

TEST(ParserA27, TfPortDeclOldStyleVar) {
  auto r = Parse(
      "module m;\n"
      "  task my_task;\n"
      "    input var int x;\n"
      "    $display(\"%0d\", x);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].direction, Direction::kInput);
}

// ---------------------------------------------------------------------------
// tf_port_item clarification 28: name omitted in prototype
// ---------------------------------------------------------------------------

TEST(ParserA27, TfPortItemNoNameInPrototype) {
  auto r = Parse(
      "module m;\n"
      "  extern task my_task(input int, output int);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 2u);
}

// ---------------------------------------------------------------------------
// tf_item_declaration: block_item_declaration and tf_port_declaration mixed
// ---------------------------------------------------------------------------

TEST(ParserA27, TfItemDeclMixed) {
  auto r = Parse(
      "module m;\n"
      "  task my_task;\n"
      "    input int a;\n"
      "    output int b;\n"
      "    int temp;\n"
      "    temp = a + 1;\n"
      "    b = temp;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 2u);
  EXPECT_GE(item->func_body_stmts.size(), 1u);
}

// ---------------------------------------------------------------------------
// Elaboration: task declaration within module
// ---------------------------------------------------------------------------

TEST(ParserA27, ElabTaskDeclInModule) {
  ElabFixture f;
  auto *design = Elaborate(
      "module m;\n"
      "  task my_task(input int a);\n"
      "    $display(\"a=%0d\", a);\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ParserA27, ElabTaskAutomaticLifetime) {
  ElabFixture f;
  auto *design = Elaborate(
      "module m;\n"
      "  task automatic my_task(input int n);\n"
      "    #10;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}
