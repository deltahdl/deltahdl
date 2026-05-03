#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(TaskAndFunctionParsing, TaskWithInoutPort) {
  auto r = Parse(
      "module m;\n"
      "  task transform(inout logic [7:0] data);\n"
      "    data = data ^ 8'hFF;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* tk = FindFunc(r, "transform");
  ASSERT_NE(tk, nullptr);
  ASSERT_EQ(tk->func_args.size(), 1u);
  EXPECT_EQ(tk->func_args[0].direction, Direction::kInout);
}

TEST(TaskAndFunctionParsing, TaskWithNoPorts) {
  auto r = Parse(
      "module m;\n"
      "  task idle();\n"
      "    #10;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* tk = FindFunc(r, "idle");
  ASSERT_NE(tk, nullptr);
  EXPECT_EQ(tk->kind, ModuleItemKind::kTaskDecl);
  EXPECT_TRUE(tk->func_args.empty());
}

TEST(TaskDeclParsing, TfPortItemVarWithDirection) {
  auto r = Parse(
      "module m;\n"
      "  task my_task(input var int x);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(item->func_args[0].name, "x");
}

TEST(TaskDeclParsing, TfPortItemNoNameInPrototype) {
  auto r = Parse(
      "module m;\n"
      "  extern task my_task(input int, output int);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 2u);
}

TEST(BlockItemDeclParsing, BlockItemInTask) {
  auto r = Parse(
      "module m;\n"
      "  task my_task();\n"
      "    int x;\n"
      "    x = 5;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  ASSERT_GE(item->func_body_stmts.size(), 1u);
  EXPECT_EQ(item->func_body_stmts[0]->kind, StmtKind::kVarDecl);
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

TEST(TaskDeclParsing, TfItemDeclMixed) {
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
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 2u);
  EXPECT_GE(item->func_body_stmts.size(), 1u);
}

TEST(TaskAndFunctionParsing, MultipleDimsOnFuncArg) {
  auto r = Parse(
      "module m;\n"
      "  task bar(logic mem[16][8]);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* tk = FindFunc(r, "bar");
  ASSERT_NE(tk, nullptr);
  ASSERT_EQ(tk->func_args.size(), 1u);
  EXPECT_EQ(tk->func_args[0].unpacked_dims.size(), 2u);
}

TEST(TaskAndFunctionParsing, OldStyleTask) {
  auto r = Parse(
      "module m;\n"
      "  task mytask;\n"
      "    input a;\n"
      "    output b;\n"
      "    b = a;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* tk = FindFunc(r, "mytask");
  ASSERT_NE(tk, nullptr);
  ASSERT_EQ(tk->func_args.size(), 2u);
  EXPECT_EQ(tk->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(tk->func_args[1].direction, Direction::kOutput);
}

TEST(TaskAndFunctionParsing, OldStyleTaskMultipleInputs) {
  auto r = Parse(
      "module m;\n"
      "  task add;\n"
      "    input a;\n"
      "    input b;\n"
      "    output c;\n"
      "    c = a + b;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* tk = FindFunc(r, "add");
  ASSERT_NE(tk, nullptr);
  ASSERT_EQ(tk->func_args.size(), 3u);
  const Direction kExpected[] = {Direction::kInput, Direction::kInput,
                                 Direction::kOutput};
  for (size_t i = 0; i < 3u; ++i) {
    EXPECT_EQ(tk->func_args[i].direction, kExpected[i]);
  }
}

TEST(TaskAndFunctionParsing, TaskEndLabel) {
  auto r = Parse(
      "module m;\n"
      "  task do_work(int x);\n"
      "    $display(\"%d\", x);\n"
      "  endtask : do_work\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* tk = FindFunc(r, "do_work");
  ASSERT_NE(tk, nullptr);
  EXPECT_EQ(tk->kind, ModuleItemKind::kTaskDecl);
}

TEST(TaskAndFunctionParsing, TaskWithTimingControl) {
  auto r = Parse(
      "module m;\n"
      "  task wait_clk(input int n);\n"
      "    repeat (n) @(posedge clk);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* tk = FindFunc(r, "wait_clk");
  ASSERT_NE(tk, nullptr);
  EXPECT_EQ(tk->kind, ModuleItemKind::kTaskDecl);
  ASSERT_EQ(tk->func_args.size(), 1u);
  EXPECT_EQ(tk->func_args[0].direction, Direction::kInput);
}

TEST(DeclarationListParsing, ListOfTfVariableIdentifiersTask) {
  auto r = Parse(
      "module m;\n"
      "  task report;\n"
      "    input int addr, data;\n"
      "    output int status;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  EXPECT_EQ(item->func_args.size(), 3u);
  EXPECT_EQ(item->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(item->func_args[1].direction, Direction::kInput);
  EXPECT_EQ(item->func_args[2].direction, Direction::kOutput);
}

TEST(TaskDeclParsing, TaskBodyNewStyleEmptyPorts) {
  auto r = Parse(
      "module m;\n"
      "  task my_task();\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  EXPECT_TRUE(item->func_args.empty());
}

static void VerifyTwoArgTask(ParseResult& r) {
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 2u);
  EXPECT_EQ(item->func_args[0].name, "a");
  EXPECT_EQ(item->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(item->func_args[1].name, "b");
}

TEST(TaskDeclParsing, TaskBodyNewStyleWithArgs) {
  auto r = Parse(
      "module m;\n"
      "  task my_task(input int a, input int b);\n"
      "  endtask\n"
      "endmodule\n");
  VerifyTwoArgTask(r);
}

TEST(TaskDeclParsing, TaskBodyNewStyleMultipleDirections) {
  auto r = Parse(
      "module m;\n"
      "  task xfer(input int a, output int b, inout int c, ref int d);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  VerifyFuncArgDirections(r.cu->modules[0]->items[0],
                          {Direction::kInput, Direction::kOutput,
                           Direction::kInout, Direction::kRef});
}

TEST(TaskDeclParsing, TaskBodyNewStyleStickyDirection) {
  auto r = Parse(
      "module m;\n"
      "  task my_task(input int a, int b, int c);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  VerifyFuncArgDirections(
      r.cu->modules[0]->items[0],
      {Direction::kInput, Direction::kInput, Direction::kInput});
}

TEST(TaskDeclParsing, TaskBodyWithEndLabel) {
  auto r = Parse(
      "module m;\n"
      "  task my_task();\n"
      "  endtask : my_task\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->name, "my_task");
}

TEST(TaskDeclParsing, TaskBodyOldStylePorts) {
  auto r = Parse(
      "module m;\n"
      "  task my_task;\n"
      "    input int a;\n"
      "    input int b;\n"
      "    $display(\"a=%0d b=%0d\", a, b);\n"
      "  endtask\n"
      "endmodule\n");
  VerifyTwoArgTask(r);
}

TEST(TaskDeclParsing, TaskBodyOldStyleOutputPort) {
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
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 2u);
  EXPECT_EQ(item->func_args[1].direction, Direction::kOutput);
}
TEST(DataTypeParsing, VoidTaskReturnType) {
  auto r = Parse(
      "module t;\n"
      "  task do_nothing();\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
}

TEST(TaskAndFunctionParsing, TaskDefaultDirectionInput) {
  auto r = Parse(
      "module m;\n"
      "  task t(int a, int b);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 2u);
  EXPECT_EQ(item->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(item->func_args[1].direction, Direction::kInput);
}

TEST(TaskAndFunctionParsing, TaskEmptyBody) {
  auto r = Parse(
      "module m;\n"
      "  task empty_task;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  EXPECT_TRUE(item->func_body_stmts.empty());
}

TEST(TaskAndFunctionParsing, TaskDirectionStickyOutput) {
  auto r = Parse(
      "module m;\n"
      "  task t(output logic [7:0] a, b);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 2u);
  EXPECT_EQ(item->func_args[0].direction, Direction::kOutput);
  EXPECT_EQ(item->func_args[1].direction, Direction::kOutput);
}

TEST(TaskAndFunctionParsing, TaskMultipleStatements) {
  auto r = Parse(
      "module m;\n"
      "  task compute(input int a, output int b, output int c);\n"
      "    b = a + 1;\n"
      "    c = a * 2;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_GE(item->func_body_stmts.size(), 2u);
}

TEST(TaskAndFunctionParsing, TaskReturnStatement) {
  auto r = Parse(
      "module m;\n"
      "  task t(input int a);\n"
      "    if (a == 0) return;\n"
      "    $display(\"%d\", a);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §13.3: "If the data type is not explicitly declared, then the default data
// type is logic if it is the first argument or if the argument direction is
// explicitly specified. Otherwise, the data type is inherited from the
// previous argument." After an explicit `output logic [15:0] u`, the bare-
// identifier formal `v` shall inherit u's logic [15:0] type.
TEST(TaskAndFunctionParsing, FormalArgDataTypeInheritedFromPrevious) {
  auto r = Parse(
      "module m;\n"
      "  task t(output logic [15:0] u, v);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 2u);
  EXPECT_EQ(item->func_args[1].name, "v");
  EXPECT_EQ(item->func_args[1].data_type.kind, DataTypeKind::kLogic);
  ASSERT_NE(item->func_args[1].data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->func_args[1].data_type.packed_dim_left->int_val, 15u);
  ASSERT_NE(item->func_args[1].data_type.packed_dim_right, nullptr);
  EXPECT_EQ(item->func_args[1].data_type.packed_dim_right->int_val, 0u);
}

// §13.3: A bare identifier formal following an explicitly typed formal of a
// different built-in kind shall inherit that kind, not silently default to
// the implicit/logic type.
TEST(TaskAndFunctionParsing, FormalArgInheritsBuiltinType) {
  auto r = Parse(
      "module m;\n"
      "  task t(input int a, b);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 2u);
  EXPECT_EQ(item->func_args[1].name, "b");
  EXPECT_EQ(item->func_args[1].data_type.kind, DataTypeKind::kInt);
}

// §13.3: When the second formal supplies its own direction keyword, the data
// type is *not* inherited from the previous formal — the direction was
// explicitly specified, so the default data type is logic.
TEST(TaskAndFunctionParsing, FormalArgExplicitDirectionDefaultsLogic) {
  auto r = Parse(
      "module m;\n"
      "  task t(input int a, output b);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 2u);
  EXPECT_EQ(item->func_args[1].name, "b");
  EXPECT_EQ(item->func_args[1].data_type.kind, DataTypeKind::kLogic);
  EXPECT_EQ(item->func_args[1].data_type.packed_dim_left, nullptr);
}

// §13.3 example: `task mytask3(a, b, output logic [15:0] u, v);`. The LRM
// states that a and b default to inputs and u and v are outputs. By the
// data-type rule, a and b default to logic (first arg / direction not
// explicit but applied at first position) while v inherits u's logic [15:0].
TEST(TaskAndFunctionParsing, FormalArgListMatchesLrmMytask3) {
  auto r = Parse(
      "module m;\n"
      "  task mytask3(a, b, output logic [15:0] u, v);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 4u);
  EXPECT_EQ(item->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(item->func_args[0].data_type.kind, DataTypeKind::kLogic);
  EXPECT_EQ(item->func_args[1].direction, Direction::kInput);
  EXPECT_EQ(item->func_args[1].data_type.kind, DataTypeKind::kLogic);
  EXPECT_EQ(item->func_args[2].direction, Direction::kOutput);
  EXPECT_EQ(item->func_args[2].data_type.kind, DataTypeKind::kLogic);
  ASSERT_NE(item->func_args[2].data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->func_args[2].data_type.packed_dim_left->int_val, 15u);
  EXPECT_EQ(item->func_args[3].direction, Direction::kOutput);
  EXPECT_EQ(item->func_args[3].data_type.kind, DataTypeKind::kLogic);
  ASSERT_NE(item->func_args[3].data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->func_args[3].data_type.packed_dim_left->int_val, 15u);
}

// §13.3: "Once a direction is given, subsequent formals default to the same
// direction." A list that explicitly switches direction in the middle must
// preserve the new direction sticky across the rest of the list — exercised
// here by `input int a, int b, output int c, int d`.
TEST(TaskAndFunctionParsing, FormalArgDirectionStickyAcrossSwitch) {
  auto r = Parse(
      "module m;\n"
      "  task my_task(input int a, int b, output int c, int d);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 4u);
  EXPECT_EQ(item->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(item->func_args[1].direction, Direction::kInput);
  EXPECT_EQ(item->func_args[2].direction, Direction::kOutput);
  EXPECT_EQ(item->func_args[3].direction, Direction::kOutput);
}

// §13.3 footnote 28: "In a tf_port_item, it shall be illegal to omit the
// explicit port_identifier except within a function_prototype or
// task_prototype." A bare data type with no identifier in a non-prototype
// task declaration must be diagnosed by the parser.
TEST(TaskAndFunctionParsing, FormalArgRequiresIdentifierInTaskBody) {
  auto r = Parse(
      "module m;\n"
      "  task my_task(input int);\n"
      "  endtask\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §13.3 footnote 28: same rule for function declarations — both share the
// tf_port_item production.
TEST(TaskAndFunctionParsing, FormalArgRequiresIdentifierInFunctionBody) {
  auto r = Parse(
      "module m;\n"
      "  function int f(input int);\n"
      "    return 0;\n"
      "  endfunction\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// §13.3 footnote 28: the prototype carve-out — `extern task` and
// `extern function` are prototypes and are therefore allowed to omit
// identifiers. This is the positive control for the rule.
TEST(TaskAndFunctionParsing, FormalArgIdentifierOptionalInPrototype) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  extern task my_task(input int, output int);\n"
              "endmodule\n"));
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  extern function int f(input int);\n"
              "endmodule\n"));
}

// §13.3: "The const and static qualifiers on the ref direction are
// included in this default." A formal that inherits the ref direction
// from the previous formal must also inherit the `static` qualifier.
TEST(TaskAndFunctionParsing, RefStaticQualifierStickyInherited) {
  auto r = Parse(
      "module m;\n"
      "  task t(ref static int a, b);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 2u);
  EXPECT_EQ(item->func_args[0].direction, Direction::kRef);
  EXPECT_TRUE(item->func_args[0].is_ref_static);
  EXPECT_EQ(item->func_args[1].direction, Direction::kRef);
  EXPECT_TRUE(item->func_args[1].is_ref_static);
}

// §13.3: Same propagation rule for the `const` qualifier on a sticky
// ref direction — inheriting `ref` also carries `const` to the next
// formal that omits its own direction keyword.
TEST(TaskAndFunctionParsing, ConstRefQualifierStickyInherited) {
  auto r = Parse(
      "module m;\n"
      "  task t(const ref int a, b);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 2u);
  EXPECT_EQ(item->func_args[0].direction, Direction::kRef);
  EXPECT_TRUE(item->func_args[0].is_const);
  EXPECT_EQ(item->func_args[1].direction, Direction::kRef);
  EXPECT_TRUE(item->func_args[1].is_const);
}

// §13.3 inverse: when the next formal supplies its OWN explicit `ref`
// direction without `static`, the static qualifier is *not* inherited
// from the previous formal — the propagation only kicks in when the
// direction itself is sticky-inherited.
TEST(TaskAndFunctionParsing,
     RefStaticQualifierNotInheritedAcrossExplicitDirection) {
  auto r = Parse(
      "module m;\n"
      "  task t(ref static int a, ref int b);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 2u);
  EXPECT_TRUE(item->func_args[0].is_ref_static);
  EXPECT_EQ(item->func_args[1].direction, Direction::kRef);
  EXPECT_FALSE(item->func_args[1].is_ref_static);
}

// §13.3: For a function (not just a task), the same data-type inheritance
// rule applies — both share the tf_port_item production in A.2.7.
TEST(TaskAndFunctionParsing, FunctionFormalArgDataTypeInherited) {
  auto r = Parse(
      "module m;\n"
      "  function int f(input logic [3:0] x, y);\n"
      "    return 0;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 2u);
  EXPECT_EQ(item->func_args[1].name, "y");
  EXPECT_EQ(item->func_args[1].data_type.kind, DataTypeKind::kLogic);
  ASSERT_NE(item->func_args[1].data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->func_args[1].data_type.packed_dim_left->int_val, 3u);
}

}  // namespace
