// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

static ModuleItem* FindFunc(ParseResult& r, std::string_view name) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kFunctionDecl &&
        item->kind != ModuleItemKind::kTaskDecl) {
      continue;
    }
    if (item->name == name) return item;
  }
  return nullptr;
}

namespace {

// =============================================================================
// LRM section 13.4.1 -- Function return type
// =============================================================================
TEST(ParserSection13, FunctionReturnTypeInt) {
  auto r = Parse(
      "module m;\n"
      "  function int foo();\n"
      "    return 42;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* fn = FindFunc(r, "foo");
  ASSERT_NE(fn, nullptr);
  EXPECT_EQ(fn->return_type.kind, DataTypeKind::kInt);
}

TEST(ParserSection13, FunctionReturnTypeVoid) {
  auto r = Parse(
      "module m;\n"
      "  function void bar();\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* fn = FindFunc(r, "bar");
  ASSERT_NE(fn, nullptr);
  EXPECT_EQ(fn->return_type.kind, DataTypeKind::kVoid);
}

TEST(ParserSection13, FunctionReturnTypeLogicVec) {
  auto r = Parse(
      "module m;\n"
      "  function logic [7:0] get_byte();\n"
      "    return 8'hAB;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* fn = FindFunc(r, "get_byte");
  ASSERT_NE(fn, nullptr);
  EXPECT_EQ(fn->return_type.kind, DataTypeKind::kLogic);
}

// =============================================================================
// LRM section 13.3.1 -- Static and automatic tasks/functions
// =============================================================================
TEST(ParserSection13, AutomaticFunction) {
  auto r = Parse(
      "module m;\n"
      "  function automatic int fact(int n);\n"
      "    if (n <= 1) return 1;\n"
      "    return n * fact(n - 1);\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* fn = FindFunc(r, "fact");
  ASSERT_NE(fn, nullptr);
  EXPECT_TRUE(fn->is_automatic);
  EXPECT_FALSE(fn->is_static);
}

TEST(ParserSection13, StaticTask) {
  auto r = Parse(
      "module m;\n"
      "  task static do_stuff();\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* tk = FindFunc(r, "do_stuff");
  ASSERT_NE(tk, nullptr);
  EXPECT_TRUE(tk->is_static);
  EXPECT_FALSE(tk->is_automatic);
}

// =============================================================================
// LRM section 13.6 -- DPI import / export
// =============================================================================
TEST(ParserSection13, DpiImportFunction) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" function int c_add(int a, int b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ModuleItem* dpi = nullptr;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kDpiImport) {
      dpi = item;
      break;
    }
  }
  ASSERT_NE(dpi, nullptr);
  EXPECT_EQ(dpi->name, "c_add");
  EXPECT_FALSE(dpi->dpi_is_task);
  EXPECT_FALSE(dpi->dpi_is_pure);
}

TEST(ParserSection13, DpiImportPureFunction) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" pure function int c_mul(int a, int b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ModuleItem* dpi = nullptr;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kDpiImport) {
      dpi = item;
      break;
    }
  }
  ASSERT_NE(dpi, nullptr);
  EXPECT_TRUE(dpi->dpi_is_pure);
  EXPECT_FALSE(dpi->dpi_is_context);
}

TEST(ParserSection13, DpiImportContextTask) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" context task c_display(input int x);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ModuleItem* dpi = nullptr;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kDpiImport) {
      dpi = item;
      break;
    }
  }
  ASSERT_NE(dpi, nullptr);
  EXPECT_TRUE(dpi->dpi_is_context);
  EXPECT_TRUE(dpi->dpi_is_task);
}

TEST(ParserSection13, DpiImportWithCName) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" c_real_name = function void sv_wrapper();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ModuleItem* dpi = nullptr;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kDpiImport) {
      dpi = item;
      break;
    }
  }
  ASSERT_NE(dpi, nullptr);
  EXPECT_EQ(dpi->dpi_c_name, "c_real_name");
  EXPECT_EQ(dpi->name, "sv_wrapper");
}

TEST(ParserSection13, DpiExportFunction) {
  auto r = Parse(
      "module m;\n"
      "  export \"DPI-C\" function my_sv_func;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ModuleItem* dpi = nullptr;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kDpiExport) {
      dpi = item;
      break;
    }
  }
  ASSERT_NE(dpi, nullptr);
  EXPECT_EQ(dpi->name, "my_sv_func");
}

TEST(ParserSection13, DpiExportTask) {
  auto r = Parse(
      "module m;\n"
      "  export \"DPI-C\" task my_sv_task;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ModuleItem* dpi = nullptr;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kDpiExport) {
      dpi = item;
      break;
    }
  }
  ASSERT_NE(dpi, nullptr);
  EXPECT_EQ(dpi->name, "my_sv_task");
  EXPECT_TRUE(dpi->dpi_is_task);
}

// =============================================================================
// LRM section 13.3-13.4 -- Old-style (non-ANSI) task/function declarations
// =============================================================================
// =============================================================================
// LRM section 13.8 -- Parameterized tasks and functions
// =============================================================================
TEST(ParserSection13, ParameterizedSubroutine_VirtualClassWithStaticMethod) {
  auto r = Parse(
      "virtual class C#(parameter DECODE_W = 8,\n"
      "                 parameter ENCODE_W = $clog2(DECODE_W));\n"
      "  static function logic [ENCODE_W-1:0] ENCODER_f\n"
      "      (input logic [DECODE_W-1:0] DecodeIn);\n"
      "    ENCODER_f = '0;\n"
      "    for (int i = 0; i < DECODE_W; i++) begin\n"
      "      if (DecodeIn[i]) begin\n"
      "        ENCODER_f = i[ENCODE_W-1:0];\n"
      "        break;\n"
      "      end\n"
      "    end\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection13, ParameterizedSubroutine_ClassScopeCall) {
  auto r = Parse(
      "module top;\n"
      "  logic [7:0] encoder_in;\n"
      "  logic [2:0] encoder_out;\n"
      "  assign encoder_out = C#(8)::ENCODER_f(encoder_in);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection13, ParameterizedSubroutine_MultipleStaticMethods) {
  auto r = Parse(
      "virtual class C#(parameter W = 4);\n"
      "  static function logic [W-1:0] encode(input logic [W-1:0] x);\n"
      "    return x;\n"
      "  endfunction\n"
      "  static function logic [W-1:0] decode(input logic [W-1:0] x);\n"
      "    return x;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection13, ParameterizedSubroutine_DifferentSpecializations) {
  auto r = Parse(
      "module m;\n"
      "  logic [3:0] a;\n"
      "  logic [7:0] b;\n"
      "  logic [1:0] ra;\n"
      "  logic [2:0] rb;\n"
      "  assign ra = C#(4)::ENCODER_f(a);\n"
      "  assign rb = C#(8)::ENCODER_f(b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

// =============================================================================
// LRM section 13.3-13.4 -- Old-style (non-ANSI) task/function declarations
// =============================================================================
TEST(ParserSection13, OldStyleTaskMultipleInputs) {
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

// =============================================================================
// LRM section 13.5.2 -- Const ref arguments (additional tests)
// =============================================================================
TEST(ParserSection13, ConstRefArgOnTask) {
  auto r = Parse(
      "module m;\n"
      "  task process_data(const ref int data[]);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* tk = FindFunc(r, "process_data");
  ASSERT_NE(tk, nullptr);
  ASSERT_EQ(tk->func_args.size(), 1u);
  EXPECT_TRUE(tk->func_args[0].is_const);
  EXPECT_EQ(tk->func_args[0].direction, Direction::kRef);
}

TEST(ParserSection13, ConstRefMixedWithOtherDirections) {
  auto r = Parse(
      "module m;\n"
      "  function void compute(input int a, const ref int b, output int c);\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* fn = FindFunc(r, "compute");
  ASSERT_NE(fn, nullptr);
  ASSERT_EQ(fn->func_args.size(), 3u);
  EXPECT_EQ(fn->func_args[0].direction, Direction::kInput);
  EXPECT_FALSE(fn->func_args[0].is_const);
  EXPECT_EQ(fn->func_args[1].direction, Direction::kRef);
  EXPECT_TRUE(fn->func_args[1].is_const);
  EXPECT_EQ(fn->func_args[2].direction, Direction::kOutput);
}

TEST(ParserSection13, RefArgOnFunction) {
  auto r = Parse(
      "module m;\n"
      "  function void swap(ref int a, ref int b);\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* fn = FindFunc(r, "swap");
  ASSERT_NE(fn, nullptr);
  ASSERT_EQ(fn->func_args.size(), 2u);
  EXPECT_EQ(fn->func_args[0].direction, Direction::kRef);
  EXPECT_EQ(fn->func_args[1].direction, Direction::kRef);
}

// =============================================================================
// LRM section 13.1 -- Tasks and functions overview (additional tests)
// =============================================================================
// Function with end label matching the function name (LRM section 13.4).
TEST(ParserSection13, FunctionEndLabel) {
  auto r = Parse(
      "module m;\n"
      "  function int add(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction : add\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* fn = FindFunc(r, "add");
  ASSERT_NE(fn, nullptr);
  EXPECT_EQ(fn->return_type.kind, DataTypeKind::kInt);
}

// Task with end label matching the task name (LRM section 13.3).
TEST(ParserSection13, TaskEndLabel) {
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

// Function with empty body.
TEST(ParserSection13, FunctionEmptyBody) {
  auto r = Parse(
      "module m;\n"
      "  function void nop();\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* fn = FindFunc(r, "nop");
  ASSERT_NE(fn, nullptr);
  EXPECT_EQ(fn->return_type.kind, DataTypeKind::kVoid);
  EXPECT_TRUE(fn->func_body_stmts.empty());
}

// =============================================================================
// LRM section 13.3 -- Tasks (additional tests)
// =============================================================================
// Task with timing control in body (tasks may have time-controlling stmts).
TEST(ParserSection13, TaskWithTimingControl) {
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

}  // namespace
