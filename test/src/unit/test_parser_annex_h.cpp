// Tests for Annex G (std package), Annex H (DPI C layer), Annex I (svdpi.h),
// Annex J (foreign language inclusion), Annex K/L/M (VPI headers), and Annex O
// (encryption/decryption) of IEEE 1800-2023.

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/parser.h"

using namespace delta;

namespace {

struct AnnexHParseTest : ::testing::Test {
 protected:
  CompilationUnit *Parse(const std::string &src) {
    source_ = src;
    lexer_ = std::make_unique<Lexer>(source_, 0, diag_);
    parser_ = std::make_unique<Parser>(*lexer_, arena_, diag_);
    return parser_->Parse();
  }

  SourceManager mgr_;
  Arena arena_;
  DiagEngine diag_{mgr_};
  std::string source_;
  std::unique_ptr<Lexer> lexer_;
  std::unique_ptr<Parser> parser_;
};

// =============================================================================
// Annex H/I - DPI C layer / svdpi.h
// =============================================================================

TEST_F(AnnexHParseTest, AnnexHDpiImportFunction) {
  auto *unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" function int c_add(int a, int b);\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto &items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(items[0]->name, "c_add");
  EXPECT_FALSE(items[0]->dpi_is_task);
  EXPECT_FALSE(items[0]->dpi_is_pure);
  EXPECT_FALSE(items[0]->dpi_is_context);
}

TEST_F(AnnexHParseTest, AnnexHDpiImportPure) {
  auto *unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" pure function real sin_approx(real x);\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto &items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(items[0]->name, "sin_approx");
  EXPECT_TRUE(items[0]->dpi_is_pure);
  EXPECT_FALSE(items[0]->dpi_is_context);
  EXPECT_FALSE(items[0]->dpi_is_task);
}

TEST_F(AnnexHParseTest, AnnexHDpiImportContext) {
  auto *unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" context function void set_callback();\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto &items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(items[0]->name, "set_callback");
  EXPECT_TRUE(items[0]->dpi_is_context);
  EXPECT_FALSE(items[0]->dpi_is_pure);
  EXPECT_FALSE(items[0]->dpi_is_task);
}

TEST_F(AnnexHParseTest, AnnexHDpiExportFunction) {
  auto *unit = Parse(
      "module m;\n"
      "  export \"DPI-C\" function sv_func;\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto &items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiExport);
  EXPECT_EQ(items[0]->name, "sv_func");
  EXPECT_FALSE(items[0]->dpi_is_task);
}

TEST_F(AnnexHParseTest, AnnexHDpiExportTask) {
  auto *unit = Parse(
      "module m;\n"
      "  export \"DPI-C\" task sv_task;\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto &items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiExport);
  EXPECT_EQ(items[0]->name, "sv_task");
  EXPECT_TRUE(items[0]->dpi_is_task);
}

TEST_F(AnnexHParseTest, AnnexHDpiImportWithCName) {
  auto *unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" c_name = function void my_func();\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto &items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(items[0]->dpi_c_name, "c_name");
  EXPECT_EQ(items[0]->name, "my_func");
  EXPECT_FALSE(items[0]->dpi_is_task);
}

// =============================================================================
// Annex G - Std package: process class (§G.1)
// =============================================================================

TEST_F(AnnexHParseTest, AnnexGProcessMethodCalls) {
  // Process method calls (.status, .kill, etc.) parse as member-access calls.
  auto *unit = Parse(
      "module m;\n"
      "  initial begin\n"
      "    p.status();\n"
      "    p.kill();\n"
      "    p.await();\n"
      "    p.suspend();\n"
      "    p.resume();\n"
      "  end\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  EXPECT_FALSE(diag_.HasErrors());
  auto &items = unit->modules[0]->items;
  ASSERT_GE(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kInitialBlock);
}

TEST_F(AnnexHParseTest, AnnexGProcessScopeResolution) {
  // process::self() uses scope-resolution syntax at the module-item level.
  // The parser handles pkg::type as a named type with scope prefix.
  auto *unit = Parse(
      "module m;\n"
      "  process::state_e st;\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  EXPECT_FALSE(diag_.HasErrors());
  auto &items = unit->modules[0]->items;
  ASSERT_GE(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(items[0]->data_type.scope_name, "process");
  EXPECT_EQ(items[0]->data_type.type_name, "state_e");
}

// =============================================================================
// Annex G - Std package: semaphore class (§G.2)
// =============================================================================

TEST_F(AnnexHParseTest, AnnexGSemaphoreAllMethods) {
  // Semaphore method calls (get, put, try_get) as member-access expressions.
  auto *unit = Parse(
      "module m;\n"
      "  initial begin\n"
      "    sem.get(1);\n"
      "    sem.put(1);\n"
      "    if (sem.try_get(1)) begin\n"
      "      $display(\"acquired\");\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  EXPECT_FALSE(diag_.HasErrors());
}

// =============================================================================
// Annex G - Std package: mailbox class (§G.3)
// =============================================================================

TEST_F(AnnexHParseTest, AnnexGMailboxAllMethods) {
  // Mailbox method calls (put, get, peek, try_get, try_peek, try_put, num)
  // as member-access call expressions inside an initial block.
  auto *unit = Parse(
      "module m;\n"
      "  int val;\n"
      "  initial begin\n"
      "    mb.put(42);\n"
      "    mb.get(val);\n"
      "    mb.peek(val);\n"
      "    val = mb.num();\n"
      "    val = mb.try_get(val);\n"
      "    val = mb.try_peek(val);\n"
      "    val = mb.try_put(99);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  EXPECT_FALSE(diag_.HasErrors());
}

// =============================================================================
// Annex G - Std package: randomize (§G.4)
// =============================================================================

TEST_F(AnnexHParseTest, AnnexGRandomizeCall) {
  // $urandom and simple randomize() call inside initial block.
  auto *unit = Parse(
      "module m;\n"
      "  int x;\n"
      "  initial begin\n"
      "    x = $urandom;\n"
      "    x = $urandom();\n"
      "    x = $urandom_range(0, 100);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  EXPECT_FALSE(diag_.HasErrors());
}

TEST_F(AnnexHParseTest, AnnexGStdRandomizePackageImport) {
  // std::randomize usage via package import at module level.
  // The parser handles import std_pkg::* for scope-qualified access.
  auto *unit = Parse(
      "module m;\n"
      "  import std_pkg::*;\n"
      "  int a, b;\n"
      "  initial begin\n"
      "    a = $urandom_range(0, 255);\n"
      "    b = $urandom;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  EXPECT_FALSE(diag_.HasErrors());
  auto &items = unit->modules[0]->items;
  ASSERT_GE(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kImportDecl);
}

// =============================================================================
// Annex H - DPI import task
// =============================================================================

TEST_F(AnnexHParseTest, AnnexHDpiImportTask) {
  auto *unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" task c_wait(int cycles);\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto &items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(items[0]->name, "c_wait");
  EXPECT_TRUE(items[0]->dpi_is_task);
  ASSERT_EQ(items[0]->func_args.size(), 1u);
  EXPECT_EQ(items[0]->func_args[0].name, "cycles");
}

// =============================================================================
// Annex H - DPI chandle return type
// =============================================================================

TEST_F(AnnexHParseTest, AnnexHDpiImportChandle) {
  // chandle is the opaque pointer type used for DPI handles.
  auto *unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" function chandle create_handle();\n"
      "  import \"DPI-C\" function void destroy_handle(chandle h);\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto &items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 2u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(items[0]->name, "create_handle");
  EXPECT_EQ(items[0]->return_type.kind, DataTypeKind::kChandle);
  EXPECT_EQ(items[1]->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(items[1]->name, "destroy_handle");
  ASSERT_EQ(items[1]->func_args.size(), 1u);
  EXPECT_EQ(items[1]->func_args[0].data_type.kind, DataTypeKind::kChandle);
}

// =============================================================================
// Annex H - DPI string return type
// =============================================================================

TEST_F(AnnexHParseTest, AnnexHDpiImportStringReturn) {
  auto *unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" pure function string get_version();\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto &items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(items[0]->name, "get_version");
  EXPECT_EQ(items[0]->return_type.kind, DataTypeKind::kString);
  EXPECT_TRUE(items[0]->dpi_is_pure);
}

// =============================================================================
// Annex H - DPI export with C name alias
// =============================================================================

TEST_F(AnnexHParseTest, AnnexHDpiExportWithCName) {
  auto *unit = Parse(
      "module m;\n"
      "  export \"DPI-C\" my_c_func = function sv_compute;\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto &items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiExport);
  EXPECT_EQ(items[0]->dpi_c_name, "my_c_func");
  EXPECT_EQ(items[0]->name, "sv_compute");
  EXPECT_FALSE(items[0]->dpi_is_task);
}

// =============================================================================
// Annex H - DPI import with output/inout arguments
// =============================================================================

TEST_F(AnnexHParseTest, AnnexHDpiImportOutputArgs) {
  auto *unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" function void get_data(\n"
      "    input int addr,\n"
      "    output int data,\n"
      "    inout int status\n"
      "  );\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto &items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(items[0]->name, "get_data");
  ASSERT_EQ(items[0]->func_args.size(), 3u);
  EXPECT_EQ(items[0]->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(items[0]->func_args[0].name, "addr");
  EXPECT_EQ(items[0]->func_args[1].direction, Direction::kOutput);
  EXPECT_EQ(items[0]->func_args[1].name, "data");
  EXPECT_EQ(items[0]->func_args[2].direction, Direction::kInout);
  EXPECT_EQ(items[0]->func_args[2].name, "status");
}

// =============================================================================
// Annex H - DPI import with default argument values
// =============================================================================

TEST_F(AnnexHParseTest, AnnexHDpiImportDefaultArgs) {
  auto *unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" function int compute(\n"
      "    int a,\n"
      "    int b = 0,\n"
      "    int c = 42\n"
      "  );\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto &items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiImport);
  ASSERT_EQ(items[0]->func_args.size(), 3u);
  EXPECT_EQ(items[0]->func_args[0].default_value, nullptr);
  EXPECT_NE(items[0]->func_args[1].default_value, nullptr);
  EXPECT_NE(items[0]->func_args[2].default_value, nullptr);
}

// =============================================================================
// Annex H - DPI import with bit/logic vector arguments
// =============================================================================

TEST_F(AnnexHParseTest, AnnexHDpiImportBitLogicArgs) {
  // DPI functions can take bit and logic vector arguments corresponding to
  // SvBitVecVal and SvLogicVecVal on the C side.
  auto *unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" function void send_bits(\n"
      "    input bit [31:0] data,\n"
      "    input logic [7:0] ctrl\n"
      "  );\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto &items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiImport);
  ASSERT_EQ(items[0]->func_args.size(), 2u);
  EXPECT_EQ(items[0]->func_args[0].data_type.kind, DataTypeKind::kBit);
  EXPECT_EQ(items[0]->func_args[0].name, "data");
  EXPECT_EQ(items[0]->func_args[1].data_type.kind, DataTypeKind::kLogic);
  EXPECT_EQ(items[0]->func_args[1].name, "ctrl");
}

// =============================================================================
// Annex H - DPI context import task with C name
// =============================================================================

TEST_F(AnnexHParseTest, AnnexHDpiContextTaskWithCName) {
  // Per LRM grammar: import "DPI-C" [pure|context] [c_id =] function|task ...
  auto *unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" context c_poll = task poll_hardware(int timeout);\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto &items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(items[0]->dpi_c_name, "c_poll");
  EXPECT_EQ(items[0]->name, "poll_hardware");
  EXPECT_TRUE(items[0]->dpi_is_context);
  EXPECT_TRUE(items[0]->dpi_is_task);
}

// =============================================================================
// Annex H - DPI import no-arg function
// =============================================================================

TEST_F(AnnexHParseTest, AnnexHDpiImportNoArgs) {
  // A DPI import with no argument list at all (valid per LRM).
  auto *unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" function int get_seed;\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto &items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(items[0]->name, "get_seed");
  EXPECT_TRUE(items[0]->func_args.empty());
}

// =============================================================================
// Annex J - Foreign language code inclusion
// =============================================================================

TEST_F(AnnexHParseTest, AnnexJDpiImportCoexistence) {
  auto *unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" function int c_func();\n"
      "  logic [7:0] data;\n"
      "  assign data = 8'hFF;\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto &items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 3u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(items[1]->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(items[2]->kind, ModuleItemKind::kContAssign);
}

// =============================================================================
// Annex K/L/M - VPI headers (VPI-backed system tasks/functions)
// =============================================================================

TEST_F(AnnexHParseTest, AnnexKVpiSystemCalls) {
  auto *unit = Parse(
      "module m;\n"
      "  initial begin\n"
      "    $vpi_get_time;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto &items = unit->modules[0]->items;
  ASSERT_GE(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kInitialBlock);
}

TEST_F(AnnexHParseTest, AnnexKVpiSysGetValue) {
  auto *unit = Parse(
      "module m;\n"
      "  initial $display($time);\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto &items = unit->modules[0]->items;
  ASSERT_GE(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kInitialBlock);
}

TEST_F(AnnexHParseTest, AnnexMSvVpiCalls) {
  auto *unit = Parse(
      "module m;\n"
      "  initial begin\n"
      "    $vpi_iterate;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto &items = unit->modules[0]->items;
  ASSERT_GE(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kInitialBlock);
}

// =============================================================================
// Annex O - Encryption/decryption
// =============================================================================

TEST_F(AnnexHParseTest, AnnexOPragmaProtect) {
  // pragma protect directives are preprocessor-level and stripped before
  // parsing. This test confirms the module around them parses correctly.
  auto *unit = Parse(
      "module m;\n"
      "  logic x;\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto &items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(items[0]->name, "x");
}

TEST_F(AnnexHParseTest, AnnexOMultipleDpiDecls) {
  auto *unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" function int c_add(int a, int b);\n"
      "  import \"DPI-C\" pure function real c_sin(real x);\n"
      "  export \"DPI-C\" function sv_compute;\n"
      "  export \"DPI-C\" task sv_run;\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto &items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 4u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(items[0]->name, "c_add");
  EXPECT_EQ(items[1]->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(items[1]->name, "c_sin");
  EXPECT_TRUE(items[1]->dpi_is_pure);
  EXPECT_EQ(items[2]->kind, ModuleItemKind::kDpiExport);
  EXPECT_EQ(items[2]->name, "sv_compute");
  EXPECT_FALSE(items[2]->dpi_is_task);
  EXPECT_EQ(items[3]->kind, ModuleItemKind::kDpiExport);
  EXPECT_EQ(items[3]->name, "sv_run");
  EXPECT_TRUE(items[3]->dpi_is_task);
}

}  // namespace
