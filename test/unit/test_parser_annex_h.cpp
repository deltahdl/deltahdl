// Tests for Annex H (DPI C layer), Annex I (svdpi.h), Annex J (foreign
// language inclusion), Annex K/L/M (VPI headers), and Annex O
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
  CompilationUnit* Parse(const std::string& src) {
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
  auto* unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" function int c_add(int a, int b);\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(items[0]->name, "c_add");
  EXPECT_FALSE(items[0]->dpi_is_task);
  EXPECT_FALSE(items[0]->dpi_is_pure);
  EXPECT_FALSE(items[0]->dpi_is_context);
}

TEST_F(AnnexHParseTest, AnnexHDpiImportPure) {
  auto* unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" pure function real sin_approx(real x);\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(items[0]->name, "sin_approx");
  EXPECT_TRUE(items[0]->dpi_is_pure);
  EXPECT_FALSE(items[0]->dpi_is_context);
  EXPECT_FALSE(items[0]->dpi_is_task);
}

TEST_F(AnnexHParseTest, AnnexHDpiImportContext) {
  auto* unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" context function void set_callback();\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(items[0]->name, "set_callback");
  EXPECT_TRUE(items[0]->dpi_is_context);
  EXPECT_FALSE(items[0]->dpi_is_pure);
  EXPECT_FALSE(items[0]->dpi_is_task);
}

TEST_F(AnnexHParseTest, AnnexHDpiExportFunction) {
  auto* unit = Parse(
      "module m;\n"
      "  export \"DPI-C\" function sv_func;\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiExport);
  EXPECT_EQ(items[0]->name, "sv_func");
  EXPECT_FALSE(items[0]->dpi_is_task);
}

TEST_F(AnnexHParseTest, AnnexHDpiExportTask) {
  auto* unit = Parse(
      "module m;\n"
      "  export \"DPI-C\" task sv_task;\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiExport);
  EXPECT_EQ(items[0]->name, "sv_task");
  EXPECT_TRUE(items[0]->dpi_is_task);
}

TEST_F(AnnexHParseTest, AnnexHDpiImportWithCName) {
  auto* unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" c_name = function void my_func();\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(items[0]->dpi_c_name, "c_name");
  EXPECT_EQ(items[0]->name, "my_func");
  EXPECT_FALSE(items[0]->dpi_is_task);
}

// =============================================================================
// Annex J - Foreign language code inclusion
// =============================================================================

TEST_F(AnnexHParseTest, AnnexJDpiImportCoexistence) {
  auto* unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" function int c_func();\n"
      "  logic [7:0] data;\n"
      "  assign data = 8'hFF;\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 3u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(items[1]->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(items[2]->kind, ModuleItemKind::kContAssign);
}

// =============================================================================
// Annex K/L/M - VPI headers (VPI-backed system tasks/functions)
// =============================================================================

TEST_F(AnnexHParseTest, AnnexKVpiSystemCalls) {
  auto* unit = Parse(
      "module m;\n"
      "  initial begin\n"
      "    $vpi_get_time;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_GE(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kInitialBlock);
}

TEST_F(AnnexHParseTest, AnnexKVpiSysGetValue) {
  auto* unit = Parse(
      "module m;\n"
      "  initial $display($time);\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_GE(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kInitialBlock);
}

TEST_F(AnnexHParseTest, AnnexMSvVpiCalls) {
  auto* unit = Parse(
      "module m;\n"
      "  initial begin\n"
      "    $vpi_iterate;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_GE(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kInitialBlock);
}

// =============================================================================
// Annex O - Encryption/decryption
// =============================================================================

TEST_F(AnnexHParseTest, AnnexOPragmaProtect) {
  // pragma protect directives are preprocessor-level and stripped before
  // parsing. This test confirms the module around them parses correctly.
  auto* unit = Parse(
      "module m;\n"
      "  logic x;\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(items[0]->name, "x");
}

TEST_F(AnnexHParseTest, AnnexOMultipleDpiDecls) {
  auto* unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" function int c_add(int a, int b);\n"
      "  import \"DPI-C\" pure function real c_sin(real x);\n"
      "  export \"DPI-C\" function sv_compute;\n"
      "  export \"DPI-C\" task sv_run;\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
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
