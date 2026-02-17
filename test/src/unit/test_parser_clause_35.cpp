// Tests for §35 Direct Programming Interface (DPI)

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/parser.h"

using namespace delta;

namespace {

struct DpiParseTest : ::testing::Test {
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
// §35.3 DPI-C import declarations
// =============================================================================

TEST_F(DpiParseTest, ImportFunction) {
  auto* unit = Parse(R"(
    module m;
      import "DPI-C" function int add(input int a, input int b);
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(items[0]->name, "add");
  EXPECT_FALSE(items[0]->dpi_is_task);
  EXPECT_FALSE(items[0]->dpi_is_pure);
  EXPECT_FALSE(items[0]->dpi_is_context);
}

TEST_F(DpiParseTest, ImportTask) {
  auto* unit = Parse(R"(
    module m;
      import "DPI-C" task do_something();
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(items[0]->name, "do_something");
  EXPECT_TRUE(items[0]->dpi_is_task);
}

TEST_F(DpiParseTest, ImportWithCName) {
  auto* unit = Parse(R"(
    module m;
      import "DPI-C" c_add = function int add(input int a, input int b);
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(items[0]->dpi_c_name, "c_add");
  EXPECT_EQ(items[0]->name, "add");
}

TEST_F(DpiParseTest, ImportPureFunction) {
  auto* unit = Parse(R"(
    module m;
      import "DPI-C" pure function int get_val();
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_TRUE(items[0]->dpi_is_pure);
  EXPECT_FALSE(items[0]->dpi_is_context);
  EXPECT_EQ(items[0]->name, "get_val");
}

TEST_F(DpiParseTest, ImportContextFunction) {
  auto* unit = Parse(R"(
    module m;
      import "DPI-C" context function void set_val(input int v);
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_TRUE(items[0]->dpi_is_context);
  EXPECT_FALSE(items[0]->dpi_is_pure);
  EXPECT_EQ(items[0]->name, "set_val");
}

// =============================================================================
// §35.3 DPI-C export declarations
// =============================================================================

TEST_F(DpiParseTest, ExportFunction) {
  auto* unit = Parse(R"(
    module m;
      export "DPI-C" function my_func;
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiExport);
  EXPECT_EQ(items[0]->name, "my_func");
  EXPECT_FALSE(items[0]->dpi_is_task);
}

TEST_F(DpiParseTest, ExportTask) {
  auto* unit = Parse(R"(
    module m;
      export "DPI-C" task my_task;
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiExport);
  EXPECT_EQ(items[0]->name, "my_task");
  EXPECT_TRUE(items[0]->dpi_is_task);
}

TEST_F(DpiParseTest, ExportWithCName) {
  auto* unit = Parse(R"(
    module m;
      export "DPI-C" c_func = function sv_func;
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiExport);
  EXPECT_EQ(items[0]->dpi_c_name, "c_func");
  EXPECT_EQ(items[0]->name, "sv_func");
}

// =============================================================================
// Coexistence with package imports/exports
// =============================================================================

TEST_F(DpiParseTest, PackageImportStillWorks) {
  auto* unit = Parse(R"(
    module m;
      import pkg::*;
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kImportDecl);
}

TEST_F(DpiParseTest, DpiImportCoexistsWithPackageImport) {
  auto* unit = Parse(R"(
    module m;
      import pkg::foo;
      import "DPI-C" function int c_func();
      export "DPI-C" function sv_func;
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 3u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kImportDecl);
  EXPECT_EQ(items[1]->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(items[2]->kind, ModuleItemKind::kDpiExport);
}

// =============================================================================
// §35.2.1 Attributes on modules/instances
// =============================================================================

TEST_F(DpiParseTest, AttributeOnModuleDefinition) {
  auto* unit = Parse(R"(
    (* optimize_power *)
    module m;
      wire a;
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  EXPECT_EQ(unit->modules[0]->name, "m");
}

TEST_F(DpiParseTest, AttributeOnModuleInstantiation) {
  auto* unit = Parse(R"(
    module m;
      (* dont_touch *)
      sub u1(.a(x));
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kModuleInst);
  ASSERT_FALSE(items[0]->attrs.empty());
  EXPECT_EQ(items[0]->attrs[0].name, "dont_touch");
}

TEST_F(DpiParseTest, AttributeWithValueOnInstance) {
  auto* unit = Parse(R"(
    module m;
      (* optimize_power = 0 *)
      sub u1(.a(x));
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  ASSERT_FALSE(items[0]->attrs.empty());
  EXPECT_EQ(items[0]->attrs[0].name, "optimize_power");
  EXPECT_NE(items[0]->attrs[0].value, nullptr);
}

// =============================================================================
// §35.5 Attribute compatibility (multiple attributes)
// =============================================================================

TEST_F(DpiParseTest, MultipleAttributesOnDecl) {
  auto* unit = Parse(R"(
    module m;
      (* full_case, parallel_case *)
      wire a;
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  ASSERT_GE(items[0]->attrs.size(), 2u);
  EXPECT_EQ(items[0]->attrs[0].name, "full_case");
  EXPECT_EQ(items[0]->attrs[1].name, "parallel_case");
}

TEST_F(DpiParseTest, AttributeWithAndWithoutValue) {
  auto* unit = Parse(R"(
    module m;
      (* full_case, parallel_case = 1 *)
      wire a;
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_GE(items[0]->attrs.size(), 2u);
  EXPECT_EQ(items[0]->attrs[0].value, nullptr);
  EXPECT_NE(items[0]->attrs[1].value, nullptr);
}

}  // namespace
