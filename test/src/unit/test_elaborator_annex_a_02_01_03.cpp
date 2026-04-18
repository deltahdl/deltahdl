#include "fixture_elaborator.h"

using namespace delta;

namespace {

// --- data_declaration: variable declarations elaborate into RtlirVariable ---

TEST(TypeDeclElaboration, DataDeclVariableElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic [7:0] data;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& v : mod->variables) {
    if (v.name == "data") {
      EXPECT_EQ(v.width, 8u);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(TypeDeclElaboration, DataDeclMultipleVariables) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic a, b, c;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  int count = 0;
  for (const auto& v : mod->variables) {
    if (v.name == "a" || v.name == "b" || v.name == "c") count++;
  }
  EXPECT_GE(count, 3);
}

TEST(TypeDeclElaboration, DataDeclVarPrefix) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  var logic x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& v : mod->variables) {
    if (v.name == "x") found = true;
  }
  EXPECT_TRUE(found);
}

// --- net_declaration: wire/tri/wand/wor elaborate into RtlirNet ---

TEST(TypeDeclElaboration, NetDeclWireElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire [7:0] bus;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& n : mod->nets) {
    if (n.name == "bus") {
      EXPECT_EQ(n.width, 8u);
      EXPECT_EQ(n.net_type, NetType::kWire);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(TypeDeclElaboration, NetDeclTriElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  tri t;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& n : mod->nets) {
    if (n.name == "t") {
      EXPECT_EQ(n.net_type, NetType::kTri);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(TypeDeclElaboration, NetDeclMultipleNets) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b, c;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  int count = 0;
  for (const auto& n : mod->nets) {
    if (n.name == "a" || n.name == "b" || n.name == "c") count++;
  }
  EXPECT_GE(count, 3);
}

// --- type_declaration (typedef): enum elaborates members into variables ---

TEST(TypeDeclElaboration, TypedefEnumElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  EXPECT_TRUE(mod->enum_types.count("color_t"));
  EXPECT_EQ(mod->enum_types.at("color_t").size(), 3u);
}

TEST(TypeDeclElaboration, TypedefStructRegistersType) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TypeDeclElaboration, TypedefDataTypeUsable) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  typedef logic [7:0] byte_t;\n"
      "  byte_t val;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& v : mod->variables) {
    if (v.name == "val") {
      EXPECT_EQ(v.width, 8u);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

// --- genvar_declaration ---

TEST(TypeDeclElaboration, GenvarDeclElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  genvar i;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// --- package_import_declaration ---

TEST(TypeDeclElaboration, PackageImportElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "package pkg; endpackage\n"
      "module m;\n"
      "  import pkg::*;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// --- Error conditions ---

TEST(TypeDeclElaboration, ErrorRedeclarationDetected) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic x;\n"
      "  logic x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
