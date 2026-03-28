#include "fixture_elaborator.h"

using namespace delta;

namespace {

// --- R1+R2: packed width from dims before name, unpacked size from dims after ---

TEST(PackedAndUnpackedArrayElaboration, PackedAndUnpackedDims) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic [7:0] x [0:3];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& v : mod->variables) {
    if (v.name == "x") {
      found = true;
      EXPECT_EQ(v.width, 8u);
      EXPECT_EQ(v.unpacked_size, 4u);
    }
  }
  EXPECT_TRUE(found);
}

// --- R4: all four unpacked kinds elaborate with packed dims ---

TEST(PackedAndUnpackedArrayElaboration, PackedAndDynamicDims) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic [7:0] d [];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& v : mod->variables) {
    if (v.name == "d") {
      found = true;
      EXPECT_EQ(v.width, 8u);
      EXPECT_TRUE(v.is_dynamic);
    }
  }
  EXPECT_TRUE(found);
}

TEST(PackedAndUnpackedArrayElaboration, PackedAndQueueDims) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic [7:0] q [$];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& v : mod->variables) {
    if (v.name == "q") {
      found = true;
      EXPECT_EQ(v.width, 8u);
      EXPECT_TRUE(v.is_queue);
    }
  }
  EXPECT_TRUE(found);
}

TEST(PackedAndUnpackedArrayElaboration, PackedAndAssocDims) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic [7:0] a [int];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& v : mod->variables) {
    if (v.name == "a") {
      found = true;
      EXPECT_EQ(v.width, 8u);
      EXPECT_TRUE(v.is_assoc);
    }
  }
  EXPECT_TRUE(found);
}

// --- R5: unpacked arrays from any data type ---

TEST(PackedAndUnpackedArrayElaboration, UnpackedArrayOfRealType) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  real u [0:7];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& v : mod->variables) {
    if (v.name == "u") {
      found = true;
      EXPECT_TRUE(v.is_real);
      EXPECT_EQ(v.unpacked_size, 8u);
    }
  }
  EXPECT_TRUE(found);
}

TEST(PackedAndUnpackedArrayElaboration, UnpackedArrayOfStringType) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  string s [0:3];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& v : mod->variables) {
    if (v.name == "s") {
      found = true;
      EXPECT_TRUE(v.is_string);
      EXPECT_EQ(v.unpacked_size, 4u);
    }
  }
  EXPECT_TRUE(found);
}

}  // namespace
