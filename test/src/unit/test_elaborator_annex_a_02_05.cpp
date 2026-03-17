#include "fixture_elaborator.h"

using namespace delta;

namespace {

// --- unpacked_dimension ---

TEST(DeclarationRangeElaboration, UnpackedDimensionRangeSize) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  int arr [7:0];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& v : mod->variables) {
    if (v.name == "arr") {
      found = true;
      EXPECT_EQ(v.unpacked_size, 8u);
      EXPECT_EQ(v.unpacked_lo, 0u);
      EXPECT_TRUE(v.is_descending);
    }
  }
  EXPECT_TRUE(found);
}

TEST(DeclarationRangeElaboration, UnpackedDimensionAscendingRange) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  int arr [0:3];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& v : mod->variables) {
    if (v.name == "arr") {
      found = true;
      EXPECT_EQ(v.unpacked_size, 4u);
      EXPECT_EQ(v.unpacked_lo, 0u);
      EXPECT_FALSE(v.is_descending);
    }
  }
  EXPECT_TRUE(found);
}

TEST(DeclarationRangeElaboration, UnpackedDimensionConstantExprSize) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  int arr [4];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& v : mod->variables) {
    if (v.name == "arr") {
      found = true;
      EXPECT_EQ(v.unpacked_size, 4u);
    }
  }
  EXPECT_TRUE(found);
}

// --- packed_dimension ---

TEST(DeclarationRangeElaboration, PackedDimensionWidth) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic [7:0] x;\n"
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
    }
  }
  EXPECT_TRUE(found);
}

TEST(DeclarationRangeElaboration, PackedDimensionMultipleWidth) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic [3:0][7:0] x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& v : mod->variables) {
    if (v.name == "x") {
      found = true;
      EXPECT_EQ(v.width, 32u);
    }
  }
  EXPECT_TRUE(found);
}

// --- unsized_dimension ---

TEST(DeclarationRangeElaboration, UnsizedDimensionDynamic) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  int d[];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& v : mod->variables) {
    if (v.name == "d") {
      found = true;
      EXPECT_TRUE(v.is_dynamic);
    }
  }
  EXPECT_TRUE(found);
}

// --- queue_dimension ---

TEST(DeclarationRangeElaboration, QueueDimensionUnbounded) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  int q [$];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& v : mod->variables) {
    if (v.name == "q") {
      found = true;
      EXPECT_TRUE(v.is_queue);
      EXPECT_EQ(v.queue_max_size, -1);
    }
  }
  EXPECT_TRUE(found);
}

TEST(DeclarationRangeElaboration, QueueDimensionBounded) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  int q [$:255];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& v : mod->variables) {
    if (v.name == "q") {
      found = true;
      EXPECT_TRUE(v.is_queue);
      EXPECT_EQ(v.queue_max_size, 256);
    }
  }
  EXPECT_TRUE(found);
}

// --- associative_dimension ---

TEST(DeclarationRangeElaboration, AssociativeDimensionWildcard) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  int a [*];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& v : mod->variables) {
    if (v.name == "a") {
      found = true;
      EXPECT_TRUE(v.is_assoc);
      EXPECT_FALSE(v.is_string_index);
    }
  }
  EXPECT_TRUE(found);
}

TEST(DeclarationRangeElaboration, AssociativeDimensionStringIndex) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  int a [string];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& v : mod->variables) {
    if (v.name == "a") {
      found = true;
      EXPECT_TRUE(v.is_assoc);
      EXPECT_TRUE(v.is_string_index);
    }
  }
  EXPECT_TRUE(found);
}

TEST(DeclarationRangeElaboration, AssociativeDimensionIntIndex) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  int a [int];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& v : mod->variables) {
    if (v.name == "a") {
      found = true;
      EXPECT_TRUE(v.is_assoc);
      EXPECT_EQ(v.assoc_index_width, 32u);
    }
  }
  EXPECT_TRUE(found);
}

TEST(DeclarationRangeElaboration, AssociativeDimensionByteIndex) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  int a [byte];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& v : mod->variables) {
    if (v.name == "a") {
      found = true;
      EXPECT_TRUE(v.is_assoc);
      EXPECT_EQ(v.assoc_index_width, 8u);
    }
  }
  EXPECT_TRUE(found);
}

TEST(DeclarationRangeElaboration, AssociativeDimensionLongintIndex) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  int a [longint];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& v : mod->variables) {
    if (v.name == "a") {
      found = true;
      EXPECT_TRUE(v.is_assoc);
      EXPECT_EQ(v.assoc_index_width, 64u);
    }
  }
  EXPECT_TRUE(found);
}

// --- mixed dimensions ---

TEST(DeclarationRangeElaboration, PackedAndUnpackedDims) {
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

}  // namespace
