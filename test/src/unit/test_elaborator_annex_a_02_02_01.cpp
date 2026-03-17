#include "fixture_elaborator.h"

using namespace delta;

namespace {

// --- integer_vector_type elaboration ---

TEST(NetAndVariableTypeElaboration, LogicVariableWidth) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic [7:0] x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables.empty());
  EXPECT_EQ(mod->variables[0].width, 8u);
}

// --- integer_atom_type elaboration ---

TEST(NetAndVariableTypeElaboration, IntAtomTypeWidth) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  int x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables.empty());
  EXPECT_EQ(mod->variables[0].width, 32u);
}

// --- non_integer_type elaboration ---

TEST(NetAndVariableTypeElaboration, RealVariableElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  real r;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables.empty());
  EXPECT_TRUE(mod->variables[0].is_real);
}

// --- net_type elaboration ---

TEST(NetAndVariableTypeElaboration, WireNetElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire [3:0] w;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->nets.empty());
  EXPECT_EQ(mod->nets[0].net_type, NetType::kWire);
  EXPECT_EQ(mod->nets[0].width, 4u);
}

// --- string / chandle / event elaboration ---

TEST(NetAndVariableTypeElaboration, StringVariableElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  string s;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables.empty());
  EXPECT_TRUE(mod->variables[0].is_string);
}

TEST(NetAndVariableTypeElaboration, ChandleVariableElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  chandle h;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables.empty());
  EXPECT_TRUE(mod->variables[0].is_chandle);
}

TEST(NetAndVariableTypeElaboration, EventVariableElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  event e;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables.empty());
  EXPECT_TRUE(mod->variables[0].is_event);
}

// --- enum elaboration ---

TEST(NetAndVariableTypeElaboration, EnumRegistersMembers) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  typedef enum {A, B, C} color_t;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  EXPECT_TRUE(mod->enum_types.count("color_t"));
  EXPECT_EQ(mod->enum_types.at("color_t").size(), 3u);
}

// --- struct elaboration ---

TEST(NetAndVariableTypeElaboration, StructTypedefElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// --- signing elaboration ---

TEST(NetAndVariableTypeElaboration, SignedVariableElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic signed [7:0] x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
