#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ChargeDecayElaboration, NoDecaySpecMeansIdeal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  trireg cap;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& net : mod->nets) {
    if (net.name == "cap") {
      EXPECT_EQ(net.decay_ticks, 0u);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(ChargeDecayElaboration, ThirdDelayBecomesDecayTicks) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  trireg #(2, 4, 17) cap;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& net : mod->nets) {
    if (net.name == "cap") {
      EXPECT_EQ(net.decay_ticks, 17u);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

// §28.16.2: the third delay specifies the charge decay time, which is a
// constant expression. A literal is covered above; here the decay time is given
// as a module parameter. Elaboration must resolve the parameter in the module's
// scope (not treat the identifier as unresolvable and fall back to zero), so
// the decay ticks equal the parameter's value.
TEST(ChargeDecayElaboration, DecayTimeFromParameter) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t #(parameter int P = 21);\n"
      "  trireg #(2, 4, P) cap;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& net : mod->nets) {
    if (net.name == "cap") {
      EXPECT_EQ(net.decay_ticks, 21u);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

// §28.16.2 constant-expression input form, localparam: a localparam takes the
// same scope-resolution path as a parameter but is a distinct constant kind, so
// exercise it separately. The decay ticks equal the localparam's value.
TEST(ChargeDecayElaboration, DecayTimeFromLocalparam) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  localparam int LP = 13;\n"
      "  trireg #(2, 4, LP) cap;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& net : mod->nets) {
    if (net.name == "cap") {
      EXPECT_EQ(net.decay_ticks, 13u);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

}  // namespace
