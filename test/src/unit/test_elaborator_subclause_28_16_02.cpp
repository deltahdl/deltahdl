#include "fixture_elaborator.h"
#include "helpers_rtlir_lookup.h"

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

// §28.16.2: "Like all nets, the delay specification in a trireg net declaration
// can contain up to three delays. The first two delays shall specify the delay
// for transition to the 1 and 0 logic states when the trireg net is driven to
// these states by a driver. The third delay shall specify the charge decay time
// instead of the delay in a transition to the z logic state." "Like all nets"
// carries §28.16.1's three-valued form into each of the three slots, so a
// declaration may write a triple in every one of them and the charge decay time
// is the third triple's.
//
// The charge decay time is 8, the typical member of the third triple. §11.11
// orders the three as "minimum, typical, and maximum values -- in that order",
// and the typical member is the one elaboration can reach: nothing in
// production writes the DelayMode in src/simulator/sim_context_types.h that
// would name another, which is #3264. A decay time read off the first triple
// answers 2, one taking the third triple's minimum answers 7, and a fold that
// gives up on a triple answers 0 -- which §28.16.2.1 makes a trireg that never
// decays, the opposite of what this declaration asks for.
TEST(ChargeDecayElaboration, DecayTimeIsTheThirdTripleWhenEveryDelayIsATriple) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  trireg #(1:2:3, 4:5:6, 7:8:9) cap;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* cap = FindNet(design, "t", "cap");
  ASSERT_NE(cap, nullptr);
  EXPECT_EQ(cap->decay_ticks, 8u);
}

}  // namespace
