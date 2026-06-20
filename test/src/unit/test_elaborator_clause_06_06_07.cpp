#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(NettypeElaboration, NettypeDeclRegistersType) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  nettype logic my_net;\n"
      "  my_net x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& n : mod->nets) {
    if (n.name == "x") found = true;
  }
  EXPECT_TRUE(found);
}

// §6.6.7: a net declared with a user-defined nettype takes on that nettype --
// the elaborated net is marked as a user nettype and records the nettype name.
TEST(NettypeElaboration, NetCarriesNettypeIdentity) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  nettype logic my_net;\n"
      "  my_net x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  const RtlirNet* net = nullptr;
  for (const auto& n : mod->nets) {
    if (n.name == "x") net = &n;
  }
  ASSERT_NE(net, nullptr);
  EXPECT_TRUE(net->is_user_nettype);
  EXPECT_EQ(net->nettype_name, "my_net");
}

// §6.6.7: a net declared with a nettype also takes on the nettype's associated
// resolution function.
TEST(NettypeElaboration, NetCarriesResolutionFunction) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  nettype logic [7:0] busnt with my_resolve;\n"
      "  busnt bus;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  const RtlirNet* net = nullptr;
  for (const auto& n : mod->nets) {
    if (n.name == "bus") net = &n;
  }
  ASSERT_NE(net, nullptr);
  EXPECT_TRUE(net->is_user_nettype);
  EXPECT_EQ(net->resolve_func, "my_resolve");
}

// §6.6.7: the second declaration form names another nettype for an existing
// one; a net of the alias resolves to the source nettype's resolution function.
TEST(NettypeElaboration, AliasNetInheritsResolutionFunction) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  nettype logic [7:0] basent with my_resolve;\n"
      "  nettype basent aliasnt;\n"
      "  aliasnt n;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  const RtlirNet* net = nullptr;
  for (const auto& nn : mod->nets) {
    if (nn.name == "n") net = &nn;
  }
  ASSERT_NE(net, nullptr);
  EXPECT_TRUE(net->is_user_nettype);
  EXPECT_EQ(net->resolve_func, "my_resolve");
}

// §6.6.7 resolution-function signature constraints, exercised through the
// production validator.
static NettypeResolutionSig ConformingSig() {
  NettypeResolutionSig sig;
  sig.return_type_matches_nettype = true;
  sig.single_input_argument = true;
  sig.argument_is_dynamic_array_of_type = true;
  sig.is_automatic = true;
  sig.is_class_method = false;
  sig.is_static_method = false;
  return sig;
}

TEST(NettypeElaboration, ResolutionFunctionConformingSignatureAccepted) {
  EXPECT_TRUE(ValidateNettypeResolutionFunction(ConformingSig()));
}

TEST(NettypeElaboration, ResolutionFunctionWrongReturnTypeRejected) {
  auto sig = ConformingSig();
  sig.return_type_matches_nettype = false;
  EXPECT_FALSE(ValidateNettypeResolutionFunction(sig));
}

TEST(NettypeElaboration, ResolutionFunctionMultipleArgumentsRejected) {
  auto sig = ConformingSig();
  sig.single_input_argument = false;
  EXPECT_FALSE(ValidateNettypeResolutionFunction(sig));
}

TEST(NettypeElaboration, ResolutionFunctionNonDynamicArrayArgumentRejected) {
  auto sig = ConformingSig();
  sig.argument_is_dynamic_array_of_type = false;
  EXPECT_FALSE(ValidateNettypeResolutionFunction(sig));
}

TEST(NettypeElaboration, ResolutionFunctionNonAutomaticRejected) {
  auto sig = ConformingSig();
  sig.is_automatic = false;
  EXPECT_FALSE(ValidateNettypeResolutionFunction(sig));
}

TEST(NettypeElaboration, ResolutionFunctionNonStaticClassMethodRejected) {
  auto sig = ConformingSig();
  sig.is_class_method = true;
  sig.is_static_method = false;
  EXPECT_FALSE(ValidateNettypeResolutionFunction(sig));
}

TEST(NettypeElaboration, ResolutionFunctionStaticClassMethodAccepted) {
  auto sig = ConformingSig();
  sig.is_class_method = true;
  sig.is_static_method = true;
  EXPECT_TRUE(ValidateNettypeResolutionFunction(sig));
}

}  // namespace
