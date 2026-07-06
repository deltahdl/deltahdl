#include "fixture_elaborator.h"

using namespace delta;

namespace {

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

TEST(NettypeElaboration, ResolutionFunctionWrongReturnTypeRejected) {
  auto sig = ConformingSig();
  sig.return_type_matches_nettype = false;
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

// §6.6.7 data-type restriction: a real (or shortreal) type is one of the
// permitted nettype data types, so a nettype declared over it elaborates
// cleanly. Driven from real source through parse + elaborate.
TEST(NettypeElaboration, RealDataTypeAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  nettype real rnt;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §6.6.7 data-type restriction: an unpacked struct is a legal fixed-size
// aggregate nettype data type, so it is accepted.
TEST(NettypeElaboration, StructDataTypeAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  typedef struct { real field1; bit field2; } T;\n"
      "  nettype T wt;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §6.6.7 data-type restriction (negative form): a string is not among the
// permitted nettype data types, so declaring a nettype over it is an error.
TEST(NettypeElaboration, StringDataTypeRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  nettype string snt;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §6.6.7 data-type restriction (negative form): a chandle is not a legal
// nettype data type.
TEST(NettypeElaboration, ChandleDataTypeRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  nettype chandle cnt;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §6.6.7 data-type restriction (negative form): an event is not a legal
// nettype data type.
TEST(NettypeElaboration, EventDataTypeRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  nettype event ent;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §6.6.7 resolution-function signature: a function with exactly one dynamic
// array input argument conforms, so a nettype naming it elaborates cleanly.
// Built from real source (the function and nettype declarations) and driven
// through parse + elaborate so the wired check observes it.
TEST(NettypeElaboration, ConformingResolutionFunctionAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  typedef struct { real field1; bit field2; } T;\n"
      "  function T Tsum(input T driver[]);\n"
      "    return driver[0];\n"
      "  endfunction\n"
      "  nettype T wt with Tsum;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §6.6.7 resolution-function signature (negative form): a resolution function
// with more than one input argument violates the single-argument requirement.
TEST(NettypeElaboration, ResolutionFunctionTwoArgumentsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  typedef struct { real field1; bit field2; } T;\n"
      "  function T Tsum(input T a[], input T b[]);\n"
      "    return a[0];\n"
      "  endfunction\n"
      "  nettype T wt with Tsum;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §6.6.7 resolution-function signature (negative form): the single input
// argument shall be a dynamic array; a fixed-size array argument is rejected.
TEST(NettypeElaboration, ResolutionFunctionFixedArrayArgumentRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  typedef struct { real field1; bit field2; } T;\n"
      "  function T Tsum(input T driver[4]);\n"
      "    return driver[0];\n"
      "  endfunction\n"
      "  nettype T wt with Tsum;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §6.6.7 resolution-function signature (negative form): the resolution function
// shall return the nettype's data type. A function returning a different named
// type than the nettype is rejected. Built from real source and driven through
// parse + elaborate.
TEST(NettypeElaboration, ResolutionFunctionMismatchedReturnTypeRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  typedef struct { real field1; bit field2; } T;\n"
      "  typedef struct { int other; } U;\n"
      "  function U Tsum(input T driver[]);\n"
      "    U u;\n"
      "    return u;\n"
      "  endfunction\n"
      "  nettype T wt with Tsum;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §6.6.7 data-type restriction: a 2-state integral type (here a packed bit
// vector) is a permitted nettype data type, so it elaborates without error.
TEST(NettypeElaboration, TwoStateIntegralDataTypeAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  nettype bit [3:0] bnt;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §6.6.7 data-type restriction: shortreal (the other floating-point form
// alongside real) is a permitted nettype data type.
TEST(NettypeElaboration, ShortrealDataTypeAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  nettype shortreal snt;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §6.6.7 data-type restriction: a fixed-size unpacked array is a permitted
// nettype data type. The array type is built from a real typedef (§6.18) and
// driven through parse + elaborate, exercising the named-type acceptance path.
TEST(NettypeElaboration, FixedUnpackedArrayDataTypeAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  typedef bit AT[4];\n"
      "  nettype AT ant;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
