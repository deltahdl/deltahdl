#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"

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
// production validator. This signature breaks no requirement §6.6.7 states.
// Each case below moves one field away from it, so the rule
// ValidateNettypeResolutionFunction returns is the rule that field carries.
static NettypeResolutionSig ConformingSig() {
  NettypeResolutionSig sig;
  sig.return_type_matches_nettype = true;
  sig.single_input_argument = true;
  sig.argument_is_input = true;
  sig.argument_is_dynamic_array = true;
  sig.argument_element_type_matches = true;
  sig.is_automatic = true;
  sig.is_class_method = false;
  sig.is_static_method = false;
  return sig;
}

// §6.6.7: "A user-defined resolution function for a net of a user-defined
// nettype with a data type T shall be a function with a return type of T and a
// single input argument whose type is a dynamic array of elements of type T."
// The case fails when ValidateNettypeResolutionFunction answers anything but
// kReturnType for a signature whose only fault is the return type.
TEST(NettypeElaboration, ResolutionFunctionWrongReturnTypeRejected) {
  auto sig = ConformingSig();
  sig.return_type_matches_nettype = false;
  EXPECT_EQ(ValidateNettypeResolutionFunction(sig),
            NettypeResolutionRule::kReturnType);
}

// §6.6.7: "A resolution function shall be automatic (or preserve no state
// information) and have no side effects." The case fails when
// ValidateNettypeResolutionFunction answers anything but kAutomaticLifetime for
// a signature whose only fault is the lifetime.
TEST(NettypeElaboration, ResolutionFunctionNonAutomaticRejected) {
  auto sig = ConformingSig();
  sig.is_automatic = false;
  EXPECT_EQ(ValidateNettypeResolutionFunction(sig),
            NettypeResolutionRule::kAutomaticLifetime);
}

// §6.6.7: "While a class function method may be used for a resolution function,
// such functions shall be class static methods as the method call occurs in a
// context where no class object is involved in the call." The case fails when
// ValidateNettypeResolutionFunction answers anything but kClassStaticMethod for
// a class method that is not static.
TEST(NettypeElaboration, ResolutionFunctionNonStaticClassMethodRejected) {
  auto sig = ConformingSig();
  sig.is_class_method = true;
  sig.is_static_method = false;
  EXPECT_EQ(ValidateNettypeResolutionFunction(sig),
            NettypeResolutionRule::kClassStaticMethod);
}

// §6.6.7 admits the class method that is static: "While a class function method
// may be used for a resolution function, such functions shall be class static
// methods". The case fails when ValidateNettypeResolutionFunction names any
// rule broken by a static class method conforming in every other field.
TEST(NettypeElaboration, ResolutionFunctionStaticClassMethodAccepted) {
  auto sig = ConformingSig();
  sig.is_class_method = true;
  sig.is_static_method = true;
  EXPECT_EQ(ValidateNettypeResolutionFunction(sig),
            NettypeResolutionRule::kConforming);
}

// §6.6.7: "While a class function method may be used for a resolution function,
// such functions shall be class static methods as the method call occurs in a
// context where no class object is involved in the call." The case fails unless
// the run reports "shall be a static class method" at line 7, the `nettype`
// declaration, under §6.6.7. Driven from source through parse + elaborate,
// where ResolutionFunctionNonStaticClassMethodRejected above hands
// ValidateNettypeResolutionFunction the two flags directly: this one asserts
// that `with C::res` reaches the class method the source named, and `res`
// breaks no other requirement §6.6.7 states, so the class-static rule is the
// one left to report.
TEST(NettypeElaboration, NonStaticClassMethodResolutionFunctionIsRejected) {
  ElabFixture f;
  Elaborate(
      "class C;\n"
      "  function logic [7:0] res(input logic [7:0] driver[]);\n"
      "    return driver[0];\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  nettype logic [7:0] wt with C::res;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "resolution function 'res' of user-defined nettype "
                            "'wt' shall be a static class method",
                            7, "6.6.7"));
}

// §6.6.7 admits the class method that is static, so the same source with
// `static` on `res` breaks nothing the clause states. The case fails when the
// run reports any error, and it is what stops
// NonStaticClassMethodResolutionFunctionIsRejected from passing on a source the
// elaborator would reject whether `res` were static or not.
TEST(NettypeElaboration, StaticClassMethodResolutionFunctionIsAccepted) {
  ElabFixture f;
  Elaborate(
      "class C;\n"
      "  static function logic [7:0] res(input logic [7:0] driver[]);\n"
      "    return driver[0];\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  nettype logic [7:0] wt with C::res;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §6.6.7's Syntax 6-1 writes the with clause as `with [ package_scope |
// class_scope ] tf_identifier`, so a qualifier that names neither a package nor
// a class names no resolution function at all. The case fails unless the run
// reports "names unknown package or class 'Nope'" at line 2, the `nettype`
// declaration, under §6.6.7.
TEST(NettypeElaboration,
     ResolutionFunctionScopeNamingNeitherPackageNorClassRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  nettype logic [7:0] wt with Nope::res;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "resolution function of user-defined nettype 'wt' "
                            "names unknown package or class 'Nope'",
                            2, "6.6.7"));
}

// §6.6.7: a qualifier reaching a class that declares no function of that name
// is a different mistake from a qualifier reaching nothing, and draws its own
// report. The case fails unless the run reports "'C::missing' ... does not
// exist" at line 7, the `nettype` declaration, under §6.6.7.
TEST(NettypeElaboration, ClassResolutionFunctionMissingFromItsClassRejected) {
  ElabFixture f;
  Elaborate(
      "class C;\n"
      "  static function logic [7:0] res(input logic [7:0] driver[]);\n"
      "    return driver[0];\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  nettype logic [7:0] wt with C::missing;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "resolution function 'C::missing' of user-defined "
                            "nettype 'wt' does not exist",
                            7, "6.6.7"));
}

// §6.6.7: a net of a nettype declared `with C::res` resolves through the class
// method the with clause named, and not through a module-level function that
// happens to share the bare name `res`. Both functions here conform to §6.6.7,
// so nothing but the qualifier distinguishes them, and the case fails unless
// the elaborated net's resolution function is 'C::res'. It is what the net
// carries into the simulator, so binding the wrong one costs a wrong
// simulation rather than a missing report.
TEST(NettypeElaboration,
     QualifiedResolutionFunctionDoesNotBindAnUnrelatedPlainFunction) {
  ElabFixture f;
  auto* design = Elaborate(
      "class C;\n"
      "  static function logic [7:0] res(input logic [7:0] driver[]);\n"
      "    return driver[0];\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  function logic [7:0] res(input logic [7:0] driver[]);\n"
      "    return driver[0];\n"
      "  endfunction\n"
      "  nettype logic [7:0] wt with C::res;\n"
      "  wt n;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const RtlirNet* net = FindNet(design, "m", "n");
  ASSERT_NE(net, nullptr);
  EXPECT_EQ(net->resolve_func, "C::res");
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "data type of user-defined nettype 'snt' is not a "
                            "legal nettype data type",
                            2, "6.6.7"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "data type of user-defined nettype 'cnt' is not a "
                            "legal nettype data type",
                            2, "6.6.7"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "data type of user-defined nettype 'ent' is not a "
                            "legal nettype data type",
                            2, "6.6.7"));
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

// §6.6.7 requires "a single input argument", and Tsum here takes two. The case
// fails unless the run reports "shall take a single input argument" at line 6,
// the `nettype` declaration, under §6.6.7. No other §6.6.7 report ends there:
// the argument-direction report continues "and this one is not declared input".
TEST(NettypeElaboration, ResolutionFunctionArgumentCountNamesItsOwnRule) {
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "shall take a single input argument", 6, "6.6.7"));
}

// §6.6.7 requires a resolution function for a nettype with data type T to "be a
// function with a return type of T", and Tsum here returns U. The case fails
// unless the run reports "shall have a return type of 'T'" at line 8, the
// `nettype` declaration, under §6.6.7.
TEST(NettypeElaboration, ResolutionFunctionReturnTypeNamesItsOwnRule) {
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "shall have a return type of 'T'", 8, "6.6.7"));
}

// §6.6.7 requires the argument's "type is a dynamic array of elements of type
// T", and `input T driver[4]` is a fixed-size array. The case fails unless the
// run reports "a dynamic array rather than a fixed-size array" at line 6, the
// `nettype` declaration, under §6.6.7.
TEST(NettypeElaboration,
     ResolutionFunctionDynamicArrayArgumentNamesItsOwnRule) {
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a dynamic array rather than a fixed-size array", 6,
                            "6.6.7"));
}

// §6.6.7 admits "a single input argument", so an `output` argument breaks the
// clause even though the count is right. The case fails unless the run reports
// "and this one is not declared input" at line 6, the `nettype` declaration,
// under §6.6.7.
TEST(NettypeElaboration, ResolutionFunctionOutputArgumentRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  typedef struct { real field1; bit field2; } T;\n"
      "  function T Tsum(output T driver[]);\n"
      "    return driver[0];\n"
      "  endfunction\n"
      "  nettype T wt with Tsum;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "and this one is not declared input", 6, "6.6.7"));
}

// §6.6.7 admits "a single input argument", so a `ref` argument breaks the
// clause as an `output` one does. The case fails unless the run reports "and
// this one is not declared input" at line 6, the `nettype` declaration, under
// §6.6.7.
TEST(NettypeElaboration, ResolutionFunctionRefArgumentRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  typedef struct { real field1; bit field2; } T;\n"
      "  function T Tsum(ref T driver[]);\n"
      "    return driver[0];\n"
      "  endfunction\n"
      "  nettype T wt with Tsum;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "and this one is not declared input", 6, "6.6.7"));
}

// §6.6.7 requires the argument to be "a dynamic array of elements of type T",
// and Tsum here takes a dynamic array of U against a nettype whose data type is
// T. The case fails unless the run reports "dynamic array of elements of type
// 'T'" at line 8, the `nettype` declaration, under §6.6.7.
TEST(NettypeElaboration,
     ResolutionFunctionArgumentElementTypeMismatchRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  typedef struct { real field1; bit field2; } T;\n"
      "  typedef struct { int other; } U;\n"
      "  function T Tsum(input U driver[]);\n"
      "    T t;\n"
      "    return t;\n"
      "  endfunction\n"
      "  nettype T wt with Tsum;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "dynamic array of elements of type 'T'", 8,
                            "6.6.7"));
}

// §6.6.7's own example declares `function automatic T Tsum (input T driver[]);`
// beside a nettype whose data type is T, which breaks none of the clause's
// requirements. The case fails when the elaborator reports any §6.6.7 rule
// against a signature that breaks none of them.
TEST(NettypeElaboration, ConformingResolutionFunctionStillAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  typedef struct { real field1; bit field2; } T;\n"
      "  function automatic T Tsum(input T driver[]);\n"
      "    return driver[0];\n"
      "  endfunction\n"
      "  nettype T wt with Tsum;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
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
