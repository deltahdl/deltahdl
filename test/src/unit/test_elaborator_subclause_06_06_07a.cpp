#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"

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

// §6.6.7: the resolution function of a user-defined nettype over data type T
// returns T and takes one input argument, a dynamic array of T elements. The
// case fails when ValidateNettypeResolutionFunction answers anything but
// kReturnType for a signature whose only fault is the return type.
TEST(NettypeElaboration, ResolutionFunctionWrongReturnTypeRejected) {
  auto sig = ConformingSig();
  sig.return_type_matches_nettype = false;
  EXPECT_EQ(ValidateNettypeResolutionFunction(sig),
            NettypeResolutionRule::kReturnType);
}

// §6.6.7: a resolution function is automatic, or keeps no state, and has no
// side effects. The case fails when ValidateNettypeResolutionFunction answers
// anything but kAutomaticLifetime for a signature whose only fault is the
// lifetime.
TEST(NettypeElaboration, ResolutionFunctionNonAutomaticRejected) {
  auto sig = ConformingSig();
  sig.is_automatic = false;
  EXPECT_EQ(ValidateNettypeResolutionFunction(sig),
            NettypeResolutionRule::kAutomaticLifetime);
}

// §6.6.7: a class function method may serve as a resolution function only if it
// is static, since the call happens with no class object involved. The case
// fails when ValidateNettypeResolutionFunction answers anything but
// kClassStaticMethod for a class method that is not static.
TEST(NettypeElaboration, ResolutionFunctionNonStaticClassMethodRejected) {
  auto sig = ConformingSig();
  sig.is_class_method = true;
  sig.is_static_method = false;
  EXPECT_EQ(ValidateNettypeResolutionFunction(sig),
            NettypeResolutionRule::kClassStaticMethod);
}

// §6.6.7 admits the class method that is static, a class function method
// serving as a resolution function only when static. The case fails when
// ValidateNettypeResolutionFunction names any rule broken by a static class
// method conforming in every other field.
TEST(NettypeElaboration, ResolutionFunctionStaticClassMethodAccepted) {
  auto sig = ConformingSig();
  sig.is_class_method = true;
  sig.is_static_method = true;
  EXPECT_EQ(ValidateNettypeResolutionFunction(sig),
            NettypeResolutionRule::kConforming);
}

// §6.6.7: a class function method may serve as a resolution function only if it
// is static, since the call happens with no class object involved. The case
// fails unless the run reports "shall be a static class method" at line 7, the
// `nettype` declaration, under §6.6.7. Driven from source through parse +
// elaborate, where ResolutionFunctionNonStaticClassMethodRejected above hands
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

// §6.6.7 requires exactly one input argument, and Tsum here takes two. The case
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

// §6.6.7 requires a resolution function for a nettype with data type T to
// return T, and Tsum here returns U. The case fails unless the run reports
// "shall have a return type of 'T'" at line 8, the `nettype` declaration, under
// §6.6.7.
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

// §6.6.7 requires the argument to be a dynamic array of T elements, and
// `input T driver[4]` is a fixed-size array. The case fails unless the run
// reports "a dynamic array rather than a fixed-size array" at line 6, the
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

// §6.6.7 admits exactly one input argument, so an `output` argument breaks the
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

// §6.6.7 admits exactly one input argument, so a `ref` argument breaks the
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

// §6.6.7 requires the argument to be a dynamic array of T elements, and Tsum
// here takes a dynamic array of U against a nettype whose data type is T. The
// case fails unless the run reports "dynamic array argument whose elements are
// of type 'T'" at line 8, the `nettype` declaration, under §6.6.7.
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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "dynamic array argument whose elements are of type 'T'", 8, "6.6.7"));
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

// §6.6.7's own example scopes a resolution function by a typedef of a class
// specialization, `typedef Base#(32) MyBaseT;` and `with MyBaseT::Ssum`, so
// the typedef names the class whose static function resolves the net and no
// scope is reported unknown.
TEST(NettypeElaboration, ResolutionFunctionScopedByATypedefOfASpecialization) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  class Base #(parameter p = 1);\n"
             "    typedef struct { real r; bit [p-1:0] data; } S;\n"
             "    static function S Ssum(input S driver[]);\n"
             "      Ssum.r = 0.0;\n"
             "    endfunction\n"
             "  endclass\n"
             "  typedef Base#(32) MyBaseT;\n"
             "  nettype MyBaseT::S narrowTsum with MyBaseT::Ssum;\n"
             "  typedef MyBaseT alias_t;\n"
             "  nettype alias_t::S aliasTsum with alias_t::Ssum;\n"
             "endmodule\n"));
}

// The typedef still has to lead to a class declaring the function: one naming
// a class without it is reported as a missing function, not an unknown scope.
TEST(NettypeElaboration, ResolutionFunctionMissingFromATypedefsClassReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  class Base #(parameter p = 1);\n"
      "    typedef struct { real r; bit [p-1:0] data; } S;\n"
      "  endclass\n"
      "  typedef Base#(32) MyBaseT;\n"
      "  nettype MyBaseT::S narrowTsum with MyBaseT::Ssum;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "resolution function 'MyBaseT::Ssum' of "
                            "user-defined nettype 'narrowTsum' does not exist",
                            6, "6.6.7"));
}

// §6.6.7 with §3.12.1: a nettype declaration is a net declaration, which a
// compilation unit may hold as a package may (A.1.2, A.1.11, A.2.1.3), and
// the modules after it declare nets of its type.
constexpr const char* kCompilationUnitNettype =
    "nettype logic mynet;\n"
    "module top; mynet n; endmodule\n";

TEST(NettypeElaboration, ACompilationUnitNettypeIsDeclared) {
  ElabFixture f;
  auto* design = Elaborate(kCompilationUnitNettype, f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NettypeElaboration, ANetOfACompilationUnitNettypeCarriesIt) {
  ElabFixture f;
  auto* design = Elaborate(kCompilationUnitNettype, f);
  ASSERT_NE(design, nullptr);
  const RtlirNet* net = nullptr;
  for (const auto& n : design->top_modules[0]->nets) {
    if (n.name == "n") net = &n;
  }
  ASSERT_NE(net, nullptr);
  EXPECT_EQ(net->nettype_name, "mynet");
}

// §6.6.7 with §6.18: a nettype or typedef name stands for the type it was
// declared with, so a chain of names is followed to the packed vector type at
// its end, whose range a net of the first name takes. A name the table does
// not hold, a name for an enumeration or for a type with no packed dimension,
// and a chain with no end stand for none.
TEST(NettypeElaboration, NamedPackedVectorTypeFollowsAChainOfNames) {
  Arena arena;
  Expr left;
  Expr right;
  DataType vector;
  vector.kind = DataTypeKind::kLogic;
  vector.packed_dim_left = &left;
  vector.packed_dim_right = &right;
  DataType to_vector;
  to_vector.kind = DataTypeKind::kNamed;
  to_vector.type_name = "vec_net";
  DataType integer;
  integer.kind = DataTypeKind::kInteger;
  DataType enumeration;
  enumeration.kind = DataTypeKind::kEnum;
  enumeration.packed_dim_left = &left;
  enumeration.packed_dim_right = &right;
  DataType to_b;
  to_b.kind = DataTypeKind::kNamed;
  to_b.type_name = "b_t";
  DataType to_a;
  to_a.kind = DataTypeKind::kNamed;
  to_a.type_name = "a_t";
  const TypedefMap kTable{{"vec_net", vector},  {"alias_t", to_vector},
                          {"int_net", integer}, {"enum_t", enumeration},
                          {"a_t", to_b},        {"b_t", to_a}};

  DataType written;
  written.kind = DataTypeKind::kNamed;
  written.type_name = "alias_t";
  const DataType* found = NamedPackedVectorType(written, kTable, arena);
  ASSERT_NE(found, nullptr);
  EXPECT_EQ(found->packed_dim_left, &left);
  EXPECT_EQ(found->packed_dim_right, &right);

  written.type_name = "int_net";
  EXPECT_EQ(NamedPackedVectorType(written, kTable, arena), nullptr);
  written.type_name = "enum_t";
  EXPECT_EQ(NamedPackedVectorType(written, kTable, arena), nullptr);
  written.type_name = "missing_t";
  EXPECT_EQ(NamedPackedVectorType(written, kTable, arena), nullptr);
  EXPECT_EQ(NamedPackedVectorType(to_a, kTable, arena), nullptr);
}

// --- The data type a nettype resolves to (§6.6.7 items a to d) ---
// The rule judges a type, so a typedef name is judged as what it stands for, an
// array by whether it is fixed-size and by its element, and an unpacked
// structure member by member.

void ExpectIllegalNettypeDataType(const std::string& body) {
  ElabFixture f;
  const std::string kSrc =
      "module m;\n" + body + "  nettype bad_t n;\nendmodule\n";
  Elaborate(kSrc, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "data type of user-defined nettype 'n' is not a "
                            "legal nettype data type",
                            LineHolding(kSrc, "nettype bad_t"), "6.6.7"));
}

TEST(NettypeElaboration, TypedefOfAStringDataTypeRejected) {
  ExpectIllegalNettypeDataType("  typedef string bad_t;\n");
}

TEST(NettypeElaboration, TypedefOfAClassDataTypeRejected) {
  ExpectIllegalNettypeDataType(
      "  class C; endclass\n"
      "  typedef C bad_t;\n");
}

TEST(NettypeElaboration, TypedefOfADynamicArrayDataTypeRejected) {
  ExpectIllegalNettypeDataType("  typedef logic [3:0] bad_t[];\n");
}

TEST(NettypeElaboration, TypedefOfAQueueOfRealDataTypeRejected) {
  ExpectIllegalNettypeDataType("  typedef real bad_t[$];\n");
}

TEST(NettypeElaboration, UnpackedStructWithAStringMemberDataTypeRejected) {
  ExpectIllegalNettypeDataType(
      "  typedef struct { real r; string s; } bad_t;\n");
}

// Item d asks of each element that it be fixed-size, so a member that is a
// queue makes the structure illegal even though its element type is real.
TEST(NettypeElaboration, UnpackedStructWithAQueueMemberDataTypeRejected) {
  ExpectIllegalNettypeDataType("  typedef struct { real r[$]; } bad_t;\n");
}

// void and a virtual interface name no value at all, and neither is among
// items a to d.
TEST(NettypeElaboration, VoidDataTypeRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  nettype void vn;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "data type of user-defined nettype 'vn' is not a "
                            "legal nettype data type",
                            2, "6.6.7"));
}

TEST(NettypeElaboration, VirtualInterfaceDataTypeRejected) {
  ElabFixture f;
  Elaborate(
      "interface I; endinterface\n"
      "module m;\n"
      "  nettype virtual I vn;\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "data type of user-defined nettype 'vn' is not a "
                            "legal nettype data type",
                            3, "6.6.7"));
}

// A class named directly is a data type too, and no more a legal one.
TEST(NettypeElaboration, ClassDataTypeRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  class C; endclass\n"
      "  nettype C cn;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "data type of user-defined nettype 'cn' is not a "
                            "legal nettype data type",
                            3, "6.6.7"));
}

// The counterpart: a fixed-size array of an unpacked structure whose members
// are real and 2-state integral is item d applied twice over, and an alias of
// the nettype names a nettype rather than a data type.
TEST(NettypeElaboration, FixedArrayOfARealAndTwoStateStructDataTypeAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  typedef struct { real r; bit [3:0] b; struct { shortreal s; } n; } "
      "ok_t;\n"
      "  typedef ok_t ok_arr_t[2];\n"
      "  nettype ok_arr_t n5;\n"
      "  nettype n5 n6;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
